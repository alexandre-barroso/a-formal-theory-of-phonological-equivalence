from __future__ import annotations

import argparse
import hashlib
import json
import math
import platform
from dataclasses import dataclass
from pathlib import Path
from typing import Sequence

import numpy as np
from scipy.optimize import minimize
from scipy.special import gammaln

import uyghur_hu_gradient_check_v1 as gradient_check
import uyghur_hu_newton_polish_v1 as newton_polish
import uyghur_hu_regularized_v1 as regularized
from statistical_protocol_v2 import HUGLMMFit, HU_COLUMNS, hu_design_diagnostics, hu_glmm_gate


FROZEN_V2_SHA256 = "9428d7f030f31f3ac2122806bad36d3cc3641399bec4b5a12ad031d54af977fd"
DEPENDENCY_HASHES = {
    "uyghur_laplace_vectorized_v3.py": "f184822f46f8c92e344cf003aeea142a6cd00d51b824b3e644271f10e7c0c519",
    "uyghur_gh_vectorized_v3.py": "b1aeeb8741a28f81277c91034a7910594215e51a17dddf4105ba141e9f566f73",
    "uyghur_gh_gradient_v3.py": "cd1c784b02cc3060b9280b92ea81d56e27bfaa36c9b166dee3c226016fd55a71",
    "uyghur_hu_gradient_check_v1.py": "10bd3dbb02c16189e438d255a9a648324396d745a8d04123bf3b009c0c815ca0",
    "uyghur_laplace_hessian_v1.py": "b76f02dcf9891024377fe16d22dce0d0aa02340bf641a026480144537d781552",
    "uyghur_hu_newton_polish_v1.py": "e00f084b963d90466a621923e5d554c335c3b1531de2005281ac8b504c96314a",
    "uyghur_hu_regularized_v1.py": "75487a3cba8fd63502e9f029c5eace411964d4f2dc9ff222f59aeaaa0ca7ff26",
}
ALLOWED_TAUS = (20.0, 50.0)
START_SIGMAS = (0.1, 0.5, 2.0)
LOWER_LOG_SIGMA = -8.0
UPPER_LOG_SIGMA = math.log(20.0)


@dataclass(frozen=True)
class RegularizedHUGLMMFit(HUGLMMFit):
    tau: float
    data_negative_log_likelihood: float
    gaussian_penalty: float
    unpenalized_gradient: tuple[float, ...]
    unpenalized_projected_gradient_max_abs: float
    selected_start_sigma: float
    selected_controlled_gradient_check: dict[str, object]
    optimization_attempts: tuple[dict[str, object], ...]
    rank_revealing_active_columns: tuple[str, ...]
    rank_revealing_dependent_columns: tuple[str, ...]
    fixed_effect_coordinates_fitted: int
    prior_normalizing_constant_omitted: bool


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate_dependencies() -> None:
    here = Path(__file__).resolve().parent
    if sha256(here / "statistical_protocol_v2.py") != FROZEN_V2_SHA256:
        raise RuntimeError("frozen v2 hash mismatch")
    for name, expected in DEPENDENCY_HASHES.items():
        if sha256(here / name) != expected:
            raise RuntimeError(f"dependency hash mismatch: {name}")


def validate_tau(tau: float) -> float:
    value = float(tau)
    if value not in ALLOWED_TAUS:
        raise ValueError(f"tau must be one of {ALLOWED_TAUS}")
    return value


def log_choose(successes: np.ndarray, totals: np.ndarray) -> np.ndarray:
    return gammaln(totals + 1.0) - gammaln(successes + 1.0) - gammaln(totals - successes + 1.0)


def aggregate_identical_root_rows(
    X: np.ndarray,
    successes: Sequence[float],
    totals: Sequence[float],
    root_ids: Sequence[str],
) -> tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray, float]:
    X = np.asarray(X, dtype=float)
    y = np.asarray(successes, dtype=float)
    n = np.asarray(totals, dtype=float)
    roots = np.asarray(root_ids, dtype=object)
    if X.ndim != 2 or X.shape[0] != len(y) or y.shape != n.shape or roots.shape != y.shape:
        raise ValueError("invalid HU aggregation dimensions")
    if np.any(~np.isfinite(X)) or np.any(~np.isfinite(y)) or np.any(~np.isfinite(n)):
        raise ValueError("HU aggregation inputs must be finite")
    if np.any(y < 0) or np.any(n < 0) or np.any(y > n):
        raise ValueError("require 0 <= successes <= totals")

    names, inverse = np.unique(roots, return_inverse=True)
    aggregate_X, aggregate_y, aggregate_n = [], [], []
    original_constants = 0.0
    aggregate_constants = 0.0
    for index, name in enumerate(names):
        rows = np.flatnonzero(inverse == index)
        reference = X[rows[0]]
        if any(not np.array_equal(X[row], reference) for row in rows[1:]):
            raise ValueError(f"root {name!r} has nonidentical HU covariate rows")
        root_y = float(y[rows].sum())
        root_n = float(n[rows].sum())
        aggregate_X.append(reference)
        aggregate_y.append(root_y)
        aggregate_n.append(root_n)
        original_constants += float(log_choose(y[rows], n[rows]).sum())
        aggregate_constants += float(log_choose(np.array([root_y]), np.array([root_n]))[0])
    return (
        np.asarray(aggregate_X, dtype=float),
        np.asarray(aggregate_y, dtype=float),
        np.asarray(aggregate_n, dtype=float),
        names,
        float(aggregate_constants - original_constants),
    )


def projected_gradient(theta: np.ndarray, gradient: np.ndarray) -> np.ndarray:
    projected = np.asarray(gradient, dtype=float).copy()
    if theta[-1] <= LOWER_LOG_SIGMA + 1e-8:
        projected[-1] = min(projected[-1], 0.0)
    elif theta[-1] >= UPPER_LOG_SIGMA - 1e-8:
        projected[-1] = max(projected[-1], 0.0)
    return projected


def result_stage(result: object) -> dict[str, object]:
    theta = np.asarray(result.x, dtype=float)
    analytic = np.asarray(result.jac, dtype=float)
    raw_status = getattr(result, "status", None)
    return {
        "success": bool(result.success),
        "status": None if raw_status is None else int(raw_status),
        "message": str(result.message),
        "iterations": int(result.nit),
        "objective": float(result.fun),
        "theta_native": theta.tolist(),
        "penalized_analytic_gradient_native": analytic.tolist(),
        "penalized_projected_gradient_native_max_abs": float(
            np.max(np.abs(projected_gradient(theta, analytic)))
        ),
        "all_finite": bool(
            np.all(np.isfinite(theta))
            and np.all(np.isfinite(analytic))
            and math.isfinite(float(result.fun))
        ),
    }


def fit_native_regularized(
    aggregate_X: np.ndarray,
    y: np.ndarray,
    n: np.ndarray,
    column_names: Sequence[str],
    approximation: str,
    tau: float,
    objective_adjustment: float,
) -> RegularizedHUGLMMFit:
    tau = validate_tau(tau)
    if aggregate_X.shape[1] != len(HU_COLUMNS) or tuple(column_names) != tuple(HU_COLUMNS):
        raise ValueError("regularized HU fitting requires all eleven native source columns in order")
    diagnostics = hu_design_diagnostics(aggregate_X, column_names)
    if approximation == "laplace":
        approximation_name = "laplace"
    elif approximation == "gh":
        approximation_name = "gh80"
    else:
        raise ValueError("approximation must be laplace or gh")
    objective_gradient = lambda theta: regularized.objective_gradient(
        theta, aggregate_X, y, n, tau, approximation_name,
    )
    hessian = lambda theta: regularized.hessian(
        theta, aggregate_X, y, n, tau, approximation_name,
    )
    bounds = [(None, None)] * len(HU_COLUMNS) + [(LOWER_LOG_SIGMA, UPPER_LOG_SIGMA)]
    attempts: list[dict[str, object]] = []
    results: list[dict[str, object]] = []
    for initial_sigma in START_SIGMAS:
        initial = np.zeros(len(HU_COLUMNS) + 1)
        initial[-1] = math.log(initial_sigma)
        lbfgs = minimize(
            lambda theta: objective_gradient(theta),
            initial,
            jac=True,
            method="L-BFGS-B",
            bounds=bounds,
            options={"maxiter": 2000, "ftol": 1e-12, "gtol": 1e-7, "maxls": 50},
        )
        polished = newton_polish.polish(lbfgs.x, objective_gradient, hessian)
        objective, penalized_gradient = objective_gradient(polished.x)
        components = regularized.components(
            polished.x, aggregate_X, y, n, tau, approximation_name,
        )
        unpenalized_gradient = np.asarray(components["unpenalized_gradient"], dtype=float)
        try:
            controlled = gradient_check.check_gradient(
                lambda theta: objective_gradient(theta)[0],
                polished.x,
                penalized_gradient,
                aggregate_X,
            )
        except RuntimeError as error:
            controlled = {"passed": False, "error": str(error)}
        penalized_projected = projected_gradient(polished.x, penalized_gradient)
        unpenalized_projected = projected_gradient(polished.x, unpenalized_gradient)
        component_error = abs(
            float(objective)
            - float(components["data_negative_log_likelihood"])
            - float(components["gaussian_penalty"])
        )
        record = {
            "initial_sigma": initial_sigma,
            "lbfgsb": result_stage(lbfgs),
            "polish": {**result_stage(polished), "history": polished.polish_history},
            "theta_native": np.asarray(polished.x, dtype=float).tolist(),
            "sigma": math.exp(float(polished.x[-1])),
            "distance_from_lower_log_sigma_bound": float(polished.x[-1] - LOWER_LOG_SIGMA),
            "distance_from_upper_log_sigma_bound": float(UPPER_LOG_SIGMA - polished.x[-1]),
            "penalized_objective_aggregated": float(objective),
            "data_negative_log_likelihood_aggregated": float(components["data_negative_log_likelihood"]),
            "gaussian_penalty": float(components["gaussian_penalty"]),
            "component_identity_abs_error": component_error,
            "penalized_gradient_native": np.asarray(penalized_gradient, dtype=float).tolist(),
            "unpenalized_gradient_native": unpenalized_gradient.tolist(),
            "penalized_projected_gradient_native_max_abs": float(np.max(np.abs(penalized_projected))),
            "unpenalized_projected_gradient_native_max_abs": float(np.max(np.abs(unpenalized_projected))),
            "controlled_penalized_gradient_check_native": controlled,
        }
        attempts.append(record)
        results.append({
            "initial_sigma": initial_sigma,
            "lbfgs": lbfgs,
            "polished": polished,
            "objective": float(objective),
            "components": components,
            "penalized_gradient": np.asarray(penalized_gradient, dtype=float),
            "unpenalized_gradient": unpenalized_gradient,
            "penalized_projected": penalized_projected,
            "unpenalized_projected": unpenalized_projected,
            "controlled": controlled,
            "component_error": component_error,
        })

    selected = min(results, key=lambda item: item["objective"])
    all_attempts_valid = all(
        item["polished"].success
        and item["controlled"].get("passed", False)
        and item["component_error"] <= 1e-10
        and float(np.max(np.abs(item["penalized_projected"]))) <= 5e-3
        and np.all(np.isfinite(item["lbfgs"].x))
        and np.all(np.isfinite(item["lbfgs"].jac))
        and math.isfinite(float(item["lbfgs"].fun))
        and np.all(np.isfinite(item["polished"].x))
        and np.all(np.isfinite(item["penalized_gradient"]))
        and np.all(np.isfinite(item["unpenalized_gradient"]))
        and math.isfinite(float(item["components"]["data_negative_log_likelihood"]))
        and math.isfinite(float(item["components"]["gaussian_penalty"]))
        and math.isfinite(item["objective"])
        for item in results
    )
    selected_components = selected["components"]
    method = (
        "laplace_native11_gaussian_map_lbfgsb_newton_one_row_per_root"
        if approximation == "laplace"
        else "gh80_native11_gaussian_map_lbfgsb_newton_one_row_per_root"
    )
    return RegularizedHUGLMMFit(
        beta=tuple(map(float, selected["polished"].x[:-1])),
        sigma=math.exp(float(selected["polished"].x[-1])),
        objective=float(selected["objective"] + objective_adjustment),
        method=method,
        quadrature_nodes=1 if approximation == "laplace" else 80,
        converged=bool(all_attempts_valid),
        iterations=int(selected["lbfgs"].nit + selected["polished"].nit),
        design_rank=int(diagnostics["rank"]),
        active_columns=tuple(column_names),
        dropped_columns=(),
        constant_columns=tuple(diagnostics["constant_columns"]),
        projected_gradient_max_abs=float(np.max(np.abs(selected["penalized_projected"]))),
        multistart_objectives=tuple(
            float(item["objective"] + objective_adjustment) for item in results
        ),
        tau=tau,
        data_negative_log_likelihood=float(
            selected_components["data_negative_log_likelihood"] + objective_adjustment
        ),
        gaussian_penalty=float(selected_components["gaussian_penalty"]),
        unpenalized_gradient=tuple(map(float, selected["unpenalized_gradient"])),
        unpenalized_projected_gradient_max_abs=float(
            np.max(np.abs(selected["unpenalized_projected"]))
        ),
        selected_start_sigma=float(selected["initial_sigma"]),
        selected_controlled_gradient_check=selected["controlled"],
        optimization_attempts=tuple(attempts),
        rank_revealing_active_columns=tuple(diagnostics["active_columns"]),
        rank_revealing_dependent_columns=tuple(diagnostics["dropped_columns"]),
        fixed_effect_coordinates_fitted=len(HU_COLUMNS),
        prior_normalizing_constant_omitted=bool(selected_components["prior_normalizing_constant_omitted"]),
    )


def fit_hu_glmm_vectorized_laplace(
    X: np.ndarray,
    successes: Sequence[float],
    totals: Sequence[float],
    root_ids: Sequence[str],
    tau: float,
    column_names: Sequence[str] = HU_COLUMNS,
) -> RegularizedHUGLMMFit:
    validate_dependencies()
    aggregate_X, y, n, _, adjustment = aggregate_identical_root_rows(X, successes, totals, root_ids)
    return fit_native_regularized(aggregate_X, y, n, column_names, "laplace", tau, adjustment)


def fit_hu_glmm_vectorized_gh(
    X: np.ndarray,
    successes: Sequence[float],
    totals: Sequence[float],
    root_ids: Sequence[str],
    tau: float,
    nodes: int = 80,
    column_names: Sequence[str] = HU_COLUMNS,
) -> RegularizedHUGLMMFit:
    validate_dependencies()
    if nodes != 80:
        raise ValueError("the frozen HU sensitivity uses exactly 80 adaptive GH nodes")
    aggregate_X, y, n, _, adjustment = aggregate_identical_root_rows(X, successes, totals, root_ids)
    return fit_native_regularized(aggregate_X, y, n, column_names, "gh", tau, adjustment)


def synthetic_check(seed: int) -> dict[str, object]:
    rng = np.random.default_rng(seed)
    roots = 60
    X = np.column_stack([np.ones(roots), rng.normal(size=(roots, len(HU_COLUMNS) - 1))])
    beta = np.array([-0.2, 0.5, -0.3, 0.25, 0.1, -0.15, 0.08, -0.05, 0.2, -0.1, 0.12])
    random = rng.normal(0.0, 0.7, roots)
    n = rng.integers(8, 90, roots)
    probability = 1.0 / (1.0 + np.exp(-(X @ beta + random)))
    y = rng.binomial(n, probability)
    ids = [f"r{index:03d}" for index in range(roots)]
    rank_deficient_X = X.copy()
    rank_deficient_X[:, 4] = rank_deficient_X[:, 3]
    rank_deficient_X[:, 10] = 0.0
    records = {}
    for tau in ALLOWED_TAUS:
        laplace = fit_hu_glmm_vectorized_laplace(X, y, n, ids, tau=tau)
        gh = fit_hu_glmm_vectorized_gh(X[:32], y[:32], n[:32], ids[:32], tau=tau, nodes=80)
        rank_deficient_laplace = fit_hu_glmm_vectorized_laplace(
            rank_deficient_X, y, n, ids, tau=tau,
        )
        rank_deficient_gh = fit_hu_glmm_vectorized_gh(
            rank_deficient_X[:32], y[:32], n[:32], ids[:32], tau=tau, nodes=80,
        )
        laplace_gate = hu_glmm_gate(laplace)
        gh_gate = hu_glmm_gate(gh)
        rank_deficient_laplace_gate = hu_glmm_gate(rank_deficient_laplace)
        rank_deficient_gh_gate = hu_glmm_gate(rank_deficient_gh)
        if not all(gate.passed for gate in (
            laplace_gate, gh_gate, rank_deficient_laplace_gate, rank_deficient_gh_gate,
        )):
            raise AssertionError((
                tau, laplace_gate, gh_gate,
                rank_deficient_laplace_gate, rank_deficient_gh_gate,
            ))
        for fit in (rank_deficient_laplace, rank_deficient_gh):
            if not (
                fit.design_rank < len(HU_COLUMNS)
                and fit.fixed_effect_coordinates_fitted == len(HU_COLUMNS)
                and len(fit.active_columns) == len(HU_COLUMNS)
                and not fit.dropped_columns
                and fit.rank_revealing_dependent_columns
            ):
                raise AssertionError((tau, "rank-deficient native-coordinate contract", fit))
        records[str(tau)] = {
            "laplace": {
                "objective": laplace.objective,
                "data_objective": laplace.data_negative_log_likelihood,
                "penalty": laplace.gaussian_penalty,
                "sigma": laplace.sigma,
                "span": float(np.ptp(laplace.multistart_objectives)),
            },
            "gh80": {
                "objective": gh.objective,
                "data_objective": gh.data_negative_log_likelihood,
                "penalty": gh.gaussian_penalty,
                "sigma": gh.sigma,
                "span": float(np.ptp(gh.multistart_objectives)),
            },
            "rank_deficient_laplace": {
                "objective": rank_deficient_laplace.objective,
                "design_rank": rank_deficient_laplace.design_rank,
                "fixed_effect_coordinates_fitted": rank_deficient_laplace.fixed_effect_coordinates_fitted,
                "rank_revealing_dependent_columns": rank_deficient_laplace.rank_revealing_dependent_columns,
                "span": float(np.ptp(rank_deficient_laplace.multistart_objectives)),
            },
            "rank_deficient_gh80": {
                "objective": rank_deficient_gh.objective,
                "design_rank": rank_deficient_gh.design_rank,
                "fixed_effect_coordinates_fitted": rank_deficient_gh.fixed_effect_coordinates_fitted,
                "rank_revealing_dependent_columns": rank_deficient_gh.rank_revealing_dependent_columns,
                "span": float(np.ptp(rank_deficient_gh.multistart_objectives)),
            },
        }
    return {"status": "PASS_SYNTHETIC_ONLY_NO_CORPUS_FIT", "seed": seed, "tau": records}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--synthetic-check", action="store_true")
    parser.add_argument("--seed", type=int, default=20260920)
    parser.add_argument("--output")
    args = parser.parse_args()
    if not args.synthetic_check:
        parser.error("only --synthetic-check is exposed")
    result = {
        "python": platform.python_version(),
        "numpy": np.__version__,
        "dependencies": DEPENDENCY_HASHES,
        "result": synthetic_check(args.seed),
    }
    text = json.dumps(result, indent=2) + "\n"
    if args.output:
        Path(args.output).write_text(text, encoding="utf-8")
    print(text, end="")


if __name__ == "__main__":
    main()
