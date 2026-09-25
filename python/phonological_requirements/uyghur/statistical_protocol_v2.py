from __future__ import annotations

import argparse
import hashlib
import json
import math
import platform
import sys
from collections import defaultdict
from dataclasses import dataclass
from pathlib import Path
from typing import Callable, Sequence

import numpy as np
from numpy.polynomial.hermite import hermgauss
from scipy.integrate import quad
from scipy.linalg import qr
from scipy.optimize import minimize
from scipy.special import betaln, digamma, expit, gammaln, logsumexp


HU_COLUMNS = (
    "intercept",
    "last_one_F",
    "log_acc_frequency",
    "acc_raised_prop",
    "last_one_F:log_acc_frequency",
    "last_one_F:acc_raised_prop",
    "log_acc_frequency:acc_raised_prop",
    "last_one_F:log_acc_frequency:acc_raised_prop",
    "has_name",
    "has_ane",
    "has_che",
)


@dataclass(frozen=True)
class BetaBinomialFit:
    alpha: float
    beta: float
    objective: float
    converged: bool
    iterations: int
    gradient_max_abs: float
    at_bound: bool
    multistart: tuple[dict[str, float | bool], ...]


@dataclass(frozen=True)
class HUGLMMFit:
    beta: tuple[float, ...]
    sigma: float
    objective: float
    method: str
    quadrature_nodes: int
    converged: bool
    iterations: int
    design_rank: int
    active_columns: tuple[str, ...]
    dropped_columns: tuple[str, ...]
    constant_columns: tuple[str, ...]
    projected_gradient_max_abs: float
    multistart_objectives: tuple[float, ...]


@dataclass(frozen=True)
class GrammarFit:
    model: str
    parameters: dict[str, float]
    objective: float
    regularization_alpha: float
    converged: bool
    iterations: int
    internal_coordinates: tuple[float, ...]
    gradient: tuple[float, ...]
    projected_gradient_max_abs: float
    finite_difference_max_abs_error: float


@dataclass(frozen=True)
class SuffixOffsetFit:
    dat_offset: float
    loc_offset: float
    objective: float
    ridge: float
    separation_detected: bool
    degrees_of_freedom: int
    converged: bool
    gradient_max_abs: float
    finite_difference_max_abs_error: float


@dataclass(frozen=True)
class FitGate:
    passed: bool
    reasons: tuple[str, ...]


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _as_count_arrays(successes: Sequence[float], totals: Sequence[float]) -> tuple[np.ndarray, np.ndarray]:
    k = np.asarray(successes, dtype=float)
    n = np.asarray(totals, dtype=float)
    if k.ndim != 1 or n.ndim != 1 or k.shape != n.shape or len(k) == 0:
        raise ValueError("successes and totals must be nonempty equal-length vectors")
    if np.any(~np.isfinite(k)) or np.any(~np.isfinite(n)):
        raise ValueError("counts must be finite")
    if np.any(n < 0) or np.any(k < 0) or np.any(k > n):
        raise ValueError("require 0 <= successes <= totals")
    return k, n


def beta_binomial_loglik(successes: Sequence[float], totals: Sequence[float], alpha: float, beta: float) -> float:

    k, n = _as_count_arrays(successes, totals)
    if alpha <= 0 or beta <= 0:
        return -math.inf
    log_choose = gammaln(n + 1) - gammaln(k + 1) - gammaln(n - k + 1)
    return float(np.sum(log_choose + betaln(k + alpha, n - k + beta) - betaln(alpha, beta)))


def beta_binomial_loglik_gradient(
    successes: Sequence[float], totals: Sequence[float], alpha: float, beta: float,
) -> np.ndarray:

    k, n = _as_count_arrays(successes, totals)
    if alpha <= 0 or beta <= 0:
        raise ValueError("alpha and beta must be positive")
    da = np.sum(digamma(k + alpha) - digamma(n + alpha + beta) - digamma(alpha) + digamma(alpha + beta))
    db = np.sum(digamma(n - k + beta) - digamma(n + alpha + beta) - digamma(beta) + digamma(alpha + beta))
    return np.array([float(da), float(db)])


def finite_difference_gradient(function: Callable[[np.ndarray], float], point: Sequence[float], step: float = 1e-5) -> np.ndarray:

    x = np.asarray(point, dtype=float)
    result = np.empty_like(x)
    for i in range(len(x)):
        h = step * max(1.0, abs(float(x[i])))
        plus, minus = x.copy(), x.copy()
        plus[i] += h
        minus[i] -= h
        result[i] = (function(plus) - function(minus)) / (2.0 * h)
    return result


def projected_gradient(theta: Sequence[float], gradient: Sequence[float], lower: float = 0.0, tolerance: float = 1e-9) -> np.ndarray:
    theta = np.asarray(theta, dtype=float)
    gradient = np.asarray(gradient, dtype=float)
    return np.where(theta <= lower + tolerance, np.minimum(gradient, 0.0), gradient)


def fit_beta_binomial(successes: Sequence[float], totals: Sequence[float]) -> BetaBinomialFit:

    k, n = _as_count_arrays(successes, totals)
    empirical = float((k.sum() + 0.5) / (n.sum() + 1.0))
    lower, upper = -16.0, 16.0

    def objective_and_gradient(theta: np.ndarray) -> tuple[float, np.ndarray]:
        alpha, beta = np.exp(theta)
        value = -beta_binomial_loglik(k, n, float(alpha), float(beta))
        raw = beta_binomial_loglik_gradient(k, n, float(alpha), float(beta))
        return value, -raw * np.array([alpha, beta])

    results = []
    for concentration in (0.1, 0.5, 1.0, 4.0, 20.0, 100.0):
        initial = np.log([
            max(empirical * concentration, math.exp(lower)),
            max((1.0 - empirical) * concentration, math.exp(lower)),
        ])
        results.append(minimize(
            objective_and_gradient, initial, method="L-BFGS-B", jac=True,
            bounds=[(lower, upper)] * 2, options={"maxiter": 2000, "ftol": 1e-13, "gtol": 1e-9},
        ))
    result = min(results, key=lambda item: float(item.fun))
    alpha, beta = np.exp(result.x)
    _, gradient = objective_and_gradient(result.x)
    fitted_mean = float(alpha / (alpha + beta))
    diagnostics = tuple({
        "objective": float(item.fun), "converged": bool(item.success),
        "alpha": float(math.exp(item.x[0])), "beta": float(math.exp(item.x[1])),
    } for item in results)
    return BetaBinomialFit(
        alpha=float(alpha), beta=float(beta), objective=float(result.fun),
        converged=bool(result.success), iterations=int(result.nit),
        gradient_max_abs=float(np.max(np.abs(gradient))),
        at_bound=bool(
            np.any(np.isclose(result.x, lower, atol=1e-6))
            or np.any(np.isclose(result.x, upper, atol=1e-6))
            or fitted_mean < 1e-8
            or fitted_mean > 1.0 - 1e-8
        ),
        multistart=diagnostics,
    )


def beta_binomial_gate(fit: BetaBinomialFit, gradient_tolerance: float = 2e-4) -> FitGate:

    reasons = []
    if not fit.converged:
        reasons.append("optimizer_not_converged")
    if fit.at_bound:
        reasons.append("boundary_or_degenerate_mean")
    if not math.isfinite(fit.objective):
        reasons.append("nonfinite_objective")
    if fit.gradient_max_abs > gradient_tolerance:
        reasons.append("gradient_above_tolerance")
    objectives = np.array([float(item["objective"]) for item in fit.multistart])
    if np.any(~np.isfinite(objectives)) or float(np.ptp(objectives)) > 1e-5:
        reasons.append("multistart_objective_disagreement")
    return FitGate(passed=not reasons, reasons=tuple(reasons))


def smoothed_raising_probability(raised: float, total: float, alpha: float, beta: float) -> float:
    if total < 0 or raised < 0 or raised > total or alpha <= 0 or beta <= 0:
        raise ValueError("invalid counts or beta prior")
    return float((raised + alpha) / (total + alpha + beta))


def raising_cost_difference(raised: float, total: float, alpha: float, beta: float) -> float:

    rho = smoothed_raising_probability(raised, total, alpha, beta)
    return float(math.log1p(-rho) - math.log(rho))


def fit_agreeing_suffix_offsets(
    suffix: Sequence[str], d: Sequence[float], raised: Sequence[float], totals: Sequence[float],
    opposed: Sequence[bool], separation_ridge: float = 1e-4,
) -> SuffixOffsetFit:






    suffix = np.asarray(suffix)
    d = np.asarray(d, dtype=float)
    k, n = _as_count_arrays(raised, totals)
    opposed = np.asarray(opposed, dtype=bool)
    if not (len(suffix) == len(d) == len(k) == len(opposed)) or np.any(opposed):
        raise ValueError("suffix offsets require aligned agreeing-only training rows")
    if np.any((suffix != "dat") & (suffix != "loc")) or separation_ridge <= 0:
        raise ValueError("suffix must be dat/loc and separation ridge must be positive")
    design = np.column_stack([suffix == "dat", suffix == "loc"]).astype(float)
    separated = any(
        float(k[suffix == label].sum()) in {0.0, float(n[suffix == label].sum())}
        for label in ("dat", "loc")
    )
    ridge = float(separation_ridge if separated else 0.0)
    incidence_count = float(n.sum())
    if incidence_count <= 0:
        raise ValueError("suffix offset fit needs at least one incidence")

    def objective_and_gradient(theta: np.ndarray) -> tuple[float, np.ndarray]:
        linear = d + design @ theta
        p_raise = expit(-linear)
        objective = float(np.sum(k * np.logaddexp(0.0, linear) + (n - k) * np.logaddexp(0.0, -linear))) / incidence_count
        objective += 0.5 * ridge * float(theta @ theta)
        gradient = design.T @ (k - n * p_raise) / incidence_count + ridge * theta
        return objective, gradient

    result = minimize(
        objective_and_gradient, np.zeros(2), method="BFGS", jac=True,
        options={"maxiter": 1000, "gtol": 1e-9},
    )
    objective, gradient = objective_and_gradient(result.x)
    finite = finite_difference_gradient(lambda value: objective_and_gradient(value)[0], result.x)
    gradient_max_abs = float(np.max(np.abs(gradient)))
    return SuffixOffsetFit(
        dat_offset=float(result.x[0]), loc_offset=float(result.x[1]), objective=float(objective),
        ridge=float(ridge), degrees_of_freedom=2,
        converged=bool(result.success or gradient_max_abs <= 1e-7),
        separation_detected=bool(separated),
        gradient_max_abs=gradient_max_abs,
        finite_difference_max_abs_error=float(np.max(np.abs(finite - gradient))),
    )


def hu_design_matrix(
    last_one: Sequence[str],
    log_acc_frequency: Sequence[float],
    acc_raised_prop: Sequence[float],
    has_name: Sequence[bool],
    has_ane: Sequence[bool],
    has_che: Sequence[bool],
) -> np.ndarray:





    last = np.asarray(last_one)
    f = (last == "F").astype(float)
    if np.any((last != "B") & (last != "F")):
        raise ValueError("last_one must be B or F")
    logn = np.asarray(log_acc_frequency, dtype=float)
    rho = np.asarray(acc_raised_prop, dtype=float)
    name = np.asarray(has_name, dtype=float)
    ane = np.asarray(has_ane, dtype=float)
    che = np.asarray(has_che, dtype=float)
    lengths = {len(x) for x in (last, logn, rho, name, ane, che)}
    if len(lengths) != 1 or not lengths or np.any(~np.isfinite(logn)) or np.any(~np.isfinite(rho)):
        raise ValueError("HU predictors must be finite equal-length vectors")
    return np.column_stack([
        np.ones(len(last)), f, logn, rho, f * logn, f * rho,
        logn * rho, f * logn * rho, name, ane, che,
    ])


def hu_design_diagnostics(X: np.ndarray, column_names: Sequence[str] = HU_COLUMNS) -> dict:
    X = np.asarray(X, dtype=float)
    if X.ndim != 2 or X.shape[1] != len(column_names):
        raise ValueError("design/column mismatch")
    constant = [str(column_names[i]) for i in range(X.shape[1]) if np.ptp(X[:, i]) <= 1e-12]
    _, r, pivots = qr(X, mode="economic", pivoting=True)
    diagonal = np.abs(np.diag(r))
    tolerance = max(X.shape) * np.finfo(float).eps * (diagonal[0] if len(diagonal) else 0.0)
    rank = int(np.sum(diagonal > tolerance))
    active_indices = sorted(map(int, pivots[:rank]))
    dropped_indices = sorted(set(range(X.shape[1])) - set(active_indices))
    return {
        "rank": rank,
        "constant_columns": constant,
        "active_indices": active_indices,
        "active_columns": [str(column_names[i]) for i in active_indices],
        "dropped_indices": dropped_indices,
        "dropped_columns": [str(column_names[i]) for i in dropped_indices],
    }


def _binomial_log_kernel(y: np.ndarray, n: np.ndarray, eta: np.ndarray) -> np.ndarray:
    return y * (-np.logaddexp(0.0, -eta)) + (n - y) * (-np.logaddexp(0.0, eta))


def _root_groups(root_ids: Sequence[str]) -> tuple[np.ndarray, list[np.ndarray]]:
    ids = np.asarray(root_ids, dtype=object)
    if ids.ndim != 1:
        raise ValueError("root_ids must be a vector")
    names, inverse = np.unique(ids, return_inverse=True)
    groups = [np.flatnonzero(inverse == i) for i in range(len(names))]
    return names, groups


def _root_logposterior(mode: float, eta: np.ndarray, y: np.ndarray, n: np.ndarray, sigma: float) -> float:
    kernel = float(np.sum(_binomial_log_kernel(y, n, eta + mode)))
    return kernel - 0.5 * (mode / sigma) ** 2 - math.log(sigma) - 0.5 * math.log(2.0 * math.pi)


def _root_mode_curvature(
    eta: np.ndarray, y: np.ndarray, n: np.ndarray, sigma: float,
) -> tuple[float, float, int]:

    if sigma <= 0:
        raise ValueError("sigma must be positive")
    total_success = float(np.sum(y))
    total_count = float(np.sum(n))
    variance = sigma * sigma
    lower = variance * (total_success - total_count)
    upper = variance * total_success
    point = min(max(0.0, lower), upper)
    inv_variance = 1.0 / variance
    for iteration in range(1, 201):
        p = expit(eta + point)
        score = float(np.sum(y - n * p) - point * inv_variance)
        curvature = float(np.sum(n * p * (1.0 - p)) + inv_variance)
        if abs(score) <= 1e-11 * max(1.0, total_count):
            return point, curvature, iteration
        if score > 0:
            lower = point
        else:
            upper = point
        candidate = point + score / curvature
        if not math.isfinite(candidate) or candidate <= lower or candidate >= upper:
            candidate = 0.5 * (lower + upper)
        if abs(candidate - point) <= 1e-12 * max(1.0, abs(point)):
            point = candidate
            p = expit(eta + point)
            curvature = float(np.sum(n * p * (1.0 - p)) + inv_variance)
            return point, curvature, iteration
        point = candidate
    raise RuntimeError("safeguarded conditional-mode solver failed")


def _conditional_modes(
    beta: np.ndarray, sigma: float, X: np.ndarray, y: np.ndarray, n: np.ndarray,
    groups: Sequence[np.ndarray],
) -> tuple[np.ndarray, np.ndarray, np.ndarray]:
    eta = X @ beta
    modes, curvatures, iterations = [], [], []
    for idx in groups:
        mode, curvature, count = _root_mode_curvature(eta[idx], y[idx], n[idx], sigma)
        modes.append(mode)
        curvatures.append(curvature)
        iterations.append(count)
    return np.asarray(modes), np.asarray(curvatures), np.asarray(iterations)


def hu_loglik_adaptive_gh(
    beta: Sequence[float], sigma: float, X: np.ndarray,
    successes: Sequence[float], totals: Sequence[float], root_ids: Sequence[str],
    nodes: int = 30,
) -> float:

    y, n = _as_count_arrays(successes, totals)
    X = np.asarray(X, dtype=float)
    b = np.asarray(beta, dtype=float)
    if X.shape != (len(y), len(b)) or sigma <= 0 or nodes < 3:
        raise ValueError("invalid GLMM dimensions, sigma or quadrature order")
    _, groups = _root_groups(root_ids)
    if sum(map(len, groups)) != len(y):
        raise ValueError("root_ids length mismatch")
    modes, curvatures, _ = _conditional_modes(b, sigma, X, y, n, groups)
    gh_x, gh_w = hermgauss(nodes)
    log_weights = np.log(gh_w)
    eta = X @ b
    total = 0.0
    for mode, curvature, idx in zip(modes, curvatures, groups):
        root_eta = eta[idx]
        height = _root_logposterior(float(mode), root_eta, y[idx], n[idx], sigma)
        scale = math.sqrt(2.0 / float(curvature))
        shifted = mode + scale * gh_x
        relative = np.array([
            _root_logposterior(float(value), root_eta, y[idx], n[idx], sigma) - height + node * node
            for value, node in zip(shifted, gh_x)
        ])
        total += height + math.log(scale) + float(logsumexp(log_weights + relative))
    constants = gammaln(n + 1) - gammaln(y + 1) - gammaln(n - y + 1)
    return total + float(constants.sum())


def hu_loglik_gh(*args, **kwargs) -> float:

    return hu_loglik_adaptive_gh(*args, **kwargs)


def hu_loglik_laplace(
    beta: Sequence[float], sigma: float, X: np.ndarray,
    successes: Sequence[float], totals: Sequence[float], root_ids: Sequence[str],
) -> float:

    y, n = _as_count_arrays(successes, totals)
    X = np.asarray(X, dtype=float)
    b = np.asarray(beta, dtype=float)
    if X.shape != (len(y), len(b)) or sigma <= 0:
        raise ValueError("invalid GLMM dimensions or sigma")
    _, groups = _root_groups(root_ids)
    modes, curvatures, _ = _conditional_modes(b, sigma, X, y, n, groups)
    eta = X @ b
    total = 0.0
    for mode, curvature, idx in zip(modes, curvatures, groups):
        height = _root_logposterior(float(mode), eta[idx], y[idx], n[idx], sigma)
        total += height + 0.5 * math.log(2.0 * math.pi / float(curvature))
    constants = gammaln(n + 1) - gammaln(y + 1) - gammaln(n - y + 1)
    return total + float(constants.sum())


def hu_root_loglik_quad(
    beta: Sequence[float], sigma: float, X: np.ndarray,
    successes: Sequence[float], totals: Sequence[float],
) -> float:

    y, n = _as_count_arrays(successes, totals)
    X = np.asarray(X, dtype=float)
    b = np.asarray(beta, dtype=float)
    eta = X @ b
    mode, curvature, _ = _root_mode_curvature(eta, y, n, sigma)
    height = _root_logposterior(mode, eta, y, n, sigma)
    scale = math.sqrt(curvature)

    def integrand(standardized: float) -> float:
        random_intercept = mode + standardized / scale
        return math.exp(_root_logposterior(random_intercept, eta, y, n, sigma) - height) / scale

    value, error = quad(integrand, -math.inf, math.inf, epsabs=1e-11, epsrel=1e-11, limit=500)
    if value <= 0 or error > max(1e-9, value * 1e-8):
        raise RuntimeError(f"reference quadrature failed: value={value}, error={error}")
    constants = gammaln(n + 1) - gammaln(y + 1) - gammaln(n - y + 1)
    return height + math.log(value) + float(constants.sum())


def fit_hu_glmm(
    X: np.ndarray, successes: Sequence[float], totals: Sequence[float], root_ids: Sequence[str],
    method: str = "laplace", nodes: int = 40,
) -> HUGLMMFit:

    y, n = _as_count_arrays(successes, totals)
    X = np.asarray(X, dtype=float)
    if X.ndim != 2 or X.shape[0] != len(y):
        raise ValueError("invalid design matrix")
    if method not in {"gh", "laplace"}:
        raise ValueError("method must be gh or laplace")
    if len(root_ids) != len(y):
        raise ValueError("root_ids length mismatch")
    diagnostics = hu_design_diagnostics(X)
    active_indices = diagnostics["active_indices"]
    active_X = X[:, active_indices]
    lower_sigma, upper_sigma = -8.0, math.log(20.0)

    def objective(theta: np.ndarray) -> float:
        beta = theta[:-1]
        sigma = math.exp(float(theta[-1]))
        if method == "gh":
            return -hu_loglik_adaptive_gh(beta, sigma, active_X, y, n, root_ids, nodes)
        return -hu_loglik_laplace(beta, sigma, active_X, y, n, root_ids)

    results = []
    bounds = [(None, None)] * len(active_indices) + [(lower_sigma, upper_sigma)]
    for initial_sigma in (0.1, 0.5, 2.0):
        initial = np.zeros(len(active_indices) + 1)
        initial[-1] = math.log(initial_sigma)
        results.append(minimize(
            objective, initial, method="L-BFGS-B", bounds=bounds,
            options={"maxiter": 2000, "ftol": 1e-12, "gtol": 1e-7, "maxls": 50},
        ))
    result = min(results, key=lambda item: float(item.fun))
    full_beta = np.zeros(X.shape[1])
    full_beta[active_indices] = result.x[:-1]
    numeric_gradient = finite_difference_gradient(objective, result.x, step=2e-5)
    projected = numeric_gradient.copy()
    if result.x[-1] <= lower_sigma + 1e-8:
        projected[-1] = min(projected[-1], 0.0)
    elif result.x[-1] >= upper_sigma - 1e-8:
        projected[-1] = max(projected[-1], 0.0)
    return HUGLMMFit(
        beta=tuple(map(float, full_beta)), sigma=math.exp(float(result.x[-1])),
        objective=float(result.fun), method=method, quadrature_nodes=nodes if method == "gh" else 1,
        converged=bool(result.success), iterations=int(result.nit),
        design_rank=int(diagnostics["rank"]),
        active_columns=tuple(diagnostics["active_columns"]),
        dropped_columns=tuple(diagnostics["dropped_columns"]),
        constant_columns=tuple(diagnostics["constant_columns"]),
        projected_gradient_max_abs=float(np.max(np.abs(projected))),
        multistart_objectives=tuple(float(item.fun) for item in results),
    )


def hu_glmm_gate(fit: HUGLMMFit, gradient_tolerance: float = 5e-3) -> FitGate:

    reasons = []
    if not fit.converged:
        reasons.append("optimizer_not_converged")
    if not math.isfinite(fit.objective) or not np.all(np.isfinite(fit.beta)) or not math.isfinite(fit.sigma):
        reasons.append("nonfinite_fit")
    if fit.sigma <= math.exp(-8.0) * (1.0 + 1e-5) or fit.sigma >= 20.0 * (1.0 - 1e-5):
        reasons.append("sigma_at_optimization_bound")
    if fit.design_rank < 1:
        reasons.append("zero_design_rank")
    if fit.projected_gradient_max_abs > gradient_tolerance:
        reasons.append("projected_gradient_above_tolerance")
    objectives = np.asarray(fit.multistart_objectives, dtype=float)
    if np.any(~np.isfinite(objectives)) or float(np.ptp(objectives)) > 1e-4:
        reasons.append("multistart_objective_disagreement")
    return FitGate(passed=not reasons, reasons=tuple(reasons))


def predict_hu_probability(fit: HUGLMMFit, X: np.ndarray) -> np.ndarray:






    X = np.asarray(X, dtype=float)
    eta = X @ np.asarray(fit.beta)
    return expit(eta)


def assign_input_stratified_folds(
    roots: Sequence[str], strata: Sequence[str], folds: int, seed: str,
) -> dict[str, int]:

    if folds < 2 or len(roots) != len(strata) or len(set(roots)) != len(roots):
        raise ValueError("invalid folds or duplicate/misaligned roots")
    grouped: dict[str, list[str]] = defaultdict(list)
    for root, stratum in zip(roots, strata):
        grouped[str(stratum)].append(str(root))
    result: dict[str, int] = {}
    for stratum, members in sorted(grouped.items()):
        ordered = sorted(
            members,
            key=lambda root: hashlib.sha256(f"{seed}\0{stratum}\0{root}".encode()).hexdigest(),
        )
        offset = int(hashlib.sha256(f"{seed}\0{stratum}".encode()).hexdigest()[:8], 16) % folds
        for position, root in enumerate(ordered):
            result[root] = (position + offset) % folds
    return result


def assign_nested_root_folds(
    roots: Sequence[str], strata: Sequence[str], outer_folds: int, inner_folds: int, seed: str,
) -> dict[str, object]:

    outer = assign_input_stratified_folds(roots, strata, outer_folds, seed)
    root_to_stratum = dict(zip(map(str, roots), map(str, strata)))
    inner: dict[str, dict[str, int]] = {}
    for held_out in range(outer_folds):
        training_roots = sorted(root for root, fold in outer.items() if fold != held_out)
        training_strata = [root_to_stratum[root] for root in training_roots]
        inner[str(held_out)] = assign_input_stratified_folds(
            training_roots, training_strata, inner_folds, f"{seed}\0inner\0{held_out}",
        )
    return {"seed": seed, "outer": outer, "inner_by_outer_fold": inner}


def select_regularization_alpha(
    root_balanced_mean_log_density: dict[float, float], tolerance: float = 1e-8,
) -> float:

    if not root_balanced_mean_log_density or tolerance < 0:
        raise ValueError("regularization scores must be nonempty and tolerance nonnegative")
    if any(alpha < 0 or not math.isfinite(score) for alpha, score in root_balanced_mean_log_density.items()):
        raise ValueError("regularization alphas and scores must be valid")
    best = max(root_balanced_mean_log_density.values())
    return float(max(alpha for alpha, score in root_balanced_mean_log_density.items() if best - score <= tolerance))


def predictive_log_density_metrics(
    root_ids: Sequence[str], log_probabilities: Sequence[float], multiplicities: Sequence[float],
) -> dict[str, float]:

    roots = np.asarray(root_ids, dtype=object)
    logp = np.asarray(log_probabilities, dtype=float)
    counts = np.asarray(multiplicities, dtype=float)
    if not (len(roots) == len(logp) == len(counts)) or len(roots) == 0:
        raise ValueError("predictive vectors must be nonempty and aligned")
    if np.any(~np.isfinite(logp)) or np.any(~np.isfinite(counts)) or np.any(counts < 0) or counts.sum() <= 0:
        raise ValueError("predictive log probabilities/counts are invalid")
    names, groups = _root_groups(roots)
    root_means = []
    for idx in groups:
        denominator = float(counts[idx].sum())
        if denominator <= 0:
            raise ValueError("every scored root must have positive multiplicity")
        root_means.append(float(counts[idx] @ logp[idx] / denominator))
    return {
        "root_count": int(len(names)),
        "root_balanced_mean_log_density": float(np.mean(root_means)),
        "incidence_weighted_mean_log_density": float(counts @ logp / counts.sum()),
    }


def candidate_costs(
    model: str, opposed: bool, d: float, parameters: dict[str, float], p_hc_b: float | None = None,
    old_is_back: bool = True,
) -> np.ndarray:

    if model in {"retention", "retention_nonnegative"}:
        A, B = parameters["A"], parameters["B"]
        if A < 0 or B < 0 or (model == "retention" and B > A):
            raise ValueError("retention requires A,B >= 0 and bounded retention also requires B <= A")
        return np.array([0.0, A, d + (B if opposed else 0.0), d + A])
    if model == "current_only":
        C = parameters["C"]
        if C < 0:
            raise ValueError("current-only weight must be nonnegative")
        return np.array([0.0, C, d + (C if opposed else 0.0), d + (0.0 if opposed else C)])
    if model == "input_surface":
        a, b = parameters["input"], parameters["surface"]
        if a < 0 or b < 0:
            raise ValueError("input/surface weights must be nonnegative")
        if opposed:
            return np.array([0.0, a + b, d + b, d + a])
        return np.array([0.0, a + b, d, d + a + b])
    if model in {"hu_surface", "retention_hu"}:
        if p_hc_b is None or not 0.0 <= p_hc_b <= 1.0:
            raise ValueError("HU requires P(HC=B)")
        hu_weight = parameters["HU"]
        if hu_weight < 0:
            raise ValueError("HU weight must be nonnegative")
        suffix_old_is_back = old_is_back
        hu_old = (1.0 - p_hc_b) if suffix_old_is_back else p_hc_b
        hu_opposite = p_hc_b if suffix_old_is_back else (1.0 - p_hc_b)
        hu = hu_weight * np.array([hu_old, hu_opposite, hu_old, hu_opposite])
        if model == "hu_surface":
            return candidate_costs("current_only", opposed, d, {"C": parameters["surface"]}) + hu
        return candidate_costs("retention", opposed, d, {"A": parameters["A"], "B": parameters["B"]}) + hu
    raise ValueError(f"unknown model: {model}")


def probabilities(costs: Sequence[float]) -> np.ndarray:
    costs = np.asarray(costs, dtype=float)
    return np.exp(-costs - logsumexp(-costs))


def _grammar_feature_tensor(
    model: str, opposed: np.ndarray, p_hc: np.ndarray, old_is_back: np.ndarray,
) -> np.ndarray:

    row_count = len(opposed)
    if model in {"retention", "retention_nonnegative", "input_surface"}:
        features = np.zeros((row_count, 4, 2))
    elif model == "current_only":
        features = np.zeros((row_count, 4, 1))
    elif model == "hu_surface":
        features = np.zeros((row_count, 4, 2))
    elif model == "retention_hu":
        features = np.zeros((row_count, 4, 3))
    else:
        raise ValueError(f"unknown model: {model}")

    if model in {"retention", "retention_hu"}:
        
        features[:, 1, 0:2] = [1.0, 1.0]
        features[:, 2, 0] = opposed.astype(float)
        features[:, 3, 0:2] = [1.0, 1.0]
    elif model == "retention_nonnegative":
        
        features[:, 1, 0] = 1.0
        features[:, 2, 1] = opposed.astype(float)
        features[:, 3, 0] = 1.0
    elif model in {"current_only", "hu_surface"}:
        features[:, 1, 0] = 1.0
        features[:, 2, 0] = opposed.astype(float)
        features[:, 3, 0] = (~opposed).astype(float)
    elif model == "input_surface":
        features[:, 1, :] = [1.0, 1.0]
        features[:, 2, 1] = opposed.astype(float)
        features[:, 3, 0] = opposed.astype(float)
        features[:, 3, :] += (~opposed)[:, None].astype(float)

    if model in {"hu_surface", "retention_hu"}:
        if np.any(~np.isfinite(p_hc)) or np.any((p_hc < 0) | (p_hc > 1)):
            raise ValueError("HU models require finite probabilities")
        hu_index = features.shape[2] - 1
        hu_old = np.where(old_is_back, 1.0 - p_hc, p_hc)
        hu_opposite = np.where(old_is_back, p_hc, 1.0 - p_hc)
        features[:, 0, hu_index] = hu_old
        features[:, 1, hu_index] = hu_opposite
        features[:, 2, hu_index] = hu_old
        features[:, 3, hu_index] = hu_opposite
    return features


def grammar_objective_gradient(
    theta: Sequence[float], model: str, counts: np.ndarray, opposed: Sequence[bool],
    d: Sequence[float], p_hc_b: Sequence[float] | None = None,
    old_is_back: Sequence[bool] | None = None, alpha: float = 0.0,
) -> tuple[float, np.ndarray]:
    counts = np.asarray(counts, dtype=float)
    opposed = np.asarray(opposed, dtype=bool)
    d = np.asarray(d, dtype=float)
    theta = np.asarray(theta, dtype=float)
    if counts.ndim != 2 or counts.shape != (len(opposed), 4) or len(d) != len(opposed):
        raise ValueError("counts must be n-by-4 and predictors length n")
    if np.any(counts < 0) or alpha < 0:
        raise ValueError("counts and regularization alpha must be nonnegative")
    old = np.ones(len(opposed), dtype=bool) if old_is_back is None else np.asarray(old_is_back, dtype=bool)
    p_hc = np.full(len(opposed), np.nan) if p_hc_b is None else np.asarray(p_hc_b, dtype=float)
    if len(old) != len(opposed) or len(p_hc) != len(opposed):
        raise ValueError("grammar predictor length mismatch")
    features = _grammar_feature_tensor(model, opposed, p_hc, old)
    if features.shape[2] != len(theta):
        raise ValueError("parameter dimension mismatch")
    fixed = np.zeros_like(counts)
    fixed[:, 2:] = d[:, None]
    costs = fixed + np.einsum("ncp,p->nc", features, theta)
    log_normalizer = logsumexp(-costs, axis=1)
    probs = np.exp(-costs - log_normalizer[:, None])
    totals = counts.sum(axis=1)
    incidence_count = float(totals.sum())
    if incidence_count <= 0:
        raise ValueError("grammar fit needs at least one incidence")
    objective = float((np.sum(counts * costs) + totals @ log_normalizer) / incidence_count + 0.5 * alpha * (theta @ theta))
    residual = counts - totals[:, None] * probs
    gradient = np.einsum("ncp,nc->p", features, residual) / incidence_count + alpha * theta
    return objective, gradient


def fit_grammar(
    model: str,
    counts: np.ndarray,
    opposed: Sequence[bool],
    d: Sequence[float],
    p_hc_b: Sequence[float] | None = None,
    old_is_back: Sequence[bool] | None = None,
    alpha: float = 0.0,
) -> GrammarFit:





    counts = np.asarray(counts, dtype=float)
    opposed = np.asarray(opposed, dtype=bool)
    d = np.asarray(d, dtype=float)
    old_is_back = np.ones(len(opposed), dtype=bool) if old_is_back is None else np.asarray(old_is_back, dtype=bool)
    p_hc = np.full(len(opposed), np.nan) if p_hc_b is None else np.asarray(p_hc_b, dtype=float)
    dimensions = {
        "retention": 2,
        "retention_nonnegative": 2,
        "current_only": 1,
        "input_surface": 2,
        "hu_surface": 2,
        "retention_hu": 3,
    }
    if model not in dimensions:
        raise ValueError(f"unknown model: {model}")

    def unpack(theta: np.ndarray) -> dict[str, float]:
        if model == "retention":
            B, gap = theta
            return {"A": float(B + gap), "B": float(B)}
        if model == "retention_nonnegative":
            A, B = theta
            return {"A": float(A), "B": float(B)}
        if model == "current_only":
            return {"C": float(theta[0])}
        if model == "input_surface":
            return {"input": float(theta[0]), "surface": float(theta[1])}
        if model == "hu_surface":
            return {"surface": float(theta[0]), "HU": float(theta[1])}
        B, gap, hu = theta
        return {"A": float(B + gap), "B": float(B), "HU": float(hu)}

    def objective_and_gradient(theta: np.ndarray) -> tuple[float, np.ndarray]:
        return grammar_objective_gradient(theta, model, counts, opposed, d, p_hc, old_is_back, alpha)

    result = minimize(
        objective_and_gradient, np.full(dimensions[model], 0.25), method="L-BFGS-B", jac=True,
        bounds=[(0.0, None)] * dimensions[model], options={"maxiter": 1000, "ftol": 1e-13, "gtol": 1e-9},
    )
    objective, gradient = objective_and_gradient(result.x)
    projected = projected_gradient(result.x, gradient)
    finite = finite_difference_gradient(lambda value: objective_and_gradient(value)[0], result.x)
    return GrammarFit(
        model=model, parameters=unpack(result.x), objective=float(objective), regularization_alpha=alpha,
        converged=bool(result.success), iterations=int(result.nit),
        internal_coordinates=tuple(map(float, result.x)), gradient=tuple(map(float, gradient)),
        projected_gradient_max_abs=float(np.max(np.abs(projected))),
        finite_difference_max_abs_error=float(np.max(np.abs(finite - gradient))),
    )


def grammar_fit_gate(
    fit: GrammarFit, kkt_tolerance: float = 1e-5, finite_difference_tolerance: float = 2e-5,
) -> FitGate:
    reasons = []
    if not fit.converged:
        reasons.append("optimizer_not_converged")
    if not math.isfinite(fit.objective) or not np.all(np.isfinite(fit.internal_coordinates)):
        reasons.append("nonfinite_fit")
    if fit.projected_gradient_max_abs > kkt_tolerance:
        reasons.append("projected_kkt_above_tolerance")
    if fit.finite_difference_max_abs_error > finite_difference_tolerance:
        reasons.append("analytic_gradient_disagreement")
    return FitGate(passed=not reasons, reasons=tuple(reasons))


def stress_hu_quadrature() -> dict:

    records = []
    for total in (1, 10, 100, 1000, 10000):
        for successes in sorted({0, total // 2, total}):
            for sigma in (0.01, 0.5, 2.0, 10.0):
                for eta in (-10.0, 0.0, 10.0):
                    X = np.ones((1, 1))
                    direct = hu_root_loglik_quad([eta], sigma, X, [successes], [total])
                    gh40 = hu_loglik_adaptive_gh([eta], sigma, X, [successes], [total], ["stress"], 40)
                    gh80 = hu_loglik_adaptive_gh([eta], sigma, X, [successes], [total], ["stress"], 80)
                    laplace = hu_loglik_laplace([eta], sigma, X, [successes], [total], ["stress"])
                    mode, curvature, iterations = _root_mode_curvature(
                        np.array([eta]), np.array([float(successes)]), np.array([float(total)]), sigma,
                    )
                    records.append({
                        "n": total, "y": successes, "sigma": sigma, "eta": eta,
                        "mode": mode, "curvature": curvature, "mode_iterations": iterations,
                        "gh40_error": abs(gh40 - direct), "gh80_error": abs(gh80 - direct),
                        "laplace_error": abs(laplace - direct),
                    })
    if not all(math.isfinite(value) for row in records for key, value in row.items() if key not in {"n", "y"}):
        raise AssertionError("nonfinite HU stress result")
    key40 = max(records, key=lambda row: row["gh40_error"])
    key80 = max(records, key=lambda row: row["gh80_error"])
    key_laplace = max(records, key=lambda row: row["laplace_error"])
    
    
    
    if key80["gh80_error"] > 2e-2:
        raise AssertionError(("adaptive GH80 stress discrepancy exceeds declared guard", key80))
    return {
        "cases": len(records),
        "grid": {
            "n": [1, 10, 100, 1000, 10000],
            "successes": "zero, integer midpoint, all",
            "sigma": [0.01, 0.5, 2.0, 10.0],
            "eta": [-10.0, 0.0, 10.0],
        },
        "max_mode_iterations": max(row["mode_iterations"] for row in records),
        "worst_gh40": key40,
        "worst_gh80": key80,
        "worst_laplace": key_laplace,
    }


def run_synthetic_checks(seed: int) -> dict:
    rng = np.random.default_rng(seed)

    
    alpha_true, beta_true = 2.4, 4.1
    totals = rng.integers(3, 70, size=1200)
    propensities = rng.beta(alpha_true, beta_true, size=len(totals))
    raised = rng.binomial(totals, propensities)
    bb_fit = fit_beta_binomial(raised, totals)
    bb_gate = beta_binomial_gate(bb_fit)
    if not bb_gate.passed:
        raise AssertionError(("beta-binomial production gate", bb_gate))
    fitted_mean = bb_fit.alpha / (bb_fit.alpha + bb_fit.beta)
    true_mean = alpha_true / (alpha_true + beta_true)
    if abs(fitted_mean - true_mean) > 0.035:
        raise AssertionError((fitted_mean, true_mean))
    boundary_d = [
        raising_cost_difference(0, 0, bb_fit.alpha, bb_fit.beta),
        raising_cost_difference(0, 10, bb_fit.alpha, bb_fit.beta),
        raising_cost_difference(10, 10, bb_fit.alpha, bb_fit.beta),
    ]
    if not all(np.isfinite(boundary_d)) or not (boundary_d[1] > boundary_d[0] > boundary_d[2]):
        raise AssertionError(boundary_d)
    bb_test_theta = np.log([1.7, 3.2])
    def bb_objective(theta: np.ndarray) -> float:
        alpha, beta = np.exp(theta)
        return -beta_binomial_loglik(raised, totals, float(alpha), float(beta))
    bb_analytic = -beta_binomial_loglik_gradient(raised, totals, 1.7, 3.2) * np.array([1.7, 3.2])
    bb_finite = finite_difference_gradient(bb_objective, bb_test_theta)
    bb_gradient_error = float(np.max(np.abs(bb_analytic - bb_finite)))
    if bb_gradient_error > 2e-5 or bb_fit.gradient_max_abs > 2e-4:
        raise AssertionError((bb_gradient_error, bb_fit.gradient_max_abs))
    bb_boundary_fits = {
        "all_zero": fit_beta_binomial(np.zeros(24), np.full(24, 20.0)),
        "all_success": fit_beta_binomial(np.full(24, 20.0), np.full(24, 20.0)),
        "zero_mid_all": fit_beta_binomial(
            np.tile(np.array([0.0, 10.0, 20.0]), 12), np.full(36, 20.0),
        ),
    }
    if any(not math.isfinite(fit.objective) for fit in bb_boundary_fits.values()):
        raise AssertionError(bb_boundary_fits)
    if not (
        bb_boundary_fits["all_zero"].at_bound
        and bb_boundary_fits["all_success"].at_bound
        and not bb_boundary_fits["zero_mid_all"].at_bound
        and bb_boundary_fits["zero_mid_all"].converged
    ):
        raise AssertionError(("beta-binomial boundary diagnostic", bb_boundary_fits))

    
    root_count = 180
    last = np.where(rng.random(root_count) < 0.5, "B", "F")
    logn = rng.normal(0, 0.8, root_count)
    rho = rng.beta(2.0, 3.0, root_count)
    name = rng.random(root_count) < 0.10
    ane = rng.random(root_count) < 0.12
    che = rng.random(root_count) < 0.09
    X = hu_design_matrix(last, logn, rho, name, ane, che)
    beta_true_vec = np.array([-0.3, 0.8, 0.25, -0.5, 0.15, 0.2, -0.1, 0.08, 0.3, -0.2, 0.25])
    sigma_true = 0.55
    random_intercepts = rng.normal(0.0, sigma_true, root_count)
    hu_totals = rng.integers(18, 55, root_count)
    hu_successes = rng.binomial(hu_totals, expit(X @ beta_true_vec + random_intercepts))
    root_ids = [f"synthetic_{i:04d}" for i in range(root_count)]

    
    quadrature_differences = []
    laplace_differences = []
    for i in (3, 77, 141):
        gh = hu_loglik_adaptive_gh(beta_true_vec, sigma_true, X[i:i+1], hu_successes[i:i+1], hu_totals[i:i+1], [root_ids[i]], 60)
        direct = hu_root_loglik_quad(beta_true_vec, sigma_true, X[i:i+1], hu_successes[i:i+1], hu_totals[i:i+1])
        laplace = hu_loglik_laplace(beta_true_vec, sigma_true, X[i:i+1], hu_successes[i:i+1], hu_totals[i:i+1], [root_ids[i]])
        quadrature_differences.append(abs(gh - direct))
        laplace_differences.append(abs(laplace - direct))
    if max(quadrature_differences) > 1e-8:
        raise AssertionError(quadrature_differences)
    quadrature_stress = stress_hu_quadrature()

    hu_fit = fit_hu_glmm(X, hu_successes, hu_totals, root_ids, method="laplace")
    hu_gate = hu_glmm_gate(hu_fit)
    if not hu_gate.passed:
        raise AssertionError(("HU GLMM production gate", hu_gate))
    prediction_rmse = float(np.sqrt(np.mean((predict_hu_probability(hu_fit, X) - expit(X @ beta_true_vec)) ** 2)))
    if prediction_rmse > 0.12:
        raise AssertionError(prediction_rmse)
    adaptive_at_laplace = hu_loglik_adaptive_gh(hu_fit.beta, hu_fit.sigma, X, hu_successes, hu_totals, root_ids, 80)
    laplace_at_laplace = hu_loglik_laplace(hu_fit.beta, hu_fit.sigma, X, hu_successes, hu_totals, root_ids)
    adaptive_laplace_discrepancy = float(adaptive_at_laplace - laplace_at_laplace)
    hu_adaptive_fit = fit_hu_glmm(X, hu_successes, hu_totals, root_ids, method="gh", nodes=80)
    hu_adaptive_gate = hu_glmm_gate(hu_adaptive_fit)
    if not hu_adaptive_gate.passed:
        raise AssertionError(("adaptive HU GLMM numerical-sensitivity gate", hu_adaptive_gate))
    if hu_fit.design_rank != len(HU_COLUMNS) or hu_fit.projected_gradient_max_abs > 5e-3:
        raise AssertionError((hu_fit.design_rank, hu_fit.projected_gradient_max_abs))

    
    strata = [f"{last[i]}|{'a' if i % 2 else 'e'}" for i in range(root_count)]
    folds_one = assign_input_stratified_folds(root_ids, strata, 5, "uyghur-t7-synthetic-v1")
    folds_two = assign_input_stratified_folds(root_ids, strata, 5, "uyghur-t7-synthetic-v1")
    if folds_one != folds_two or set(folds_one) != set(root_ids):
        raise AssertionError("fold assignment is not deterministic/exhaustive")
    nested = assign_nested_root_folds(root_ids, strata, 5, 3, "AUDIT-POLISH-2.0-CODEX-UYGHUR-NOMINAL-V1")
    for outer_fold, inner in nested["inner_by_outer_fold"].items():
        held_out = {root for root, fold in nested["outer"].items() if fold == int(outer_fold)}
        if held_out.intersection(inner) or set(inner) != set(root_ids) - held_out:
            raise AssertionError("nested fold leakage or omission")
    selected_alpha = select_regularization_alpha({0.0: -1.3, 0.0001: -1.2, 0.001: -1.2 - 5e-9, 0.01: -1.4}, 1e-8)
    if selected_alpha != 0.001:
        raise AssertionError(selected_alpha)
    metric_check = predictive_log_density_metrics(
        ["r1", "r1", "r2"], [-0.1, -0.2, -1.0], [1, 3, 1],
    )
    if not np.allclose(
        [metric_check["root_balanced_mean_log_density"], metric_check["incidence_weighted_mean_log_density"]],
        [-0.5875, -0.34],
    ):
        raise AssertionError(metric_check)

    
    A, B, d = 1.7, 0.6, -0.2
    retention = candidate_costs("retention", True, d, {"A": A, "B": B})
    retention_nonnegative = candidate_costs("retention_nonnegative", True, d, {"A": A, "B": A + 0.4})
    current = candidate_costs("current_only", True, d, {"C": A})
    matched = candidate_costs("input_surface", True, d, {"input": A - B / 2.0, "surface": B / 2.0})
    if not np.allclose(retention, [0.0, A, d + B, d + A]):
        raise AssertionError(retention)
    if np.allclose(retention, current):
        raise AssertionError("current-only was collapsed into a retention endpoint")
    if not np.allclose(retention_nonnegative, [0.0, A, d + A + 0.4, d + A]):
        raise AssertionError(retention_nonnegative)
    
    if not np.allclose([retention[1] - retention[0], retention[3] - retention[2]],
                       [matched[1] - matched[0], matched[3] - matched[2]]):
        raise AssertionError((retention, matched))
    
    if not np.allclose(retention[2:] - matched[2:], [B / 2.0, B / 2.0]):
        raise AssertionError((retention, matched))

    
    
    tensor_checks = {
        "retention": (np.array([0.4, 0.9]), {"A": 1.3, "B": 0.4}),
        "retention_nonnegative": (np.array([1.3, 0.4]), {"A": 1.3, "B": 0.4}),
        "current_only": (np.array([0.7]), {"C": 0.7}),
        "input_surface": (np.array([0.8, 0.3]), {"input": 0.8, "surface": 0.3}),
        "hu_surface": (np.array([0.7, 0.5]), {"surface": 0.7, "HU": 0.5}),
        "retention_hu": (np.array([0.4, 0.9, 0.5]), {"A": 1.3, "B": 0.4, "HU": 0.5}),
    }
    for model, (coordinates, parameters) in tensor_checks.items():
        for is_opposed in (False, True):
            p_hc, old_back, baseline_d = 0.3, True, -0.17
            tensor = _grammar_feature_tensor(
                model, np.array([is_opposed]), np.array([p_hc]), np.array([old_back]),
            )[0]
            fixed = np.array([0.0, 0.0, baseline_d, baseline_d])
            scalar = candidate_costs(model, is_opposed, baseline_d, parameters, p_hc, old_back)
            if not np.allclose(fixed + tensor @ coordinates, scalar):
                raise AssertionError(("scalar/vectorized cost mismatch", model, is_opposed, tensor, scalar))

    
    grammar_rows = 160
    grammar_opposed = rng.random(grammar_rows) < 0.5
    grammar_d = rng.normal(0.0, 0.8, grammar_rows)
    grammar_counts = np.vstack([
        rng.multinomial(
            500,
            probabilities(candidate_costs("retention", bool(grammar_opposed[i]), float(grammar_d[i]), {"A": 1.4, "B": 0.5})),
        )
        for i in range(grammar_rows)
    ])
    grammar_fit = fit_grammar("retention", grammar_counts, grammar_opposed, grammar_d)
    grammar_gate = grammar_fit_gate(grammar_fit)
    if not grammar_gate.passed:
        raise AssertionError(("grammar production gate", grammar_gate))
    if abs(grammar_fit.parameters["A"] - 1.4) > 0.08 or abs(grammar_fit.parameters["B"] - 0.5) > 0.08:
        raise AssertionError(grammar_fit)
    if grammar_fit.projected_gradient_max_abs > 1e-5 or grammar_fit.finite_difference_max_abs_error > 2e-5:
        raise AssertionError(grammar_fit)

    
    gradient_checks = {}
    check_counts = grammar_counts[:12]
    check_opposed = grammar_opposed[:12]
    check_d = grammar_d[:12]
    check_p = rng.uniform(0.05, 0.95, len(check_counts))
    check_old = rng.random(len(check_counts)) < 0.5
    check_parameters = {
        "retention": np.array([0.4, 0.9]),
        "retention_nonnegative": np.array([1.3, 0.4]),
        "current_only": np.array([0.7]),
        "input_surface": np.array([0.8, 0.3]),
        "hu_surface": np.array([0.7, 0.5]),
        "retention_hu": np.array([0.4, 0.9, 0.5]),
    }
    for model, theta in check_parameters.items():
        hu = check_p if "hu" in model else None
        objective, analytic = grammar_objective_gradient(theta, model, check_counts, check_opposed, check_d, hu, check_old, 0.17)
        finite = finite_difference_gradient(
            lambda value: grammar_objective_gradient(value, model, check_counts, check_opposed, check_d, hu, check_old, 0.17)[0],
            theta,
        )
        error = float(np.max(np.abs(analytic - finite)))
        if error > 2e-5:
            raise AssertionError((model, objective, analytic, finite))
        gradient_checks[model] = {"analytic": analytic.tolist(), "finite_difference": finite.tolist(), "max_abs_error": error}

    
    offset_rows = 240
    offset_suffix = np.where(np.arange(offset_rows) % 2 == 0, "dat", "loc")
    offset_d = rng.normal(0.0, 0.8, offset_rows)
    true_offsets = np.where(offset_suffix == "dat", 0.28, -0.36)
    offset_totals = rng.integers(30, 100, offset_rows)
    offset_raised = rng.binomial(offset_totals, expit(-(offset_d + true_offsets)))
    offset_fit = fit_agreeing_suffix_offsets(
        offset_suffix, offset_d, offset_raised, offset_totals,
        np.zeros(offset_rows, dtype=bool), separation_ridge=1e-4,
    )
    if not offset_fit.converged or abs(offset_fit.dat_offset - 0.28) > 0.08 or abs(offset_fit.loc_offset + 0.36) > 0.08:
        raise AssertionError(offset_fit)
    separation_offset_fit = fit_agreeing_suffix_offsets(
        ["dat", "loc"], [0.0, 0.0], [0.0, 40.0], [40.0, 40.0],
        [False, False], separation_ridge=1e-4,
    )
    if not separation_offset_fit.separation_detected or not np.all(np.isfinite([
        separation_offset_fit.dat_offset, separation_offset_fit.loc_offset,
    ])):
        raise AssertionError(separation_offset_fit)

    return {
        "status": "PASS_SYNTHETIC_ONLY_NO_CORPUS_FIT",
        "seed": seed,
        "python": sys.version,
        "platform": platform.platform(),
        "numpy": np.__version__,
        "beta_binomial": {
            "true": {"alpha": alpha_true, "beta": beta_true, "mean": true_mean},
            "fit": bb_fit.__dict__,
            "production_gate": bb_gate.__dict__,
            "fit_mean": fitted_mean,
            "boundary_cost_differences": boundary_d,
            "analytic_vs_finite_gradient_max_abs_error": bb_gradient_error,
            "boundary_multistart_diagnostics": {
                label: {
                    "fit": fit.__dict__,
                    "production_gate": beta_binomial_gate(fit).__dict__,
                }
                for label, fit in bb_boundary_fits.items()
            },
        },
        "hu_glmm": {
            "columns": HU_COLUMNS,
            "true_sigma": sigma_true,
            "fit": hu_fit.__dict__,
            "production_gate": hu_gate.__dict__,
            "adaptive_fit": hu_adaptive_fit.__dict__,
            "adaptive_fit_gate": hu_adaptive_gate.__dict__,
            "fixed_prediction_rmse": prediction_rmse,
            "adaptive_gh60_vs_mode_shifted_direct_quad_absolute_differences": quadrature_differences,
            "laplace_vs_direct_quad_absolute_differences": laplace_differences,
            "adaptive_minus_laplace_loglik_at_laplace_fit": adaptive_laplace_discrepancy,
            "extreme_grid": quadrature_stress,
            "grammar_feature_prediction_rule": "fixed effects only for training and withheld roots; conditional random intercept exactly zero for both",
        },
        "folds": {
            "outer_count": 5,
            "inner_count": 3,
            "production_seed": "AUDIT-POLISH-2.0-CODEX-UYGHUR-NOMINAL-V1",
            "synthetic_outer_sizes": dict(sorted((str(k), list(folds_one.values()).count(k)) for k in set(folds_one.values()))),
            "nested_partition_invariants": "PASS",
            "regularization_tie_rule_check": selected_alpha,
            "metric_check": metric_check,
        },
        "score_semantics": {
            "retention_opposed": retention.tolist(),
            "retention_nonnegative_opposed_B_gt_A": retention_nonnegative.tolist(),
            "current_only_opposed": current.tolist(),
            "matched_input_surface_opposed": matched.tolist(),
            "retention_minus_matched_raised": (retention[2:] - matched[2:]).tolist(),
            "synthetic_retention_fit": grammar_fit.__dict__,
            "synthetic_retention_gate": grammar_gate.__dict__,
            "all_model_gradient_checks": gradient_checks,
        },
        "agreeing_control_suffix_offset_sensitivity": {
            "fit": offset_fit.__dict__,
            "separation_fit": separation_offset_fit.__dict__,
            "true_offsets": {"dat": 0.28, "loc": -0.36},
            "rule": "training agreeing BB/FF only; two penalized offsets frozen before opposed scoring; common to all models",
        },
        "disclosure": {
            "R_glmer": "not available in the audited runtime",
            "python_route": "SciPy binomial-logit random-intercept marginal likelihood; Laplace primary as glmer nAGQ=1 reconstruction; adaptive GH checked against mode-shifted direct quadrature",
            "corpus_fit": False,
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--synthetic-check", action="store_true")
    parser.add_argument("--seed", type=int, default=764891)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if not args.synthetic_check:
        parser.error("only --synthetic-check is enabled before joint empirical freeze")
    result = run_synthetic_checks(args.seed)
    payload = json.dumps(result, ensure_ascii=False, indent=2) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(payload, encoding="utf-8")
    print(payload, end="")


if __name__ == "__main__":
    main()
