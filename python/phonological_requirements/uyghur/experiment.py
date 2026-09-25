from __future__ import annotations

import argparse
import csv
import hashlib
import json
import math
from collections import defaultdict
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Callable, Iterable, Sequence

import numpy as np
from scipy.special import expit, logsumexp

from hu_laplace_vectorized_wrapper_v4 import (
    fit_hu_glmm_vectorized_gh,
    fit_hu_glmm_vectorized_laplace,
)
from uyghur_beta_posterior_v1 import (
    BetaPosteriorFit,
    beta_binomial_posterior_gate,
    fit_beta_binomial_posterior,
)
from uyghur_grammar_optimizer_v1 import fit_grammar
from statistical_protocol_v2 import (
    GrammarFit,
    HUGLMMFit,
    candidate_costs,
    fit_agreeing_suffix_offsets,
    grammar_fit_gate,
    hu_design_matrix,
    hu_glmm_gate,
    raising_cost_difference,
    select_regularization_alpha,
    _grammar_feature_tensor,
)


HERE = Path(__file__).resolve().parent
REPO = HERE.parents[2]
DATA = REPO / "data/uyghur"
SEED = "AUDIT-POLISH-2.0-CODEX-UYGHUR-NOMINAL-V1"
ALPHA_GRID = (0.0, 0.0001, 0.001, 0.01, 0.1)
MODELS = (
    "retention_bounded",
    "retention_nonnegative",
    "current_only",
    "input_plus_surface",
    "HU_plus_surface",
    "retention_bounded_plus_HU",
)
HU_MODELS = frozenset({"HU_plus_surface", "retention_bounded_plus_HU"})
ANALYSIS_VARIANTS = ("all_strict", "all_agreeing_offsets", "unrounded_strict")
INFORMATION_PROTOCOLS = ("side_informed", "wholly_unseen")
RHO_PRIORS = ("uniform", "beta_half_half")
HU_TAUS = (20.0, 50.0)
MODEL_TO_V2 = {
    "retention_bounded": "retention",
    "retention_nonnegative": "retention_nonnegative",
    "current_only": "current_only",
    "input_plus_surface": "input_surface",
    "HU_plus_surface": "hu_surface",
    "retention_bounded_plus_HU": "retention_hu",
}
EXPECTED_HASHES = {'uyghur_laplace_hessian_v1.py': 'b76f02dcf9891024377fe16d22dce0d0aa02340bf641a026480144537d781552', 'hu_laplace_vectorized_wrapper_v4.py': '382700f1437592f8b91808d5858a1d83c28184756b220d9c4a015d6b568f7017', 'uyghur_hu_gradient_check_v1.py': '10bd3dbb02c16189e438d255a9a648324396d745a8d04123bf3b009c0c815ca0', 'uyghur_laplace_vectorized_v3.py': 'f184822f46f8c92e344cf003aeea142a6cd00d51b824b3e644271f10e7c0c519', 'statistical_protocol_v2.py': '9428d7f030f31f3ac2122806bad36d3cc3641399bec4b5a12ad031d54af977fd', 'uyghur_gh_vectorized_v3.py': 'b1aeeb8741a28f81277c91034a7910594215e51a17dddf4105ba141e9f566f73', 'uyghur_gh_gradient_v3.py': 'cd1c784b02cc3060b9280b92ea81d56e27bfaa36c9b166dee3c226016fd55a71', 'uyghur_beta_posterior_v1.py': '0f270b6fcc04785e2ae9d232016f4fbc4555ca3c27adc2b7e87c311ac60e27d9', 'uyghur_grammar_optimizer_v1.py': 'b8ba0b8d2e22b3bae1c2f4a3601d0d953ae0190b59d8a723e2e443635b3e907c', 'uyghur_hu_regularized_v1.py': '75487a3cba8fd63502e9f029c5eace411964d4f2dc9ff222f59aeaaa0ca7ff26', 'uyghur_hu_newton_polish_v1.py': 'e00f084b963d90466a621923e5d554c335c3b1531de2005281ac8b504c96314a', 'clean_morphology_panel_v3.csv': 'd3ee14c623af2e0c6f7f842d68adfcadc188d05bde8d664b34da020d4964b130', 'clean_transfer_root_table_v2.csv': '8ed463dba3e78218a1625bc073c58562ff4c07d1bbc83ce06e52c4a12e31ecb0', 'uyghur_outer_fold_manifest_v1.csv': 'fded6710f48c1b63cfec4e8939537836c2a15b43c72b75d789d0a57b7ba448a6', 'uyghur_inner_fold_manifest_v1.csv': '314b784a12cfa5406fff3b673790aa881ab6e0e94ac2750e75c356ddf46a128e', 'specification.json': '22b3be3758e8ac8a188127b445c02c0bf2616b802848a1647a6413768be47bc5'}

ANE_EXCEPTIONS = frozenset({"bahane", "epsane", "i'ane", "jerimane", "perwane", "perghane", "péshane", "zamane"})
CHE_EXCEPTIONS = frozenset({"anche", "bunche", "qanche", "birqanche"})


class GateFailure(RuntimeError):
    pass


@dataclass(frozen=True)
class RootRecord:
    root: str
    template: str
    final_low_vowel: str
    unrounded: bool
    outer_fold: int
    target_intended: int
    target_covered: int
    acc_intended: int
    acc_raised: int
    acc_total: int

    @property
    def opposed(self) -> bool:
        return self.template in {"BF", "FB"}

    @property
    def old_is_back(self) -> bool:
        return self.template[-1] == "B"


@dataclass(frozen=True)
class TargetCell:
    root: str
    morphology: str
    source: str
    counts: tuple[int, int, int, int]

    @property
    def total(self) -> int:
        return sum(self.counts)


@dataclass(frozen=True)
class Dataset:
    roots: dict[str, RootRecord]
    cells: tuple[TargetCell, ...]
    inner_folds: dict[tuple[int, str], int]
    input_hashes: dict[str, str]


@dataclass(frozen=True)
class Block:
    roots: tuple[str, ...]
    sample_scope: str
    key: str


@dataclass(frozen=True)
class BetaBundle:
    key: str
    rho_prior: str
    fits: dict[str, BetaPosteriorFit]


@dataclass(frozen=True)
class HUBundle:
    key: str
    approximation: str
    tau: float
    fit: HUGLMMFit
    log_frequency_mean: float
    log_frequency_sd: float


@dataclass(frozen=True)
class OffsetBundle:
    key: str
    dat: float
    loc: float
    diagnostics: dict[str, object]


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def stable_hash(value: object) -> str:
    payload = json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":"))
    return hashlib.sha256(payload.encode("utf-8")).hexdigest()


def bool_field(value: str) -> bool:
    if value.lower() not in {"true", "false"}:
        raise ValueError(f"invalid boolean field: {value}")
    return value.lower() == "true"


def integer_field(value: str) -> int:
    parsed = float(value)
    if not parsed.is_integer() or parsed < 0:
        raise ValueError(f"invalid count: {value}")
    return int(parsed)


def verify_frozen_hashes() -> dict[str, str]:
    actual = {}
    for relative, expected in EXPECTED_HASHES.items():
        path = (HERE / relative if relative.endswith(".py") else DATA / relative).resolve()
        observed = sha256(path)
        if observed != expected:
            raise RuntimeError(f"frozen hash mismatch: {relative}: {observed} != {expected}")
        actual[relative] = observed
    decisions = json.loads((DATA / "specification.json").read_text())
    if tuple(decisions["models"]) != MODELS:
        raise RuntimeError("model list disagrees with frozen decisions")
    if tuple(map(float, decisions["grammar_fitting"]["alpha_grid"])) != ALPHA_GRID:
        raise RuntimeError("alpha grid disagrees with frozen decisions")
    if (float(decisions["HU_estimator"]["primary_tau"]), float(decisions["HU_estimator"]["fixed_sensitivity_tau"])) != HU_TAUS:
        raise RuntimeError("HU tau values disagree with frozen decisions")
    return actual


def load_dataset() -> Dataset:
    input_hashes = verify_frozen_hashes()
    outer_path = DATA / "uyghur_outer_fold_manifest_v1.csv"
    with outer_path.open(newline="", encoding="utf-8") as stream:
        outer_rows = list(csv.DictReader(stream))
    roots: dict[str, RootRecord] = {}
    for row in outer_rows:
        record = RootRecord(
            root=row["root"], template=row["template"], final_low_vowel=row["final_low_vowel"],
            unrounded=bool_field(row["unrounded"]), outer_fold=int(row["outer_fold"]),
            target_intended=integer_field(row["target_intended_incidences"]),
            target_covered=integer_field(row["target_covered_incidences"]),
            acc_intended=integer_field(row["acc_intended_incidences"]),
            acc_raised=0, acc_total=0,
        )
        if record.root in roots:
            raise RuntimeError(f"duplicate outer root: {record.root}")
        roots[record.root] = record

    inner_path = DATA / "uyghur_inner_fold_manifest_v1.csv"
    with inner_path.open(newline="", encoding="utf-8") as stream:
        inner_rows = list(csv.DictReader(stream))
    inner = {(int(row["outer_fold"]), row["root"]): int(row["inner_fold"]) for row in inner_rows}
    if len(inner) != len(inner_rows):
        raise RuntimeError("duplicate inner manifest row")

    panel_path = DATA / "clean_morphology_panel_v3.csv"
    with panel_path.open(newline="", encoding="utf-8") as stream:
        panel = list(csv.DictReader(stream))
    acc: dict[str, list[int]] = defaultdict(lambda: [0, 0])
    target_counts: dict[tuple[str, str, str], np.ndarray] = defaultdict(lambda: np.zeros(4, dtype=int))
    for row in panel:
        root = row["root"]
        if root not in roots or not bool_field(row["primary_observer_covered"]):
            continue
        count = integer_field(row["incidences"])
        morphology = row["morphology"]
        raised_class = row["observed_root_surface_class"]
        if morphology == "acc":
            if raised_class not in {"neutral_i", "unraised"}:
                raise RuntimeError("covered accusative row has an unsupported root outcome")
            acc[root][1] += count
            if raised_class == "neutral_i":
                acc[root][0] += count
            continue
        if morphology not in {"dat", "loc"}:
            continue
        harmony = row["harmony_visibility"]
        if raised_class not in {"neutral_i", "unraised"} or harmony not in {"front", "back"}:
            raise RuntimeError("covered target row has an unsupported observer outcome")
        old_back = roots[root].old_is_back
        suffix_back = harmony == "back"
        old = suffix_back == old_back
        raised = raised_class == "neutral_i"
        index = (2 if raised else 0) + (0 if old else 1)
        target_counts[(root, morphology, row["source"])][index] += count

    roots = {
        root: RootRecord(**{
            **asdict(record), "acc_raised": acc[root][0], "acc_total": acc[root][1],
        })
        for root, record in roots.items()
    }
    cells = tuple(
        TargetCell(root=root, morphology=morphology, source=source, counts=tuple(map(int, counts)))
        for (root, morphology, source), counts in sorted(target_counts.items())
    )
    if len(roots) != 524 or sum(record.target_covered > 0 for record in roots.values()) != 515:
        raise RuntimeError("root denominators changed")
    if sum(record.target_intended for record in roots.values()) != 59632:
        raise RuntimeError("intended target incidence count changed")
    if sum(cell.total for cell in cells) != 58577:
        raise RuntimeError("covered target incidence count changed")
    if sum(record.acc_intended > 0 for record in roots.values()) != 377:
        raise RuntimeError("accusative input availability count changed")
    if sum(record.acc_total > 0 for record in roots.values()) != 369:
        raise RuntimeError("interpretable accusative availability count changed")
    for fold in range(5):
        expected_training = {root for root, record in roots.items() if record.outer_fold != fold}
        observed_training = {root for (outer, root), _ in inner.items() if outer == fold}
        if expected_training != observed_training:
            raise RuntimeError(f"inner manifest does not equal outer training set for fold {fold}")
    return Dataset(roots=roots, cells=cells, inner_folds=inner, input_hashes=input_hashes)


def roots_for_scope(dataset: Dataset, roots: Iterable[str], sample_scope: str) -> tuple[str, ...]:
    members = sorted(set(roots))
    if sample_scope == "all":
        return tuple(members)
    if sample_scope == "unrounded":
        return tuple(root for root in members if dataset.roots[root].unrounded)
    raise ValueError(f"unknown sample scope: {sample_scope}")


def variant_scope(variant: str) -> str:
    return "unrounded" if variant == "unrounded_strict" else "all"


def make_block(dataset: Dataset, training_roots: Iterable[str], sample_scope: str) -> Block:
    roots = roots_for_scope(dataset, training_roots, sample_scope)
    cells = [cell for cell in dataset.cells if cell.root in set(roots)]
    signature = {
        "roots": [asdict(dataset.roots[root]) for root in roots],
        "cells": [asdict(cell) for cell in cells],
        "sample_scope": sample_scope,
        "panel_sha256": dataset.input_hashes["clean_morphology_panel_v3.csv"],
        "numerics_sha256": dataset.input_hashes["statistical_protocol_v2.py"],
        "wrapper_sha256": dataset.input_hashes["hu_laplace_vectorized_wrapper_v4.py"],
        "decision_sha256": dataset.input_hashes["specification.json"],
    }
    return Block(roots=roots, sample_scope=sample_scope, key=stable_hash(signature))


def target_rows(dataset: Dataset, roots: Sequence[str]) -> list[tuple[str, str, np.ndarray]]:
    selected = set(roots)
    aggregated: dict[tuple[str, str], np.ndarray] = defaultdict(lambda: np.zeros(4, dtype=float))
    for cell in dataset.cells:
        if cell.root in selected:
            aggregated[(cell.root, cell.morphology)] += np.asarray(cell.counts, dtype=float)
    return [(root, morphology, counts) for (root, morphology), counts in sorted(aggregated.items())]


def fit_beta_bundle(
    dataset: Dataset, block: Block, rho_prior: str,
    failure: Callable[[str, dict[str, object]], None] | None = None,
) -> BetaBundle:
    if rho_prior not in RHO_PRIORS:
        raise ValueError(f"unknown fixed rho prior: {rho_prior}")
    fits = {}
    for vowel in ("a", "e"):
        records = [dataset.roots[root] for root in block.roots if dataset.roots[root].final_low_vowel == vowel]
        if not records:
            raise GateFailure(f"beta-binomial has no {vowel} roots in block {block.key}")
        fit = fit_beta_binomial_posterior(
            [record.acc_raised for record in records],
            [record.acc_total for record in records],
            rho_prior=rho_prior,
        )
        gate = beta_binomial_posterior_gate(fit)
        if not gate.passed:
            if failure is not None:
                failure("beta", {
                    "block_key": block.key, "roots": block.roots, "final_low_vowel": vowel,
                    "rho_prior": rho_prior,
                    "successes": [record.acc_raised for record in records],
                    "totals": [record.acc_total for record in records],
                    "fit": asdict(fit), "gate": asdict(gate),
                })
            raise GateFailure(f"beta-binomial gate failed for {vowel}/{block.key}: {gate.reasons}")
        fits[vowel] = fit
    return BetaBundle(
        key=stable_hash({
            "kind": "beta_posterior", "block": block.key, "rho_prior": rho_prior,
            "implementation_sha256": EXPECTED_HASHES["uyghur_beta_posterior_v1.py"],
        }),
        rho_prior=rho_prior,
        fits=fits,
    )


def root_d(dataset: Dataset, beta: BetaBundle, root: str, side_visible: bool) -> float:
    record = dataset.roots[root]
    raised = record.acc_raised if side_visible else 0
    total = record.acc_total if side_visible else 0
    fit = beta.fits[record.final_low_vowel]
    return raising_cost_difference(raised, total, fit.alpha, fit.beta)


def exception_flags(root: str) -> tuple[bool, bool, bool]:
    return root.endswith("name"), root.endswith("ane") and root not in ANE_EXCEPTIONS, root.endswith("che") and root not in CHE_EXCEPTIONS


def hu_matrix_for_roots(
    dataset: Dataset,
    beta: BetaBundle,
    roots: Sequence[str],
    log_frequency_mean: float,
    log_frequency_sd: float,
    side_visible: bool,
) -> np.ndarray:
    last = []
    log_frequency = []
    raised_prop = []
    name, ane, che = [], [], []
    if log_frequency_sd <= 0 or not math.isfinite(log_frequency_sd):
        raise GateFailure("invalid training log-frequency scale")
    for root in roots:
        record = dataset.roots[root]
        visible_n = record.acc_total if side_visible else 0
        visible_k = record.acc_raised if side_visible else 0
        beta_fit = beta.fits[record.final_low_vowel]
        last.append(record.template[-1])
        log_frequency.append((math.log1p(visible_n) - log_frequency_mean) / log_frequency_sd)
        raised_prop.append((visible_k + beta_fit.alpha) / (visible_n + beta_fit.alpha + beta_fit.beta))
        is_name, is_ane, is_che = exception_flags(root)
        name.append(is_name); ane.append(is_ane); che.append(is_che)
    return hu_design_matrix(last, log_frequency, raised_prop, name, ane, che)


def fit_hu_bundle(
    dataset: Dataset, block: Block, beta: BetaBundle, approximation: str,
    tau: float,
    failure: Callable[[str, dict[str, object]], None] | None = None,
) -> HUBundle:
    log_frequency = np.asarray([math.log1p(dataset.roots[root].acc_total) for root in block.roots])
    mean = float(log_frequency.mean())
    sd = float(log_frequency.std(ddof=0))
    if not math.isfinite(sd) or sd <= 1e-12:
        raise GateFailure(f"HU log-frequency scale degenerates in block {block.key}")
    response: dict[str, list[int]] = {root: [0, 0] for root in block.roots}
    for root, _, counts in target_rows(dataset, block.roots):
        record = dataset.roots[root]
        back = int(counts[0] + counts[2]) if record.old_is_back else int(counts[1] + counts[3])
        response[root][0] += back
        response[root][1] += int(counts.sum())
    response_roots = [root for root in block.roots if response[root][1] > 0]
    X = hu_matrix_for_roots(dataset, beta, response_roots, mean, sd, side_visible=True)
    y = [response[root][0] for root in response_roots]
    n = [response[root][1] for root in response_roots]
    if approximation == "laplace":
        fit = fit_hu_glmm_vectorized_laplace(X, y, n, response_roots, tau=tau)
    elif approximation == "gh80":
        fit = fit_hu_glmm_vectorized_gh(X, y, n, response_roots, tau=tau, nodes=80)
    else:
        raise ValueError(f"unknown HU approximation: {approximation}")
    gate = hu_glmm_gate(fit)
    if not gate.passed:
        if failure is not None:
            failure("hu", {
                "block_key": block.key, "roots": block.roots, "beta_key": beta.key,
                "approximation": approximation, "tau": tau, "response_roots": response_roots,
                "successes": y, "totals": n, "design_sha256": stable_hash(X.tolist()),
                "design_shape": list(X.shape), "log_frequency_mean": mean,
                "log_frequency_sd": sd, "fit": asdict(fit), "gate": asdict(gate),
            })
        raise GateFailure(f"HU {approximation} gate failed for {block.key}: {gate.reasons}")
    return HUBundle(
        key=stable_hash({
            "kind": "HU", "block": block.key, "beta": beta.key,
            "approximation": approximation, "tau": tau,
        }),
        approximation=approximation, tau=tau, fit=fit,
        log_frequency_mean=mean, log_frequency_sd=sd,
    )


def q_hu(dataset: Dataset, beta: BetaBundle, hu: HUBundle, root: str, side_visible: bool) -> float:
    X = hu_matrix_for_roots(
        dataset, beta, [root], hu.log_frequency_mean, hu.log_frequency_sd, side_visible,
    )
    return float(expit(X @ np.asarray(hu.fit.beta))[0])


def fit_offsets(
    dataset: Dataset, block: Block, beta: BetaBundle,
    failure: Callable[[str, dict[str, object]], None] | None = None,
) -> OffsetBundle:
    suffix, d, raised, total = [], [], [], []
    for root, morphology, counts in target_rows(dataset, block.roots):
        record = dataset.roots[root]
        if record.opposed:
            continue
        suffix.append(morphology)
        d.append(root_d(dataset, beta, root, side_visible=True))
        raised.append(float(counts[2] + counts[3]))
        total.append(float(counts.sum()))
    fit = fit_agreeing_suffix_offsets(
        suffix, d, raised, total, [False] * len(suffix), separation_ridge=0.0001,
    )
    if (
        not fit.converged or not np.all(np.isfinite([fit.dat_offset, fit.loc_offset, fit.objective]))
        or fit.gradient_max_abs > 1e-7 or fit.finite_difference_max_abs_error > 2e-5
    ):
        if failure is not None:
            failure("offset", {
                "block_key": block.key, "roots": block.roots, "beta_key": beta.key,
                "suffix": suffix, "d": d, "raised": raised, "total": total,
                "fit": asdict(fit),
            })
        raise GateFailure(f"agreeing-offset gate failed for {block.key}: {fit}")
    return OffsetBundle(
        key=stable_hash({"kind": "offset", "block": block.key, "beta": beta.key, "fit": asdict(fit)}),
        dat=fit.dat_offset, loc=fit.loc_offset, diagnostics=asdict(fit),
    )


class FitStore:


    def __init__(self, directory: Path, rho_prior: str, hu_tau: float):
        if rho_prior not in RHO_PRIORS:
            raise ValueError(f"unknown fixed rho prior: {rho_prior}")
        if float(hu_tau) not in HU_TAUS:
            raise ValueError(f"unknown fixed HU tau: {hu_tau}")
        self.directory = directory
        self.directory.mkdir(parents=True, exist_ok=True)
        self.rho_prior = rho_prior
        self.hu_tau = float(hu_tau)
        self.beta: dict[str, BetaBundle] = {}
        self.hu: dict[tuple[str, str, float], HUBundle] = {}
        self.offset: dict[str, OffsetBundle] = {}
        self.grammar: dict[str, GrammarFit] = {}

    def record(self, kind: str, key: str, payload: dict[str, object]) -> None:
        path = self.directory / f"{kind}_{key}.json"
        serialized = json.dumps({"kind": kind, "cache_key": key, **payload}, ensure_ascii=False, indent=2) + "\n"
        if path.exists() and path.read_text(encoding="utf-8") != serialized:
            raise RuntimeError(f"cache collision/mutation: {path}")
        path.write_text(serialized, encoding="utf-8")

    def failure(self, kind: str, payload: dict[str, object]) -> None:
        key = stable_hash({"kind": kind, "payload": payload})
        self.record(f"failure_{kind}", key, {
            "status": "HARD_STOP_FULL_DIAGNOSTICS_PRESERVED", **payload,
        })

    def beta_bundle(self, dataset: Dataset, block: Block) -> BetaBundle:
        if block.key not in self.beta:
            bundle = fit_beta_bundle(dataset, block, self.rho_prior, self.failure)
            self.beta[block.key] = bundle
            self.record("beta", bundle.key, {
                "block_key": block.key, "roots": block.roots, "rho_prior": self.rho_prior,
                "fits": {label: asdict(fit) for label, fit in bundle.fits.items()},
            })
        return self.beta[block.key]

    def hu_bundle(self, dataset: Dataset, block: Block, approximation: str) -> HUBundle:
        lookup = (block.key, approximation, self.hu_tau)
        if lookup not in self.hu:
            beta = self.beta_bundle(dataset, block)
            bundle = fit_hu_bundle(
                dataset, block, beta, approximation, self.hu_tau, self.failure,
            )
            self.hu[lookup] = bundle
            self.record("hu", bundle.key, {
                "block_key": block.key, "beta_key": beta.key, "approximation": approximation,
                "tau": self.hu_tau,
                "fit": asdict(bundle.fit), "log_frequency_mean": bundle.log_frequency_mean,
                "log_frequency_sd": bundle.log_frequency_sd,
            })
        return self.hu[lookup]

    def offset_bundle(self, dataset: Dataset, block: Block) -> OffsetBundle:
        if block.key not in self.offset:
            beta = self.beta_bundle(dataset, block)
            bundle = fit_offsets(dataset, block, beta, self.failure)
            self.offset[block.key] = bundle
            self.record("offset", bundle.key, {
                "block_key": block.key, "beta_key": beta.key, "dat": bundle.dat, "loc": bundle.loc,
                "diagnostics": bundle.diagnostics,
            })
        return self.offset[block.key]


def grammar_training_arrays(
    dataset: Dataset,
    block: Block,
    store: FitStore,
    variant: str,
    model: str,
    approximation: str,
) -> tuple[np.ndarray, np.ndarray, np.ndarray, np.ndarray | None, np.ndarray]:
    beta = store.beta_bundle(dataset, block)
    hu = store.hu_bundle(dataset, block, approximation) if model in HU_MODELS else None
    offsets = store.offset_bundle(dataset, block) if variant == "all_agreeing_offsets" else None
    rows = target_rows(dataset, block.roots)
    counts, opposed, d_values, q_values, old_back = [], [], [], [], []
    for root, morphology, observed in rows:
        record = dataset.roots[root]
        d_value = root_d(dataset, beta, root, side_visible=True)
        if offsets is not None:
            d_value += offsets.dat if morphology == "dat" else offsets.loc
        counts.append(observed)
        opposed.append(record.opposed)
        d_values.append(d_value)
        old_back.append(record.old_is_back)
        if hu is not None:
            q_values.append(q_hu(dataset, beta, hu, root, side_visible=True))
    return (
        np.asarray(counts), np.asarray(opposed), np.asarray(d_values),
        np.asarray(q_values) if hu is not None else None, np.asarray(old_back),
    )


def grammar_support_diagnostics(
    model: str,
    counts: np.ndarray,
    opposed: np.ndarray,
    q_values: np.ndarray | None,
    old_back: np.ndarray,
) -> dict[str, object]:
    q = np.full(len(counts), np.nan) if q_values is None else np.asarray(q_values, dtype=float)
    features = _grammar_feature_tensor(MODEL_TO_V2[model], opposed, q, old_back)
    differences = features[:, 1:, :] - features[:, :1, :]
    matrix = differences.reshape(-1, differences.shape[-1])
    support_masks: dict[str, int] = defaultdict(int)
    for row in counts:
        support_masks["".join("1" if value > 0 else "0" for value in row)] += 1
    return {
        "four_cell_totals": list(map(float, counts.sum(axis=0))),
        "support_mask_row_counts": dict(sorted(support_masks.items())),
        "training_rows": int(len(counts)),
        "feature_difference_rows": int(matrix.shape[0]),
        "feature_difference_columns": int(matrix.shape[1]),
        "feature_difference_rank": int(np.linalg.matrix_rank(matrix)),
        "feature_difference_sha256": stable_hash(matrix.tolist()),
        "coercivity_status": "REQUIRES_ROOT_SEPARABILITY_REVIEW" if np.any(counts.sum(axis=0) == 0) else "SUPPORT_RECORDED_REQUIRES_ROOT_SEPARABILITY_REVIEW",
    }


def grammar_fit_cached(
    dataset: Dataset,
    block: Block,
    store: FitStore,
    variant: str,
    model: str,
    approximation: str,
    alpha: float,
) -> tuple[str, GrammarFit]:
    numerical_approximation = approximation if model in HU_MODELS else "not_applicable"
    beta = store.beta_bundle(dataset, block)
    hu = store.hu_bundle(dataset, block, approximation) if model in HU_MODELS else None
    offsets = store.offset_bundle(dataset, block) if variant == "all_agreeing_offsets" else None
    key = stable_hash({
        "kind": "grammar", "block": block.key, "variant": variant, "model": model,
        "approximation": numerical_approximation, "alpha": alpha, "beta": beta.key,
        "hu": hu.key if hu else None, "offset": offsets.key if offsets else None,
    })
    if key not in store.grammar:
        counts, opposed, d_values, q_values, old_back = grammar_training_arrays(
            dataset, block, store, variant, model, approximation,
        )
        fit = fit_grammar(
            MODEL_TO_V2[model], counts, opposed, d_values,
            p_hc_b=q_values, old_is_back=old_back, alpha=alpha,
        )
        gate = grammar_fit_gate(fit)
        support = grammar_support_diagnostics(model, counts, opposed, q_values, old_back)
        if not gate.passed:
            store.failure("grammar", {
                "cache_key": key, "block_key": block.key, "roots": block.roots,
                "variant": variant, "model": model,
                "approximation": numerical_approximation, "alpha": alpha,
                "beta_key": beta.key, "hu_key": hu.key if hu else None,
                "offset_key": offsets.key if offsets else None,
                "counts": counts.tolist(), "opposed": opposed.tolist(),
                "d_values": d_values.tolist(),
                "q_values": q_values.tolist() if q_values is not None else None,
                "old_back": old_back.tolist(), "fit": asdict(fit),
                "gate": asdict(gate), "support_diagnostics": support,
            })
            raise GateFailure(f"grammar gate failed for {key}: {gate.reasons}")
        store.grammar[key] = fit
        store.record("grammar", key, {
            "block_key": block.key, "variant": variant, "model": model,
            "approximation": numerical_approximation, "alpha": alpha,
            "beta_key": beta.key, "hu_key": hu.key if hu else None,
            "offset_key": offsets.key if offsets else None, "fit": asdict(fit), "gate": asdict(gate),
            "support_diagnostics": support,
            "alpha_zero_status": (
                "NUMERIC_CANDIDATE_PENDING_SEPARABILITY_AND_COERCIVITY_REVIEW"
                if alpha == 0.0 else "REGULARIZED_FINITE_FIT"
            ),
        })
    return key, store.grammar[key]


def scoring_rows(
    dataset: Dataset,
    block: Block,
    store: FitStore,
    variant: str,
    protocol: str,
    model: str,
    approximation: str,
    grammar_key: str,
    grammar: GrammarFit,
    evaluation_roots: Sequence[str],
    outer_fold: int,
    selected_alpha: float,
    fit_alpha: float,
    regularization_view: str,
) -> tuple[list[dict[str, object]], dict[str, float]]:
    beta = store.beta_bundle(dataset, block)
    hu = store.hu_bundle(dataset, block, approximation) if model in HU_MODELS else None
    offsets = store.offset_bundle(dataset, block) if variant == "all_agreeing_offsets" else None
    visible = protocol == "side_informed"
    selected_roots = set(roots_for_scope(dataset, evaluation_roots, variant_scope(variant)))
    rows = []
    root_log = defaultdict(float)
    root_n = defaultdict(int)
    for cell in dataset.cells:
        if cell.root not in selected_roots:
            continue
        record = dataset.roots[cell.root]
        d_value = root_d(dataset, beta, cell.root, side_visible=visible)
        if offsets is not None:
            d_value += offsets.dat if cell.morphology == "dat" else offsets.loc
        q_value = q_hu(dataset, beta, hu, cell.root, side_visible=visible) if hu is not None else math.nan
        costs = candidate_costs(
            MODEL_TO_V2[model], record.opposed, d_value, grammar.parameters,
            p_hc_b=q_value if hu is not None else None, old_is_back=record.old_is_back,
        )
        log_predicted = -costs - logsumexp(-costs)
        predicted = np.exp(log_predicted)
        observed = np.asarray(cell.counts, dtype=float)
        log_score = float(observed @ log_predicted)
        root_log[cell.root] += log_score
        root_n[cell.root] += cell.total
        rows.append({
            "root": cell.root,
            "outer_fold": outer_fold,
            "morphology": cell.morphology,
            "source": cell.source,
            "analysis_variant": variant,
            "information_protocol": protocol,
            "rho_prior": store.rho_prior,
            "hu_tau": store.hu_tau,
            "hu_estimator": "native11_gaussian_MAP_fixed_tau",
            "approximation": approximation if model in HU_MODELS else "not_applicable",
            "model": model,
            "regularization_view": regularization_view,
            "selected_alpha": selected_alpha,
            "fit_alpha": fit_alpha,
            "observed_unraised_old": cell.counts[0],
            "observed_unraised_opposite": cell.counts[1],
            "observed_raised_old": cell.counts[2],
            "observed_raised_opposite": cell.counts[3],
            "predicted_unraised_old": float(predicted[0]),
            "predicted_unraised_opposite": float(predicted[1]),
            "predicted_raised_old": float(predicted[2]),
            "predicted_raised_opposite": float(predicted[3]),
            "log_predicted_unraised_old": float(log_predicted[0]),
            "log_predicted_unraised_opposite": float(log_predicted[1]),
            "log_predicted_raised_old": float(log_predicted[2]),
            "log_predicted_raised_opposite": float(log_predicted[3]),
            "d": d_value,
            "q_HU": q_value,
            "parameters_json": json.dumps(grammar.parameters, sort_keys=True, separators=(",", ":")),
            "native_coordinates_json": json.dumps(grammar.internal_coordinates, separators=(",", ":")),
            "training_block_hash": block.key,
            "grammar_fit_hash": grammar_key,
        })
    scores = {root: root_log[root] / root_n[root] for root in root_log if root_n[root] > 0}
    return rows, scores


def choose_alpha(
    dataset: Dataset,
    store: FitStore,
    outer_fold: int,
    variant: str,
    protocol: str,
    model: str,
    approximation: str,
) -> tuple[float, list[dict[str, object]]]:
    outer_training = {root for root, record in dataset.roots.items() if record.outer_fold != outer_fold}
    pooled_scores: dict[float, dict[str, float]] = {alpha: {} for alpha in ALPHA_GRID}
    diagnostics = []
    for inner_fold in range(3):
        inner_training = {
            root for root in outer_training if dataset.inner_folds[(outer_fold, root)] != inner_fold
        }
        validation = {
            root for root in outer_training if dataset.inner_folds[(outer_fold, root)] == inner_fold
        }
        block = make_block(dataset, inner_training, variant_scope(variant))
        for alpha in ALPHA_GRID:
            grammar_key, grammar = grammar_fit_cached(
                dataset, block, store, variant, model, approximation, alpha,
            )
            _, root_scores = scoring_rows(
                dataset, block, store, variant, protocol, model, approximation,
                grammar_key, grammar, sorted(validation), outer_fold,
                selected_alpha=math.nan, fit_alpha=alpha, regularization_view="inner_tuning",
            )
            overlap = set(pooled_scores[alpha]).intersection(root_scores)
            if overlap:
                raise RuntimeError(f"inner validation roots scored twice: {sorted(overlap)}")
            pooled_scores[alpha].update(root_scores)
            diagnostics.append({
                "outer_fold": outer_fold, "inner_fold": inner_fold, "analysis_variant": variant,
                "information_protocol": protocol, "approximation": approximation,
                "rho_prior": store.rho_prior, "hu_tau": store.hu_tau,
                "model": model, "alpha": alpha, "training_block_hash": block.key,
                "grammar_fit_hash": grammar_key, "validation_scoreable_roots": len(root_scores),
            })
    means = {}
    expected_scoreable = {
        root for root in roots_for_scope(dataset, outer_training, variant_scope(variant))
        if dataset.roots[root].target_covered > 0
    }
    for alpha, scores in pooled_scores.items():
        if set(scores) != expected_scoreable:
            raise RuntimeError("inner root-score pool is incomplete; equal-fold averaging is prohibited")
        means[alpha] = float(np.mean(list(scores.values())))
    selected = select_regularization_alpha(means, tolerance=1e-8)
    for row in diagnostics:
        row["pooled_root_balanced_mean_log_density"] = means[row["alpha"]]
        row["selected_alpha"] = selected
    return selected, diagnostics


OOF_FIELDS = [
    "root", "outer_fold", "morphology", "source", "analysis_variant", "information_protocol",
    "rho_prior", "hu_tau", "hu_estimator", "approximation", "model", "regularization_view",
    "selected_alpha", "fit_alpha",
    "observed_unraised_old", "observed_unraised_opposite", "observed_raised_old", "observed_raised_opposite",
    "predicted_unraised_old", "predicted_unraised_opposite", "predicted_raised_old", "predicted_raised_opposite",
    "log_predicted_unraised_old", "log_predicted_unraised_opposite",
    "log_predicted_raised_old", "log_predicted_raised_opposite",
    "d", "q_HU", "parameters_json", "native_coordinates_json", "training_block_hash", "grammar_fit_hash",
]


def write_csv(path: Path, fieldnames: Sequence[str], rows: Sequence[dict[str, object]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="", encoding="utf-8") as stream:
        writer = csv.DictWriter(stream, fieldnames=fieldnames, extrasaction="raise")
        writer.writeheader()
        writer.writerows(rows)


def run_fits(
    dataset: Dataset, output_dir: Path, rho_prior: str, hu_tau: float,
) -> dict[str, object]:
    store = FitStore(output_dir / "fit_cache", rho_prior, hu_tau)
    selected_rows: list[dict[str, object]] = []
    alpha_zero_rows: list[dict[str, object]] = []
    tuning_rows: list[dict[str, object]] = []
    plan = [(model, "laplace") for model in MODELS]
    plan += [(model, "gh80") for model in MODELS if model in HU_MODELS]
    for outer_fold in range(5):
        outer_training = {root for root, record in dataset.roots.items() if record.outer_fold != outer_fold}
        outer_test = {root for root, record in dataset.roots.items() if record.outer_fold == outer_fold}
        for variant in ANALYSIS_VARIANTS:
            block = make_block(dataset, outer_training, variant_scope(variant))
            for protocol in INFORMATION_PROTOCOLS:
                for model, approximation in plan:
                    selected_alpha, tuning = choose_alpha(
                        dataset, store, outer_fold, variant, protocol, model, approximation,
                    )
                    tuning_rows.extend(tuning)
                    grammar_key, grammar = grammar_fit_cached(
                        dataset, block, store, variant, model, approximation, selected_alpha,
                    )
                    rows, _ = scoring_rows(
                        dataset, block, store, variant, protocol, model, approximation,
                        grammar_key, grammar, sorted(outer_test), outer_fold,
                        selected_alpha, selected_alpha, "selected",
                    )
                    selected_rows.extend(rows)
                    zero_key, zero_grammar = grammar_fit_cached(
                        dataset, block, store, variant, model, approximation, 0.0,
                    )
                    zero_rows, _ = scoring_rows(
                        dataset, block, store, variant, protocol, model, approximation,
                        zero_key, zero_grammar, sorted(outer_test), outer_fold,
                        selected_alpha, 0.0,
                        "alpha_zero_numeric_candidate_pending_separability",
                    )
                    alpha_zero_rows.extend(zero_rows)

    selected_path = output_dir / "uyghur_oof_predictions_selected_v1.csv"
    zero_path = output_dir / "uyghur_oof_predictions_alpha0_v1.csv"
    tuning_path = output_dir / "uyghur_inner_tuning_v1.csv"
    write_csv(selected_path, OOF_FIELDS, selected_rows)
    write_csv(zero_path, OOF_FIELDS, alpha_zero_rows)
    tuning_fields = list(tuning_rows[0]) if tuning_rows else []
    write_csv(tuning_path, tuning_fields, tuning_rows)
    return {
        "status": "FIT_COMPLETE_PENDING_INDEPENDENT_SCORE_RECOMPUTATION",
        "rho_prior": rho_prior,
        "hu_tau": hu_tau,
        "hu_estimator": "native11_gaussian_MAP_fixed_tau",
        "hu_estimator_decision_sha256": dataset.input_hashes["specification.json"],
        "hu_regularized_module_sha256": dataset.input_hashes["uyghur_hu_regularized_v1.py"],
        "hu_wrapper_sha256": dataset.input_hashes["hu_laplace_vectorized_wrapper_v4.py"],
        "beta_estimation": "POSTERIOR_MEAN_MU_RHO_WITH_DECLARED_BETA_PLUGIN",
        "selected_oof": {"path": str(selected_path), "sha256": sha256(selected_path), "rows": len(selected_rows)},
        "alpha_zero_oof": {"path": str(zero_path), "sha256": sha256(zero_path), "rows": len(alpha_zero_rows)},
        "tuning": {"path": str(tuning_path), "sha256": sha256(tuning_path), "rows": len(tuning_rows)},
        "cache_files": len(list((output_dir / "fit_cache").glob("*.json"))),
        "warning": (
            "Use the independent prediction checks to recompute "
            "scores/marginals/paired-root summaries from the row-level OOF export. "
            "Alpha-zero fits are numeric candidates pending separability/coercivity review, "
            "not assertions that a finite unregularized MLE is attained."
        ),
    }


def validate_only(
    dataset: Dataset, rho_prior: str | None, hu_tau: float | None,
) -> dict[str, object]:
    outer_sizes = defaultdict(int)
    for record in dataset.roots.values():
        outer_sizes[record.outer_fold] += 1
    return {
        "status": "PASS_ORCHESTRATOR_VALIDATION_ONLY_NO_CORPUS_FIT",
        "fitting_available": True,
        "rho_prior": rho_prior,
        "allowed_rho_priors": RHO_PRIORS,
        "hu_tau": hu_tau,
        "allowed_hu_taus": HU_TAUS,
        "hu_estimator": "native11_gaussian_MAP_fixed_tau",
        "beta_estimation": "POSTERIOR_MEAN_MU_RHO_WITH_DECLARED_BETA_PLUGIN",
        "root_count": len(dataset.roots),
        "scoreable_roots": sum(record.target_covered > 0 for record in dataset.roots.values()),
        "covered_target_incidences": sum(cell.total for cell in dataset.cells),
        "target_source_root_morphology_rows": len(dataset.cells),
        "outer_fold_sizes": dict(sorted(outer_sizes.items())),
        "inner_manifest_rows": len(dataset.inner_folds),
        "models": MODELS,
        "analysis_variants": ANALYSIS_VARIANTS,
        "information_protocols": INFORMATION_PROTOCOLS,
        "alpha_grid": ALPHA_GRID,
        "wholly_unseen_rule": "validation/test accusative masked; all training-root accusative predictors remain observed",
        "inner_selection_pooling": "per-root validation log scores pooled across all three inner folds before one mean; folds are not equally averaged",
        "OOF_fields": OOF_FIELDS,
        "input_hashes": dataset.input_hashes,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--validate-only", action="store_true")
    mode.add_argument("--fit", action="store_true")
    parser.add_argument("--rho-prior", choices=RHO_PRIORS)
    parser.add_argument("--hu-tau", type=float, choices=HU_TAUS)
    parser.add_argument("--output-dir", type=Path, default=Path("fit_run"))
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    dataset = load_dataset()
    if args.fit:
        if args.rho_prior is None:
            parser.error("--rho-prior is required for a real fit")
        if args.hu_tau is None:
            parser.error("--hu-tau is required for a real fit")
        result = run_fits(dataset, args.output_dir, args.rho_prior, args.hu_tau)
    else:
        result = validate_only(dataset, args.rho_prior, args.hu_tau)
    payload = json.dumps(result, ensure_ascii=False, indent=2) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(payload, encoding="utf-8")
    print(payload, end="")


if __name__ == "__main__":
    main()
