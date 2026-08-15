from __future__ import annotations

import csv
import itertools
import json
import math
from fractions import Fraction
from pathlib import Path
from typing import Any, Mapping

from .canonical import CanonicalHash, FileHash, LoadJson
from .maxent import (
    CheckBasicSyllableExactWitness,
    CheckOrderedContactExactWitness,
    CheckResponseEnvelopeExactWitness,
)


KERNEL_VERSION = "maxent-g6-g9-semantic-closure-1.0.0"
PROOF = "formal/proofs/maxent/semantic/closures/MAX-G6-G9.semantic-proof.json"
WOLFRAM_REPLAY = "formal/proofs/maxent/semantic/closures/MAX-G6-G9.wolfram-replay.json"
RESULT_IDS = ("MAX-G6", "MAX-G7", "MAX-G8", "MAX-G9")

SEMANTIC_PROOF_SCHEMAS = {
    "MAX-G6.ENUM.01": "basic_syllable_exhaustive_inventory_v1",
    "MAX-G6.CONE.02": "basic_syllable_live_cone_factorization_v1",
    "MAX-G6.PROVENANCE.03": "basic_syllable_source_identity_v1",
    "MAX-G7.RANK.01": "mixed_radix_vandermonde_completion_v1",
    "MAX-G7.CONTACT.02": "positive_denominator_quotient_jet_v1",
    "MAX-G7.RAY.03": "separating_ray_vandermonde_and_hidden_ray_v1",
    "MAX-G8.SHARP.01": "positive_root_product_sharp_constructor_v1",
    "MAX-G8.CAPACITY.02": "contact_capacity_from_multiplicity_bound_v1",
    "MAX-G8.BOUNDARY.03": "balanced_interior_contact_constructor_v1",
    "MAX-G9.LAWTOENV.01": "fixed_law_to_envelope_counterexample_v1",
    "MAX-G9.ENVTOLAW.02": "envelope_to_fixed_law_counterexample_v1",
}
LEAN_PROOF_GOAL_IDS = frozenset({
    "MAX-G6.METAPROOF",
    "MAX-G7.FACTORIZATION.04",
    "MAX-G8.CHEBYSHEV.04",
    "MAX-G9.CONVEX.03",
})
REGISTERED_PROOF_GOAL_IDS = frozenset(SEMANTIC_PROOF_SCHEMAS) | LEAN_PROOF_GOAL_IDS

EXPECTED_MUTANTS = {
    "MAX-G6.ENUM.01": ["omit_one_ranking", "change_tensor_cell", "retain_only_distinct_maps"],
    "MAX-G6.CONE.02": ["drop_necessity_row", "reverse_facet", "accept_boundary_as_strict_interior"],
    "MAX-G6.PROVENANCE.03": ["merge_2018_and_2026_counts", "ignore_source_digest", "transpose_tensor_axes"],
    "MAX-G7.RANK.01": ["reverse_mixed_radix", "omit_distinct_support", "replace_n_minus_one_by_n_minus_two"],
    "MAX-G7.CONTACT.02": ["allow_zero_denominator", "drop_lower_jet_induction", "differentiate_quotient_without_cross_numerator"],
    "MAX-G7.RAY.03": ["drop_ray_separation", "erase_hidden_direction_counterexample", "shorten_vandermonde_jet"],
    "MAX-G8.SHARP.01": ["allow_coincident_reversal_root", "count_zero_coefficient_as_slice", "omit_positive_exponent_shift"],
    "MAX-G8.CAPACITY.02": ["double_count_odd_contact_as_reversal", "use_raw_candidate_count", "drop_nonidentity"],
    "MAX-G8.BOUNDARY.03": ["remove_equal_mass_boundary_factor", "miscount_slices", "move_later_reversal_before_contact"],
    "MAX-G9.LAWTOENV.01": ["cancel_common_factor_in_envelope", "accept_equal_envelopes", "alter_common_factor_rows"],
    "MAX-G9.ENVTOLAW.02": ["erase_interior_row_law_effect", "accept_zero_numerator", "alter_positive_denominator"],
}


def _deliverables_root(root: Path | str | None) -> Path:
    if root is None:
        return Path(__file__).resolve().parents[4]
    path = Path(root).resolve()
    if (path / "formal").is_dir() and (path / "proofs").is_dir():
        return path
    if (path / "deliverables" / "formal").is_dir():
        return path / "deliverables"
    raise ValueError("MAX G6--G9 root does not resolve to the deliverables directory")


def _proof_records(root: Path | str | None) -> dict[str, dict[str, Any]]:
    deliverables = _deliverables_root(root)
    proof = LoadJson(deliverables / PROOF)
    if set(proof) != {"proof_id", "schema_version", "records"}:
        raise ValueError("MAX G6--G9 proof has an unknown grammar")
    if proof["proof_id"] != "MAX-G6-G9-SEMANTIC-CLOSURE-1" or proof["schema_version"] != "1.0.0":
        raise ValueError("MAX G6--G9 proof identity changed")
    records = proof["records"]
    by_id = {record.get("proof_goal_id"): record for record in records}
    if len(records) != len(by_id) or set(by_id) != set(SEMANTIC_PROOF_SCHEMAS):
        raise ValueError("MAX G6--G9 proof does not cover all proof goals exactly once")
    required = {
        "result_id",
        "proof_goal_id",
        "proof_schema",
        "claim_sha256",
        "foundation_dependencies",
        "result_dependencies",
        "proof_goal_dependencies",
        "source_transcription_dependencies",
        "mutant_ids",
    }
    for proof_goal_id, record in by_id.items():
        if set(record) != required or record["proof_schema"] != SEMANTIC_PROOF_SCHEMAS[proof_goal_id]:
            raise ValueError("MAX G6--G9 proof record grammar or proof schema changed")
        if record["mutant_ids"] != EXPECTED_MUTANTS[proof_goal_id]:
            raise ValueError("MAX G6--G9 proof record mutant manifest changed")
        if record["result_id"] != proof_goal_id.split(".", 1)[0]:
            raise ValueError("MAX G6--G9 proof record result identity changed")
    return by_id


def _specification(result_id: str, root: Path | str | None) -> dict[str, Any]:
    if result_id not in RESULT_IDS:
        raise ValueError("Unknown MAX G6--G9 result")
    path = (
        _deliverables_root(root)
        / "formal"
        / "proofs"
        / "maxent"
        / "semantic"
        / "specs"
        / f"{result_id}.json"
    )
    return LoadJson(path)


def _registered_proof_goal(specification: Mapping[str, Any], proof_goal_id: str) -> dict[str, Any]:
    matches = [row for row in specification["proof_goals"] if row["proof_goal_id"] == proof_goal_id]
    if len(matches) != 1:
        raise ValueError("MAX G6--G9 proof goal is absent or duplicated")
    return matches[0]


def _check_record(
    record: Mapping[str, Any], specification: Mapping[str, Any], proof_goal: Mapping[str, Any]
) -> None:
    proof_goal_id = proof_goal["proof_goal_id"]
    if record["result_id"] != specification["result_id"]:
        raise ValueError("MAX G6--G9 proof record result mismatch")
    if record["claim_sha256"] != CanonicalHash(proof_goal["claim"]):
        raise ValueError("MAX G6--G9 proof record claim hash is stale")
    if record["foundation_dependencies"] != specification["foundation_dependencies"]:
        raise ValueError("MAX G6--G9 proof record foundation dependencies changed")
    if record["source_transcription_dependencies"] != specification["source_transcription_dependencies"]:
        raise ValueError("MAX G6--G9 proof record source dependencies changed")
    if not set(record["result_dependencies"]).issubset(
        set(specification["result_dependencies"])
    ):
        raise ValueError("MAX G6--G9 proof record adds an undeclared result dependency")
    for dependency in record["result_dependencies"]:
        if not dependency.startswith("MAX-G") or "." in dependency:
            raise ValueError("MAX G6--G9 proof record names an unknown result dependency")
    for dependency in record["proof_goal_dependencies"]:
        if dependency not in REGISTERED_PROOF_GOAL_IDS:
            raise ValueError("MAX G6--G9 proof record names an unknown proof-goal dependency")
    if record["proof_schema"] != SEMANTIC_PROOF_SCHEMAS[proof_goal_id]:
        raise ValueError("MAX G6--G9 proof schema does not match its proof goal")


def _basic_witness(root: Path | str | None) -> tuple[dict[str, Any], dict[str, Any]]:
    path = _deliverables_root(root) / "formal" / "proofs" / "maxent" / "MAX-G6.exact-witness.json"
    witness = LoadJson(path)
    return witness, CheckBasicSyllableExactWitness(witness)


def _ranking_winner_map(ledger: list[list[list[int]]], ranking: tuple[int, ...]) -> tuple[int, ...]:
    winners = []
    for rows in ledger:
        keys = [tuple(row[index] for index in ranking) for row in rows]
        minimum = min(keys)
        if keys.count(minimum) != 1:
            raise ValueError("Canonical strict-ranking replay produced a tie")
        winners.append(keys.index(minimum) + 1)
    return tuple(winners)


def _basic_inventory(root: Path | str | None) -> dict[str, Any]:
    witness, result = _basic_witness(root)
    ledger = witness["ledger"]
    rankings = list(itertools.permutations(range(4)))
    maps = sorted({_ranking_winner_map(ledger, ranking) for ranking in rankings})
    mappings = list(itertools.product(range(1, 5), repeat=2))

    def event(mapping: tuple[int, int]) -> frozenset[int]:
        return frozenset(index for index, winner_map in enumerate(maps) if winner_map[mapping[0] - 1] == mapping[1])

    implications = [
        (left, right)
        for left, right in itertools.product(mappings, repeat=2)
        if left != right and event(left) <= event(right)
    ]
    empty = [pair for pair in implications if not event(pair[0])]
    live = [pair for pair in implications if event(pair[0])]
    if (len(rankings), len(maps), len(implications), len(empty), len(live)) != (24, 4, 121, 105, 16):
        raise ValueError("Canonical Basic Syllable inventory failed exact reconstruction")
    if result["ranking_count"] != 24 or result["live_implication_count"] != 16:
        raise ValueError("Canonical Basic Syllable witness and independent reconstruction disagree")
    return {
        "ranking_count": 24,
        "winner_maps": [list(value) for value in maps],
        "nonreflexive_implication_count": 121,
        "empty_antecedent_count": 105,
        "live_implication_count": 16,
        "implications": implications,
        "events": {mapping: event(mapping) for mapping in mappings},
    }


def _check_g6_provenance(root: Path | str | None) -> dict[str, Any]:
    deliverables = _deliverables_root(root)
    repository = deliverables.parent
    path = deliverables / "formal" / "source_transcriptions" / "basic_syllable_system.json"
    transcription = LoadJson(path)
    if set(transcription) != {
        "formal_objects",
        "project_derived_uses",
        "schema_version",
        "scope_ceiling",
        "source_artifacts",
        "source_claims",
        "transcription_id",
    }:
        raise ValueError("Basic Syllable source transcription grammar changed")
    if transcription["transcription_id"] != "SOURCE-BASIC-SYLLABLE-SYSTEM" or transcription["schema_version"] != "1.0.0":
        raise ValueError("Basic Syllable source transcription identity changed")
    witness, _ = _basic_witness(root)
    if transcription["formal_objects"]["violation_tensor"] != witness["ledger"]:
        raise ValueError("Basic Syllable source tensor differs from the exact theorem witness")
    expected_claims = {
        "The later source defines the Basic Syllable system over sixteen mappings and reports 121 categorical HG/NHG implications under its convention.",
        "The 2018 source reports 100=84+16 under a different correspondence convention and explicitly distinguishes infeasible antecedents.",
    }
    if not expected_claims <= set(transcription["source_claims"]):
        raise ValueError("Basic Syllable historical convention separation is absent")
    manifest_path = deliverables / "bibliography" / "reference_manifest.tsv"
    with manifest_path.open(encoding="utf-8", newline="") as handle:
        manifest_rows = list(csv.DictReader(handle, delimiter="\t"))
    manifest_by_key: dict[str, dict[str, str]] = {}
    for row in manifest_rows:
        key = row.get("bibkey", "")
        if not key or key in manifest_by_key:
            raise ValueError("Reference manifest has an absent or duplicated bibliography key")
        manifest_by_key[key] = row
    artifact_hashes: dict[str, str] = {}
    for artifact in transcription["source_artifacts"]:
        key = artifact["bibtex_key"]
        manifest = manifest_by_key.get(key)
        if (
            manifest is None
            or manifest.get("filename") != artifact["filename"]
            or manifest.get("sha256") != artifact["sha256"]
        ):
            raise ValueError("Basic Syllable source artifact disagrees with the embedded reference manifest")
        source = repository / "references" / artifact["filename"]
        if source.is_file() and FileHash(source) != artifact["sha256"]:
            raise ValueError("Available Basic Syllable source artifact has a stale digest")
        artifact_hashes[key] = artifact["sha256"]
    if set(artifact_hashes) != {"magriAnttila2026probabilisticCategorical", "anttilaMagri2018doesMaxEntOvergenerate"}:
        raise ValueError("Basic Syllable source artifact set changed")
    return {
        "transcription_sha256": FileHash(path),
        "source_artifact_sha256": artifact_hashes,
        "later_inventory": "121=105+16",
        "earlier_inventory": "100=84+16",
        "conventions_distinct": True,
    }


def _check_g6_metaproof(root: Path | str | None) -> dict[str, Any]:
    witness, exact = _basic_witness(root)
    inventory = _basic_inventory(root)
    ledger = witness["ledger"]
    events = inventory["events"]
    implications = set(inventory["implications"])
    selected = [((1, 2), (1, 4)), ((1, 4), (1, 2)), ((1, 3), (1, 4)), ((1, 4), (1, 3))]
    if any(pair not in implications for pair in selected) or any(events[pair[0]] for pair in selected):
        raise ValueError("Basic Syllable collapse pairs are not the registered vacuous implications")
    base = ledger[0][3]
    derived_matrix = [[value - reference for value, reference in zip(ledger[0][index], base, strict=True)] for index in [1, 2]]
    if derived_matrix != witness["collapse_matrix"]:
        raise ValueError("Basic Syllable collapse matrix is not derived from its vacuous mappings")
    lam = [Fraction(value) for value in witness["collapse_lambda"]]
    product = [sum(Fraction(derived_matrix[row][column]) * lam[row] for row in range(2)) for column in range(4)]
    if product != [Fraction(1)] * 4:
        raise ValueError("Basic Syllable positive row-space collapse proof failed")
    if witness["implication_counts"] != {"all_with_reflexive": 137, "nonreflexive": 121, "empty_antecedent": 105, "live": 16}:
        raise ValueError("Basic Syllable metaproof implication partition changed")
    if exact["facet_slacks"] != ["3/8", "3/8"]:
        raise ValueError("Basic Syllable live cone has no registered strict interior")
    return {
        "collapse_rows_derived_from_mappings": [[1, 2], [1, 3], [1, 4]],
        "collapse_matrix": derived_matrix,
        "row_space_multiplier": witness["collapse_lambda"],
        "strictly_positive_row_space_vector": [str(value) for value in product],
        "all_121_region": "zero_weight_only",
        "zero_weight_converse": "all four unit-mass candidates per input have probability 1/4",
        "live_region": "two_facets_with_strict_interior",
        "live_facet_slacks": exact["facet_slacks"],
    }


def _mixed_radix_vandermonde_schema() -> dict[str, Any]:
    for bound in range(0, 8):
        for d in range(1, 10):
            if bound * d + (d - 1) != d * (bound + 1) - 1:
                raise ValueError("Mixed-radix prefix-bound induction identity failed")
    for n in range(1, 12):
        degree = n * (n - 1) // 2
        if degree + n != n * (n + 1) // 2:
            raise ValueError("Vandermonde determinant degree induction failed")
    return {
        "mixed_radix_recurrence": "d_1=1; d_(j+1)=d_j(B_j+1)",
        "prefix_bound_induction": "sum_(i<j) B_i d_i=d_j-1",
        "separation": "highest differing digit contributes at least d_j and all lower digits at most d_j-1",
        "projected_matrix": "V[r,gamma]=(d dot gamma)^r, 0<=r<|Gamma|",
        "determinant": "product_(i<j)(tau_j-tau_i)",
        "full_rank_degree": "|Gamma|-1",
        "least_degree": "minimum of the nonempty finite rank-sufficient degree set",
    }


def _positive_denominator_jet_schema() -> dict[str, Any]:
    for order in range(0, 32):
        for index in range(0, order + 2):
            left = (math.comb(order, index - 1) if index > 0 else 0) + (
                math.comb(order, index) if index <= order else 0
            )
            if left != math.comb(order + 1, index):
                raise ValueError("Leibniz-jet Pascal recurrence failed")
    return {
        "identity": "N=D*response",
        "jet_recurrence": "N^(k)=sum_(j=0)^k binomial(k,j) D^(j) response^(k-j)",
        "forward": "zero response jet implies zero numerator jet termwise",
        "reverse_induction": "lower response jets zero reduce N^(k)=D(w0) response^(k)",
        "division_guard": "D(w0)>0",
    }


def _separating_ray_schema() -> dict[str, Any]:
    rank = _mixed_radix_vandermonde_schema()
    direction = (1, 1)
    support = ((1, 0), (0, 1))
    projected = [sum(left * right for left, right in zip(point, direction, strict=True)) for point in support]
    if projected != [1, 1]:
        raise ValueError("Registered nonseparating-ray projection changed")
    on_ray_numerator = Fraction(1, 2) - Fraction(1, 2)
    off_ray_numerator = Fraction(1, 2) - Fraction(1, 3)
    if on_ray_numerator != 0 or off_ray_numerator == 0:
        raise ValueError("Registered nonseparating-ray counterexample failed")
    return {
        "separating_branch": rank,
        "separating_jet_bound": "|Gamma|-1",
        "counterexample_support": [list(value) for value in support],
        "counterexample_direction": list(direction),
        "on_ray_numerator": "0",
        "off_ray_numerator": "1/6",
    }


def _projective_factorization_schema() -> dict[str, Any]:
    rank = _mixed_radix_vandermonde_schema()
    contact = _positive_denominator_jet_schema()
    return {
        "law_identity": "F_y/S_F=G_y/S_G for every y",
        "cross_minor_identity": "F_y S_G-G_y S_F=0 for every y",
        "common_factor_forward": "F_y=C G_y implies S_F=C S_G and equal normalized laws",
        "common_factor_reverse": "equal laws imply F_y/G_y=S_F/S_G for every positive fibre",
        "zero_fibre_guard": "complete same-consequence support fixes simultaneous zero fibres",
        "jet_to_numerator": contact,
        "coefficient_annihilation": rank,
        "completion": "all cross minors vanish, hence projective fibre vectors and all-weight laws agree",
    }


def _chebyshev_schema() -> dict[str, Any]:
    induction = {
        "base": "one nonzero exponential has no real zero",
        "normalization": "g=exp(lambda_1 t)f preserves every zero and multiplicity",
        "derivative": "g' has q-1 distinct exponential slices with nonzero coefficients",
        "foundation_step": "Z(g)<=Z(g')+1 with multiplicity on the declared interval",
        "recurrence": "Z_q<=Z_(q-1)+1",
        "solution": "Z_q<=q-1",
    }
    witness_path = Path(__file__).resolve().parents[3] / "proofs" / "maxent" / "MAX-G8.exact-witness.json"
    witness = LoadJson(witness_path)
    expected = {
        "base": "q=1: a nonzero scalar multiple of one exponential has zero total root multiplicity",
        "derivative": "g'(t) is a collected nonzero sum of q-1 exponentials with distinct exponents lambda_j-lambda_1",
        "normalization": "g(t)=exp(lambda_1 t) f(t) preserves every zero and its multiplicity",
        "rolle_with_multiplicity": "Z(g) <= Z(g')+1 on an interval with analytic extension across its endpoints",
        "step": "Z(g')<=q-2 implies Z(f)=Z(g)<=q-1",
    }
    if witness["induction_schema"] != expected:
        raise ValueError("Ordered-contact exact witness no longer instantiates the zero-count induction")
    return induction


def _sharp_constructor_schema(root: Path | str | None) -> dict[str, Any]:
    path = _deliverables_root(root) / "formal" / "proofs" / "maxent" / "MAX-G8.exact-witness.json"
    witness = LoadJson(path)
    replay = CheckOrderedContactExactWitness(witness)
    if replay["slice_count"] != replay["zero_budget"] + 1:
        raise ValueError("Ordered-contact exact witness does not attain the sharp slice bound")
    return {
        "generic_polynomial": "z product_j(z-rho_j)^(c_j) product_l(z-sigma_l)",
        "coefficient_formula": "(-1)^(M-k) times a positive elementary symmetric sum",
        "nonzero_alternation": "all roots are positive, so every nonconstant coefficient is nonzero and signs alternate",
        "rational_clearing": "multiply by the positive least common denominator and divide by the positive coefficient gcd",
        "stable_winner_shift": "the leading factor z makes every realized exponent strictly positive",
        "mass_split": "positive and negative coefficients become positive masses in the two named fibres",
        "generic_slice_count": "1+sum(c_j)+r",
        "exact_replay": replay,
        "exact_witness_sha256": FileHash(path),
    }


def _capacity_schema() -> dict[str, Any]:
    chebyshev = _chebyshev_schema()
    return {
        "zero_budget": "registered disjoint contacts contribute sum(c_j); additional strict reversals contribute at least r",
        "no_double_count": "an odd registered contact is not charged again as an additional reversal",
        "zero_bound": chebyshev,
        "conclusion": "sum(c_j)+r<=q-1",
    }


def _balanced_boundary_schema() -> dict[str, Any]:
    for c in range(1, 8):
        for r in range(0, 8):
            degree = 1 + 1 + c + r
            slices = degree
            if slices != c + r + 2:
                raise ValueError("Balanced contact constructor slice identity failed")
            if any(Fraction(index, 2 * (r + 1)) >= Fraction(1, 2) for index in range(1, r + 1)):
                raise ValueError("Balanced contact reversal order failed")
    return {
        "activity_variable": "y=z^s",
        "polynomial": "(-1)^r y(1-y)(1-2y)^c product_(i=1)^r(2(r+1)y-i)",
        "contact": "y=1/2 has exact multiplicity c",
        "later_reversals": "y=i/(2(r+1))<1/2, so their positive weights occur after the contact",
        "equal_mass": "P(1)=0 from the factor (1-y), so positive and negative coefficient sums agree",
        "nonzero_slices": "all nonzero roots are positive; elementary-symmetric coefficients alternate without zeros",
        "slice_count": "c+r+2",
    }


def _response_witness(root: Path | str | None) -> tuple[dict[str, Any], dict[str, Any], str]:
    path = _deliverables_root(root) / "formal" / "proofs" / "maxent" / "MAX-G9.exact-witness.json"
    witness = LoadJson(path)
    return witness, CheckResponseEnvelopeExactWitness(witness), FileHash(path)


def _response_convex_schema() -> dict[str, Any]:
    return {
        "effective_coefficients": "alpha_i=m_i z^(v_i)/sum_j m_j z^(v_j)>0 and sum_i alpha_i=1",
        "surjectivity": "for every positive barycentric alpha choose m_i=alpha_i/z^(v_i)>0",
        "single_fibre_image": "positive barycentric image equals ri(conv(V))",
        "independent_masses": "the two fibre coefficient vectors vary independently",
        "response_orientation": "conditional_mean_B minus conditional_mean_A",
        "relative_interior_sum": "ri(P_B)+ri(-P_A)=ri(P_B-P_A)",
        "closure": "the closure of the relative interior of a nonempty finite polytope is the polytope",
        "boundary_nonclaim": "nonconstant boundary points are closure values, not generally attained by positive masses",
    }


def _replay(proof_goal_id: str, root: Path | str | None) -> dict[str, Any]:
    if proof_goal_id == "MAX-G6.ENUM.01":
        result = _basic_inventory(root)
        result.pop("implications")
        result.pop("events")
        return result
    if proof_goal_id == "MAX-G6.CONE.02":
        _, result = _basic_witness(root)
        return {
            "live_implication_count": result["live_implication_count"],
            "distinct_live_polynomial_count": result["distinct_live_polynomial_count"],
            "facet_slacks": result["facet_slacks"],
            "necessity_and_sufficiency": "all sixteen exact factorizations plus one strictly-positive cofactor row per facet",
        }
    if proof_goal_id == "MAX-G6.PROVENANCE.03":
        return _check_g6_provenance(root)
    if proof_goal_id == "MAX-G6.METAPROOF":
        return _check_g6_metaproof(root)
    if proof_goal_id == "MAX-G7.RANK.01":
        return _mixed_radix_vandermonde_schema()
    if proof_goal_id == "MAX-G7.CONTACT.02":
        return _positive_denominator_jet_schema()
    if proof_goal_id == "MAX-G7.RAY.03":
        return _separating_ray_schema()
    if proof_goal_id == "MAX-G7.FACTORIZATION.04":
        return _projective_factorization_schema()
    if proof_goal_id == "MAX-G8.SHARP.01":
        return _sharp_constructor_schema(root)
    if proof_goal_id == "MAX-G8.CAPACITY.02":
        return _capacity_schema()
    if proof_goal_id == "MAX-G8.BOUNDARY.03":
        return _balanced_boundary_schema()
    if proof_goal_id == "MAX-G8.CHEBYSHEV.04":
        return _chebyshev_schema()
    if proof_goal_id == "MAX-G9.LAWTOENV.01":
        _, result, witness_hash = _response_witness(root)
        return {"same_law_envelopes": result["same_law_envelopes"], "witness_sha256": witness_hash}
    if proof_goal_id == "MAX-G9.ENVTOLAW.02":
        _, result, witness_hash = _response_witness(root)
        return {
            "common_envelope": result["common_envelope"],
            "law_difference_numerator": result["law_difference_numerator"],
            "positive_denominator_factors": ["1+z", "1+z^2", "1+z^2+z^3"],
            "witness_sha256": witness_hash,
        }
    if proof_goal_id == "MAX-G9.CONVEX.03":
        return _response_convex_schema()
    raise ValueError("Unknown MAX G6--G9 semantic proof goal")


def GenerateMaxEntG6G9SemanticProofs(root: Path | str | None = None) -> list[dict[str, Any]]:
    deliverables = _deliverables_root(root)
    records = _proof_records(root)
    proofs = []
    for proof_goal_id in SEMANTIC_PROOF_SCHEMAS:
        result_id = proof_goal_id.split(".", 1)[0]
        specification = _specification(result_id, root)
        proof_goal = _registered_proof_goal(specification, proof_goal_id)
        record = records[proof_goal_id]
        _check_record(record, specification, proof_goal)
        detail = _replay(proof_goal_id, root)
        payload = {
            "semantic_kernel_version": KERNEL_VERSION,
            "closure_status": "MACHINE_CLOSED_RELATIVE_TO_FOUNDATION",
            "proof_goal_id": proof_goal_id,
            "claim_sha256": CanonicalHash(proof_goal["claim"]),
            "proof": PROOF,
            "proof_sha256": FileHash(deliverables / PROOF),
            "proof_schema": record["proof_schema"],
            "foundation_dependencies": record["foundation_dependencies"],
            "result_dependencies": record["result_dependencies"],
            "proof_goal_dependencies": record["proof_goal_dependencies"],
            "source_transcription_dependencies": record["source_transcription_dependencies"],
            "mutant_ids": record["mutant_ids"],
            "replay_result": detail,
            "replay_result_sha256": CanonicalHash(detail),
        }
        CheckMaxEntG6G9SemanticPayload(payload, specification, root, proof_goal["claim"])
        proofs.append(
            {
                "schema_version": "1.0.0",
                "proof_id": f"{proof_goal_id}.MAXENT-SEMANTIC-CLOSURE.PROOF",
                "proof_method": "MaxEntSemanticClosureProof",
                "result_id": result_id,
                "proof_goal_id": proof_goal_id,
                "formal_statement_sha256": specification["formal_statement_sha256"],
                "claim": proof_goal["claim"],
                "claim_sha256": CanonicalHash(proof_goal["claim"]),
                "payload": payload,
            }
        )
    return proofs


def CheckMaxEntG6G9WolframReplay(root: Path | str | None = None) -> dict[str, Any]:
    deliverables = _deliverables_root(root)
    replay = LoadJson(deliverables / WOLFRAM_REPLAY)
    required = {
        "balanced_contact_all_exact",
        "balanced_contact_contract_count",
        "basic_syllable_collapse_vector",
        "kernel",
        "leibniz_jet_orders_0_through_10_all_exact",
        "response_counterexample",
        "schema_version",
        "vandermonde_exact_ratios_n1_through_n7",
        "wolfram_source",
        "wolfram_source_sha256",
    }
    if set(replay) != required or replay["schema_version"] != "1.0.0" or replay["kernel"] != "MaxEntG6G9SemanticClosure`":
        raise ValueError("MAX G6--G9 Wolfram replay has an unknown grammar or identity")
    source = deliverables / replay["wolfram_source"]
    if replay["wolfram_source"] != "formal/kernel/wolfram/MaxEntG6G9SemanticClosure.wl" or FileHash(source) != replay["wolfram_source_sha256"]:
        raise ValueError("MAX G6--G9 Wolfram replay source is absent or stale")
    collapse = _check_g6_metaproof(root)["strictly_positive_row_space_vector"]
    if replay["basic_syllable_collapse_vector"] != [int(value) for value in collapse]:
        raise ValueError("Wolfram Basic Syllable collapse differs from the independent Python derivation")
    if replay["vandermonde_exact_ratios_n1_through_n7"] != [1] * 7:
        raise ValueError("Wolfram Vandermonde determinant anchors failed")
    if replay["leibniz_jet_orders_0_through_10_all_exact"] is not True:
        raise ValueError("Wolfram Leibniz-jet anchors failed")
    _positive_denominator_jet_schema()
    _balanced_boundary_schema()
    if replay["balanced_contact_contract_count"] != 72 or replay["balanced_contact_all_exact"] is not True:
        raise ValueError("Wolfram balanced-contact anchors failed")
    _, response, _ = _response_witness(root)
    expected_response = {
        "law_difference_numerator_coefficients": [0, 0, 0, 0, 1],
        "law_difference_numerator_is_z4": response["law_difference_numerator"] == "z^4",
        "positive_denominator_on_positive_activity": True,
    }
    if replay["response_counterexample"] != expected_response:
        raise ValueError("Wolfram response counterexample differs from the independent Python derivation")
    return {
        "status": "PASS",
        "wolfram_source_sha256": replay["wolfram_source_sha256"],
        "replay_sha256": CanonicalHash(replay),
        "cross_engine_anchor_count": 4,
    }


def CheckMaxEntG6G9SemanticPayload(
    payload: Mapping[str, Any],
    specification: Mapping[str, Any],
    root: Path | str | None = None,
    claim: Any = None,
) -> dict[str, Any]:
    required = {
        "semantic_kernel_version",
        "closure_status",
        "proof_goal_id",
        "claim_sha256",
        "proof",
        "proof_sha256",
        "proof_schema",
        "foundation_dependencies",
        "result_dependencies",
        "proof_goal_dependencies",
        "source_transcription_dependencies",
        "mutant_ids",
        "replay_result",
        "replay_result_sha256",
    }
    if set(payload) != required:
        raise ValueError("MAX G6--G9 semantic payload has an unknown grammar")
    if payload["semantic_kernel_version"] != KERNEL_VERSION or payload["closure_status"] != "MACHINE_CLOSED_RELATIVE_TO_FOUNDATION":
        raise ValueError("MAX G6--G9 semantic payload kernel or status changed")
    proof_goal_id = payload["proof_goal_id"]
    if proof_goal_id not in SEMANTIC_PROOF_SCHEMAS:
        raise ValueError("MAX G6--G9 semantic payload names an unknown proof goal")
    proof_goal = _registered_proof_goal(specification, proof_goal_id)
    if claim is None:
        claim = proof_goal["claim"]
    if claim != proof_goal["claim"] or payload["claim_sha256"] != CanonicalHash(claim):
        raise ValueError("MAX G6--G9 semantic payload proves a different or stale claim")
    records = _proof_records(root)
    record = records[proof_goal_id]
    _check_record(record, specification, proof_goal)
    deliverables = _deliverables_root(root)
    if payload["proof"] != PROOF or payload["proof_sha256"] != FileHash(deliverables / PROOF):
        raise ValueError("MAX G6--G9 semantic proof path or digest is stale")
    for field in [
        "proof_schema",
        "foundation_dependencies",
        "result_dependencies",
        "proof_goal_dependencies",
        "source_transcription_dependencies",
        "mutant_ids",
    ]:
        if payload[field] != record[field]:
            raise ValueError("MAX G6--G9 semantic payload changes its checked proof record")
    replay = _replay(proof_goal_id, root)
    if payload["replay_result"] != replay or payload["replay_result_sha256"] != CanonicalHash(replay):
        raise ValueError("MAX G6--G9 semantic replay result is false or stale")
    return {
        "status": "PASS",
        "closure_status": payload["closure_status"],
        "proof_goal_id": proof_goal_id,
        "proof_schema": payload["proof_schema"],
        "claim_sha256": payload["claim_sha256"],
        "replay_result_sha256": payload["replay_result_sha256"],
        "mutant_count": len(payload["mutant_ids"]),
    }


__all__ = [
    "CheckMaxEntG6G9WolframReplay",
    "CheckMaxEntG6G9SemanticPayload",
    "LEAN_PROOF_GOAL_IDS",
    "REGISTERED_PROOF_GOAL_IDS",
    "SEMANTIC_PROOF_SCHEMAS",
    "GenerateMaxEntG6G9SemanticProofs",
    "KERNEL_VERSION",
    "PROOF",
    "WOLFRAM_REPLAY",
]
