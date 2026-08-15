from __future__ import annotations

import csv
import math
from collections import Counter
from fractions import Fraction
from pathlib import Path
from typing import Any, Iterable, Mapping, Sequence

from .common import ROOT, ReadTsv, Sha256File, WriteJson, WriteTsv


def FractionText(value: Fraction) -> str:
    return str(value.numerator) if value.denominator == 1 else f"{value.numerator}/{value.denominator}"


def DecimalText(value: Fraction) -> str:
    return f"{float(value):.12g}"


def QuadraticFirstZero(harmony_weight: int, markedness_weight: int) -> int:
    index = 1
    while markedness_weight * index * (index + 1) < 4 * harmony_weight:
        index += 1
    return index


def EqualityQuadraticProfile(harmony_weight: int, markedness_weight: int, horizon: int) -> list[Fraction]:
    first_zero = QuadraticFirstZero(harmony_weight, markedness_weight)
    if markedness_weight * first_zero * (first_zero + 1) != 4 * harmony_weight:
        raise ValueError("Profile helper requires an equality-boundary example")
    coefficient = Fraction(markedness_weight, 2 * harmony_weight)
    values = [Fraction(1)]
    running = Fraction(1)
    for position in range(1, horizon + 1):
        drop = coefficient * max(first_zero - position + 1, 0)
        running = max(Fraction(0), running - drop)
        values.append(running)
    return values


def WriteDataset(path: Path, rows: Sequence[Mapping[str, Any]], fields: Sequence[str]) -> None:
    WriteTsv(path, rows, fields)


def BuildFiniteData() -> list[Path]:
    report = ROOT / "verification" / "reports" / "machine_verification.json"
    import json
    content = json.loads(report.read_text(encoding="utf-8"))
    results = {result["ResultID"]: result for result in content["Results"]}
    destination = ROOT / "data" / "canonical" / "finite_calculus"
    regressions = []
    for index in range(1, 16):
        identifier = f"CALC-R{index:02d}"
        result = results[identifier]
        regressions.append({"id": identifier, "title": result["Title"], "status": result["Status"], "exact_result": result["ExactResult"], "scope": result["Scope"]})
    WriteDataset(destination / "regressions.tsv", regressions, ["id", "title", "status", "exact_result", "scope"])
    contract = {
        "contract_id": "CALC-F1-DEMONSTRATION",
        "domain": ["s1", "s2"],
        "source_answers": {"s1": "t1", "s2": "t2"},
        "target_answers": {"s1": "t1", "s2": "t3"},
        "registered_query": "exact transported answer identity",
        "admitted_outcomes": ["Q-CONSERVATIVE", "Q-NONCONSERVATIVE", "NOT EVALUATED"],
        "scope": "finite duplicate-free complete contract",
    }
    WriteJson(destination / "contracts.json", {"contracts": [contract]})
    witnesses = []
    refusals = []
    for result in content["Results"]:
        for proof_goal in result["ProofGoalResults"]:
            row = {"result_id": result["ResultID"], "proof_goal_id": proof_goal["ProofGoalID"], "title": proof_goal["Title"], "status": proof_goal["Status"], "exact_result": proof_goal["ExactResult"]}
            if "WITNESS" in proof_goal["ProofGoalID"] or "COUNTER" in proof_goal["ProofGoalID"] or result["ResultID"] in {"CALC-R04", "CALC-R05", "CALC-R07"}:
                witnesses.append(row)
            if "REFUS" in proof_goal["ProofGoalID"] or result["ResultID"] in {"CALC-R03", "CALC-R08", "CALC-R15"}:
                refusals.append(row)
    WriteDataset(destination / "witnesses.tsv", witnesses, ["result_id", "proof_goal_id", "title", "status", "exact_result"])
    WriteDataset(destination / "refusals.tsv", refusals, ["result_id", "proof_goal_id", "title", "status", "exact_result"])
    sorts = [
        ("winner_identity", "candidate_or_tie_set", "grammar", "exact winner identity including ties"),
        ("candidate_order", "total_preorder", "grammar", "complete candidate preorder"),
        ("hg_margin", "rational_margin_vector", "grammar", "registered pairwise HG margins"),
        ("maxent_law", "exact_probability_law", "grammar", "fixed-mass normalized distribution"),
        ("serial_trace", "typed_trace_or_path_law", "grammar", "derivational history with stopping semantics"),
        ("terminal_output", "typed_output", "grammar", "terminal grammatical output"),
        ("realized_form", "realization_value", "realization", "output after a declared grammar-to-phonetics map"),
        ("observed_property", "observation_or_corpus_value", "observation", "registered measurement or corpus decision"),
    ]
    rows = [{"query_sort": name, "answer_type": answer, "layer": layer, "definition": definition} for name, answer, layer, definition in sorts]
    WriteDataset(destination / "query_sort_registry.tsv", rows, ["query_sort", "answer_type", "layer", "definition"])
    return sorted(destination.iterdir())


def BuildContinuousHgData() -> list[Path]:
    destination = ROOT / "data" / "canonical" / "continuous_hg"
    profile = EqualityQuadraticProfile(5, 1, 8)
    profile_rows = []
    for position, value in enumerate(profile):
        profile_rows.append({"example_id": "KAZAKH-FORMAL-H5-M1-P2", "h": 5, "m": 1, "p": 2, "position": position, "exact_value": FractionText(value), "decimal_value": DecimalText(value), "support_status": "positive" if value > 0 else "zero"})
    WriteDataset(destination / "exact_profiles.tsv", profile_rows, ["example_id", "h", "m", "p", "position", "exact_value", "decimal_value", "support_status"])
    phase_rows = []
    for positive_followers in range(0, 9):
        lower = Fraction(positive_followers * (positive_followers + 1), 4)
        upper = Fraction((positive_followers + 1) * (positive_followers + 2), 4)
        phase_rows.append({"p": 2, "positive_followers": positive_followers, "lower_ratio_exclusive": FractionText(lower), "upper_ratio_inclusive": FractionText(upper), "condition": f"{positive_followers}({positive_followers}+1)<4h/m<=({positive_followers}+1)({positive_followers}+2)"})
    WriteDataset(destination / "support_phase_boundaries.tsv", phase_rows, ["p", "positive_followers", "lower_ratio_exclusive", "upper_ratio_inclusive", "condition"])
    comparisons = []
    for step in range(11):
        x = Fraction(step, 10)
        objective = 21 * (1 - x) ** 2 + x
        comparisons.append({"case_id": "KYRGYZ-H21-M1", "candidate_exact": FractionText(x), "candidate_decimal": DecimalText(x), "objective_exact": FractionText(objective), "objective_decimal": DecimalText(objective), "candidate_domain": "tenths_grid", "winner": x == 1})
    optimum = Fraction(41, 42)
    optimum_objective = 21 * (1 - optimum) ** 2 + optimum
    comparisons.append({"case_id": "KYRGYZ-H21-M1", "candidate_exact": FractionText(optimum), "candidate_decimal": DecimalText(optimum), "objective_exact": FractionText(optimum_objective), "objective_decimal": DecimalText(optimum_objective), "candidate_domain": "continuum", "winner": True})
    WriteDataset(destination / "lattice_continuum_comparisons.tsv", comparisons, ["case_id", "candidate_exact", "candidate_decimal", "objective_exact", "objective_decimal", "candidate_domain", "winner"])
    extension_rows = []
    for horizon in [4, 5, 6, 8]:
        values = EqualityQuadraticProfile(5, 1, horizon)
        for position, value in enumerate(values):
            extension_rows.append({"horizon": horizon, "position": position, "exact_value": FractionText(value), "decimal_value": DecimalText(value), "prefix_stable": position <= 4})
    WriteDataset(destination / "extension_stability.tsv", extension_rows, ["horizon", "position", "exact_value", "decimal_value", "prefix_stable"])
    sweep_rows = []
    for p_text, shape in [("3/2", "(1-u)^3"), ("2", "(1-u)^2"), ("3", "(1-u)^(3/2)"), ("4", "(1-u)^(4/3)")]:
        p_value = Fraction(p_text)
        for ratio in [1, 2, 5, 10, 20]:
            q_value = Fraction(1, 1) / (p_value - 1)
            sweep_rows.append({"p_exact": p_text, "p_decimal": DecimalText(p_value), "h_over_m_exact": str(ratio), "h_over_m_decimal": str(ratio), "asymptotic_shape": shape, "reach_control": "h/m", "shape_control": "p", "q_exact": FractionText(q_value)})
    WriteDataset(destination / "reach_shape_sweeps.tsv", sweep_rows, ["p_exact", "p_decimal", "h_over_m_exact", "h_over_m_decimal", "asymptotic_shape", "reach_control", "shape_control", "q_exact"])
    bifurcations = []
    for follower in range(1, 7):
        boundary = Fraction(follower * (follower + 1), 4)
        bifurcations.append({"follower": follower, "critical_h_over_m_exact": FractionText(boundary), "critical_h_over_m_decimal": DecimalText(boundary), "equality_support": follower - 1, "above_boundary_support": follower, "onset_side": "strictly_above"})
    WriteDataset(destination / "support_bifurcations.tsv", bifurcations, ["follower", "critical_h_over_m_exact", "critical_h_over_m_decimal", "equality_support", "above_boundary_support", "onset_side"])
    contacts = [
        {"contact_order": 1, "support_birth_exponent_exact": "1", "support_birth_exponent_decimal": "1", "leading_coefficient_exact": "25/2", "anchor": "FLUX-D4"},
        {"contact_order": 2, "support_birth_exponent_exact": "2", "support_birth_exponent_decimal": "2", "leading_coefficient_exact": "8125*pi^2/12", "anchor": "FLUX-D4"},
        {"contact_order": 3, "support_birth_exponent_exact": "3", "support_birth_exponent_decimal": "3", "leading_coefficient_exact": "declared_by_contact_normal_form", "anchor": "FLUX-D4"},
    ]
    WriteDataset(destination / "contact_response.tsv", contacts, ["contact_order", "support_birth_exponent_exact", "support_birth_exponent_decimal", "leading_coefficient_exact", "anchor"])
    identifiability = [
        {"audit": "persistence_only", "identified": "phase_cell_for_h_over_m", "not_identified": "exact_ratio;common_scale", "required_bridge": "none", "anchor": "CHG-B11"},
        {"audit": "two_powered_gaps_known_p", "identified": "h_over_m", "not_identified": "common_scale", "required_bridge": "grammar_internal_profile", "anchor": "CHG-B11"},
        {"audit": "admissible_log_concave_triple", "identified": "p;h_over_m", "not_identified": "common_scale", "required_bridge": "grammar_internal_profile", "anchor": "CHG-B11"},
        {"audit": "finite_constitutive_ledger", "identified": "registered_scores_only", "not_identified": "constitutive_law", "required_bridge": "accumulating_exact_response", "anchor": "FLUX-D5"},
    ]
    WriteDataset(destination / "identifiability_examples.tsv", identifiability, ["audit", "identified", "not_identified", "required_bridge", "anchor"])
    continuation = []
    finite = EqualityQuadraticProfile(5, 1, 7)
    for position, value in enumerate(finite):
        continuation.append({"family": "linear_site_finite_support", "position": position, "exact_value": FractionText(value), "decimal_value": DecimalText(value), "objective_scope": "CHG-B2"})
    for position in range(8):
        value = Fraction(3, 5) ** position
        continuation.append({"family": "matched_power_geometric", "position": position, "exact_value": FractionText(value), "decimal_value": DecimalText(value), "objective_scope": "SUP-E3/SUP-E4"})
    WriteDataset(destination / "continuation_comparisons.tsv", continuation, ["family", "position", "exact_value", "decimal_value", "objective_scope"])
    return sorted(destination.iterdir())


def BuildMaxEntData() -> list[Path]:
    destination = ROOT / "data" / "canonical" / "maxent"
    merger = [
        {"analysis": "unmerged", "candidate": "A1", "score": 0, "base_mass": 1, "category": "A", "category_probability_exact": "2/3"},
        {"analysis": "unmerged", "candidate": "A2", "score": 0, "base_mass": 1, "category": "A", "category_probability_exact": "2/3"},
        {"analysis": "unmerged", "candidate": "B", "score": 0, "base_mass": 1, "category": "B", "category_probability_exact": "1/3"},
        {"analysis": "merged_equal_mass", "candidate": "A", "score": 0, "base_mass": 1, "category": "A", "category_probability_exact": "1/2"},
        {"analysis": "merged_inherited_mass", "candidate": "A", "score": 0, "base_mass": 2, "category": "A", "category_probability_exact": "2/3"},
    ]
    WriteDataset(destination / "candidate_merger_examples.tsv", merger, ["analysis", "candidate", "score", "base_mass", "category", "category_probability_exact"])
    same_input = [
        {"case_id": "dominance", "row_a": "1,1", "row_b": "2,1", "relation": "P(A)>=P(B)", "condition": "w1>=0", "regime": "same_input"},
        {"case_id": "identity", "row_a": "1,2", "row_b": "1,2", "relation": "P(A)=P(B)", "condition": "all_nonnegative_weights", "regime": "same_input"},
        {"case_id": "incomparable", "row_a": "1,2", "row_b": "2,1", "relation": "weight_dependent", "condition": "w1-w2_changes_sign", "regime": "same_input"},
    ]
    WriteDataset(destination / "same_input_order_examples.tsv", same_input, ["case_id", "row_a", "row_b", "relation", "condition", "regime"])
    equalities = [
        {"case_id": "multiplicity_preserved", "input_a_rows": "0;1;1", "input_b_rows": "0;1;1", "base_masses": "1;1;1", "universal_equality": True},
        {"case_id": "multiplicity_deleted", "input_a_rows": "0;1;1", "input_b_rows": "0;1", "base_masses": "1;1", "universal_equality": False},
    ]
    WriteDataset(destination / "cross_input_equalities.tsv", equalities, ["case_id", "input_a_rows", "input_b_rows", "base_masses", "universal_equality"])
    reversals = [
        {"case_id": "MAX-G4", "parameter_exact": "1/2", "left_probability_exact": "3/4", "right_probability_exact": "32/59", "relation": "left_greater"},
        {"case_id": "MAX-G4", "parameter_exact": "1", "left_probability_exact": "1/2", "right_probability_exact": "4/5", "relation": "left_less"},
        {"case_id": "MAX-G4", "parameter_exact": "2", "left_probability_exact": "1/4", "right_probability_exact": "32/33", "relation": "left_less"},
    ]
    WriteDataset(destination / "order_reversal_witnesses.tsv", reversals, ["case_id", "parameter_exact", "left_probability_exact", "right_probability_exact", "relation"])
    decomposition = []
    for index in range(1, 122):
        live = index > 105
        facet = "wMax<=2wNoCoda+wDep" if live and index % 2 else "wDep<=2wOnset+wMax" if live else "not_applicable"
        decomposition.append({"implication_id": f"BS-{index:03d}", "antecedent_status": "nonempty" if live else "empty", "transport_status": "live_probability_order" if live else "vacuous_categorical_truth", "facet": facet})
    WriteDataset(destination / "basic_syllable_decomposition.tsv", decomposition, ["implication_id", "antecedent_status", "transport_status", "facet"])
    reductions = [
        {"proof_id": "MAX-G3-SMALL", "restriction": "globally_duplicate_free_rows_1_to_5", "forward_check": True, "reverse_check": True, "sign_preserved": True, "classification": "exact_compiler_relative_to_explicit_compact_minimum_foundation"},
        {"proof_id": "MAX-G4-BINARY", "restriction": "globally_duplicate_free_rows_1_or_2", "forward_check": True, "reverse_check": True, "sign_preserved": True, "classification": "exact_selector_bridge_with_conditional_conventional_coNP_boundary"},
    ]
    WriteDataset(destination / "reduction_proof_examples.tsv", reductions, ["proof_id", "restriction", "forward_check", "reverse_check", "sign_preserved", "classification"])
    capacity = [{"distinct_slices_q": q, "maximum_contact_plus_reversals": q - 1, "minimum_slices_for_pattern": q, "sharp": True} for q in range(1, 11)]
    WriteDataset(destination / "response_capacity.tsv", capacity, ["distinct_slices_q", "maximum_contact_plus_reversals", "minimum_slices_for_pattern", "sharp"])
    incomparability = [
        {"witness": "common_factor", "preserved_consumer": "fixed_mass_normalized_law", "changed_consumer": "arbitrary_mass_response_envelope", "exact_proof": "[1,1] versus [-1,3]"},
        {"witness": "interior_row_deletion", "preserved_consumer": "arbitrary_mass_response_envelope", "changed_consumer": "fixed_mass_normalized_law", "exact_proof": "z^4/((1+z)(1+z^2)(1+z^2+z^3))"},
    ]
    WriteDataset(destination / "law_envelope_incomparability.tsv", incomparability, ["witness", "preserved_consumer", "changed_consumer", "exact_proof"])
    return sorted(destination.iterdir())


def BuildApplicationData() -> list[Path]:
    destination = ROOT / "data" / "canonical" / "applications"
    grid = []
    for step in range(11):
        x = Fraction(step, 10)
        value = 21 * (1 - x) ** 2 + x
        grid.append({"domain": "tenths_grid", "candidate_exact": FractionText(x), "candidate_decimal": DecimalText(x), "objective_exact": FractionText(value), "winner": x == 1})
    optimum = Fraction(41, 42)
    grid.append({"domain": "continuum", "candidate_exact": FractionText(optimum), "candidate_decimal": DecimalText(optimum), "objective_exact": FractionText(21 * (1 - optimum) ** 2 + optimum), "winner": True})
    WriteDataset(destination / "mccollum_grid_continuum.tsv", grid, ["domain", "candidate_exact", "candidate_decimal", "objective_exact", "winner"])
    length_rows = []
    for position, value in enumerate(EqualityQuadraticProfile(5, 1, 9)):
        length_rows.append({"formal_case": "h5_m1_p2", "position": position, "exact_value": FractionText(value), "decimal_value": DecimalText(value), "positive": value > 0})
    WriteDataset(destination / "mccollum_length_profile.tsv", length_rows, ["formal_case", "position", "exact_value", "decimal_value", "positive"])
    goldrick = [
        {"object": "pair_1", "complete_score_row": "0,20,-17,1", "statistic_kind": "minimum_selected_output_onset_square", "euclidean_squared_exact": "361/5", "frobenius_squared_exact": "361/3", "order": "pairwise_first_selected_second"},
        {"object": "pair_2", "complete_score_row": "0,3,17,18", "statistic_kind": "minimum_selected_output_onset_square", "euclidean_squared_exact": "1010/9", "frobenius_squared_exact": "618/5", "order": "pairwise_second_selected_first"},
        {"object": "region_gap", "complete_score_row": "not_applicable", "statistic_kind": "ordered_onset_square_gap_second_minus_first", "euclidean_squared_exact": "1801/45", "frobenius_squared_exact": "49/15", "order": "reversal_proof"},
    ]
    WriteDataset(destination / "goldrick_daland_counterexample.tsv", goldrick, ["object", "complete_score_row", "statistic_kind", "euclidean_squared_exact", "frobenius_squared_exact", "order"])
    basic = [
        {"total_implications": 121, "empty_antecedent": 105, "nonempty_antecedent": 16, "full_lift_solution": "all_weights_zero", "live_cone_facets": "wMax<=2wNoCoda+wDep;wDep<=2wOnset+wMax", "nonzero_witness": "(log(2),0,0,0)"}
    ]
    WriteDataset(destination / "basic_syllable.tsv", basic, ["total_implications", "empty_antecedent", "nonempty_antecedent", "full_lift_solution", "live_cone_facets", "nonzero_witness"])
    walker = []
    values = [Fraction(7, 10), Fraction(8, 10), Fraction(9, 10)]
    for x in values:
        for y in values:
            if x == y:
                continue
            difference = y - x
            assimilation_cost = 1 + 20 * x
            faithful_cost = 2 + 20 * y
            outcome = "assimilation" if assimilation_cost < faithful_cost else "faithful" if faithful_cost < assimilation_cost else "tie"
            walker.append({"row_id": f"source_{len(walker) + 1:02d}", "row_origin": "source_transcribed", "x_exact": FractionText(x), "y_exact": FractionText(y), "difference_exact": FractionText(difference), "assimilation_cost_exact": FractionText(assimilation_cost), "faithful_cost_exact": FractionText(faithful_cost), "outcome": outcome, "boundary_exact": "-1/20"})
    for row_id, row_origin, x, y in [
        ("project_open_strip", "project_constructed_counterwitness", Fraction(4, 5), Fraction(39, 50)),
        ("project_tie", "project_constructed_boundary", Fraction(4, 5), Fraction(3, 4)),
    ]:
        difference = y - x
        assimilation_cost = 1 + 20 * x
        faithful_cost = 2 + 20 * y
        outcome = "assimilation" if assimilation_cost < faithful_cost else "faithful" if faithful_cost < assimilation_cost else "tie"
        walker.append({"row_id": row_id, "row_origin": row_origin, "x_exact": FractionText(x), "y_exact": FractionText(y), "difference_exact": FractionText(difference), "assimilation_cost_exact": FractionText(assimilation_cost), "faithful_cost_exact": FractionText(faithful_cost), "outcome": outcome, "boundary_exact": "-1/20"})
    WriteDataset(destination / "walker_boundary.tsv", walker, ["row_id", "row_origin", "x_exact", "y_exact", "difference_exact", "assimilation_cost_exact", "faithful_cost_exact", "outcome", "boundary_exact"])
    cabrera = []
    markedness = Fraction(1, 2)
    response_intercept = Fraction(3, 2)
    for n in range(6):
        cabrera.append({"n": n, "markedness_slope_exact": FractionText(markedness), "lexical_ratio_exact_expression": "exp(-1/2)", "response_logit_exact": FractionText(response_intercept - markedness * n), "response_exact_expression": f"1/(1+exp({FractionText(markedness * n - response_intercept)}))", "identified_from_lexicon": "markedness_slope", "requires_response_bridge": "intercept"})
    WriteDataset(destination / "cabrera_identifiability.tsv", cabrera, ["n", "markedness_slope_exact", "lexical_ratio_exact_expression", "response_logit_exact", "response_exact_expression", "identified_from_lexicon", "requires_response_bridge"])
    pater = []
    for scale in [0, 1, 2, 5, 10]:
        pater.append({"scenario": "symmetric_four_parse", "row_origin": "project_derived_counterwitness", "scale": scale, "best_hidden_output_a_count": 1, "best_hidden_output_b_count": 1, "probability_a_exact": "1/2", "probability_b_exact": "1/2", "source_strict_success_at_scale": False, "converges_to_intended_output": False, "criterion": "all_global_best_hidden_parses_must_share_overt_fibre"})
    pater.extend([
        {"scenario": "three_target_one_better_wrong", "row_origin": "project_derived_counterwitness", "scale": "log(2)", "best_hidden_output_a_count": 0, "best_hidden_output_b_count": 1, "probability_a_exact": "3/5", "probability_b_exact": "2/5", "source_strict_success_at_scale": True, "converges_to_intended_output": False, "criterion": "strict_success_but_common_scaling_limit_zero"},
        {"scenario": "three_target_one_better_wrong", "row_origin": "project_derived_counterwitness", "scale": "log(3)", "best_hidden_output_a_count": 0, "best_hidden_output_b_count": 1, "probability_a_exact": "1/2", "probability_b_exact": "1/2", "source_strict_success_at_scale": False, "converges_to_intended_output": False, "criterion": "strict_success_boundary"},
        {"scenario": "three_target_one_better_wrong", "row_origin": "project_derived_counterwitness", "scale": "t_to_infinity", "best_hidden_output_a_count": 0, "best_hidden_output_b_count": 1, "probability_a_exact": "0", "probability_b_exact": "1", "source_strict_success_at_scale": False, "converges_to_intended_output": False, "criterion": "fixed_support_best_fibre_limit"},
    ])
    WriteDataset(destination / "pater_scaling.tsv", pater, ["scenario", "row_origin", "scale", "best_hidden_output_a_count", "best_hidden_output_b_count", "probability_a_exact", "probability_b_exact", "source_strict_success_at_scale", "converges_to_intended_output", "criterion"])
    return sorted(destination.iterdir())


def CopyRows(source: Path, destination: Path) -> int:
    rows = ReadTsv(source)
    if not rows:
        raise ValueError(f"Source ledger has no rows: {source}")
    WriteTsv(destination, rows, list(rows[0]))
    return len(rows)


def BuildDemonstrationData() -> list[Path]:
    destination = ROOT / "data" / "canonical" / "demonstrations"
    source = ROOT / "data" / "source_ledgers"
    source_rows = []
    for source_path in sorted(path for path in source.glob("*.tsv") if path.name != "source_manifest.tsv"):
        source_rows.append({"file": source_path.relative_to(ROOT).as_posix(), "rows": len(ReadTsv(source_path)), "sha256": Sha256File(source_path), "role": "immutable reduced extraction input", "external_dependency": "source corpus media and complete extraction environment are not redistributed"})
    WriteTsv(source / "source_manifest.tsv", source_rows, ["file", "rows", "sha256", "role", "external_dependency"])
    CopyRows(source / "portuguese_reduced_source.tsv", destination / "portuguese_cells.tsv")
    portuguese_rows = ReadTsv(destination / "portuguese_cells.tsv")
    variants = ["full", "leave_flatness_out", "leave_high_low_out", "leave_zcr_out"]
    cell_key = lambda row: (row["window_id"], row["band_lower_hz"])
    full_decisions = {cell_key(row): row["development_gate_pass"] for row in portuguese_rows if row["score_variant"] == "full"}
    weak_total = sum(Fraction(row["median_delta"]) > 0 for row in portuguese_rows)
    changed_union: set[tuple[str, str]] = set()
    portuguese_summary = []
    for variant in variants:
        selected = [row for row in portuguese_rows if row["score_variant"] == variant]
        changed = {cell_key(row) for row in selected if row["development_gate_pass"] != full_decisions[cell_key(row)]}
        if variant != "full":
            changed_union.update(changed)
        portuguese_summary.append({"reader": variant, "weak_positive_cells": weak_total, "strong_pass_cells": sum(row["development_gate_pass"] == "YES" for row in selected), "strong_total_cells": len(selected), "changed_decisions_from_full": len(changed)})
    portuguese_summary.append({"reader": "union_of_reduction_witnesses", "weak_positive_cells": weak_total, "strong_pass_cells": "not_applicable", "strong_total_cells": len(full_decisions), "changed_decisions_from_full": len(changed_union)})
    WriteDataset(destination / "portuguese_decision_summary.tsv", portuguese_summary, ["reader", "weak_positive_cells", "strong_pass_cells", "strong_total_cells", "changed_decisions_from_full"])
    CopyRows(source / "english_speaker_scenario_source.tsv", destination / "english_speaker_scenario_margins.tsv")
    CopyRows(source / "english_aggregate_source.tsv", destination / "english_aggregate_cells.tsv")
    english_margins = ReadTsv(destination / "english_speaker_scenario_margins.tsv")
    english_aggregate = ReadTsv(destination / "english_aggregate_cells.tsv")
    scenario_keys = {(row["tracker_id"], row["start_offset_ms"], row["end_offset_ms"]) for row in english_aggregate}
    splits = {row["speaker_split"] for row in english_aggregate}
    median_fields = [field for field in english_aggregate[0] if field.endswith("_median_hz")]
    positive_medians = sum(Fraction(row[field]) > 0 for row in english_aggregate for field in median_fields)
    illustrative = next((row for row in english_aggregate for field in row if field.endswith("_positive_speakers") and row[field] == "29" and int(row["paired_speaker_support"]) - int(row[field]) == 13), None)
    if illustrative is None:
        raise ValueError("The registered 29-versus-13 English anchor is absent")
    strict_majority_boundary = int(illustrative["paired_speaker_support"]) // 2
    english_summary = [{"scenarios": len(scenario_keys), "splits": len(splits), "aggregate_rows": len(english_aggregate), "positive_median_cells": positive_medians, "speaker_scenario_rows": len(english_margins), "illustrative_support": "29_vs_13", "raw_surplus": 29 - 13, "above_strict_majority": 29 - strict_majority_boundary}]
    WriteDataset(destination / "english_decision_summary.tsv", english_summary, ["scenarios", "splits", "aggregate_rows", "positive_median_cells", "speaker_scenario_rows", "illustrative_support", "raw_surplus", "above_strict_majority"])
    CopyRows(source / "mandarin_corrected_source.tsv", destination / "mandarin_rows.tsv")
    mandarin_rows = ReadTsv(destination / "mandarin_rows.tsv")
    original_counts = Counter(row["original_decision"] for row in mandarin_rows)
    corrected_counts = Counter(row["corrected_decision"] for row in mandarin_rows)
    clear_retyped = sum(row["construction_scope_class"].startswith("CLEAR_COMPLEX") and row["original_decision"] != "MATCH" and row["corrected_decision"] == "MATCH" for row in mandarin_rows)
    mandarin_summary = [
        {"stage": "coarse_substring", "matches": original_counts["MATCH"], "counterexamples": original_counts["COUNTEREXAMPLE"], "refusals": original_counts["NO_CONCLUSION_SCOPE"], "clear_complex_final_retyped_as_match": 0},
        {"stage": "construction_sensitive", "matches": corrected_counts["MATCH"], "counterexamples": corrected_counts["COUNTEREXAMPLE"], "refusals": corrected_counts["NO_CONCLUSION_SCOPE"], "clear_complex_final_retyped_as_match": clear_retyped},
    ]
    WriteDataset(destination / "mandarin_decision_summary.tsv", mandarin_summary, ["stage", "matches", "counterexamples", "refusals", "clear_complex_final_retyped_as_match"])
    return sorted(destination.iterdir())


def InferType(values: Iterable[str]) -> str:
    nonempty = [value for value in values if value != ""]
    if not nonempty:
        return "string"
    if all(value in {"true", "false", "True", "False"} for value in nonempty):
        return "boolean"
    try:
        for value in nonempty:
            int(value)
        return "integer"
    except ValueError:
        return "string"


def BuildSchemasAndManifest(paths: Sequence[Path]) -> None:
    schema_directory = ROOT / "data" / "schemas"
    manifest = []
    for path in sorted(paths):
        relative = path.relative_to(ROOT).as_posix()
        if path.suffix == ".json":
            schema = {"$schema": "https://json-schema.org/draft/2020-12/schema", "title": relative, "type": "object", "additionalProperties": True}
            row_count = 1
            fields = "JSON object"
        else:
            rows = ReadTsv(path)
            columns = list(rows[0]) if rows else []
            properties = {column: {"type": InferType(row[column] for row in rows)} for column in columns}
            schema = {"$schema": "https://json-schema.org/draft/2020-12/schema", "title": relative, "type": "array", "items": {"type": "object", "properties": properties, "required": columns, "additionalProperties": False}}
            row_count = len(rows)
            fields = ";".join(columns)
        schema_path = schema_directory / (path.stem + ".schema.json")
        WriteJson(schema_path, schema)
        manifest.append({"dataset": relative, "schema": schema_path.relative_to(ROOT).as_posix(), "row_count": row_count, "sha256": Sha256File(path), "fields": fields, "units": "declared_per_field; exact expressions are dimensionless unless named otherwise", "missing_value_semantics": "empty means unavailable only where the schema permits a string; no undocumented missing values", "provenance": "project-derived exact result or reduced registered decision ledger; underlying third-party corpus media are not redistributed", "license_status": "research facts and project-authored tabulation; underlying source rights remain with cited owners", "relationship": "result registry, verification checks, figures, and tables"})
    WriteTsv(ROOT / "data" / "dataset_manifest.tsv", manifest, ["dataset", "schema", "row_count", "sha256", "fields", "units", "missing_value_semantics", "provenance", "license_status", "relationship"])
    checksum_directory = ROOT / "data" / "checksums"
    checksum_directory.mkdir(parents=True, exist_ok=True)
    (checksum_directory / "canonical_data.sha256").write_text("\n".join(f"{row['sha256']}  {row['dataset']}" for row in manifest) + "\n", encoding="utf-8", newline="\n")
    source_manifest = ROOT / "data" / "source_ledgers" / "source_manifest.tsv"
    source_rows = ReadTsv(source_manifest)
    (checksum_directory / "source_ledgers.sha256").write_text("\n".join(f"{row['sha256']}  {row['file']}" for row in source_rows) + "\n", encoding="utf-8", newline="\n")


def BuildCanonicalData() -> dict[str, int]:
    paths = [*BuildFiniteData(), *BuildContinuousHgData(), *BuildMaxEntData(), *BuildApplicationData(), *BuildDemonstrationData()]
    paths = [path for path in paths if path.is_file()]
    BuildSchemasAndManifest(paths)
    return {"dataset_count": len(paths), "total_rows": sum(1 if path.suffix == ".json" else len(ReadTsv(path)) for path in paths)}
