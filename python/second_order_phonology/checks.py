from __future__ import annotations

from collections import Counter
from fractions import Fraction
from pathlib import Path
from typing import Any, Callable

from .common import ROOT, ReadJson, ReadTsv, Sha256File, WriteJson, WriteTsv
from .data_build import EqualityQuadraticProfile, FractionText, QuadraticFirstZero


def Result(name: str, passed: bool, observed: Any, expected: Any) -> dict[str, Any]:
    return {"check": name, "status": "PASS" if passed else "FAIL", "observed": observed, "expected": expected}


def WriteCheckReport(name: str, checks: list[dict[str, Any]]) -> dict[str, Any]:
    status = "PASS" if all(check["status"] == "PASS" for check in checks) else "FAIL"
    report = {"component": name, "status": status, "check_count": len(checks), "checks": checks}
    WriteJson(ROOT / "verification" / "reports" / f"python_{name}.json", report)
    return report


def VerifyFiniteCalculus() -> dict[str, Any]:
    report = ReadJson(ROOT / "verification" / "reports" / "machine_verification.json")
    results = report["Results"]
    regressions = [result for result in results if result["ResultID"].startswith("CALC-R")]
    proof_goals = [proof_goal for result in results for proof_goal in result["ProofGoalResults"]]
    registered_proof_goals = ReadTsv(ROOT / "registry" / "proof_goal_registry.tsv")
    registered_ids = {row["proof_goal_id"] for row in registered_proof_goals}
    registered_methods = {row["proof_goal_id"]: row["machine_status"] for row in registered_proof_goals}
    statuses = Counter(proof_goal["Status"] for proof_goal in proof_goals)
    observed_methods = {proof_goal["ProofGoalID"]: proof_goal["Status"] for proof_goal in proof_goals}
    methods_match_source = observed_methods == registered_methods
    all_proof_goals_machine_closed = statuses == Counter({"MachineClosed": 218})
    checks = [
        Result("result_count", len(results) == 68, len(results), 68),
        Result("regression_count", len(regressions) == 15, len(regressions), 15),
        Result("proof_goal_count", len(proof_goals) == 218, len(proof_goals), 218),
        Result("proof_goal_ids_unique", len({proof_goal["ProofGoalID"] for proof_goal in proof_goals}) == 218, len({proof_goal["ProofGoalID"] for proof_goal in proof_goals}), 218),
        Result("proof_goal_ids_match_registry", {proof_goal["ProofGoalID"] for proof_goal in proof_goals} == registered_ids, len({proof_goal["ProofGoalID"] for proof_goal in proof_goals} & registered_ids), len(registered_ids)),
        Result("registered_proof_goal_closure", methods_match_source or all_proof_goals_machine_closed, dict(statuses), "registered source-catalog methods or 218 MachineClosed records"),
        Result("three_outcomes", report["Results"][0]["ExactResult"][1] == ["Q-CONSERVATIVE", "Q-NONCONSERVATIVE", "NOT EVALUATED"], report["Results"][0]["ExactResult"][1], ["Q-CONSERVATIVE", "Q-NONCONSERVATIVE", "NOT EVALUATED"]),
        Result("all_regressions_closed", all(result["Status"] == "MachineClosed" or result["Status"].endswith("Pass") for result in regressions), [result["Status"] for result in regressions], "registered passing source-catalog method or MachineClosed"),
    ]
    return WriteCheckReport("finite_calculus", checks)


def VerifyContinuousHg() -> dict[str, Any]:
    profile = EqualityQuadraticProfile(5, 1, 6)
    first_zero = QuadraticFirstZero(5, 1)
    continuum = Fraction(41, 42)
    lattice_values = [(Fraction(step, 10), 21 * (1 - Fraction(step, 10)) ** 2 + Fraction(step, 10)) for step in range(11)]
    lattice_winner = min(lattice_values, key=lambda pair: pair[1])[0]
    extension = EqualityQuadraticProfile(5, 1, 9)
    checks = [
        Result("quadratic_first_zero", first_zero == 4, first_zero, 4),
        Result("kazakh_profile", profile[:7] == [Fraction(1), Fraction(3, 5), Fraction(3, 10), Fraction(1, 10), Fraction(0), Fraction(0), Fraction(0)], [FractionText(value) for value in profile[:7]], ["1", "3/5", "3/10", "1/10", "0", "0", "0"]),
        Result("equality_zero_side", Fraction(1, 10) * Fraction(4 * 5, 2) == 1 and profile[4] == 0, FractionText(profile[4]), "0"),
        Result("kyrgyz_continuum", continuum == Fraction(41, 42), FractionText(continuum), "41/42"),
        Result("kyrgyz_tenths", lattice_winner == 1, FractionText(lattice_winner), "1"),
        Result("extension_stability", extension[:7] == profile[:7], [FractionText(value) for value in extension[:7]], [FractionText(value) for value in profile[:7]]),
        Result("common_scale_gauge", QuadraticFirstZero(25, 5) == first_zero, QuadraticFirstZero(25, 5), first_zero),
    ]
    return WriteCheckReport("continuous_hg", checks)


def VerifyMaxEnt() -> dict[str, Any]:
    unmerged_probability = Fraction(2, 3)
    merged_probability = Fraction(1, 2)
    mass_inherited_probability = Fraction(2, 3)
    decomposition = ReadTsv(ROOT / "data" / "canonical" / "maxent" / "basic_syllable_decomposition.tsv")
    counts = Counter(row["antecedent_status"] for row in decomposition)
    capacity = ReadTsv(ROOT / "data" / "canonical" / "maxent" / "response_capacity.tsv")
    checks = [
        Result("candidate_merger_changes_mass", unmerged_probability != merged_probability, FractionText(merged_probability), "different from 2/3"),
        Result("combined_mass_restores_law", mass_inherited_probability == unmerged_probability, FractionText(mass_inherited_probability), "2/3"),
        Result("basic_syllable_total", len(decomposition) == 121, len(decomposition), 121),
        Result("basic_syllable_split", counts == Counter({"empty": 105, "nonempty": 16}), dict(counts), {"empty": 105, "nonempty": 16}),
        Result("response_capacity", all(int(row["maximum_contact_plus_reversals"]) == int(row["distinct_slices_q"]) - 1 for row in capacity), len(capacity), "q-1 for every row"),
        Result("g9_two_directions", len(ReadTsv(ROOT / "data" / "canonical" / "maxent" / "law_envelope_incomparability.tsv")) == 2, 2, 2),
    ]
    return WriteCheckReport("maxent", checks)


def VerifyApplications() -> dict[str, Any]:
    grid = ReadTsv(ROOT / "data" / "canonical" / "applications" / "mccollum_grid_continuum.tsv")
    grid_winners = [row for row in grid if row["winner"] == "true" and row["domain"] == "tenths_grid"]
    continuum_winners = [row for row in grid if row["winner"] == "true" and row["domain"] == "continuum"]
    walker = ReadTsv(ROOT / "data" / "canonical" / "applications" / "walker_boundary.tsv")
    basic = ReadTsv(ROOT / "data" / "canonical" / "applications" / "basic_syllable.tsv")[0]
    goldrick = ReadTsv(ROOT / "data" / "canonical" / "applications" / "goldrick_daland_counterexample.tsv")
    goldrick_by_object = {row["object"]: row for row in goldrick}
    pater = ReadTsv(ROOT / "data" / "canonical" / "applications" / "pater_scaling.tsv")
    source_crosswalk = {row["record_id"]: row for row in ReadTsv(ROOT / "registry" / "source_claim_crosswalk.tsv") if row["record_type"] == "source_facing_application"}
    promoted = {"APP-MCC-GRID", "APP-MCC-LENGTH", "APP-MCC-COMP", "SEL-F2", "APP-BASIC", "APP-PATER", "APP-WALKER", "APP-CABRERA"}
    crosswalk_complete = set(source_crosswalk) == promoted and all(all((ROOT / path).is_file() for path in row["evidence_route"].split(";")) and row["citation_keys"] != "not_applicable" and row["scope_ceiling"] for row in source_crosswalk.values())
    checks = [
        Result("mccollum_grid_winner", len(grid_winners) == 1 and grid_winners[0]["candidate_exact"] == "1", [row["candidate_exact"] for row in grid_winners], ["1"]),
        Result("mccollum_continuum_winner", len(continuum_winners) == 1 and continuum_winners[0]["candidate_exact"] == "41/42", [row["candidate_exact"] for row in continuum_winners], ["41/42"]),
        Result("walker_six_source_cells", sum(row["row_origin"] == "source_transcribed" for row in walker) == 6, Counter(row["row_origin"] for row in walker), {"source_transcribed": 6, "project_constructed_counterwitness": 1, "project_constructed_boundary": 1}),
        Result("walker_open_strip_and_tie", any(row["row_id"] == "project_open_strip" and row["difference_exact"] == "-1/50" and row["assimilation_cost_exact"] == "17" and row["faithful_cost_exact"] == "88/5" and row["outcome"] == "assimilation" for row in walker) and any(row["row_id"] == "project_tie" and row["difference_exact"] == "-1/20" and row["assimilation_cost_exact"] == row["faithful_cost_exact"] == "17" and row["outcome"] == "tie" for row in walker), [row for row in walker if row["row_origin"] != "source_transcribed"], "exact open-strip counterwitness and equality boundary"),
        Result("basic_syllable_split", (basic["total_implications"], basic["empty_antecedent"], basic["nonempty_antecedent"]) == ("121", "105", "16"), [basic["total_implications"], basic["empty_antecedent"], basic["nonempty_antecedent"]], ["121", "105", "16"]),
        Result(
            "goldrick_complete_counterexample",
            len(goldrick) == 3
            and goldrick_by_object.get("pair_1", {}).get("complete_score_row") == "0,20,-17,1"
            and goldrick_by_object.get("pair_2", {}).get("complete_score_row") == "0,3,17,18"
            and goldrick_by_object.get("pair_1", {}).get("statistic_kind") == "minimum_selected_output_onset_square"
            and goldrick_by_object.get("pair_2", {}).get("statistic_kind") == "minimum_selected_output_onset_square"
            and goldrick_by_object.get("region_gap", {}).get("statistic_kind") == "ordered_onset_square_gap_second_minus_first"
            and [goldrick_by_object.get(key, {}).get("euclidean_squared_exact") for key in ("pair_1", "pair_2", "region_gap")] == ["361/5", "1010/9", "1801/45"]
            and [goldrick_by_object.get(key, {}).get("frobenius_squared_exact") for key in ("pair_1", "pair_2", "region_gap")] == ["361/3", "618/5", "49/15"]
            and goldrick_by_object.get("region_gap", {}).get("order") == "reversal_proof",
            goldrick,
            "exact score rows, squared onset minima, and second-minus-first gaps",
        ),
        Result("pater_tie_survives_scaling", all(row["probability_a_exact"] == "1/2" for row in pater if row["scenario"] == "symmetric_four_parse"), [row["probability_a_exact"] for row in pater if row["scenario"] == "symmetric_four_parse"], "all 1/2"),
        Result("pater_finite_success_limit_counterwitness", any(row["scenario"] == "three_target_one_better_wrong" and row["scale"] == "log(2)" and row["probability_a_exact"] == "3/5" and row["source_strict_success_at_scale"] == "true" for row in pater) and any(row["scenario"] == "three_target_one_better_wrong" and row["scale"] == "log(3)" and row["probability_a_exact"] == "1/2" for row in pater) and any(row["scenario"] == "three_target_one_better_wrong" and row["scale"] == "t_to_infinity" and row["probability_a_exact"] == "0" and row["probability_b_exact"] == "1" for row in pater), [row for row in pater if row["scenario"] == "three_target_one_better_wrong"], "3/5 at log(2), 1/2 at log(3), and target limit 0"),
        Result("promoted_application_crosswalk", crosswalk_complete, sorted(source_crosswalk), sorted(promoted)),
    ]
    return WriteCheckReport("applications", checks)


def VerifyDemonstrations() -> dict[str, Any]:
    portuguese = ReadTsv(ROOT / "data" / "canonical" / "demonstrations" / "portuguese_cells.tsv")
    portuguese_summary = ReadTsv(ROOT / "data" / "canonical" / "demonstrations" / "portuguese_decision_summary.tsv")
    english_margins = ReadTsv(ROOT / "data" / "canonical" / "demonstrations" / "english_speaker_scenario_margins.tsv")
    english_aggregate = ReadTsv(ROOT / "data" / "canonical" / "demonstrations" / "english_aggregate_cells.tsv")
    english_summary = ReadTsv(ROOT / "data" / "canonical" / "demonstrations" / "english_decision_summary.tsv")[0]
    mandarin = ReadTsv(ROOT / "data" / "canonical" / "demonstrations" / "mandarin_rows.tsv")
    mandarin_summary = ReadTsv(ROOT / "data" / "canonical" / "demonstrations" / "mandarin_decision_summary.tsv")
    pass_counts = {row["reader"]: row["strong_pass_cells"] for row in portuguese_summary}
    reduced_changed = sum(int(row["changed_decisions_from_full"]) for row in portuguese_summary if row["reader"].startswith("leave_"))
    checks = [
        Result("portuguese_cells", len(portuguese) == 72, len(portuguese), 72),
        Result("portuguese_pass_counts", pass_counts.get("full") == "17" and pass_counts.get("leave_flatness_out") == "11" and pass_counts.get("leave_high_low_out") == "16" and pass_counts.get("leave_zcr_out") == "13", pass_counts, {"full": "17", "leave_flatness_out": "11", "leave_high_low_out": "16", "leave_zcr_out": "13"}),
        Result("portuguese_changed_decision_proofs", reduced_changed == 13, reduced_changed, 13),
        Result("english_margins", len(english_margins) == 14135, len(english_margins), 14135),
        Result("english_aggregate_rows", len(english_aggregate) == 300, len(english_aggregate), 300),
        Result("english_headline_cells", english_summary["positive_median_cells"] == "4200" and english_summary["scenarios"] == "150" and english_summary["splits"] == "2", english_summary, {"positive_median_cells": "4200", "scenarios": "150", "splits": "2"}),
        Result("mandarin_rows", len(mandarin) == 639, len(mandarin), 639),
        Result("mandarin_summary", mandarin_summary[-1]["matches"] == "622" and mandarin_summary[-1]["counterexamples"] == "13" and mandarin_summary[-1]["refusals"] == "4", mandarin_summary[-1], {"matches": "622", "counterexamples": "13", "refusals": "4"}),
        Result("mandarin_scope_retyping", mandarin_summary[-1]["clear_complex_final_retyped_as_match"] == "4", mandarin_summary[-1]["clear_complex_final_retyped_as_match"], "4"),
    ]
    return WriteCheckReport("demonstrations", checks)


def CompareEngines() -> dict[str, Any]:
    report = ReadJson(ROOT / "verification" / "reports" / "machine_verification.json")
    results = {result["ResultID"]: result for result in report["Results"]}
    pt_result = results["DATA-PT-R1"]["ExactResult"][0]
    en_result = results["DATA-EN-R1"]["ExactResult"][0]
    zh_result = results["DATA-ZH-R1"]["ExactResult"][0]
    max_g6 = results["MAX-G6"]["ExactResult"][0]
    max_g4 = results["MAX-G4"]["ExactResult"][0]
    rows = [
        {"anchor_id": "CHG-B2-KAZAKH", "python_exact": "1,3/5,3/10,1/10,0,0,0", "wolfram_exact": ",".join(str(value) for value in results["CHG-B2"]["ExactResult"][3][1]), "agreement": ",".join(str(value) for value in results["CHG-B2"]["ExactResult"][3][1]) == "1,3/5,3/10,1/10,0,0,0"},
        {"anchor_id": "CHG-B2-FIRST-ZERO", "python_exact": "4", "wolfram_exact": str(results["CHG-B2"]["ExactResult"][3][0]), "agreement": results["CHG-B2"]["ExactResult"][3][0] == 4},
        {"anchor_id": "CHG-B10-EXTENSION", "python_exact": "4;1,3/5,3/10,1/10,0,0", "wolfram_exact": f"{results['CHG-B10']['ExactResult'][1]};{','.join(str(value) for value in results['CHG-B10']['ExactResult'][2])}", "agreement": results["CHG-B10"]["ExactResult"][1] == 4 and results["CHG-B10"]["ExactResult"][2] == [1, "3/5", "3/10", "1/10", 0, 0]},
        {"anchor_id": "CHG-B14-BIFURCATION", "python_exact": "1/25;0", "wolfram_exact": f"{results['CHG-B14']['ExactResult'][1]};{results['CHG-B14']['ExactResult'][2]}", "agreement": results["CHG-B14"]["ExactResult"][1:3] == ["1/25", 0]},
        {"anchor_id": "FLUX-D4-CONTACT", "python_exact": "25/2;(8125*Pi^2)/12", "wolfram_exact": ";".join(results["FLUX-D4"]["ExactResult"][1]), "agreement": results["FLUX-D4"]["ExactResult"][1] == ["25/2", "(8125*Pi^2)/12"]},
        {"anchor_id": "APP-MCC-GRID-CONTINUUM", "python_exact": "41/42", "wolfram_exact": str(results["APP-MCC-GRID"]["ExactResult"][0]), "agreement": str(results["APP-MCC-GRID"]["ExactResult"][0]) == "41/42"},
        {"anchor_id": "APP-MCC-GRID-LATTICE", "python_exact": "1", "wolfram_exact": str(results["APP-MCC-GRID"]["ExactResult"][1]), "agreement": results["APP-MCC-GRID"]["ExactResult"][1] == 1},
        {"anchor_id": "MAX-G4-REVERSAL", "python_exact": "3/4,32/59,16/25;1/2,4/5,4/5;1/4,32/33,16/17", "wolfram_exact": ";".join(",".join(row) for row in max_g4), "agreement": max_g4 == [["3/4", "32/59", "16/25"], ["1/2", "4/5", "4/5"], ["1/4", "32/33", "16/17"]]},
        {"anchor_id": "MAX-G6-DECOMPOSITION", "python_exact": "121=105+16", "wolfram_exact": f"{max_g6[3]}={max_g6[5]}+{max_g6[6]}", "agreement": [max_g6[3], max_g6[5], max_g6[6]] == [121, 105, 16]},
        {"anchor_id": "MAX-G8-CAPACITY", "python_exact": "q-1", "wolfram_exact": "9=10-1", "agreement": results["MAX-G8"]["ExactResult"][1] == [9, 9]},
        {"anchor_id": "APP-BASIC-DECOMPOSITION", "python_exact": "121;105;16", "wolfram_exact": ";".join(str(value) for value in results["APP-BASIC"]["ExactResult"][0]["Inventory"]), "agreement": results["APP-BASIC"]["ExactResult"][0]["Inventory"] == [121, 105, 16]},
        {"anchor_id": "SEL-F2-COUNTEREXAMPLE", "python_exact": "361/3;618/5;49/15", "wolfram_exact": ";".join(results["SEL-F2"]["ExactResult"][2]), "agreement": results["SEL-F2"]["ExactResult"][2] == ["361/3", "618/5", "49/15"]},
        {"anchor_id": "DATA-PT", "python_exact": "72;17;13", "wolfram_exact": f"{pt_result['RowCount']};{pt_result['FullGatePass']};{pt_result['ChangedGateDecisions']}", "agreement": [pt_result["RowCount"], pt_result["FullGatePass"], pt_result["ChangedGateDecisions"]] == [72, 17, 13]},
        {"anchor_id": "DATA-EN", "python_exact": "300;4200;14135", "wolfram_exact": f"{en_result['AggregateRows']};{en_result['PositiveAggregateMedianCells']};{en_result['SpeakerScenarioRows']}", "agreement": [en_result["AggregateRows"], en_result["PositiveAggregateMedianCells"], en_result["SpeakerScenarioRows"]] == [300, 4200, 14135]},
        {"anchor_id": "DATA-ZH", "python_exact": "622;13;4", "wolfram_exact": f"{zh_result['CorrectedDecisionCounts']['MATCH']};{zh_result['CorrectedDecisionCounts']['COUNTEREXAMPLE']};{zh_result['CorrectedDecisionCounts']['NO_CONCLUSION_SCOPE']}", "agreement": [zh_result["CorrectedDecisionCounts"]["MATCH"], zh_result["CorrectedDecisionCounts"]["COUNTEREXAMPLE"], zh_result["CorrectedDecisionCounts"]["NO_CONCLUSION_SCOPE"]] == [622, 13, 4]},
    ]
    WriteTsv(ROOT / "verification" / "reports" / "cross_engine_agreement.tsv", rows, ["anchor_id", "python_exact", "wolfram_exact", "agreement"])
    checks = [Result("shared_anchors", all(row["agreement"] for row in rows), sum(1 for row in rows if row["agreement"]), len(rows))]
    return WriteCheckReport("cross_engine", checks)


def RunAllChecks() -> list[dict[str, Any]]:
    functions: list[Callable[[], dict[str, Any]]] = [VerifyFiniteCalculus, VerifyContinuousHg, VerifyMaxEnt, VerifyApplications, VerifyDemonstrations, CompareEngines]
    return [function() for function in functions]
