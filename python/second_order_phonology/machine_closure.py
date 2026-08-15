from __future__ import annotations

import csv
import json
import shutil
from collections import Counter
from pathlib import Path
from typing import Any, Mapping, Sequence

from .common import ROOT


EXPECTED_RESULT_COUNT = 68
EXPECTED_PROOF_GOAL_COUNT = 218
PROOF_GOAL_CLOSURE_METHODS = {
    "ExactApplicationProofPass",
    "ExactConstructivePass",
    "ExactDataReplayPass",
    "ExactSymbolicPass",
    "ExhaustiveFinitePass",
    "FiniteSemanticProofPass",
    "InductionProofPass",
    "LeanKernelProofPass",
    "ReductionProofPass",
    "SemanticDerivationProofPass",
}


def GateCheck(name: str, passed: bool, observed: Any, expected: Any) -> dict[str, Any]:
    return {"check": name, "status": "PASS" if passed else "FAIL", "observed": observed, "expected": expected}


def _read_json(path: Path) -> dict[str, Any] | None:
    if not path.is_file():
        return None
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError):
        return None
    return value if isinstance(value, dict) else None


def _read_tsv(path: Path) -> list[dict[str, str]] | None:
    if not path.is_file():
        return None
    try:
        with path.open(encoding="utf-8", newline="") as handle:
            return list(csv.DictReader(handle, delimiter="\t"))
    except (OSError, UnicodeDecodeError, csv.Error):
        return None


def _exact_pass_rows(rows: Sequence[Mapping[str, str]], identifier_field: str, identifiers: set[str], truth_fields: Sequence[str]) -> bool:
    row_ids = [row.get(identifier_field, "") for row in rows]
    if len(row_ids) != len(set(row_ids)) or set(row_ids) != identifiers:
        return False
    for row in rows:
        if row.get("status") != "PASS":
            return False
        if any(row.get(field) != "true" for field in truth_fields):
            return False
    return True


def FormalReplayChecks(report: Mapping[str, Any], result_ids: set[str], proof_goal_ids: set[str]) -> list[dict[str, Any]]:
    proof_goal_results = report.get("proof_goal_results", [])
    proof_goal_rows = proof_goal_results if isinstance(proof_goal_results, list) else []
    accepted_rows = [
        row for row in proof_goal_rows
        if isinstance(row, dict) and row.get("status") == "PASS" and row.get("proof_goal_id") in proof_goal_ids
    ]
    accepted_ids = {row.get("proof_goal_id") for row in accepted_rows}
    closed_ids = report.get("machine_closed_result_ids", [])
    closed_set = set(closed_ids) if isinstance(closed_ids, list) else set()
    statement_check_values = report.get("statement_checks", [])
    statement_check_rows = statement_check_values if isinstance(statement_check_values, list) else []
    accepted_statement_rows = [
        row
        for row in statement_check_rows
        if isinstance(row, dict) and row.get("status") == "PASS" and row.get("result_id") in result_ids
    ]
    accepted_statement_result_ids = {row.get("result_id") for row in accepted_statement_rows}
    checks = [
        GateCheck("formal_checker_status", report.get("status") == "PASS", report.get("status"), "PASS"),
        GateCheck("formal_specifications_68_of_68", report.get("specification_count") == EXPECTED_RESULT_COUNT, report.get("specification_count"), EXPECTED_RESULT_COUNT),
        GateCheck("semantic_specifications_68_of_68", report.get("semantic_specification_count") == EXPECTED_RESULT_COUNT, report.get("semantic_specification_count"), EXPECTED_RESULT_COUNT),
        GateCheck("machine_closed_results_68_of_68", report.get("machine_closed_result_count") == EXPECTED_RESULT_COUNT and len(closed_ids) == EXPECTED_RESULT_COUNT and closed_set == result_ids, [report.get("machine_closed_result_count"), len(closed_ids), len(closed_set)], [EXPECTED_RESULT_COUNT, EXPECTED_RESULT_COUNT, EXPECTED_RESULT_COUNT]),
        GateCheck("registered_proof_goals_218", report.get("proof_goal_count") == EXPECTED_PROOF_GOAL_COUNT, report.get("proof_goal_count"), EXPECTED_PROOF_GOAL_COUNT),
        GateCheck("proof_goals_discharged_218_of_218", report.get("discharged_proof_goal_count") == EXPECTED_PROOF_GOAL_COUNT and len(accepted_rows) == EXPECTED_PROOF_GOAL_COUNT and accepted_ids == proof_goal_ids, [report.get("discharged_proof_goal_count"), len(accepted_rows), len(accepted_ids)], [EXPECTED_PROOF_GOAL_COUNT, EXPECTED_PROOF_GOAL_COUNT, EXPECTED_PROOF_GOAL_COUNT]),
        GateCheck("mathematical_proofs_218", report.get("proof_count") == EXPECTED_PROOF_GOAL_COUNT, report.get("proof_count"), EXPECTED_PROOF_GOAL_COUNT),
        GateCheck("statement_checks_68_of_68", report.get("statement_check_count") == EXPECTED_RESULT_COUNT and report.get("accepted_statement_check_count") == EXPECTED_RESULT_COUNT and len(accepted_statement_rows) == EXPECTED_RESULT_COUNT and accepted_statement_result_ids == result_ids, [report.get("statement_check_count"), report.get("accepted_statement_check_count"), len(accepted_statement_rows), len(accepted_statement_result_ids)], [EXPECTED_RESULT_COUNT, EXPECTED_RESULT_COUNT, EXPECTED_RESULT_COUNT, EXPECTED_RESULT_COUNT]),
        GateCheck("formal_checker_no_failures", report.get("failures") == [], report.get("failures"), []),
        GateCheck("formal_checker_no_missing_proof_goals", report.get("missing_proof_goal_ids") == [], report.get("missing_proof_goal_ids"), []),
        GateCheck("formal_checker_no_missing_results", report.get("missing_result_ids") == [], report.get("missing_result_ids"), []),
        GateCheck("formal_checker_no_missing_statement_checks", report.get("missing_statement_check_ids") == [], report.get("missing_statement_check_ids"), []),
    ]
    return checks


def ValidateMachineClosure(root: Path = ROOT) -> dict[str, Any]:
    result_rows = _read_tsv(root / "registry" / "result_registry.tsv")
    proof_goal_rows = _read_tsv(root / "registry" / "proof_goal_registry.tsv")
    status_rows = _read_tsv(root / "registry" / "result_status.tsv")
    required_registry_present = result_rows is not None and proof_goal_rows is not None and status_rows is not None
    result_ids = {row.get("result_id", "") for row in result_rows or []}
    proof_goal_ids = {row.get("proof_goal_id", "") for row in proof_goal_rows or [] if row.get("mandatory") == "true"}
    checks = [GateCheck("machine_closure_registries_present", required_registry_present, required_registry_present, True)]
    checks.extend([
        GateCheck("machine_closure_result_registry_68", len(result_rows or []) == EXPECTED_RESULT_COUNT and len(result_ids) == EXPECTED_RESULT_COUNT, [len(result_rows or []), len(result_ids)], [EXPECTED_RESULT_COUNT, EXPECTED_RESULT_COUNT]),
        GateCheck("machine_closure_proof_goal_registry_218", len(proof_goal_rows or []) == EXPECTED_PROOF_GOAL_COUNT and len(proof_goal_ids) == EXPECTED_PROOF_GOAL_COUNT, [len(proof_goal_rows or []), len(proof_goal_ids)], [EXPECTED_PROOF_GOAL_COUNT, EXPECTED_PROOF_GOAL_COUNT]),
    ])
    status_ids = [row.get("result_id", "") for row in status_rows or []]
    machine_statuses = [row.get("machine_status", "") for row in status_rows or []]
    proof_goal_statuses = [row.get("machine_status", "") for row in proof_goal_rows or [] if row.get("mandatory") == "true"]
    checks.extend([
        GateCheck("machine_closure_status_registry_exact", len(status_ids) == EXPECTED_RESULT_COUNT and len(set(status_ids)) == EXPECTED_RESULT_COUNT and set(status_ids) == result_ids, [len(status_ids), len(set(status_ids))], [EXPECTED_RESULT_COUNT, EXPECTED_RESULT_COUNT]),
        GateCheck("all_result_statuses_machine_closed", len(machine_statuses) == EXPECTED_RESULT_COUNT and set(machine_statuses) == {"MachineClosed"}, dict(Counter(machine_statuses)), {"MachineClosed": EXPECTED_RESULT_COUNT}),
        GateCheck("all_mandatory_proof_goal_closure_methods_registered", len(proof_goal_statuses) == EXPECTED_PROOF_GOAL_COUNT and set(proof_goal_statuses) <= PROOF_GOAL_CLOSURE_METHODS, dict(Counter(proof_goal_statuses)), sorted(PROOF_GOAL_CLOSURE_METHODS)),
    ])
    specifications = sorted((root / "formal" / "specs").glob("*.json")) if (root / "formal" / "specs").is_dir() else []
    checks.append(GateCheck("canonical_formal_specifications_exactly_68", {path.stem for path in specifications} == result_ids and len(specifications) == EXPECTED_RESULT_COUNT, len(specifications), EXPECTED_RESULT_COUNT))

    replay = _read_json(root / "formal" / "reports" / "proof_replay.json")
    checks.append(GateCheck("formal_checker_report_present", replay is not None, replay is not None, True))
    if replay is not None:
        checks.extend(FormalReplayChecks(replay, result_ids, proof_goal_ids))

    mutation = _read_json(root / "formal" / "reports" / "mutation_report.json")
    mutation_passed = mutation is not None and mutation.get("status") == "PASS" and mutation.get("result_count") == EXPECTED_RESULT_COUNT and isinstance(mutation.get("mandatory_non_equivalent_count"), int) and mutation["mandatory_non_equivalent_count"] > 0 and mutation.get("killed_count") == mutation.get("mandatory_non_equivalent_count") and mutation.get("survived_mutant_ids") == []
    checks.append(GateCheck("mandatory_mutation_gate", mutation_passed, mutation, {"status": "PASS", "result_count": EXPECTED_RESULT_COUNT, "kill_rate": "100%", "survived_mutant_ids": []}))

    satisfiability = _read_tsv(root / "formal" / "reports" / "assumption_satisfiability.tsv")
    usage = _read_tsv(root / "formal" / "reports" / "assumption_usage.tsv")
    satisfiability_passed = satisfiability is not None and _exact_pass_rows(satisfiability, "result_id", result_ids, ["satisfiable", "anti_vacuity"])
    usage_passed = usage is not None and _exact_pass_rows(usage, "result_id", result_ids, ["used"])
    checks.extend([
        GateCheck("assumption_satisfiability_and_antivacuity_gate", satisfiability_passed, len(satisfiability or []), EXPECTED_RESULT_COUNT),
        GateCheck("assumption_usage_gate", usage_passed, len(usage or []), EXPECTED_RESULT_COUNT),
    ])

    result_agreement = _read_tsv(root / "verification" / "reports" / "cross_engine_results.tsv")
    proof_goal_agreement = _read_tsv(root / "verification" / "reports" / "cross_engine_proof_goals.tsv")
    disagreements = _read_tsv(root / "verification" / "reports" / "cross_engine_disagreements.tsv")
    cross_proofs = _read_json(root / "verification" / "reports" / "cross_engine_proofs.json")
    result_agreement_passed = result_agreement is not None and _exact_pass_rows(result_agreement, "result_id", result_ids, ["agreement"])
    proof_goal_agreement_passed = proof_goal_agreement is not None and _exact_pass_rows(proof_goal_agreement, "proof_goal_id", proof_goal_ids, ["agreement"])
    cross_passed = result_agreement_passed and proof_goal_agreement_passed and disagreements == [] and cross_proofs is not None and cross_proofs.get("status") == "PASS"
    checks.append(GateCheck("cross_engine_68_results_218_proof_goals_gate", cross_passed, {"results": len(result_agreement or []), "proof_goals": len(proof_goal_agreement or []), "disagreements": len(disagreements or []), "proof_status": None if cross_proofs is None else cross_proofs.get("status")}, {"results": EXPECTED_RESULT_COUNT, "proof_goals": EXPECTED_PROOF_GOAL_COUNT, "disagreements": 0, "proof_status": "PASS"}))

    generation = _read_json(root / "formal" / "reports" / "proof_generation.json")
    wolfram = generation.get("wolfram") if generation is not None else None
    wolfram_passed = generation is not None and generation.get("status") == "PASS" and isinstance(wolfram, dict) and wolfram.get("status") == "PASS"
    checks.append(GateCheck("real_wolfram_machine_closed_run", wolfram_passed, wolfram, {"status": "PASS"}))
    failures = [check["check"] for check in checks if check["status"] != "PASS"]
    return {"status": "PASS" if not failures else "FAIL", "result_count": len(result_ids), "proof_goal_count": len(proof_goal_ids), "failure_count": len(failures), "failures": failures, "checks": checks}


def CleanMachineClosureReports(root: Path = ROOT) -> dict[str, Any]:
    removed: list[str] = []
    for relative in [
        Path("formal/reports"),
        Path("formal/traces/wolfram"),
        Path("verification/reports"),
    ]:
        directory = root / relative
        if not directory.is_dir():
            continue
        for path in sorted(directory.iterdir()):
            if path.is_dir():
                shutil.rmtree(path)
            else:
                path.unlink()
            removed.append(path.relative_to(root).as_posix())
    return {"status": "PASS", "removed_count": len(removed), "removed": removed}


__all__ = ["CleanMachineClosureReports", "EXPECTED_PROOF_GOAL_COUNT", "EXPECTED_RESULT_COUNT", "FormalReplayChecks", "GateCheck", "PROOF_GOAL_CLOSURE_METHODS", "ValidateMachineClosure"]
