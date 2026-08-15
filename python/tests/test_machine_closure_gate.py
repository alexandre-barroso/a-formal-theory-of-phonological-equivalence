from __future__ import annotations

import csv
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch


ROOT = Path(__file__).resolve().parents[3]
PACKAGE = ROOT / "verification" / "python"
SCRIPTS = ROOT / "scripts"
for path in (PACKAGE, SCRIPTS):
    if str(path) not in sys.path:
        sys.path.insert(0, str(path))

from build_all import Parser as BuildParser
from check_proofs import Parser as CheckerParser
from validate_package import Parser as ValidationParser
from second_order_phonology.machine_closure import CleanMachineClosureReports, FormalReplayChecks, PROOF_GOAL_CLOSURE_METHODS, ValidateMachineClosure
from second_order_phonology import pipeline, wolfram


class MachineClosureGateTests(unittest.TestCase):
    def _write_json(self, root: Path, relative: str, value: object) -> None:
        path = root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(value, sort_keys=True) + "\n", encoding="utf-8", newline="\n")

    def _write_tsv(self, root: Path, relative: str, rows: list[dict[str, str]], fields: list[str]) -> None:
        path = root / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        with path.open("w", encoding="utf-8", newline="") as handle:
            writer = csv.DictWriter(handle, fields, delimiter="\t", lineterminator="\n")
            writer.writeheader()
            writer.writerows(rows)

    def _fixture(self, root: Path) -> tuple[list[str], list[str]]:
        result_ids = [f"T{index:03d}" for index in range(68)]
        proof_goal_ids = [f"O{index:03d}" for index in range(218)]
        self._write_tsv(root, "registry/result_registry.tsv", [{"result_id": value} for value in result_ids], ["result_id"])
        self._write_tsv(root, "registry/proof_goal_registry.tsv", [{"proof_goal_id": value, "mandatory": "true", "machine_status": "ExactConstructivePass"} for value in proof_goal_ids], ["proof_goal_id", "mandatory", "machine_status"])
        self._write_tsv(root, "registry/result_status.tsv", [{"result_id": value, "machine_status": "MachineClosed"} for value in result_ids], ["result_id", "machine_status"])
        for identifier in result_ids:
            self._write_json(root, f"formal/specs/{identifier}.json", {"result_id": identifier})
        replay = {
            "status": "PASS",
            "specification_count": 68,
            "semantic_specification_count": 68,
            "machine_closed_result_count": 68,
            "machine_closed_result_ids": result_ids,
            "proof_goal_count": 218,
            "discharged_proof_goal_count": 218,
            "proof_count": 218,
            "statement_check_count": 68,
            "accepted_statement_check_count": 68,
            "failures": [],
            "missing_proof_goal_ids": [],
            "missing_result_ids": [],
            "missing_statement_check_ids": [],
            "proof_goal_results": [{"proof_goal_id": value, "status": "PASS"} for value in proof_goal_ids],
            "statement_checks": [{"result_id": value, "status": "PASS"} for value in result_ids],
        }
        self._write_json(root, "formal/reports/proof_replay.json", replay)
        self._write_json(root, "formal/reports/mutation_report.json", {"status": "PASS", "result_count": 68, "mandatory_non_equivalent_count": 136, "killed_count": 136, "survived_mutant_ids": []})
        assumption_rows = [{"result_id": value, "status": "PASS", "satisfiable": "true", "anti_vacuity": "true"} for value in result_ids]
        usage_rows = [{"result_id": value, "status": "PASS", "used": "true"} for value in result_ids]
        self._write_tsv(root, "formal/reports/assumption_satisfiability.tsv", assumption_rows, ["result_id", "status", "satisfiable", "anti_vacuity"])
        self._write_tsv(root, "formal/reports/assumption_usage.tsv", usage_rows, ["result_id", "status", "used"])
        result_rows = [{"result_id": value, "status": "PASS", "agreement": "true"} for value in result_ids]
        proof_goal_rows = [{"proof_goal_id": value, "status": "PASS", "agreement": "true"} for value in proof_goal_ids]
        self._write_tsv(root, "verification/reports/cross_engine_results.tsv", result_rows, ["result_id", "status", "agreement"])
        self._write_tsv(root, "verification/reports/cross_engine_proof_goals.tsv", proof_goal_rows, ["proof_goal_id", "status", "agreement"])
        self._write_tsv(root, "verification/reports/cross_engine_disagreements.tsv", [], ["result_id", "proof_goal_id", "detail"])
        self._write_json(root, "verification/reports/cross_engine_proofs.json", {"status": "PASS"})
        self._write_json(root, "formal/reports/proof_generation.json", {"status": "PASS", "wolfram": {"status": "PASS"}})
        return result_ids, proof_goal_ids

    def test_public_parsers_expose_machine_closed(self) -> None:
        build = BuildParser().parse_args(["--clean", "--with-wolfram", "--machine-closed", "--strict"])
        checker = CheckerParser().parse_args(["--all", "--machine-closed", "--strict"])
        validation = ValidationParser().parse_args(["--machine-closed", "--strict"])
        self.assertTrue(build.machine_closed)
        self.assertTrue(checker.machine_closed)
        self.assertTrue(validation.machine_closed)

    def test_machine_closed_pipeline_refreshes_lean_before_proof_generation(self) -> None:
        executed: list[str] = []

        def fake_callable(name: str, function: object, stages: list[dict[str, object]]) -> dict[str, object]:
            executed.append(name)
            return {"status": "PASS", "accepted_exit": True}

        def fake_command(name: str, arguments: list[str], stages: list[dict[str, object]]) -> None:
            executed.append(name)

        def fake_external_command(name: str, arguments: list[str], stages: list[dict[str, object]], working_directory: Path) -> None:
            executed.append(name)

        with (
            patch.object(pipeline, "RunCallable", side_effect=fake_callable),
            patch.object(pipeline, "RunCommand", side_effect=fake_command),
            patch.object(pipeline, "RunExternalCommand", side_effect=fake_external_command),
            patch.object(pipeline, "BuildSummary", return_value={"status": "PASS"}),
        ):
            pipeline.BuildAll(
                clean=True,
                with_wolfram=True,
                figures_only=False,
                tables_only=False,
                strict=True,
                command="ordering-regression-test",
                machine_closed=True,
            )

        self.assertEqual(executed.count("lean_verification"), 1)
        self.assertLess(executed.index("build_foundation_proofs"), executed.index("lean_verification"))
        self.assertLess(executed.index("lean_verification"), executed.index("generate_proofs"))

    def test_python_stage_timeout_fails_closed(self) -> None:
        stages: list[dict[str, object]] = []
        error = subprocess.TimeoutExpired([sys.executable, "scripts/example.py"], pipeline.MAX_STAGE_SECONDS, output="partial output", stderr="partial error")
        with patch.object(pipeline.subprocess, "run", side_effect=error):
            with self.assertRaisesRegex(RuntimeError, "Stage exceeded"):
                pipeline.RunCommand("bounded_python_stage", ["scripts/example.py"], stages)
        self.assertEqual(stages[0]["status"], "FAIL")
        self.assertIn("partial outputpartial error", stages[0]["output"])

    def test_external_stage_timeout_fails_closed(self) -> None:
        stages: list[dict[str, object]] = []
        error = subprocess.TimeoutExpired(["sh", "scripts/verify.sh"], pipeline.MAX_STAGE_SECONDS)
        with patch.object(pipeline.subprocess, "run", side_effect=error):
            with self.assertRaisesRegex(RuntimeError, "Stage exceeded"):
                pipeline.RunExternalCommand("bounded_external_stage", ["sh", "scripts/verify.sh"], stages, ROOT)
        self.assertEqual(stages[0]["status"], "FAIL")

    def test_wolfram_timeout_is_rejected_and_recorded(self) -> None:
        written: list[dict[str, object]] = []
        error = subprocess.TimeoutExpired(["wolframscript"], wolfram.MAX_WOLFRAM_SECONDS, output="partial Wolfram output")
        with (
            patch.object(wolfram, "WolframExecutable", return_value="wolframscript"),
            patch.object(wolfram.subprocess, "run", side_effect=error),
            patch.object(wolfram, "WriteJson", side_effect=lambda path, value: written.append(value)),
        ):
            report = wolfram.RunWolfram("dissertation-release", False)
        self.assertFalse(report["accepted_exit"])
        self.assertTrue(report["timed_out"])
        self.assertEqual(report, written[0])

    def test_exact_68_and_218_closure_passes(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            result_ids, proof_goal_ids = self._fixture(root)
            report = ValidateMachineClosure(root)
            self.assertEqual(report["status"], "PASS")
            replay = json.loads((root / "formal/reports/proof_replay.json").read_text())
            self.assertTrue(all(row["status"] == "PASS" for row in FormalReplayChecks(replay, set(result_ids), set(proof_goal_ids))))

    def test_reduction_proof_status_is_an_accepted_closure_method(self) -> None:
        self.assertIn("ReductionProofPass", PROOF_GOAL_CLOSURE_METHODS)

    def test_missing_proof_goal_nonclosed_status_and_surviving_mutant_fail(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            self._fixture(root)
            replay_path = root / "formal/reports/proof_replay.json"
            replay = json.loads(replay_path.read_text())
            replay["proof_goal_results"].pop()
            self._write_json(root, "formal/reports/proof_replay.json", replay)
            status_rows = [{"result_id": f"T{index:03d}", "machine_status": "Open" if index == 0 else "MachineClosed"} for index in range(68)]
            self._write_tsv(root, "registry/result_status.tsv", status_rows, ["result_id", "machine_status"])
            mutation_path = root / "formal/reports/mutation_report.json"
            mutation = json.loads(mutation_path.read_text())
            mutation["killed_count"] = 135
            mutation["survived_mutant_ids"] = ["T000.MUTANT.01"]
            self._write_json(root, "formal/reports/mutation_report.json", mutation)
            report = ValidateMachineClosure(root)
            self.assertEqual(report["status"], "FAIL")
            self.assertIn("proof_goals_discharged_218_of_218", report["failures"])
            self.assertIn("all_result_statuses_machine_closed", report["failures"])
            self.assertIn("mandatory_mutation_gate", report["failures"])

    def test_wrong_boolean_spelling_and_disagreement_fail(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            result_ids, _ = self._fixture(root)
            rows = [{"result_id": value, "status": "PASS", "satisfiable": "True", "anti_vacuity": "true"} for value in result_ids]
            self._write_tsv(root, "formal/reports/assumption_satisfiability.tsv", rows, ["result_id", "status", "satisfiable", "anti_vacuity"])
            self._write_tsv(root, "verification/reports/cross_engine_disagreements.tsv", [{"result_id": result_ids[0], "proof_goal_id": "O000", "detail": "different result"}], ["result_id", "proof_goal_id", "detail"])
            report = ValidateMachineClosure(root)
            self.assertEqual(report["status"], "FAIL")
            self.assertIn("assumption_satisfiability_and_antivacuity_gate", report["failures"])
            self.assertIn("cross_engine_68_results_218_proof_goals_gate", report["failures"])

    def test_duplicate_status_identifier_fails_closed(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            self._fixture(root)
            rows = [{"result_id": f"T{index:03d}", "machine_status": "MachineClosed"} for index in range(68)]
            rows[-1]["result_id"] = rows[0]["result_id"]
            self._write_tsv(root, "registry/result_status.tsv", rows, ["result_id", "machine_status"])
            report = ValidateMachineClosure(root)
            self.assertEqual(report["status"], "FAIL")
            self.assertIn("machine_closure_status_registry_exact", report["failures"])

    def test_clean_report_pass_preserves_ignored_audit_output(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            self._write_json(root, "formal/reports/old.json", {"stale": True})
            self._write_json(root, "formal/traces/wolfram/old.json", {"stale": True})
            self._write_json(root, "verification/reports/old.json", {"stale": True})
            audit_name = ".audit-output"
            (root / ".gitignore").write_text(f"{audit_name}/\n", encoding="utf-8")
            self._write_json(root, f"{audit_name}/audit.json", {"preserve": True})
            result = CleanMachineClosureReports(root)
            self.assertEqual(result["removed_count"], 3)
            self.assertTrue((root / audit_name / "audit.json").is_file())
            self.assertFalse((root / "formal/reports/old.json").exists())
            self.assertFalse((root / "formal/traces/wolfram/old.json").exists())
            self.assertFalse((root / "verification/reports/old.json").exists())


if __name__ == "__main__":
    unittest.main()
