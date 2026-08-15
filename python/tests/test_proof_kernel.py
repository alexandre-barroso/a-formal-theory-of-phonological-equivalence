from __future__ import annotations

import sys
import unittest
from copy import deepcopy
from pathlib import Path
from unittest.mock import patch


ROOT = Path(__file__).resolve().parents[3]
KERNEL = ROOT / "formal" / "kernel" / "python"
if str(KERNEL) not in sys.path:
    sys.path.insert(0, str(KERNEL))

from second_order_proof_kernel.canonical import CanonicalHash, LoadJson
from second_order_proof_kernel.checker import CheckProof, CheckDataReplay, CheckPolynomialIdentity, CheckSemialgebraicUnsat, FormalStatementHash, RejectFloatingPoint, ResultDependencyClosure, ValidateMaxEntCanonicalSpecification
from second_order_proof_kernel.expressions import FreeVariables, Substitute
from second_order_proof_kernel.linear import ParseMatrix, PositiveSemidefinite
from second_order_proof_kernel.rational import ParseRational


class ProofKernelTests(unittest.TestCase):
    def _specification(self) -> dict[str, object]:
        formula = {"node": "or", "arguments": [{"node": "variable", "name": "b"}, {"node": "not", "argument": {"node": "variable", "name": "b"}}]}
        specification: dict[str, object] = {
            "schema_version": "1.0.0", "result_id": "TEST-T1", "kind": "result", "group": "CALC", "variables": [{"name": "b", "sort": "Boolean"}], "sorts": ["Boolean"], "domains": [{"id": "TEST-T1.DOMAIN", "node": "set", "values": [True, False]}], "definitions": [{"id": "TEST-T1.FORMULA", "node": "or", "arguments": formula["arguments"]}], "assumptions": [{"id": "TEST-T1.A1", "node": "boolean", "value": True}], "conclusion": formula, "quantifier_prefix": [{"quantifier": "forall", "variables": ["b"]}], "registered_query_type": "test", "scope": "kernel self-test", "nonclaims": "none", "foundation_dependencies": ["FOUND-LOGIC-001"], "result_dependencies": [], "source_transcription_dependencies": [], "expected_proof_methods": ["BooleanTautologyProof"], "english_statement_sha256": "0" * 64, "portuguese_statement_sha256": "1" * 64, "withdrawal_condition": "false checker acceptance"
        }
        specification["proof_goals"] = [{"proof_goal_id": "TEST-T1.LOGIC.01", "mandatory": True, "claim": formula, "proof_methods": ["BooleanTautologyProof"]}]
        specification["formal_statement_sha256"] = FormalStatementHash(specification)
        return specification

    def _proof(self, specification: dict[str, object]) -> dict[str, object]:
        claim = specification["proof_goals"][0]["claim"]
        return {"schema_version": "1.1.0", "proof_id": "TEST-T1.LOGIC.01.PROOF", "proof_method": "BooleanTautologyProof", "result_id": "TEST-T1", "proof_goal_id": "TEST-T1.LOGIC.01", "formal_statement_sha256": specification["formal_statement_sha256"], "claim": claim, "claim_sha256": CanonicalHash(claim), "assumptions_used": [], "foundation_dependencies": [], "result_dependencies": [], "payload": {"variables": ["b"], "formula": claim, "domain_cardinality": 2}}

    def test_hidden_float_rejected(self) -> None:
        with self.assertRaises(ValueError):
            RejectFloatingPoint({"nested": ["1/3", 0.5]})
        with self.assertRaises(ValueError):
            ParseRational("0.5")

    def test_false_polynomial_identity_rejected(self) -> None:
        payload = {
            "variables": ["x"],
            "left": {"variables": ["x"], "terms": [{"coefficient": "1", "powers": [1]}]},
            "right": {"variables": ["x"], "terms": [{"coefficient": "1", "powers": [2]}]},
        }
        with self.assertRaises(ValueError):
            CheckPolynomialIdentity(payload, {}, ROOT, {"node": "polynomial_identity", "variables": payload["variables"], "left": payload["left"], "right": payload["right"]})

    def test_positive_semidefinite_exact(self) -> None:
        self.assertTrue(PositiveSemidefinite(ParseMatrix([["1", "1"], ["1", "1"]])))
        self.assertFalse(PositiveSemidefinite(ParseMatrix([["1", "2"], ["2", "1"]])))

    def test_real_infeasibility_proof(self) -> None:
        polynomial = lambda terms: {"variables": ["x"], "terms": terms}
        payload = {
            "variables": ["x"],
            "equalities": [polynomial([{"coefficient": "1", "powers": [1]}])],
            "inequalities": [polynomial([{"coefficient": "1", "powers": [2]}, {"coefficient": "-1", "powers": [0]}])],
            "equality_multipliers": [polynomial([{"coefficient": "1", "powers": [1]}])],
            "preordering_terms": [{"gram_matrix": [["1"]], "monomials": [[0]], "inequality_indices": [0]}],
        }
        claim = {"node": "semialgebraic_unsatisfiable", "variables": payload["variables"], "equalities": payload["equalities"], "nonnegative_inequalities": payload["inequalities"]}
        detail = CheckSemialgebraicUnsat(payload, {}, ROOT, claim)
        self.assertEqual(detail, {"equality_count": 1, "inequality_count": 1, "preordering_term_count": 1})
        payload["preordering_terms"][0]["gram_matrix"] = [["-1"]]
        with self.assertRaises(ValueError):
            CheckSemialgebraicUnsat(payload, {}, ROOT, claim)

    def test_capture_avoiding_substitution(self) -> None:
        formula = {"node": "forall", "bindings": [{"variable": "y", "domain": {"node": "set", "values": [1]}}], "body": {"node": "equal", "left": {"node": "variable", "name": "x"}, "right": {"node": "variable", "name": "y"}}}
        self.assertEqual(FreeVariables(formula), {"x"})
        with self.assertRaises(ValueError):
            Substitute(formula, "x", {"node": "variable", "name": "y"})

    def test_known_true_and_false_proof_suite(self) -> None:
        specification = self._specification()
        proof = self._proof(specification)
        self.assertEqual(CheckProof(proof, specification, ROOT)["status"], "PASS")
        proof["payload"]["formula"] = {"node": "variable", "name": "b"}
        with self.assertRaises(ValueError):
            CheckProof(proof, specification, ROOT)

    def test_wrong_hash_and_unknown_rule_rejected(self) -> None:
        specification = self._specification()
        proof = self._proof(specification)
        proof["formal_statement_sha256"] = "f" * 64
        with self.assertRaises(ValueError):
            CheckProof(proof, specification, ROOT)

    def test_missing_registered_proof_goals_are_rejected(self) -> None:
        specification = self._specification()
        proof = self._proof(specification)
        del specification["proof_goals"]
        with self.assertRaises(ValueError):
            CheckProof(proof, specification, ROOT)

    def test_missing_registered_claim_is_rejected(self) -> None:
        specification = self._specification()
        proof = self._proof(specification)
        del specification["proof_goals"][0]["claim"]
        with self.assertRaises(ValueError):
            CheckProof(proof, specification, ROOT)

    def test_missing_maxent_companion_proof_goals_are_rejected(self) -> None:
        specification = LoadJson(ROOT / "formal" / "specs" / "MAX-G1.json")
        companion = LoadJson(
            ROOT
            / "formal"
            / "proofs"
            / "maxent"
            / "semantic"
            / "specs"
            / "MAX-G1.json"
        )
        del companion["proof_goals"]
        with patch(
            "second_order_proof_kernel.checker.LoadJson",
            return_value=companion,
        ):
            findings = ValidateMaxEntCanonicalSpecification(specification, ROOT)
        self.assertIn(
            "MAX semantic companion lacks registered proof goals",
            findings,
        )

    def test_result_dependency_closure_is_transitive(self) -> None:
        report = ResultDependencyClosure(
            {"A": [], "B": ["A"], "C": ["B"], "D": ["C"]},
            {"A", "B", "C"},
        )
        self.assertEqual(report["closed_result_ids"], ["A", "B", "C"])
        self.assertEqual(report["rows"][3]["closed_dependencies"], ["C"])
        self.assertFalse(report["rows"][3]["own_result_complete"])
        self.assertFalse(report["rows"][3]["dependency_closed"])

    def test_unknown_and_circular_result_dependencies_are_reported(self) -> None:
        report = ResultDependencyClosure(
            {"A": ["B"], "B": ["A"], "C": ["MISSING"]},
            {"A", "B", "C"},
        )
        self.assertEqual(report["closed_result_ids"], [])
        self.assertEqual(report["cycles"], [["A", "B"]])
        self.assertEqual(report["unknown_dependencies"], {"C": ["MISSING"]})

    def test_exact_data_replay_and_mutations(self) -> None:
        for identifier in ["DATA-PT-R1", "DATA-EN-R1", "DATA-ZH-R1"]:
            specification = LoadJson(ROOT / "formal" / "specs" / f"{identifier}.json")
            proof_goal_id = specification["proof_goals"][0]["proof_goal_id"]
            proof = LoadJson(
                ROOT / "formal" / "proofs" / f"{proof_goal_id}.mathematical.json"
            )
            self.assertEqual(CheckProof(proof, specification, ROOT)["status"], "PASS")
        proof = LoadJson(
            ROOT / "formal" / "proofs" / "DATA-PT-R1.REPLAY.01.mathematical.json"
        )
        payload = deepcopy(proof["payload"])
        payload["sources"][0]["sha256"] = "0" * 64
        with self.assertRaises(ValueError):
            CheckDataReplay(payload, {}, ROOT, {"node": "exact_data_replay", **payload})
        payload = deepcopy(proof["payload"])
        payload["sources"][0]["key_fields"] = []
        with self.assertRaises(ValueError):
            CheckDataReplay(payload, {}, ROOT, {"node": "exact_data_replay", **payload})
        proof = self._proof(specification)
        proof["proof_method"] = "TrustMeProof"
        with self.assertRaises(ValueError):
            CheckProof(proof, specification, ROOT)


if __name__ == "__main__":
    unittest.main()
