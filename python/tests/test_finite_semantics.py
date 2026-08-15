from __future__ import annotations

import csv
import json
import sys
import unittest
from collections import defaultdict
from copy import deepcopy
from pathlib import Path


ROOT = Path(__file__).resolve().parents[3]
KERNEL = ROOT / "formal" / "kernel" / "python"
SCRIPTS = ROOT / "scripts"
for path in (KERNEL, SCRIPTS):
    if str(path) not in sys.path:
        sys.path.insert(0, str(path))

from build_formal_specs import BuildSpecification
from second_order_proof_kernel.ast_validation import ValidateSpecification
from second_order_proof_kernel.checker import CheckProof
from second_order_proof_kernel.finite_semantics import (
    FINITE_RESULT_IDS,
    LEAN_PROOF_METHOD,
    PROOF_METHOD,
    CheckFiniteSemanticProof,
    CheckFiniteSemanticPayload,
    GenerateFiniteSemanticProofs,
    MutateFiniteSpecification,
    ValidateFiniteSemanticSpecification,
)


class FiniteSemanticProofTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        def read_tsv(name: str) -> list[dict[str, str]]:
            with (ROOT / "registry" / name).open(encoding="utf-8", newline="") as handle:
                return list(csv.DictReader(handle, delimiter="\t"))

        result_rows = {row["result_id"]: row for row in read_tsv("result_registry.tsv")}
        proof_goals: dict[str, list[dict[str, str]]] = defaultdict(list)
        for row in read_tsv("proof_goal_registry.tsv"):
            proof_goals[row["result_id"]].append(row)
        dependencies: dict[str, list[str]] = defaultdict(list)
        for row in read_tsv("result_dependency_edges.tsv"):
            dependencies[row["target_result_id"]].append(row["source_result_id"])
        cls.specifications = {
            identifier: BuildSpecification(
                result_rows[identifier],
                proof_goals[identifier],
                sorted(dependencies[identifier]),
            )
            for identifier in FINITE_RESULT_IDS
        }

    def _roundtrip_proofs(self, identifier: str) -> list[dict[str, object]]:
        generated = GenerateFiniteSemanticProofs(self.specifications[identifier])
        return json.loads(json.dumps(generated, ensure_ascii=False))

    def _canonical_proof(self, proof_goal_id: str) -> dict[str, object]:
        path = ROOT / "formal" / "proofs" / f"{proof_goal_id}.mathematical.json"
        return json.loads(path.read_text(encoding="utf-8"))

    def test_all_eight_specs_use_the_canonical_semantic_and_lean_split(self) -> None:
        semantic_count = 0
        lean_count = 0
        for identifier in sorted(FINITE_RESULT_IDS):
            specification = self.specifications[identifier]
            self.assertEqual(ValidateSpecification(specification), [])
            ValidateFiniteSemanticSpecification(specification)
            for proof in self._roundtrip_proofs(identifier):
                result = CheckFiniteSemanticProof(proof, specification)
                self.assertEqual(result["status"], "PASS")
                self.assertEqual(result["proof_method"], PROOF_METHOD)
                self.assertNotEqual(proof["proof_goal_id"], f"{identifier}.METAPROOF")
                semantic_count += 1
            lean_goals = [
                proof_goal
                for proof_goal in specification["proof_goals"]
                if proof_goal["proof_methods"] == [LEAN_PROOF_METHOD]
            ]
            self.assertEqual(
                [proof_goal["proof_goal_id"] for proof_goal in lean_goals],
                [f"{identifier}.METAPROOF"],
            )
            for proof_goal in lean_goals:
                proof = self._canonical_proof(proof_goal["proof_goal_id"])
                result = CheckProof(proof, specification, ROOT)
                self.assertEqual(result["status"], "PASS")
                self.assertEqual(result["proof_method"], LEAN_PROOF_METHOD)
                lean_count += 1
        self.assertEqual(semantic_count, 37)
        self.assertEqual(lean_count, 8)
        self.assertEqual(semantic_count + lean_count, 45)

    def test_dispatch_adapter_replays_each_payload(self) -> None:
        for identifier in sorted(FINITE_RESULT_IDS):
            specification = self.specifications[identifier]
            for proof in self._roundtrip_proofs(identifier):
                detail = CheckFiniteSemanticPayload(proof["payload"], specification, ROOT, proof["claim"])
                self.assertEqual(detail["derivation_method"], proof["payload"]["derivation_method"])

    def test_finite_specs_require_registered_proof_goals_and_claims(self) -> None:
        specification = deepcopy(self.specifications["FIN-A1"])
        del specification["proof_goals"]
        with self.assertRaises(ValueError):
            ValidateFiniteSemanticSpecification(specification)

        specification = deepcopy(self.specifications["FIN-A1"])
        del specification["proof_goals"][0]["claim"]
        with self.assertRaises(ValueError):
            ValidateFiniteSemanticSpecification(specification)

    def test_every_result_specific_statement_mutant_is_rejected(self) -> None:
        rejected = 0
        for identifier in sorted(FINITE_RESULT_IDS):
            specification = self.specifications[identifier]
            semantic_proof = self._roundtrip_proofs(identifier)[0]
            for mutant_id in semantic_proof["payload"]["mutant_ids"]:
                mutant = MutateFiniteSpecification(specification, mutant_id)
                with self.assertRaises(ValueError):
                    ValidateFiniteSemanticSpecification(mutant)
                with self.assertRaises(ValueError):
                    CheckFiniteSemanticProof(semantic_proof, mutant)
                rejected += 1
        self.assertEqual(rejected, 20)

    def test_lean_metaproof_is_exclusive_and_tampering_is_rejected(self) -> None:
        specification = self.specifications["FIN-A5"]
        proof = self._canonical_proof("FIN-A5.METAPROOF")
        self.assertEqual(CheckProof(proof, specification, ROOT)["status"], "PASS")

        invalid_semantic_route = deepcopy(proof)
        invalid_semantic_route["proof_id"] = "FIN-A5.METAPROOF.FINITE-SEMANTIC.PROOF"
        invalid_semantic_route["proof_method"] = PROOF_METHOD
        invalid_semantic_route["payload"] = self._roundtrip_proofs("FIN-A5")[0]["payload"]
        with self.assertRaises(ValueError):
            CheckFiniteSemanticProof(invalid_semantic_route, specification)

        wrong_declaration = deepcopy(proof)
        wrong_declaration["payload"]["lean_declarations"] = ["invented.declaration"]
        with self.assertRaises(ValueError):
            CheckProof(wrong_declaration, specification, ROOT)

        stale_evidence = deepcopy(proof)
        stale_evidence["payload"]["build_log_sha256"] = "0" * 64
        with self.assertRaises(ValueError):
            CheckProof(stale_evidence, specification, ROOT)

    def test_fixture_and_numeric_tampering_are_rejected(self) -> None:
        specification = self.specifications["CALC-F1"]
        proof = next(
            value
            for value in self._roundtrip_proofs("CALC-F1")
            if value["proof_goal_id"] == "CALC-F1.PROGRESS.02"
        )
        wrong_result = deepcopy(proof)
        wrong_result["payload"]["regression_expected"] = ["Q-CONSERVATIVE"]
        with self.assertRaises(ValueError):
            CheckFiniteSemanticProof(wrong_result, specification)

        hidden_float = deepcopy(proof)
        hidden_float["payload"]["assumption_model"]["hidden"] = 0.5
        with self.assertRaises(ValueError):
            CheckFiniteSemanticProof(hidden_float, specification)

    def test_fin_a3_is_syntax_relative(self) -> None:
        conclusion = json.dumps(self.specifications["FIN-A3"]["conclusion"], sort_keys=True)
        self.assertIn("answer_tags_pairwise_disjoint", conclusion)
        self.assertIn("cross_tag_comparison_requires_registered_cast", conclusion)
        self.assertNotIn("no_lossless_encoding_exists", conclusion)
        self.assertNotIn("all_cross_tag_casts_are_lossy", conclusion)

    def test_fin_a6_separates_direct_lattice_and_contextual_meet_structure(self) -> None:
        conclusion = json.dumps(self.specifications["FIN-A6"]["conclusion"], sort_keys=True)
        self.assertIn("closure_fixed_points_form_lattice_with_intersection_and_closed_union", conclusion)
        self.assertIn("nonempty_intersection_is_strong_congruence", conclusion)
        self.assertIn("finite_refinement_yields_greatest_strong_congruence_below", conclusion)
        self.assertNotIn("contextual_join", conclusion)
        self.assertNotIn("strong_congruences_form_lattice", conclusion)

    def test_fin_a7_separates_carrier_decision_from_witness_lifting(self) -> None:
        specification = json.dumps(self.specifications["FIN-A7"], sort_keys=True)
        self.assertIn("reader_faithful_on_reachable_codes", specification)
        self.assertIn("semantic_and_query_squares_commute", specification)
        self.assertIn("carrier_verdict_independent_of_source_section", specification)
        self.assertIn("one_source_witness_lifts", specification)
        self.assertIn("all_current_mismatch_witnesses_lift", specification)
        self.assertIn("all_reachable_code_witnesses_lift", specification)
        self.assertIn("effective_least_preimage_section_exists", specification)


if __name__ == "__main__":
    unittest.main()
