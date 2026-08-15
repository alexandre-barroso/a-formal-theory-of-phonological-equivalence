from __future__ import annotations

import csv
import json
import sys
import unittest
from collections import defaultdict
from copy import deepcopy
from pathlib import Path


DELIVERABLES = Path(__file__).resolve().parents[3]
KERNEL = DELIVERABLES / "formal" / "kernel" / "python"
SCRIPTS = DELIVERABLES / "scripts"
for value in [KERNEL, SCRIPTS]:
    if str(value) not in sys.path:
        sys.path.insert(0, str(value))

from build_formal_specs import BuildSpecification
from continuous_hg_spec_catalog import COMPONENTS, ContinuousHGClaims
from second_order_proof_kernel.ast_validation import ValidateSpecification
from second_order_proof_kernel.checker import CheckProof
from second_order_proof_kernel.continuous_hg import ASSUMPTION_MODELS, ReplayContinuousHGResult, UNIVERSAL_MANIFESTS, ValidateContinuousHGAssumptionModel
from second_order_proof_kernel.semantic_replay import GenerateSemanticProof, PROOF_METHOD as SEMANTIC_PROOF_METHOD


LEAN_PROOF_METHOD = "LeanKernelProof"


class ContinuousHGSemanticTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        result_rows = {}
        with (DELIVERABLES / "registry" / "result_registry.tsv").open(encoding="utf-8", newline="") as handle:
            result_rows = {row["result_id"]: row for row in csv.DictReader(handle, delimiter="\t")}
        proof_goals: dict[str, list[dict[str, str]]] = defaultdict(list)
        with (DELIVERABLES / "registry" / "proof_goal_registry.tsv").open(encoding="utf-8", newline="") as handle:
            for row in csv.DictReader(handle, delimiter="\t"):
                proof_goals[row["result_id"]].append(row)
        dependencies: dict[str, list[str]] = defaultdict(list)
        with (DELIVERABLES / "registry" / "result_dependency_edges.tsv").open(encoding="utf-8", newline="") as handle:
            for row in csv.DictReader(handle, delimiter="\t"):
                dependencies[row["target_result_id"]].append(row["source_result_id"])
        cls.specifications = {
            result_id: BuildSpecification(result_rows[result_id], proof_goals[result_id], sorted(dependencies[result_id]))
            for result_id in COMPONENTS
        }

    def _canonical_proof(self, proof_goal_id: str) -> dict[str, object]:
        path = DELIVERABLES / "formal" / "proofs" / f"{proof_goal_id}.mathematical.json"
        return json.loads(path.read_text(encoding="utf-8"))

    def test_catalogue_covers_all_registered_chg_proof_goals(self) -> None:
        self.assertEqual(len(self.specifications), 16)
        self.assertEqual(sum(len(value["proof_goals"]) for value in self.specifications.values()), 66)
        for result_id, specification in self.specifications.items():
            self.assertEqual(list(ContinuousHGClaims(result_id)), [value["proof_goal_id"] for value in specification["proof_goals"]])
            self.assertEqual(ValidateSpecification(specification), [])

    def test_all_chg_proofs_use_the_canonical_semantic_and_lean_split(self) -> None:
        semantic_count = 0
        lean_count = 0
        for specification in self.specifications.values():
            for proof_goal in specification["proof_goals"]:
                if proof_goal["proof_methods"] == [SEMANTIC_PROOF_METHOD]:
                    proof = GenerateSemanticProof(specification, proof_goal)
                    semantic_count += 1
                else:
                    self.assertEqual(proof_goal["proof_methods"], [LEAN_PROOF_METHOD])
                    proof = self._canonical_proof(proof_goal["proof_goal_id"])
                    lean_count += 1
                result = CheckProof(proof, specification, DELIVERABLES)
                self.assertEqual(result["status"], "PASS")
                self.assertEqual(result["proof_method"], proof_goal["proof_methods"][0])
        self.assertEqual(semantic_count, 49)
        self.assertEqual(lean_count, 17)
        self.assertEqual(semantic_count + lean_count, 66)

    def test_assumption_witnesses_are_independently_satisfied(self) -> None:
        for result_id, model in ASSUMPTION_MODELS.items():
            self.assertTrue(ValidateContinuousHGAssumptionModel(result_id, model), result_id)
            mutant = deepcopy(model)
            mutant.pop(next(iter(mutant)))
            self.assertFalse(ValidateContinuousHGAssumptionModel(result_id, mutant), result_id)

    def test_universal_schema_mutants_are_rejected(self) -> None:
        for result_id, manifest in UNIVERSAL_MANIFESTS.items():
            mutant = deepcopy(manifest)
            mutant["domain"] = ["mutated"]
            with self.assertRaises(ValueError):
                ReplayContinuousHGResult(result_id, "universal_result", mutant)

    def test_proof_result_assumption_and_component_mutants_are_rejected(self) -> None:
        for specification in self.specifications.values():
            proof_goal = next(
                value
                for value in specification["proof_goals"]
                if value["proof_methods"] == [SEMANTIC_PROOF_METHOD]
            )
            proof = GenerateSemanticProof(specification, proof_goal)
            result_mutant = deepcopy(proof)
            result_mutant["payload"]["observed"] = {"mutated": True}
            with self.assertRaises(ValueError):
                CheckProof(result_mutant, specification, DELIVERABLES)
            assumption_mutant = deepcopy(proof)
            assumption_mutant["payload"]["assumption_manifest"] = {"node": "boolean", "value": True}
            with self.assertRaises(ValueError):
                CheckProof(assumption_mutant, specification, DELIVERABLES)
            component_mutant = deepcopy(proof)
            component_mutant["payload"]["claim"] = {"node": "boolean", "value": True}
            with self.assertRaises(ValueError):
                CheckProof(component_mutant, specification, DELIVERABLES)

    def test_strict_boundaries_and_narrowed_positivity(self) -> None:
        claims = ContinuousHGClaims("CHG-B6")
        self.assertEqual(claims["CHG-B6.CLASSIFY.01"]["expected"], ["UniqueWinner", "BoundaryTie", "NotWinner"])
        claims = ContinuousHGClaims("CHG-B16")
        positivity = claims["CHG-B16.POSITIVITY.03"]["expected"]
        self.assertEqual(positivity["finite_p_positivity_iff"], "p*rho>1")
        self.assertTrue(positivity["does_not_imply_full_phase_two"])

    def test_bilingual_chg_proofs_report_the_canonical_method_split(self) -> None:
        for locale in ["en", "pt_BR"]:
            for result_id, components in COMPONENTS.items():
                proof = (DELIVERABLES / "proofs" / locale / "results" / f"{result_id}.tex").read_text(encoding="utf-8")
                self.assertIn("\\ProofStatus{MachineClosed}", proof)
                specification = self.specifications[result_id]
                for proof_goal_id, _, _ in components:
                    self.assertIn(f"\\FormalID{{{proof_goal_id}}}", proof)
                semantic_count = sum(
                    value["proof_methods"] == [SEMANTIC_PROOF_METHOD]
                    for value in specification["proof_goals"]
                )
                lean_count = sum(
                    value["proof_methods"] == [LEAN_PROOF_METHOD]
                    for value in specification["proof_goals"]
                )
                self.assertEqual(proof.count("\\ProofStatus{SemanticDerivationProofPass}"), semantic_count)
                self.assertEqual(proof.count("\\ProofStatus{LeanKernelProofPass}"), lean_count)


if __name__ == "__main__":
    unittest.main()
