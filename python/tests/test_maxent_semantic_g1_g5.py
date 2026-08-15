from __future__ import annotations

import copy
import json
import sys
import unittest
from fractions import Fraction
from pathlib import Path
from unittest.mock import patch


DELIVERABLES = Path(__file__).resolve().parents[3]
KERNEL = DELIVERABLES / "formal" / "kernel" / "python"
if str(KERNEL) not in sys.path:
    sys.path.insert(0, str(KERNEL))

from second_order_proof_kernel import maxent_semantic_g1_g5 as semantic
from second_order_proof_kernel.maxent_semantic_g1_g5 import (
    BuildETRINVResidual,
    CheckMaxEntG1G5ClosureRecord,
    CheckMaxEntG1G5SemanticPayload,
    ClearLaurentPolynomial,
    CompileETRINVToMaxEnt,
    CompileIntegerPolynomial,
    CompileSelectorCNF,
    DifferenceMatrix,
    ExactConeAlternative,
    GenerateMaxEntG1G5CatalogAdapters,
    GenerateMaxEntG1G5SemanticProofs,
    GenerateMaxEntG1G5SemanticClosures,
    LEAN_PROOF_GOAL_IDS,
    LoadMaxEntG1G5Proof,
    RelativeRowMassMeasure,
    SEMANTIC_PROOF_GOAL_IDS,
)


class MaxEntG1G5SemanticClosureTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.proof = LoadMaxEntG1G5Proof(DELIVERABLES)
        cls.specifications = {
            result_id: cls._load_specification(result_id)
            for result_id in semantic.RESULT_IDS
        }

    @staticmethod
    def _load_specification(result_id: str) -> dict:
        path = (
            DELIVERABLES
            / "formal"
            / "proofs"
            / "maxent"
            / "semantic"
            / "specs"
            / f"{result_id}.json"
        )
        return json.loads(path.read_text(encoding="utf-8"))

    def _check_record(self, record: dict, claim: object = None) -> dict:
        specification = self.specifications[record["result_id"]]
        return CheckMaxEntG1G5ClosureRecord(
            record,
            specification,
            DELIVERABLES,
            claim,
        )

    def test_all_eleven_semantic_proof_goals_replay(self) -> None:
        results = GenerateMaxEntG1G5SemanticClosures(DELIVERABLES)
        self.assertEqual(
            tuple(result["proof_goal_id"] for result in results),
            SEMANTIC_PROOF_GOAL_IDS,
        )
        self.assertEqual({result["status"] for result in results}, {"PASS"})
        self.assertEqual(sum(result["mutant_count"] for result in results), 33)
        for result in results:
            self.assertEqual(
                result["closure_kind"],
                "UNIVERSAL_PROOF_SCHEMA_RELATIVE_TO_EXACT_FOUNDATIONS",
            )

    def test_catalog_adapters_carry_checked_self_contained_proofs(self) -> None:
        proofs = GenerateMaxEntG1G5SemanticProofs(DELIVERABLES)
        adapters = GenerateMaxEntG1G5CatalogAdapters(DELIVERABLES)
        self.assertEqual(len(proofs), 11)
        self.assertEqual(len(adapters), 11)
        for proof, adapter in zip(proofs, adapters, strict=True):
            self.assertEqual(
                adapter["closure_proof"],
                proof,
            )
            self.assertEqual(
                adapter["checker_module"],
                semantic.CHECKER_RELATIVE_PATH,
            )
            self.assertEqual(len(adapter["checker_module_sha256"]), 64)
            self.assertEqual(adapter["verification"]["status"], "PASS")
            self.assertTrue(adapter["supports_whole_result_closure"])
            self.assertEqual(
                adapter["replayed_universal"],
                adapter["proof_goal_id"] != "MAX-G4.TIE.02",
            )

    def test_semantic_payload_verification_and_record_tampering_is_rejected(self) -> None:
        proof = GenerateMaxEntG1G5SemanticProofs(DELIVERABLES)[6]
        specification = self.specifications[proof["result_id"]]
        result = CheckMaxEntG1G5SemanticPayload(
            proof["payload"],
            specification,
            DELIVERABLES,
            proof["claim"],
        )
        self.assertEqual(result["status"], "PASS")
        mutations = []
        verification_mutant = copy.deepcopy(proof["payload"])
        verification_mutant["verification"]["status"] = "ASSUMED"
        mutations.append(verification_mutant)
        record_mutant = copy.deepcopy(proof["payload"])
        record_mutant["closure_record"]["proof_steps"][0] = "assume_conclusion"
        mutations.append(record_mutant)
        digest_mutant = copy.deepcopy(proof["payload"])
        digest_mutant["checker_module_sha256"] = "0" * 64
        mutations.append(digest_mutant)
        for mutant in mutations:
            with self.assertRaises(ValueError):
                CheckMaxEntG1G5SemanticPayload(
                    mutant,
                    specification,
                    DELIVERABLES,
                    proof["claim"],
                )

    def test_every_record_reconstructs_its_exact_staged_claim(self) -> None:
        for record in self.proof["records"]:
            specification = self.specifications[record["result_id"]]
            proof_goal = next(
                row
                for row in specification["proof_goals"]
                if row["proof_goal_id"] == record["proof_goal_id"]
            )
            result = self._check_record(record, proof_goal["claim"])
            self.assertEqual(result["claim_sha256"], record["claim_sha256"])

    def test_all_thirty_three_declared_mutant_manifest_changes_are_rejected(self) -> None:
        rejected = 0
        for record in self.proof["records"]:
            self.assertEqual(len(record["mutant_ids"]), 3)
            for index in range(3):
                mutant = copy.deepcopy(record)
                mutant["mutant_ids"][index] += ".ALTERED"
                with self.assertRaises(ValueError):
                    self._check_record(mutant)
                rejected += 1
        self.assertEqual(rejected, 33)

    def test_claim_proof_step_and_schema_mutants_are_rejected_per_proof_goal(self) -> None:
        rejected = 0
        for record in self.proof["records"]:
            claim_hash_mutant = copy.deepcopy(record)
            claim_hash_mutant["claim_sha256"] = "0" * 64
            proof_step_mutant = copy.deepcopy(record)
            proof_step_mutant["proof_steps"][0] = "assume_the_conclusion"
            payload_mutant = copy.deepcopy(record)
            payload_mutant["schema_payload"]["tampered"] = True
            for mutant in [claim_hash_mutant, proof_step_mutant, payload_mutant]:
                with self.assertRaises(ValueError):
                    self._check_record(mutant)
                rejected += 1
        self.assertEqual(rejected, 33)

    def test_semantic_and_lean_proof_goal_sets_are_disjoint(self) -> None:
        self.assertEqual(len(SEMANTIC_PROOF_GOAL_IDS), 11)
        self.assertEqual(len(LEAN_PROOF_GOAL_IDS), 4)
        self.assertTrue(set(SEMANTIC_PROOF_GOAL_IDS).isdisjoint(LEAN_PROOF_GOAL_IDS))

    def test_dependency_and_descriptive_field_mutations_are_rejected(self) -> None:
        record = self.proof["records"][7]
        fields = [
            "proof_methods",
            "definition_dependencies",
            "foundation_dependencies",
            "result_dependencies",
            "source_transcription_dependencies",
            "proof_goal_dependencies",
        ]
        for field in fields:
            mutant = copy.deepcopy(record)
            mutant[field].append("UNREGISTERED-DEPENDENCY")
            with self.assertRaises(ValueError):
                self._check_record(mutant)
        mutations = {
            "formal_statement_sha256": "f" * 64,
            "proof_schema": "assert_theorem_true",
            "closure_scope": "UNCONDITIONAL",
        }
        for field, value in mutations.items():
            mutant = copy.deepcopy(record)
            mutant[field] = value
            with self.assertRaises(ValueError):
                self._check_record(mutant)
        extra_field = copy.deepcopy(record)
        extra_field["narrative_assurance"] = "trust me"
        with self.assertRaises(ValueError):
            self._check_record(extra_field)
        with self.assertRaises(ValueError):
            self._check_record(record, {"tampered": True})

    def test_proof_support_hash_mutation_is_rejected(self) -> None:
        mutant = copy.deepcopy(self.proof)
        mutant["checker_sha256"] = "0" * 64
        with patch.object(semantic, "LoadJson", return_value=mutant):
            with self.assertRaises(ValueError):
                LoadMaxEntG1G5Proof(DELIVERABLES)

    def test_registered_foundation_dependencies_are_exactly_resolved(self) -> None:
        results = {
            row["proof_goal_id"]: row
            for row in GenerateMaxEntG1G5SemanticClosures(DELIVERABLES)
        }
        expected = {
            "MAX-G3.CHAIN.02": "FOUND-COMPACT-POLY-MIN-001",
            "MAX-G4.MULTISET.03": "FOUND-EXPONENTIAL-INDEPENDENCE-001",
        }
        for proof_goal_id, foundation_id in expected.items():
            hashes = results[proof_goal_id]["foundation_statement_sha256"]
            self.assertIn(foundation_id, hashes)
            self.assertEqual(len(hashes[foundation_id]), 64)

    def test_laurent_clearing_is_minimal_positive_and_integral(self) -> None:
        polynomial = {
            "dimension": 2,
            "terms": [
                {"exponents": [-2, 1], "coefficient": "1/2"},
                {"exponents": [0, -1], "coefficient": "-3/4"},
            ],
        }
        result = ClearLaurentPolynomial(polynomial)
        self.assertEqual(result["shift"], [2, 1])
        self.assertEqual(result["positive_denominator_lcm"], 4)
        self.assertEqual(
            result["cleared_polynomial"]["terms"],
            [
                {"exponents": [0, 2], "coefficient": "2"},
                {"exponents": [2, 0], "coefficient": "-3"},
            ],
        )
        duplicate = copy.deepcopy(polynomial)
        duplicate["terms"].append(copy.deepcopy(duplicate["terms"][0]))
        with self.assertRaises(ValueError):
            ClearLaurentPolynomial(duplicate)

    def test_integer_compiler_preserves_coefficients_and_label_multiplicity(self) -> None:
        polynomial = {
            "dimension": 1,
            "terms": [
                {"exponents": [1], "coefficient": "-1"},
                {"exponents": [2], "coefficient": "2"},
            ],
        }
        result = CompileIntegerPolynomial(polynomial)
        self.assertEqual(result["relative_partition_difference"], polynomial)
        self.assertEqual(result["coefficient_l1_norm"], 3)
        self.assertEqual(result["compiled_candidate_count"], 5)
        self.assertEqual(result["row_multiplicity"], {"1": 1, "2": 2})
        noninteger = copy.deepcopy(polynomial)
        noninteger["terms"][0]["coefficient"] = "-1/2"
        with self.assertRaises(ValueError):
            CompileIntegerPolynomial(noninteger)

    def test_bounded_etr_inv_compiler_checks_residuals_chain_and_lift(self) -> None:
        instance = {
            "variable_count": 2,
            "equations": [{"kind": "one", "variable_index": 0}],
        }
        residual = BuildETRINVResidual(instance)
        self.assertEqual(residual["coefficient_l1_norm"], 64)
        self.assertEqual(residual["total_degree"], 2)
        result = CompileETRINVToMaxEnt(instance)
        self.assertEqual(
            result["chain_penalty_lower_bound"],
            "m*sum_i(rho_i^2)-2*r_m^2>=-4*a_m^2",
        )
        self.assertEqual(result["strict_gap_condition"], "2*a_m^2<2^-Bbar")
        self.assertTrue(result["target"]["globally_duplicate_free"])
        self.assertEqual(
            result["target"]["alternative_row_count"],
            result["strictifier_coefficient_l1_norm"],
        )
        bad_index = copy.deepcopy(instance)
        bad_index["equations"][0]["variable_index"] = 2
        with self.assertRaises(ValueError):
            BuildETRINVResidual(bad_index)

    def test_selector_compiler_checks_cnf_and_duplicate_free_one_two_rows(self) -> None:
        formula = {
            "variable_count": 2,
            "clauses": [[1, 2], [-1, -2]],
        }
        result = CompileSelectorCNF(formula)
        self.assertTrue(result["globally_duplicate_free"])
        self.assertTrue(result["multi_affine"])
        self.assertEqual(result["violation_alphabet"], [1, 2])
        self.assertLessEqual(
            result["alternative_row_count"],
            result["support_bound"],
        )
        repeated_variable = copy.deepcopy(formula)
        repeated_variable["clauses"][0] = [1, -1]
        with self.assertRaises(ValueError):
            CompileSelectorCNF(repeated_variable)

    def test_relative_row_measure_preserves_mass_and_multiplicity(self) -> None:
        ledger = {
            "constraint_count": 1,
            "candidates": ["a", "b", "c"],
            "named_candidate": "a",
            "violation_rows": {"a": [0], "b": [1], "c": [1]},
            "base_masses": {"a": "2", "b": "3", "c": "5"},
            "consequence_map": {"a": "a", "b": "b", "c": "c"},
        }
        measure = RelativeRowMassMeasure(ledger, "a")
        self.assertEqual(measure, {(0,): Fraction(1), (1,): Fraction(4)})
        missing_mass = copy.deepcopy(ledger)
        del missing_mass["base_masses"]["c"]
        with self.assertRaises(ValueError):
            RelativeRowMassMeasure(missing_mass, "a")

    def test_exact_cone_alternative_constructs_and_checks_both_branches(self) -> None:
        survivor = ExactConeAlternative([[1, -1]])
        self.assertEqual(survivor["branch"], "normalized_nonnegative_kernel")
        self.assertEqual(survivor["sum"], "1")
        row_space = ExactConeAlternative([[1, 0], [0, 1]])
        self.assertEqual(row_space["branch"], "strictly_positive_row_space")
        self.assertEqual(row_space["transpose_product"], ["1", "1"])
        with self.assertRaises(ValueError):
            ExactConeAlternative({"column_count": 2, "rows": [[1]]})

    def test_difference_matrix_is_exact_and_dimension_strict(self) -> None:
        result = DifferenceMatrix([[1, 2], [3, 1], [1, 5]])
        self.assertEqual(
            result,
            {"column_count": 2, "rows": [["2", "-1"], ["0", "3"]]},
        )
        with self.assertRaises(ValueError):
            DifferenceMatrix([[1, 2], [3]])


if __name__ == "__main__":
    unittest.main()
