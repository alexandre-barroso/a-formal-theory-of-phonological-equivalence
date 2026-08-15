from __future__ import annotations

import json
import sys
import unittest
from collections import Counter
from copy import deepcopy
from pathlib import Path


DELIVERABLES = Path(__file__).resolve().parents[3]
KERNEL = DELIVERABLES / "formal" / "kernel" / "python"
SEMANTIC = DELIVERABLES / "formal" / "proofs" / "maxent" / "semantic"
if str(KERNEL) not in sys.path:
    sys.path.insert(0, str(KERNEL))

from second_order_proof_kernel.maxent_semantic import (
    BuildMaxEntSemanticCatalog,
    BuildMaxEntSemanticSpecification,
    CheckMaxEntG1G5WolframReplay,
    CheckMaxEntSemanticPayload,
    GenerateMaxEntSemanticProofs,
    RESULT_IDS,
)


class MaxEntSemanticCatalogTests(unittest.TestCase):
    def setUp(self) -> None:
        self.records = GenerateMaxEntSemanticProofs(DELIVERABLES)
        self.by_proof_goal = {row["proof_goal_id"]: row for row in self.records}

    def test_all_nine_typed_specs_and_thirty_proof_goals_validate(self) -> None:
        proof_goal_ids = []
        for result_id in RESULT_IDS:
            specification = BuildMaxEntSemanticSpecification(result_id, DELIVERABLES)
            self.assertEqual(specification["schema_version"], "2.0.0")
            self.assertEqual(specification["result_id"], result_id)
            proof_goal_ids.extend(row["proof_goal_id"] for row in specification["proof_goals"])
        self.assertEqual(len(proof_goal_ids), 30)
        self.assertEqual(len(set(proof_goal_ids)), 30)

    def test_all_twenty_two_semantic_proof_goals_and_nine_results_machine_close(self) -> None:
        counts = Counter(row["payload"]["closure_status"] for row in self.records)
        self.assertEqual(
            counts,
            {"MACHINE_CLOSED_RELATIVE_TO_FOUNDATION": 22},
        )
        self.assertEqual(
            {row["proof_goal_id"] for row in self.records if row["payload"]["replayed_universal"]},
            {
                row["proof_goal_id"]
                for row in self.records
                if row["proof_goal_id"]
                not in {
                    "MAX-G4.TIE.02",
                    "MAX-G6.ENUM.01",
                    "MAX-G6.PROVENANCE.03",
                    "MAX-G9.LAWTOENV.01",
                    "MAX-G9.ENVTOLAW.02",
                }
            },
        )
        self.assertEqual(
            {row["result_id"] for row in self.records if row["payload"]["supports_whole_result_closure"]},
            set(RESULT_IDS),
        )

    def test_all_catalog_records_replay_at_their_honest_status(self) -> None:
        for row in self.records:
            specification = BuildMaxEntSemanticSpecification(row["result_id"], DELIVERABLES)
            result = CheckMaxEntSemanticPayload(row["payload"], specification, DELIVERABLES, row["claim"])
            self.assertEqual(result["status"], "PASS")

    def test_committed_catalog_is_rebuilt_from_the_semantic_kernel(self) -> None:
        catalog = json.loads((SEMANTIC / "semantic_proof_catalog.json").read_text(encoding="utf-8"))
        self.assertEqual(catalog, BuildMaxEntSemanticCatalog(DELIVERABLES))
        self.assertEqual(catalog["records"], self.records)
        self.assertEqual(
            catalog["closure_status_counts"],
            {"MACHINE_CLOSED_RELATIVE_TO_FOUNDATION": 22},
        )
        self.assertEqual(catalog["semantic_replay_covered_result_count"], 9)
        self.assertEqual(catalog["semantic_replay_proof_goal_count"], 22)
        self.assertEqual(catalog["lean_kernel_proof_goal_count"], 8)
        self.assertEqual(catalog["total_registered_proof_goal_count"], 30)
        self.assertTrue(set(catalog["lean_kernel_proof_goal_ids"]).isdisjoint(self.by_proof_goal))

    def test_closed_proof_goal_rejects_status_mutation(self) -> None:
        row = deepcopy(self.by_proof_goal["MAX-G8.CAPACITY.02"])
        row["payload"]["closure_status"] = "INVALID"
        specification = BuildMaxEntSemanticSpecification(row["result_id"], DELIVERABLES)
        with self.assertRaises(ValueError):
            CheckMaxEntSemanticPayload(row["payload"], specification, DELIVERABLES, row["claim"])

    def test_closed_proof_goal_rejects_attached_unrelated_witness(self) -> None:
        row = deepcopy(self.by_proof_goal["MAX-G3.RESIDUAL.01"])
        row["payload"]["witness"] = "formal/proofs/maxent/MAX-G6.exact-witness.json"
        specification = BuildMaxEntSemanticSpecification(row["result_id"], DELIVERABLES)
        with self.assertRaises(ValueError):
            CheckMaxEntSemanticPayload(row["payload"], specification, DELIVERABLES, row["claim"])

    def test_closed_proof_goal_rejects_stale_inner_proof_hash(self) -> None:
        row = deepcopy(self.by_proof_goal["MAX-G6.ENUM.01"])
        row["payload"]["closure_proof"]["payload"]["proof_sha256"] = "0" * 64
        specification = BuildMaxEntSemanticSpecification(row["result_id"], DELIVERABLES)
        with self.assertRaises(ValueError):
            CheckMaxEntSemanticPayload(row["payload"], specification, DELIVERABLES, row["claim"])

    def test_closed_proof_goal_rejects_unrelated_checker(self) -> None:
        row = deepcopy(self.by_proof_goal["MAX-G9.LAWTOENV.01"])
        row["payload"]["checker_module"] = (
            "formal/kernel/python/second_order_proof_kernel/maxent_semantic_g1_g5.py"
        )
        specification = BuildMaxEntSemanticSpecification(row["result_id"], DELIVERABLES)
        with self.assertRaises(ValueError):
            CheckMaxEntSemanticPayload(row["payload"], specification, DELIVERABLES, row["claim"])

    def test_exact_proof_goal_rejects_claim_hash_mutation(self) -> None:
        row = deepcopy(self.by_proof_goal["MAX-G6.CONE.02"])
        row["payload"]["claim_sha256"] = "f" * 64
        specification = BuildMaxEntSemanticSpecification(row["result_id"], DELIVERABLES)
        with self.assertRaises(ValueError):
            CheckMaxEntSemanticPayload(row["payload"], specification, DELIVERABLES, row["claim"])

    def test_unknown_result_is_rejected(self) -> None:
        with self.assertRaises(ValueError):
            BuildMaxEntSemanticSpecification("MAX-G10", DELIVERABLES)

    def test_flagship_g1_g5_wolfram_replay_cross_checks_exact_python(self) -> None:
        result = CheckMaxEntG1G5WolframReplay(DELIVERABLES)
        self.assertEqual(result["status"], "PASS")
        self.assertEqual(result["cross_engine_anchor_count"], 5)
        self.assertEqual(len(result["wolfram_source_sha256"]), 64)


if __name__ == "__main__":
    unittest.main()
