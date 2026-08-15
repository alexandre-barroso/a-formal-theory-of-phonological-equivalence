from __future__ import annotations

import json
import sys
import unittest
from copy import deepcopy
from pathlib import Path


DELIVERABLES = Path(__file__).resolve().parents[3]
KERNEL = DELIVERABLES / "formal" / "kernel" / "python"
if str(KERNEL) not in sys.path:
    sys.path.insert(0, str(KERNEL))

from second_order_proof_kernel.checker import CheckProof


class CanonicalProofPartitionTests(unittest.TestCase):
    def load_json(self, path: Path) -> dict[str, object]:
        return json.loads(path.read_text(encoding="utf-8"))

    def test_canonical_wolfram_and_lean_partition(self) -> None:
        replay = self.load_json(DELIVERABLES / "formal" / "reports" / "proof_replay.json")
        export = self.load_json(
            DELIVERABLES / "formal" / "traces" / "wolfram" / "neutral_proof_goals.json"
        )

        accepted = replay["proofs"]
        lean_proofs = [proof for proof in accepted if proof["proof_method"] == "LeanKernelProof"]
        wolfram_proofs = [proof for proof in accepted if proof["proof_method"] != "LeanKernelProof"]
        exported_wolfram = export["proofs"]
        lean_reference_checks = export["lean_kernel_reference_checks"]
        manifest = export["manifest"]

        self.assertEqual(replay["status"], "PASS")
        self.assertEqual(replay["proof_goal_count"], 218)
        self.assertEqual(len(accepted), 218)
        self.assertEqual(len(wolfram_proofs), 173)
        self.assertEqual(len(lean_proofs), 45)

        self.assertEqual(manifest["proof_goal_count"], 218)
        self.assertEqual(manifest["wolfram_proof_replay_count"], 173)
        self.assertEqual(manifest["wolfram_proof_replay_pass_count"], 173)
        self.assertEqual(manifest["wolfram_proof_replay_failure_ids"], [])
        self.assertEqual(manifest["lean_kernel_reference_check_count"], 45)
        self.assertEqual(manifest["lean_kernel_reference_check_pass_count"], 45)
        self.assertEqual(manifest["lean_kernel_reference_check_failure_ids"], [])
        self.assertEqual(len(exported_wolfram), 173)
        self.assertEqual(len(lean_reference_checks), 45)
        self.assertEqual(sum(manifest["proof_method_counts"].values()), 173)
        self.assertTrue(all(proof["wolfram_pass"] for proof in exported_wolfram))
        self.assertTrue(all(check["status"] == "PASS" for check in lean_reference_checks))

        wolfram_goal_ids = {proof["proof_goal_id"] for proof in wolfram_proofs}
        lean_goal_ids = {proof["proof_goal_id"] for proof in lean_proofs}
        self.assertTrue(wolfram_goal_ids.isdisjoint(lean_goal_ids))
        self.assertEqual(
            wolfram_goal_ids,
            {proof["proof_goal_id"] for proof in exported_wolfram},
        )
        self.assertEqual(
            lean_goal_ids,
            {check["proof_goal_id"] for check in lean_reference_checks},
        )

    def test_surviving_wolfram_and_lean_proofs_reject_mutants(self) -> None:
        wolfram_proof = self.load_json(
            DELIVERABLES / "formal" / "proofs" / "CALC-F1.ADMISSION.01.mathematical.json"
        )
        specification = self.load_json(
            DELIVERABLES / "formal" / "specs" / "CALC-F1.json"
        )
        self.assertEqual(CheckProof(wolfram_proof, specification, DELIVERABLES)["status"], "PASS")

        wolfram_mutant = deepcopy(wolfram_proof)
        wolfram_mutant["payload"]["observed"] = {"mutated": True}
        with self.assertRaises(ValueError):
            CheckProof(wolfram_mutant, specification, DELIVERABLES)

        lean_proof = self.load_json(
            DELIVERABLES / "formal" / "proofs" / "CALC-F1.METAPROOF.mathematical.json"
        )
        self.assertEqual(CheckProof(lean_proof, specification, DELIVERABLES)["status"], "PASS")

        lean_mutant = deepcopy(lean_proof)
        lean_mutant["payload"]["build_log_sha256"] = "0" * 64
        with self.assertRaises(ValueError):
            CheckProof(lean_mutant, specification, DELIVERABLES)


if __name__ == "__main__":
    unittest.main()
