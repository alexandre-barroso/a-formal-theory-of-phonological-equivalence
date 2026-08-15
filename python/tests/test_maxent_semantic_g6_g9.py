from __future__ import annotations

import copy
import json
import shutil
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[3]

from second_order_proof_kernel.maxent import (
    CheckBasicSyllableExactWitness,
    CheckOrderedContactExactWitness,
    CheckResponseEnvelopeExactWitness,
)
from second_order_proof_kernel.maxent_semantic_g6_g9 import (
    CheckMaxEntG6G9WolframReplay,
    CheckMaxEntG6G9SemanticPayload,
    GenerateMaxEntG6G9SemanticProofs,
    LEAN_PROOF_GOAL_IDS,
    SEMANTIC_PROOF_SCHEMAS,
    _check_g6_provenance,
)


class MaxEntG6G9SemanticClosureTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.proofs = GenerateMaxEntG6G9SemanticProofs(ROOT)
        cls.by_id = {row["proof_goal_id"]: row for row in cls.proofs}

    def _specification(self, result_id: str) -> dict:
        path = ROOT / "formal" / "proofs" / "maxent" / "semantic" / "specs" / f"{result_id}.json"
        return json.loads(path.read_text(encoding="utf-8"))

    def test_all_eleven_semantic_proof_goals_replay(self) -> None:
        self.assertEqual(len(self.proofs), 11)
        for proof in self.proofs:
            result = CheckMaxEntG6G9SemanticPayload(
                proof["payload"],
                self._specification(proof["result_id"]),
                ROOT,
                proof["claim"],
            )
            self.assertEqual(result["status"], "PASS")
            self.assertEqual(result["closure_status"], "MACHINE_CLOSED_RELATIVE_TO_FOUNDATION")
            self.assertEqual(result["mutant_count"], 3)

    def test_semantic_and_lean_proof_goal_sets_are_disjoint(self) -> None:
        self.assertEqual(len(SEMANTIC_PROOF_SCHEMAS), 11)
        self.assertEqual(len(LEAN_PROOF_GOAL_IDS), 4)
        self.assertTrue(set(SEMANTIC_PROOF_SCHEMAS).isdisjoint(LEAN_PROOF_GOAL_IDS))

    def test_independent_wolfram_replay_is_cross_checked(self) -> None:
        result = CheckMaxEntG6G9WolframReplay(ROOT)
        self.assertEqual(result["status"], "PASS")
        self.assertEqual(result["cross_engine_anchor_count"], 4)

    def test_claim_mutation_is_rejected(self) -> None:
        proof = self.by_id["MAX-G7.RANK.01"]
        payload = copy.deepcopy(proof["payload"])
        payload["claim_sha256"] = "0" * 64
        with self.assertRaises(ValueError):
            CheckMaxEntG6G9SemanticPayload(payload, self._specification("MAX-G7"), ROOT, proof["claim"])

    def test_schema_mutation_is_rejected(self) -> None:
        proof = self.by_id["MAX-G8.SHARP.01"]
        payload = copy.deepcopy(proof["payload"])
        payload["proof_schema"] = "assert_theorem_true"
        with self.assertRaises(ValueError):
            CheckMaxEntG6G9SemanticPayload(payload, self._specification("MAX-G8"), ROOT, proof["claim"])

    def test_foundation_mutation_is_rejected(self) -> None:
        proof = self.by_id["MAX-G9.LAWTOENV.01"]
        payload = copy.deepcopy(proof["payload"])
        payload["foundation_dependencies"] = ["FOUND-CONVEX-HULL-001"]
        with self.assertRaises(ValueError):
            CheckMaxEntG6G9SemanticPayload(payload, self._specification("MAX-G9"), ROOT, proof["claim"])

    def test_replay_result_mutation_is_rejected(self) -> None:
        proof = self.by_id["MAX-G6.ENUM.01"]
        payload = copy.deepcopy(proof["payload"])
        payload["replay_result"]["ranking_count"] = 23
        with self.assertRaises(ValueError):
            CheckMaxEntG6G9SemanticPayload(payload, self._specification("MAX-G6"), ROOT, proof["claim"])

    def test_proof_digest_mutation_is_rejected(self) -> None:
        proof = self.by_id["MAX-G8.SHARP.01"]
        payload = copy.deepcopy(proof["payload"])
        payload["proof_sha256"] = "f" * 64
        with self.assertRaises(ValueError):
            CheckMaxEntG6G9SemanticPayload(payload, self._specification("MAX-G8"), ROOT, proof["claim"])

    def test_basic_syllable_descriptive_tamper_is_rejected(self) -> None:
        path = ROOT / "formal" / "proofs" / "maxent" / "MAX-G6.exact-witness.json"
        witness = json.loads(path.read_text(encoding="utf-8"))
        witness["proof_design"] = {"tampered": True}
        with self.assertRaises(ValueError):
            CheckBasicSyllableExactWitness(witness)

    def test_basic_syllable_provenance_is_archive_self_contained(self) -> None:
        expected = _check_g6_provenance(ROOT)
        with tempfile.TemporaryDirectory() as directory:
            archive = Path(directory) / "deliverables"
            (archive / "formal" / "source_transcriptions").mkdir(parents=True)
            (archive / "formal" / "proofs" / "maxent").mkdir(parents=True)
            (archive / "bibliography").mkdir(parents=True)
            (archive / "proofs").mkdir()
            shutil.copy2(
                ROOT / "formal" / "source_transcriptions" / "basic_syllable_system.json",
                archive / "formal" / "source_transcriptions" / "basic_syllable_system.json",
            )
            shutil.copy2(
                ROOT / "formal" / "proofs" / "maxent" / "MAX-G6.exact-witness.json",
                archive / "formal" / "proofs" / "maxent" / "MAX-G6.exact-witness.json",
            )
            shutil.copy2(
                ROOT / "bibliography" / "reference_manifest.tsv",
                archive / "bibliography" / "reference_manifest.tsv",
            )
            self.assertEqual(_check_g6_provenance(archive), expected)

            manifest = archive / "bibliography" / "reference_manifest.tsv"
            text = manifest.read_text(encoding="utf-8")
            source_hash = next(iter(expected["source_artifact_sha256"].values()))
            manifest.write_text(
                text.replace(source_hash, "0" * 64, 1),
                encoding="utf-8",
                newline="\n",
            )
            with self.assertRaises(ValueError):
                _check_g6_provenance(archive)

    def test_ordered_contact_induction_tamper_is_rejected(self) -> None:
        path = ROOT / "formal" / "proofs" / "maxent" / "MAX-G8.exact-witness.json"
        witness = json.loads(path.read_text(encoding="utf-8"))
        witness["induction_schema"]["step"] = "the conclusion is assumed"
        with self.assertRaises(ValueError):
            CheckOrderedContactExactWitness(witness)

    def test_response_denominator_tamper_is_rejected(self) -> None:
        path = ROOT / "formal" / "proofs" / "maxent" / "MAX-G9.exact-witness.json"
        witness = json.loads(path.read_text(encoding="utf-8"))
        witness["same_envelope_different_law"]["positive_denominator_factors"] = ["FALSE"]
        with self.assertRaises(ValueError):
            CheckResponseEnvelopeExactWitness(witness)


if __name__ == "__main__":
    unittest.main()
