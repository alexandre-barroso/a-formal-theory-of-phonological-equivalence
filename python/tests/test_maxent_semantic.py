from __future__ import annotations

import json
import sys
import unittest
from copy import deepcopy
from pathlib import Path


DELIVERABLES = Path(__file__).resolve().parents[3]
KERNEL = DELIVERABLES / "formal" / "kernel" / "python"
PROOFS = DELIVERABLES / "formal" / "proofs" / "maxent"
if str(KERNEL) not in sys.path:
    sys.path.insert(0, str(KERNEL))

from second_order_proof_kernel.maxent import (
    CheckBasicSyllableExactWitness,
    CheckExactConeAlternativeWitness,
    CheckOrderedContactExactWitness,
    CheckResponseEnvelopeExactWitness,
)


def load(name: str) -> dict[str, object]:
    with (PROOFS / name).open(encoding="utf-8") as handle:
        return json.load(handle)


class MaxEntSemanticWitnessTests(unittest.TestCase):
    def test_wolfram_exact_replay_matches_python_anchors(self) -> None:
        replay = load("wolfram_exact_replay.json")
        self.assertEqual(replay["ranking_count"], 24)
        self.assertEqual(replay["winner_maps"], [[1, 1, 1, 1], [1, 1, 3, 3], [1, 2, 1, 2], [1, 2, 3, 4]])
        self.assertEqual((replay["nonreflexive_implication_count"], replay["empty_antecedent_count"], replay["live_implication_count"]), (121, 105, 16))
        self.assertEqual(replay["primitive_coefficients"], [0, 18, -309, 2267, -9302, 23388, -36952, 35872, -19584, 4608])
        self.assertEqual(replay["law_difference_numerator"], "z^4")

    def test_basic_syllable_complete_enumeration_and_cone(self) -> None:
        detail = CheckBasicSyllableExactWitness(load("MAX-G6.exact-witness.json"))
        self.assertEqual(
            detail,
            {
                "ranking_count": 24,
                "winner_map_count": 4,
                "nonreflexive_implication_count": 121,
                "empty_antecedent_count": 105,
                "live_implication_count": 16,
                "distinct_live_polynomial_count": 12,
                "facet_slacks": ["3/8", "3/8"],
            },
        )

    def test_exact_cone_alternative_row_space_witness(self) -> None:
        detail = CheckExactConeAlternativeWitness(load("MAX-G5.exact-witness.json"))
        self.assertEqual(detail["row_count"], 2)
        self.assertEqual(detail["column_count"], 4)
        self.assertEqual(detail["transpose_product"], ["1", "1", "1", "1"])

    def test_exact_cone_alternative_wrong_dimension_is_rejected(self) -> None:
        payload = load("MAX-G5.exact-witness.json")
        payload["lambda"].append(0)
        with self.assertRaises(ValueError):
            CheckExactConeAlternativeWitness(payload)

    def test_basic_syllable_missing_ranking_is_rejected(self) -> None:
        payload = load("MAX-G6.exact-witness.json")
        payload["ranking_to_winner_map"].pop()
        with self.assertRaises(ValueError):
            CheckBasicSyllableExactWitness(payload)

    def test_basic_syllable_false_factorization_is_rejected(self) -> None:
        payload = load("MAX-G6.exact-witness.json")
        payload["live_implications"][0]["factorization"] = {"op": "atom", "id": "one"}
        with self.assertRaises(ValueError):
            CheckBasicSyllableExactWitness(payload)

    def test_basic_syllable_false_polynomial_hash_is_rejected(self) -> None:
        payload = load("MAX-G6.exact-witness.json")
        payload["live_implications"][0]["polynomial_sha256"] = "0" * 64
        with self.assertRaises(ValueError):
            CheckBasicSyllableExactWitness(payload)

    def test_basic_syllable_swapped_coordinate_atom_is_rejected(self) -> None:
        payload = load("MAX-G6.exact-witness.json")
        payload["factor_atoms"]["a"]["polynomial"] = deepcopy(payload["factor_atoms"]["b"]["polynomial"])
        with self.assertRaises(ValueError):
            CheckBasicSyllableExactWitness(payload)

    def test_basic_syllable_boundary_point_is_not_strict_interior(self) -> None:
        payload = load("MAX-G6.exact-witness.json")
        payload["strict_activity_interior_witness"] = ["1", "1", "1", "1"]
        payload["strict_facet_values"] = ["0", "0"]
        with self.assertRaises(ValueError):
            CheckBasicSyllableExactWitness(payload)

    def test_ordered_contact_exact_polynomial(self) -> None:
        detail = CheckOrderedContactExactWitness(load("MAX-G8.exact-witness.json"))
        self.assertEqual(detail["zero_budget"], 8)
        self.assertEqual(detail["slice_count"], 9)
        self.assertEqual(
            detail["primitive_coefficients"],
            ["0", "18", "-309", "2267", "-9302", "23388", "-36952", "35872", "-19584", "4608"],
        )

    def test_ordered_contact_double_count_mutation_is_rejected(self) -> None:
        payload = load("MAX-G8.exact-witness.json")
        payload["ordered_contact_example"]["reversal_roots"].append("1/2")
        with self.assertRaises(ValueError):
            CheckOrderedContactExactWitness(payload)

    def test_response_envelope_nonfactorization_witnesses(self) -> None:
        detail = CheckResponseEnvelopeExactWitness(load("MAX-G9.exact-witness.json"))
        self.assertEqual(detail["same_law_envelopes"], [[1, 1], [-1, 3]])
        self.assertEqual(detail["common_envelope"], [1, 3])
        self.assertEqual(detail["law_difference_numerator"], "z^4")

    def test_response_envelope_false_numerator_is_rejected(self) -> None:
        payload = deepcopy(load("MAX-G9.exact-witness.json"))
        payload["same_envelope_different_law"]["positive_difference_numerator"]["terms"][0]["powers"] = [3]
        with self.assertRaises(ValueError):
            CheckResponseEnvelopeExactWitness(payload)


if __name__ == "__main__":
    unittest.main()
