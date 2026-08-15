from __future__ import annotations

import copy
import json
import sys
import unittest
from pathlib import Path


DELIVERABLES = Path(__file__).resolve().parents[3]
KERNEL = DELIVERABLES / "formal" / "kernel" / "python"
SCRIPTS = DELIVERABLES / "scripts"
for value in [KERNEL, SCRIPTS]:
    if str(value) not in sys.path:
        sys.path.insert(0, str(value))

from build_assumption_reports import AssumptionModel
from second_order_proof_kernel.maxent_assumptions import (
    MAXENT_ASSUMPTION_MODELS,
    RESULT_IDS,
    ValidateMaxEntAssumptionModel,
)


class MaxEntAssumptionModelTests(unittest.TestCase):
    @staticmethod
    def specification(result_id: str) -> dict:
        path = DELIVERABLES / "formal" / "specs" / f"{result_id}.json"
        return json.loads(path.read_text(encoding="utf-8"))

    def test_every_registered_max_result_has_one_valid_exact_model(self) -> None:
        self.assertEqual(set(MAXENT_ASSUMPTION_MODELS), set(RESULT_IDS))
        for result_id in RESULT_IDS:
            specification = self.specification(result_id)
            model = MAXENT_ASSUMPTION_MODELS[result_id]
            self.assertTrue(
                ValidateMaxEntAssumptionModel(result_id, model, specification),
                result_id,
            )
            reported, method = AssumptionModel(specification, [])
            self.assertEqual(reported, model)
            self.assertEqual(method, "kernel-validated exact finite MAX domain witness")

    def test_missing_assignment_field_is_rejected_for_every_model(self) -> None:
        for result_id, model in MAXENT_ASSUMPTION_MODELS.items():
            mutant = copy.deepcopy(model)
            mutant["assignment"].pop(next(iter(mutant["assignment"])))
            self.assertFalse(
                ValidateMaxEntAssumptionModel(
                    result_id, mutant, self.specification(result_id)
                ),
                result_id,
            )

    def test_semantically_decisive_domain_mutations_are_rejected(self) -> None:
        mutations = copy.deepcopy(MAXENT_ASSUMPTION_MODELS)
        mutations["MAX-G1"]["assignment"]["A"]["base_masses"]["a0"] = "0"
        mutations["MAX-G2"]["assignment"]["F"]["terms"][0]["coefficient"] = "1/2"
        mutations["MAX-G3"]["assignment"]["Phi"]["variable_count"] = 1
        mutations["MAX-G4"]["assignment"]["B"]["constraint_count"] = 2
        mutations["MAX-G5"]["assignment"]["I"]["probability_measure"]["ranking_2"] = "1/3"
        mutations["MAX-G6"]["assignment"]["source_tensor"][0][0][0] = 1
        mutations["MAX-G7"]["fixed_support"] = [[0], [2]]
        mutations["MAX-G8"]["assignment"]["response"]["slices"][1]["exponent"] = "0"
        mutations["MAX-G9"]["assignment"]["A"]["points"] = []
        for result_id, mutant in mutations.items():
            self.assertFalse(
                ValidateMaxEntAssumptionModel(
                    result_id, mutant, self.specification(result_id)
                ),
                result_id,
            )

    def test_specification_premise_identity_is_bound(self) -> None:
        for result_id, model in MAXENT_ASSUMPTION_MODELS.items():
            specification = self.specification(result_id)
            specification["assumptions"][0]["id"] += ".MUTATED"
            self.assertFalse(
                ValidateMaxEntAssumptionModel(result_id, model, specification),
                result_id,
            )


if __name__ == "__main__":
    unittest.main()
