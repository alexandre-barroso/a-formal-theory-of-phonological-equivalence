from __future__ import annotations

import copy
import sys
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[3]
KERNEL = ROOT / "formal" / "kernel" / "python"
SCRIPTS = ROOT / "scripts"
for path in (KERNEL, SCRIPTS):
    if str(path) not in sys.path:
        sys.path.insert(0, str(path))

from flux_spec_catalog import COMPONENTS, FluxClaims
from second_order_proof_kernel.flux import ReplayFluxResult


class FluxModelTests(unittest.TestCase):
    def test_all_registered_components_replay(self) -> None:
        for result_id, rows in COMPONENTS.items():
            claims = FluxClaims(result_id)
            self.assertEqual(set(claims), {proof_goal_id for proof_goal_id, _ in rows})
            for proof_goal_id, component in rows:
                observed, detail = ReplayFluxResult(result_id, component)
                self.assertEqual(observed, claims[proof_goal_id]["expected"])
                self.assertEqual(detail["result_id"], result_id)

    def test_exact_finite_ledger_witness(self) -> None:
        null, detail = ReplayFluxResult("FLUX-D3", "ledger_null_vector")
        self.assertEqual(null, [0, 0])
        self.assertEqual(detail["null_vector"], ["1/3", "-2/3", 1])
        lower, _ = ReplayFluxResult("FLUX-D3", "monotonicity_bound")
        self.assertEqual(lower, "9/10")
        heldout, _ = ReplayFluxResult("FLUX-D3", "heldout_score")
        self.assertEqual(heldout, "1/(280*Pi^2)")

    def test_load_bearing_mutants_disagree_or_refuse(self) -> None:
        claim = FluxClaims("FLUX-D4")["FLUX-D4.PERTURBATION.04"]
        mutant = copy.deepcopy(claim)
        mutant["expected"]["Gamma"] = "nu*max(1,p-1)"
        observed, _ = ReplayFluxResult("FLUX-D4", "support_birth_response")
        self.assertNotEqual(observed, mutant["expected"])

        claim = FluxClaims("FLUX-D1")["FLUX-D1.NECESSITY.04"]
        mutant = copy.deepcopy(claim)
        mutant["expected"]["general_solution"] = "F(y)=a*y"
        observed, _ = ReplayFluxResult("FLUX-D1", "fixed_load_equivalence")
        self.assertNotEqual(observed, mutant["expected"])

        with self.assertRaises(ValueError):
            ReplayFluxResult("FLUX-D5", "finite_audit_identifies_every_law")

    def test_support_birth_balance_matches_lambert_normal_form(self) -> None:
        normal_form, _ = ReplayFluxResult("FLUX-D4", "lambert_normal_form")
        response, _ = ReplayFluxResult("FLUX-D4", "support_birth_response")
        self.assertEqual(normal_form["identity"], "C*t^Gamma/(-log(t))=epsilon")
        self.assertEqual(response["leading_balance"], "t^Gamma/(-log(t))~epsilon/C")

    def test_complete_winner_bridge_manifests_are_branch_exact(self) -> None:
        d1 = FluxClaims("FLUX-D1")["FLUX-D1.NECESSITY.04"]["assumption_manifest"]["conditions"]
        self.assertIn("baseline_exact_path_KKT_iff_global_winner_contract", d1)
        self.assertIn("transformed_exact_path_KKT_iff_global_winner_contract", d1)
        self.assertIn("arbitrary_complete_box_path_family_for_shift_sufficiency", d1)
        self.assertIn("complete_free_two_edge_winner_probe_family_for_shift_necessity", d1)

        d2 = FluxClaims("FLUX-D2")["FLUX-D2.RIGIDITY.03"]["assumption_manifest"]["conditions"]
        self.assertIn("two_path_branch_F_zero_equals_zero", d2)
        self.assertIn("two_path_branch_irrational_load_ratio", d2)
        self.assertIn("star_branch_continuous_odd_recode", d2)
        self.assertIn("star_branch_nonzero_load", d2)


if __name__ == "__main__":
    unittest.main()
