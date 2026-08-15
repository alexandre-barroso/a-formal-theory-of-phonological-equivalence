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

from second_order_proof_kernel.support_selection import ReplaySupportSelection
from support_selection_spec_catalog import COMPONENTS, SupportSelectionClaims


class SupportSelectionModelTests(unittest.TestCase):
    def test_every_support_and_selection_component_replays_exactly(self) -> None:
        for result_id, rows in COMPONENTS.items():
            claims = SupportSelectionClaims(result_id)
            self.assertEqual(set(claims), {proof_goal_id for proof_goal_id, _ in rows})
            for proof_goal_id, component in rows:
                observed, detail = ReplaySupportSelection(result_id, component)
                self.assertEqual(observed, claims[proof_goal_id]["expected"])
                self.assertEqual(detail["result_id"], result_id)
                self.assertEqual(detail["component"], component)

    def test_load_bearing_mutants_are_rejected_or_disagree(self) -> None:
        e1 = SupportSelectionClaims("SUP-E1")["SUP-E1.GENERAL.03"]
        mutant = copy.deepcopy(e1)
        mutant["expected"]["zero_endpoint_slope"] = "a terminal zero is permitted"
        observed, _ = ReplaySupportSelection("SUP-E1", "endpoint_support_classification")
        self.assertNotEqual(observed, mutant["expected"])

        f1 = SupportSelectionClaims("SEL-F1")["SEL-F1.MEASURE.04"]
        mutant = copy.deepcopy(f1)
        mutant["expected"]["event_identity_iff"] = "one named margin is positive"
        observed, _ = ReplaySupportSelection("SEL-F1", "universal_radial_equivalence")
        self.assertNotEqual(observed, mutant["expected"])

        with self.assertRaises(ValueError):
            ReplaySupportSelection("SEL-F2", "pairwise_margin_only")

    def test_exact_boundaries_and_counterexample_geometry(self) -> None:
        root, root_detail = ReplaySupportSelection("SUP-E3", "quadratic_decay_root")
        self.assertEqual(root, {"minimal_polynomial": [1, -3, 1], "isolating_interval": [0, "1/2"], "unique": True})
        self.assertEqual(root_detail["endpoint_signs"], [1, "-1/4"])

        scores, _ = ReplaySupportSelection("SEL-F2", "complete_scores")
        euclidean, _ = ReplaySupportSelection("SEL-F2", "euclidean_projection")
        frobenius, _ = ReplaySupportSelection("SEL-F2", "frobenius_projection")
        self.assertEqual(scores, [[0, 20, -17, 1], [0, 3, 17, 18]])
        self.assertEqual(euclidean[:3], ["361/5", "1010/9", "1801/45"])
        self.assertEqual(frobenius, ["361/3", "618/5", "49/15"])

        common_law, _ = ReplaySupportSelection("SEL-F2", "common_radial_law")
        self.assertEqual(common_law["euclidean_intermediate_shell_radius_squared"], 80)
        self.assertEqual(common_law["euclidean_far_shell_radius_squared"], 233)
        self.assertEqual(common_law["frobenius_intermediate_shell_radius_squared"], 122)
        self.assertEqual(common_law["frobenius_far_shell_radius_squared"], 153)
        self.assertTrue(common_law["both_named_errors_positive"])
        self.assertTrue(common_law["one_common_two_shell_spherical_law_per_declared_metric"])

    def test_selection_assumption_manifests_name_the_exact_bridges(self) -> None:
        f1 = SupportSelectionClaims("SEL-F1")["SEL-F1.SPHERE.02"]["assumption_manifest"]["conditions"]
        self.assertIn("RadiusTwoSphereFixtureCoordinateTransport_for_exact_probability_fixture", f1)
        f2 = SupportSelectionClaims("SEL-F2")["SEL-F2.COMMONLAW.04"]["assumption_manifest"]["conditions"]
        self.assertIn("exact_intermediate_separating_shell_with_first_event_open_patch_and_second_event_empty", f2)
        self.assertIn("exact_far_shell_with_nonempty_open_patches_for_both_events", f2)
        self.assertIn("far_shell_mass_equals_a_over_two_times_a_plus_c_with_a_b_c_positive", f2)


if __name__ == "__main__":
    unittest.main()
