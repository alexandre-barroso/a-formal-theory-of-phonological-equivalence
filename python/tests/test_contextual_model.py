from __future__ import annotations

import sys
import unittest
from copy import deepcopy
from pathlib import Path


ROOT = Path(__file__).resolve().parents[3]
KERNEL = ROOT / "formal" / "kernel" / "python"
if str(KERNEL) not in sys.path:
    sys.path.insert(0, str(KERNEL))

from second_order_proof_kernel.contextual_model import ReplayContextualResult


class ContextualModelTests(unittest.TestCase):
    def test_exact_contextual_fixtures(self) -> None:
        result, _ = ReplayContextualResult(
            "ctx_c1_phase_fixture_v1", {"support": 4, "phases": ["1/4", "3/4"], "p": 2}
        )
        self.assertEqual(result, ["7/2", "9/2"])
        result, _ = ReplayContextualResult(
            "ctx_c1_center_fixture_v1", {"span": 8, "ratios": ["7/2", "9/2"], "p": 2}
        )
        self.assertEqual(result, [0, "1/9"])
        result, _ = ReplayContextualResult(
            "ctx_c2_order_fixture_v1",
            {"rho": "3", "p": 2, "paths": [["1", "0", "1/2"], ["1", "1", "0"]]},
        )
        self.assertEqual(result, [["7/2", 4], ["17/4", 4]])
        result, _ = ReplayContextualResult(
            "ctx_c2_shortest_fixture_v1", {"support": 2, "phase": "1/4", "p": 2}
        )
        self.assertEqual(result, [["1/6", 0], ["1/3", "1/3"]])

    def test_general_derivation_manifests_and_mutants(self) -> None:
        c1 = {
            "domain": {"p": "p>1", "q": "1/(p-1)>0", "K": "integer K>=1", "u": "0<u<=1"},
            "phase_equation": "(p*rho)^q=sum_(r=1)^K (r-1+u)^q",
            "free_flux": "p*rho*sgn(s_i)*abs(s_i)^(p-1)=(L+1-2*i)/2",
            "support_test": "C_L(q)>=2^q*(p*rho)^q",
            "critical_spans": ["2*K-1", "2*K", "2*K+1"],
            "carrier": "(K,indicator(u>1/2))",
        }
        result, detail = ReplayContextualResult("ctx_c1_general_v1", c1)
        self.assertEqual(result["regimes"]["L=2K"], "zero_iff_u<=1/2")
        self.assertEqual(detail["checked_flux_increment"], "1")
        mutant = deepcopy(c1)
        mutant["carrier"] = "K"
        with self.assertRaises(ValueError):
            ReplayContextualResult("ctx_c1_general_v1", mutant)

        c2 = {
            "domain": {"p": "p>1", "rho": "rho>0", "K": "integer K>=2"},
            "running_minimum": "y_i=min(x_0,...,x_i)",
            "one_trigger_evaluators": ["positive_part_edge", "absolute_edge"],
            "opposite_trigger_probe": "fixed right endpoint 1",
            "separator_span": "K+1",
            "imports": ["CTX-C1"],
        }
        result, detail = ReplayContextualResult("ctx_c2_general_v1", c2)
        self.assertTrue(result["all_one_trigger_winners_equal"])
        self.assertEqual(detail["dependency_used"], "CTX-C1")
        mutant = deepcopy(c2)
        mutant["separator_span"] = "K"
        with self.assertRaises(ValueError):
            ReplayContextualResult("ctx_c2_general_v1", mutant)


if __name__ == "__main__":
    unittest.main()
