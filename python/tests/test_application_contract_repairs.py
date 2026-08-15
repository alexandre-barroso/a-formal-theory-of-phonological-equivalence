from __future__ import annotations

import sys
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[3]
KERNEL = ROOT / "formal" / "kernel" / "python"
SCRIPTS = ROOT / "scripts"
for path in (KERNEL, SCRIPTS):
    if str(path) not in sys.path:
        sys.path.insert(0, str(path))

from application_spec_catalog import ApplicationProofGoals
from second_order_proof_kernel.application_model import ReplayApplication


class ApplicationContractRepairTests(unittest.TestCase):
    def test_all_horizon_contract_and_registered_counts_share_one_proof_goal(self) -> None:
        source = {
            "path": "formal/source_transcriptions/mccollum2019_directional_hg.json",
            "sha256": "test",
            "transcription_id": "SOURCE-MCCOLLUM-2019-DIRECTIONAL-HG",
        }
        claim = ApplicationProofGoals(
            "APP-MCC-COMP", {"mccollum": source, "basic": source}
        )["APP-MCC-COMP.COUNTS.01"]
        observed, detail = ReplayApplication(claim["algorithm"], claim["inputs"], {})
        self.assertEqual(observed, claim["expected"])
        self.assertEqual(observed["all_horizon_phase_carrier"]["phase_carrier_cardinality"], "K+1")
        self.assertTrue(
            observed["all_horizon_phase_carrier"][
                "decode_encode_exact_for_every_natural_horizon"
            ]
        )
        self.assertEqual(observed["registered_label_counts"], [16, 11, 46])
        self.assertEqual(detail["support_indices"], [5, 4, 9])


if __name__ == "__main__":
    unittest.main()
