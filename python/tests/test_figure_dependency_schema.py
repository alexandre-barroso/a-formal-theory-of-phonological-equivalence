from __future__ import annotations

import sys
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[3]
SCRIPTS = ROOT / "scripts"
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

import generate_figures


class FigureDependencySchemaTests(unittest.TestCase):
    def test_noncanonical_dependency_headers_are_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            path = Path(temporary) / "result_dependency_edges.tsv"
            path.write_text(
                "source_id\ttarget_id\tdependency_type\n"
                "CALC-R01\tCALC-F1\tregression_for\n",
                encoding="utf-8",
            )
            with self.assertRaisesRegex(
                ValueError,
                "source_result_id, target_result_id",
            ):
                generate_figures._read_result_dependency_edges(path)


if __name__ == "__main__":
    unittest.main()
