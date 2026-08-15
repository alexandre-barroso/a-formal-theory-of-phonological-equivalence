from __future__ import annotations

import sys
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[3]
PACKAGE = ROOT / "verification" / "python"
if str(PACKAGE) not in sys.path:
    sys.path.insert(0, str(PACKAGE))

from second_order_phonology.latex_build import SanitizeLogText


class CompilationHygieneTests(unittest.TestCase):
    def test_author_machine_paths_are_removed(self) -> None:
        volume_marker = "/" + "Volumes" + "/"
        user_marker = "/" + "Users" + "/"
        volume_path = volume_marker + "example/research/proofs/en"
        user_path = user_marker + "example/Library/cache"
        source = volume_path + "\n" + user_path
        sanitized = SanitizeLogText(source)
        self.assertNotIn(volume_marker, sanitized)
        self.assertNotIn(user_marker, sanitized)


if __name__ == "__main__":
    unittest.main()
