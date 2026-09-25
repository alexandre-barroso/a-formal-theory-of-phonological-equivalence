from __future__ import annotations

import os
from pathlib import Path


def repo_root() -> Path:
    env = os.environ.get("PHONOLOGICAL_EQUIVALENCE_ROOT")
    if env:
        return Path(env).resolve()
    for ancestor in Path(__file__).resolve().parents:
        if (ancestor / "data").is_dir() and (ancestor / "python").is_dir():
            return ancestor
    raise FileNotFoundError("repository root not found above " + __file__)


REPO = repo_root()
PYTHON = REPO / "python"
PACKAGE = PYTHON / "phonological_requirements"
VERIFICATION = PYTHON / "verification"
LEAN = REPO / "lean" / "phonological_requirements"
WOLFRAM = REPO / "wolfram" / "phonological_requirements"
RESULTS = REPO / "results" / "requirements"
CERTIFICATES = RESULTS / "certificates"
EXAMPLES = RESULTS / "examples"
WOLFRAM_OUT = RESULTS / "wolfram"
GENERATED = REPO / "build"
GENERATED_WOLFRAM = GENERATED / "wolfram"
GENERATED_LEAN = GENERATED / "lean"
