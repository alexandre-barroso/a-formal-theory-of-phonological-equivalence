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


def results_dir() -> Path:
    return repo_root() / "results"
