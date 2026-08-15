from __future__ import annotations

import hashlib
import json
from pathlib import Path
from typing import Any


def CanonicalBytes(value: Any) -> bytes:
    return json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":"), allow_nan=False).encode("utf-8")


def CanonicalHash(value: Any) -> str:
    return hashlib.sha256(CanonicalBytes(value)).hexdigest()


def FileHash(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def LoadJson(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))
