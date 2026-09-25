from __future__ import annotations

import json
from pathlib import Path

from . import paths

VOLATILE = {"utc", "recorded_utc", "generated_utc", "elapsed_s", "elapsed"}


def bare(obj):
    if isinstance(obj, dict):
        out = {}
        for k, v in obj.items():
            if str(k) in VOLATILE:
                continue
            out[str(k)] = bare(v)
        return out
    if isinstance(obj, (list, tuple)):
        return [bare(v) for v in obj]
    if isinstance(obj, (set, frozenset)):
        return sorted(bare(v) for v in obj)
    return obj


def write(name: str, record, directory: Path | None = None) -> Path:
    directory = directory or paths.CERTIFICATES
    directory.mkdir(parents=True, exist_ok=True)
    path = directory / name
    path.write_text(json.dumps(bare(record), ensure_ascii=False, indent=1, sort_keys=True, default=str) + "\n", encoding="utf-8")
    return path


def read(name: str, directory: Path | None = None):
    directory = directory or paths.CERTIFICATES
    return json.loads((directory / name).read_text(encoding="utf-8"))
