from __future__ import annotations

VOLATILE = {"utc", "recorded_utc", "generated_utc", "seconds", "elapsed_s", "elapsed", "time", "timestamp", "date", "host",
            "python", "platform", "tool", "what", "why", "note", "notes", "comment", "comments", "method", "argument",
            "claim", "statement", "summary", "remark", "rationale", "interpretation", "description", "explanation",
            "caveat", "warning", "docstring", "purpose", "reading", "source_note", "trust_boundary", "theory_version"}


def bare(obj):
    if isinstance(obj, dict):
        out = {}
        for k, v in obj.items():
            if str(k) in VOLATILE:
                continue
            if isinstance(v, str) and v.count(" ") >= 8:
                continue
            out[str(k)] = bare(v)
        return out
    if isinstance(obj, (list, tuple)):
        return [bare(v) for v in obj]
    if isinstance(obj, (set, frozenset)):
        return sorted(bare(v) for v in obj)
    return obj
