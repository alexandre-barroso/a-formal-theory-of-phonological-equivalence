from __future__ import annotations

import json
from fractions import Fraction
from typing import Mapping

from phonological_opacity.fragments.gua import MARKEDNESS, GuaFragment, all_fragments, load_spec

from .gua_decls import SCHEMA_ORDER, signature_from_spec
from .lang import Declaration, EvalContext, Signature, read
from .variants import build_declarations

MODES = ("anchor", "identity", "valued")


def trigger_key(sig: Signature, reference, state, decl: Declaration, q: int,
                mode: str):
    if mode == "anchor":
        return ()
    ctx = EvalContext(sig, reference, state, decl, q)
    ids = tuple(ctx.resolve(s.name) for s in decl.slots if s.role == "trigger")
    if mode == "identity":
        return ids
    return tuple((o, None if o is None else state[o]) for o in ids)


def locus_terms(sig: Signature, reference, state, decls: Mapping[str, Declaration],
                mode: str) -> dict[str, tuple[int, int]]:
    out: dict[str, tuple[int, int]] = {}
    n = len(sig.origins)
    for name in SCHEMA_ORDER:
        d = decls[name]
        old = new = 0
        for q in range(n):
            cur = read(sig, reference, state, d, q)
            if name in MARKEDNESS:
                ref = read(sig, reference, reference, d, q)
                same_key = (trigger_key(sig, reference, state, d, q, mode)
                            == trigger_key(sig, reference, reference, d, q, mode))
                a = bool(ref.marked) and same_key
                old += cur.pressure if a else 0
                new += cur.marked if not a else 0
            else:
                old += cur.marked
        out[name] = (old, new)
    return out


def score8(frag: GuaFragment, sig: Signature, decls, state, mode: str) -> int:
    t = locus_terms(sig, frag.reference, state, decls, mode)
    total = Fraction(0)
    for name in SCHEMA_ORDER:
        old, new = t[name]
        total += frag.weights[name] * (Fraction(old) + frag.lam * new)
    v = total * 8
    assert v.denominator == 1, v
    return int(v)


def compare(variant: str = "dynamic_next_word", spec: Mapping | None = None) -> dict:
    spec = spec or load_spec()
    decls = build_declarations(variant)
    out: dict[str, dict] = {}
    for mode in MODES:
        rows = {}
        for frag in all_fragments(spec):
            sig = signature_from_spec(spec, frag.record)
            values, obs = [], []
            for _i, cand in frag.all_candidates():
                values.append(score8(frag, sig, decls, cand, mode))
                obs.append(frag.observe(cand))
            target = frag.record["observation"]
            fiber = [i for i, y in enumerate(obs) if y == target]
            best = min(values)
            minima = [i for i, v in enumerate(values) if v == best]
            rows[frag.id] = {
                "minimum8": best, "minima": minima, "fiber": fiber,
                "exclusively_correct": bool(minima) and set(minima) <= set(fiber),
                "output_of_minima": sorted({obs[i] for i in minima}),
                "values": values,
            }
        out[mode] = {
            "all_eight_exclusively_correct":
                all(r["exclusively_correct"] for r in rows.values()),
            "per_input": rows,
        }
    base = {uid: list(r["values"]) for uid, r in out["anchor"]["per_input"].items()}
    for mode in MODES:
        diffs = {}
        for uid, r in out[mode]["per_input"].items():
            d = [i for i, (x, y) in enumerate(zip(r["values"], base[uid])) if x != y]
            diffs[uid] = {"changed": len(d), "first": d[:5]}
        out[mode]["difference_from_anchor"] = diffs
    for mode in MODES:
        for r in out[mode]["per_input"].values():
            r.pop("values", None)
    return out


if __name__ == "__main__":
    print(json.dumps(compare(), ensure_ascii=False, indent=1))
