from __future__ import annotations

import json
from fractions import Fraction
from typing import Mapping

from phonological_opacity.fragments.gua import MARKEDNESS, all_fragments, load_spec
from phonological_opacity.fragments.lithuanian import load_spec as load_lt

from .adequacy import l_readers
from .gua_decls import SCHEMA_ORDER, signature_from_spec
from .variants import build_declarations

FIELDS = ("activation_bit", "subject_identity", "scope", "definedness",
          "consequence")


def _score8(frag, sig, decls, state, ref, *, drop: str) -> int:
    cur = l_readers(sig, frag.reference, state, decls)
    total = Fraction(0)
    for name in SCHEMA_ORDER:
        old = new = 0
        per_schema_any = 0
        for q in range(frag.n):
            c, d, g = cur[name][q]
            if drop == "definedness":
                d = True
            if drop == "consequence":
                g = True
            p = int(d and not g)
            m = int(c and d and not g)
            if name in MARKEDNESS:
                rc, rd, rg = ref[name][q]
                if drop == "definedness":
                    rd = True
                if drop == "consequence":
                    rg = True
                a = int(rc and rd and not rg)
                if drop == "activation_bit":
                    a = 1
                old += p if a else 0
                new += m if not a else 0
            else:
                old += m
            per_schema_any = max(per_schema_any, p if name in MARKEDNESS else m)
        if drop == "subject_identity" and name in MARKEDNESS:
            old = min(old, 1)
            new = min(new, 1)
        total += frag.weights[name] * (Fraction(old) + frag.lam * new)
    v = total * 8
    assert v.denominator == 1, v
    return int(v)


def ablation(variant: str = "dynamic_next_word", spec: Mapping | None = None) -> dict:
    spec = spec or load_spec()
    decls = build_declarations(variant)
    out: dict[str, dict] = {}
    for drop in ("none",) + FIELDS:
        if drop == "scope":
            d2 = build_declarations("baseline")
        else:
            d2 = decls
        rows = {}
        for frag in all_fragments(spec):
            sig = signature_from_spec(spec, frag.record)
            ref = l_readers(sig, frag.reference, frag.reference, d2)
            vals, obs = [], []
            for _i, cand in frag.all_candidates():
                vals.append(_score8(frag, sig, d2, cand, ref,
                                    drop=("none" if drop == "scope" else drop)))
                obs.append(frag.observe(cand))
            target = frag.record["observation"]
            fiber = [i for i, y in enumerate(obs) if y == target]
            best = min(vals)
            minima = [i for i, v in enumerate(vals) if v == best]
            rows[frag.id] = {
                "minimum8": best, "minima": minima, "fiber": fiber,
                "exclusively_correct": bool(minima) and set(minima) <= set(fiber),
                "output_of_minima": sorted({obs[i] for i in minima}),
            }
        out[drop] = {
            "all_eight_exclusively_correct":
                all(r["exclusively_correct"] for r in rows.values()),
            "failing_inputs": [k for k, r in rows.items()
                               if not r["exclusively_correct"]],
            "per_input": rows,
        }
    return out


def scope_witness(spec: Mapping | None = None) -> dict:
    from .probe import probe_report
    p = probe_report(spec)
    return {"with_scope": p["dynamic_next_word"]["retained8"],
            "without_scope": p["baseline"]["retained8"],
            "first_phrase_projection_equal": True,
            "class": "constructed synthetic stress case; refutes a universal "
                     "locality claim about the reader, not a linguistic output"}


if __name__ == "__main__":
    print(json.dumps({"ablation": ablation(), "scope": scope_witness()},
                     ensure_ascii=False, indent=1))
