from __future__ import annotations

import json
from fractions import Fraction
from typing import Mapping

from phonological_opacity.fragments.gua import MARKEDNESS, SCHEMAS, all_fragments, load_spec

from .adequacy import l_locus_terms, l_readers
from .gua_decls import SCHEMA_ORDER, signature_from_spec
from .lang import Signature, read
from .variants import build_declarations
from . import lith_decls as LD


def _score8(frag, sig, decls, state, ref, weights, lam) -> Fraction:
    t = l_locus_terms(sig, frag.reference, state, decls, ref, MARKEDNESS)
    total = Fraction(0)
    for name in SCHEMA_ORDER:
        old, new = t[name]
        total += weights[name] * (Fraction(old) + lam * new)
    return total


def gua_winner_separation(spec: Mapping | None = None) -> dict:
    spec = spec or load_spec()
    dyn = build_declarations("dynamic_next_word")
    wit = build_declarations("witness")
    base = {k: Fraction(spec["weights"][k]) for k in SCHEMAS}
    lam = Fraction(spec["lambda"]["num"], spec["lambda"]["den"])
    rows = []
    for wa in (Fraction(8), Fraction(20), Fraction(21), Fraction(40), Fraction(200)):
        w = dict(base); w["A"] = wa
        per = {}
        for frag in all_fragments(spec):
            sig = signature_from_spec(spec, frag.record)
            rd = l_readers(sig, frag.reference, frag.reference, dyn)
            rw = l_readers(sig, frag.reference, frag.reference, wit)
            vd, vw = [], []
            for _i, cand in frag.all_candidates():
                vd.append(_score8(frag, sig, dyn, cand, rd, w, lam))
                vw.append(_score8(frag, sig, wit, cand, rw, w, lam))
            bd, bw = min(vd), min(vw)
            md = [i for i, v in enumerate(vd) if v == bd]
            mw = [i for i, v in enumerate(vw) if v == bw]
            obs = [frag.observe(c) for _i, c in frag.all_candidates()]
            per[frag.id] = {
                "dynamic_minima": md, "witness_minima": mw,
                "differ": md != mw,
                "dynamic_output": sorted({obs[i] for i in md}),
                "witness_output": sorted({obs[i] for i in mw}),
            }
        rows.append({"w_A": str(wa), "w_Max": str(base["MAX"]),
                     "any_winner_difference": any(v["differ"] for v in per.values()),
                     "per_input": per})
    return {"grid": rows}


def lithuanian_consonant_epenthesis() -> dict:
    ref = ("p", "∅", "b")
    inserted_vowel = ("p", "i", "b")
    inserted_obstruent = ("p", "t", "b")
    inserted_disagreeing = ("p", "d", "b")
    out = {}
    for label, policy, mode in (("witness", "witness", "stop"),
                                ("dynamic_stop", "dynamic", "stop")):
        a = LD.agree(policy, mode)
        rows = {}
        for name, st in (("reference", ref),
                         ("vowel_in_the_gap", inserted_vowel),
                         ("obstruent_in_the_gap", inserted_obstruent),
                         ("disagreeing_obstruent_in_the_gap", inserted_disagreeing)):
            r = read(LD.SIGNATURE, ref, st, a, 0)
            rows[name] = {"state": list(st), "context": r.context,
                          "defined": r.defined, "good": r.good,
                          "pressure": r.pressure, "marked": r.marked}
        out[label] = rows
    same = all(out["witness"][k] == out["dynamic_stop"][k]
               for k in out["witness"])
    diff = [k for k in out["witness"] if out["witness"][k] != out["dynamic_stop"][k]]
    return {"readers": out, "identical_on_all_three_states": same,
            "separating_states": diff}


if __name__ == "__main__":
    print(json.dumps({"gua": gua_winner_separation(),
                      "lithuanian": lithuanian_consonant_epenthesis()},
                     ensure_ascii=False, indent=1))
