from __future__ import annotations

import json
from collections import Counter
from fractions import Fraction
from typing import Iterable, Mapping

from phonological_opacity.fragments.gua import SCHEMAS, GuaFragment, all_fragments, load_spec

from .gua_decls import SCHEMA_ORDER, declarations, signature_from_spec
from .lang import Declaration, Readers, Signature, read


def build(fragment: GuaFragment, spec: Mapping) -> Signature:
    return signature_from_spec(spec, fragment.record)


def l_readers(sig: Signature, reference, state,
              decls: Mapping[str, Declaration]) -> dict[str, list[tuple[bool, bool, bool]]]:
    out: dict[str, list[tuple[bool, bool, bool]]] = {}
    n = len(sig.origins)
    for name in SCHEMA_ORDER:
        d = decls[name]
        out[name] = [read(sig, reference, state, d, q).triple() for q in range(n)]
    return out


def l_locus_terms(sig: Signature, reference, state,
                  decls: Mapping[str, Declaration],
                  ref_readers: Mapping[str, list[tuple[bool, bool, bool]]],
                  markedness: Iterable[str]) -> dict[str, tuple[int, int]]:
    cur = l_readers(sig, reference, state, decls)
    mk = set(markedness)
    out: dict[str, tuple[int, int]] = {}
    for name in SCHEMA_ORDER:
        old = new = 0
        for q in range(len(sig.origins)):
            c, d, g = cur[name][q]
            p = int(d and not g)
            m = int(c and d and not g)
            if name in mk:
                rc, rd, rg = ref_readers[name][q]
                a = int(rc and rd and not rg)
                old += p if a else 0
                new += m if not a else 0
            else:
                old += m
        out[name] = (old, new)
    return out


def l_score8(fragment: GuaFragment, sig: Signature,
             decls: Mapping[str, Declaration], state,
             ref_readers) -> int:
    from phonological_opacity.fragments.gua import MARKEDNESS
    terms = l_locus_terms(sig, fragment.reference, state, decls, ref_readers, MARKEDNESS)
    total = Fraction(0)
    for name in SCHEMA_ORDER:
        old, new = terms[name]
        total += fragment.weights[name] * (Fraction(old) + fragment.lam * new)
    v = total * 8
    assert v.denominator == 1, v
    return int(v)


def compare_fragment(fragment: GuaFragment, spec: Mapping,
                     decls: Mapping[str, Declaration]) -> dict:
    sig = build(fragment, spec)
    ref_l = l_readers(sig, fragment.reference, fragment.reference, decls)
    ref_base = fragment.readers(fragment.reference)
    triple_diff: Counter = Counter()
    pressure_diff: Counter = Counter()
    score_diff = 0
    examples: dict[str, dict] = {}
    for i, cand in fragment.all_candidates():
        base = fragment.readers(cand)
        mine = l_readers(sig, fragment.reference, cand, decls)
        for name in SCHEMA_ORDER:
            for q in range(fragment.n):
                b0, m0 = base[name][q], mine[name][q]
                b = (b0[0], b0[1], b0[2] if b0[1] else None)
                m = (m0[0], m0[1], m0[2] if m0[1] else None)
                if b != m:
                    triple_diff[name] += 1
                    examples.setdefault(f"triple:{name}", {
                        "input": fragment.id, "candidate": i, "origin": q,
                        "appendix": list(b), "L": list(m),
                        "state": list(cand)})
                pb = (int(b0[1] and not b0[2]), int(b0[0] and b0[1] and not b0[2]))
                pm = (int(m0[1] and not m0[2]), int(m0[0] and m0[1] and not m0[2]))
                if pb != pm:
                    pressure_diff[name] += 1
                    examples.setdefault(f"pressure:{name}", {
                        "input": fragment.id, "candidate": i, "origin": q,
                        "appendix": list(pb), "L": list(pm),
                        "state": list(cand)})
        s_base = fragment.score8(cand)
        s_mine = l_score8(fragment, sig, decls, cand, ref_base)
        if s_base != s_mine:
            score_diff += 1
            examples.setdefault("score", {
                "input": fragment.id, "candidate": i,
                "appendix": s_base, "L": s_mine, "state": list(cand)})
    return {
        "input": fragment.id,
        "candidates": fragment.size,
        "origins": fragment.n,
        "triple_disagreements": dict(triple_diff),
        "pressure_disagreements": dict(pressure_diff),
        "score_disagreements": score_diff,
        "first_examples": examples,
    }


def run(a_variant: str = "baseline", **kw) -> dict:
    spec = load_spec()
    decls = declarations(a_variant=a_variant, **kw)
    frags = all_fragments(spec)
    reports = [compare_fragment(f, spec, decls) for f in frags]
    total = sum(r["candidates"] for r in reports)
    well = {name: {"well_typed": d.well_typed()[0], "faults": list(d.well_typed()[1]),
                   "relational_subject": d.relational(),
                   "consequence_depth": d.consequence.depth(),
                   "consequence_slots": sorted(d.consequence.slots()),
                   "subject_slots": list(d.subject_slots())}
            for name, d in decls.items()}
    return {
        "variant": a_variant,
        "options": {k: (v.label if hasattr(v, "label") else v) for k, v in kw.items()},
        "total_candidates": total,
        "per_input": reports,
        "well_typedness": well,
        "triple_total": sum(sum(r["triple_disagreements"].values()) for r in reports),
        "pressure_total": sum(sum(r["pressure_disagreements"].values()) for r in reports),
        "score_total": sum(r["score_disagreements"] for r in reports),
    }


if __name__ == "__main__":
    print(json.dumps(run("baseline"), ensure_ascii=False, indent=1)[:12000])
