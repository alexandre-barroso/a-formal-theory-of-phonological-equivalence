from __future__ import annotations
from phonological_grounding.results import bare

import json
from fractions import Fraction
from pathlib import Path
from typing import Sequence

from phonological_opacity.fragments.gua import SCHEMAS, GuaFragment

from .design_boundary import POOL, build, phrase1_projection
from .guaext import fragment
from .ruleserial import RuleSerial

Weights = dict[str, Fraction]


def weighted_score8(frag: GuaFragment, segments, w: Weights, lam: Fraction) -> Fraction:
    terms = frag.locus_terms(segments)
    total = Fraction(0)
    for s in SCHEMAS:
        old, new = terms[s]
        total += w[s] * (Fraction(old) + lam * Fraction(new))
    return total


def retarget_audit(bi) -> dict:
    frag = fragment(bi.inp)
    ref = frag._ref_readers
    retained_A = [q for q in range(frag.n) if frag.marked(ref["A"][q])]
    hits = []
    for i in range(frag.size):
        segs = frag.candidate(i)
        live = [q for q in range(frag.n) if frag.ft(segs[q])["present"]]
        nxt = {a: b for a, b in zip(live, live[1:])}
        for q in retained_A:
            if not frag.ft(segs[q])["present"]:
                continue
            n = nxt.get(q)
            if n is not None and frag.origins[n].phrase != frag.origins[q].phrase:
                hits.append((i, q, n))
                break
    return {"retained_A_loci": retained_A, "retargeting_candidates": len(hits),
            "example": hits[:3]}


def winners(bi, w: Weights, lam: Fraction = Fraction(1, 8)) -> dict:
    frag = fragment(bi.inp)
    best = None
    minima: list[int] = []
    for i in range(frag.size):
        v = weighted_score8(frag, frag.candidate(i), w, lam)
        if best is None or v < best:
            best, minima = v, [i]
        elif v == best:
            minima.append(i)
    proj = sorted({phrase1_projection(frag, i, bi.phrase1_origins) for i in minima})
    return {
        "minimum": str(best),
        "n_minima": len(minima),
        "minima": minima[:6],
        "phrase1_projections": proj,
        "outputs": sorted({frag.observe(frag.candidate(i)) for i in minima}),
        "rule_serial": RuleSerial(frag).output(),
    }


def region_points() -> dict[str, Weights]:
    diss = {"MAX": 20, "IDENT_ATR": 1, "IDENT_QUAL": 1, "IDENT_NUC": 2,
            "H": 4, "A": 8, "GL": 8, "D": 24, "INITIAL_FEATURE": 1}
    big_a = dict(diss, A=1000, GL=1000, H=1000, D=2000)
    tight = {"MAX": 9, "IDENT_ATR": 2, "IDENT_QUAL": 3, "IDENT_NUC": 4,
             "H": 8, "A": 12, "GL": 12, "D": 20, "INITIAL_FEATURE": 5}
    return {k: {a: Fraction(b) for a, b in v.items()}
            for k, v in (("dissertation", diss), ("large_markedness", big_a),
                         ("tight_max", tight))}


JOINT_ITEMS = ("G34a", "G34b", "N7", "G37c", "C24ei", "OR38")


def joint_rows(items: Sequence[str] = JOINT_ITEMS) -> list:
    from .dev_regions import region_for
    from .regions import reduce_under_nonnegativity
    rj, sj, vj = region_for("RETAINED", list(items), label="RETAINED:joint")
    choice = rj.choice or {}
    rows = []
    for s in sj:
        rows.extend(s.systems[choice.get(s.item, s.representatives[0])])
    return reduce_under_nonnegativity(rows, vj)


def check_point(w: Weights, rows: Sequence) -> list[str]:
    env = {f"w_{k}": v for k, v in w.items()}
    return [r.tag for r in rows if not r.holds(env)]


DESIGNS = [
    (("anɛ", "a"), [("akʊ", "bɛ"), ("ɔtsʊ", "bɛ"), ("kubi", "tei"), ("anɛ", "bɛ")]),
    (("atʃɔ", "a"), [("akʊ", "bɛ"), ("ɔtsʊ", "bɛ"), ("kubi", "tei")]),
]


def run(out: Path | None = None, points: Sequence[str] = ("dissertation",)) -> dict:
    joint = joint_rows()
    pts = region_points()
    report: dict = {"point_admissibility": {}, "designs": []}
    for name, w in pts.items():
        report["point_admissibility"][name] = check_point(w, joint) or "IN_REGION"
    for first, seconds in DESIGNS:
        block: dict = {"first_phrase": list(first), "variants": []}
        for second in seconds:
            bi = build(tuple(first) + tuple(second))
            row = {"words": list(bi.words), "audit": retarget_audit(bi), "winners": {}}
            for name in points:
                row["winners"][name] = winners(bi, pts[name])
            block["variants"].append(row)
        projs = {tuple(v["winners"][points[0]]["phrase1_projections"]) for v in block["variants"]}
        block["phrase1_invariant"] = len(projs) == 1
        block["distinct_phrase1_projections"] = sorted(list(p) for p in projs)
        report["designs"].append(block)
    if out:
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(json.dumps(bare(report), indent=2, ensure_ascii=False))
    return report


if __name__ == "__main__":
    import sys
    out = Path(sys.argv[1]) if len(sys.argv) > 1 else None
    pts = tuple(sys.argv[2].split(",")) if len(sys.argv) > 2 else ("dissertation",)
    print(json.dumps(run(out, pts), indent=2, ensure_ascii=False)[:6000])
