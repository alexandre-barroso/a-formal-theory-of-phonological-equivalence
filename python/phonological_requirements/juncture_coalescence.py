from __future__ import annotations
from phonological_requirements import certificate, paths
import json
from fractions import Fraction
from pathlib import Path

from . import frag_tn as T
from .evaluate import activation, coefficients, loci, score
from .core import read

OUT = paths.CERTIFICATES
W = {"MAX": 40, "IDENT-cont": 6, "STRENGTHEN": 20, "NOGLOT": 60}


def table(sg, ref, cands, acts, drop_retained=False, current_markedness=False):
    rows = []
    for k, c in cands:
        cf = coefficients(sg, ref, c, T.DECLS, acts)
        if current_markedness:
            cf = {name: (sum(read(sg, ref, c, decl, n).marked
                              for n in loci(c, decl, reference=ref)), 0)
                  for name, decl in T.DECLS.items()}
        if drop_retained:
            cf = {n: ((0, v[1]) if n in ("STRENGTHEN", "NOGLOT") else v)
                  for n, v in cf.items()}
        rows.append({"key": [str(x) for x in k], "output": T.observe(sg, c),
                     "score8": str(score(cf, W, T.LAM) * 8),
                     "coefficients": {n: list(v) for n, v in cf.items()}})
    m = min(Fraction(r["score8"]) for r in rows)
    return {"rows": rows, "minimisers": sorted({r["output"] for r in rows
                                                if Fraction(r["score8"]) == m})}


def main():
    sg = T.make_sigma()
    ref, dels = T.deletion_candidates(); acts = activation(sg, ref, T.DECLS)
    ref2, coa = T.coalescence_candidates(); acts2 = activation(sg, ref2, T.DECLS)
    rec = {"weights": W,
           "deletion_with_retention": table(sg, ref, dels, acts),
           "deletion_without_retention": table(sg, ref, dels, acts, True),
           "coalescence_with_retention": table(sg, ref2, coa, acts2),
           "deletion_with_current_markedness": table(sg, ref, dels, acts, current_markedness=True),
           "union_with_retention": table(sg, ref, dels + coa, acts)}
    rec["scope"] = {
        "source": "Staroverov and Kavitskaya (2017), sections 6.1 and 6.4",
        "domain": "Four-segment V-glottal-fricative-V diagnostic; six deletion and two coalescence candidates",
        "interpretation": "Unique-key discharge illustration, not a translation of the source grammar",
        "deletion_without_retention": "Old terms removed; not ordinary current markedness",
        "omitted_source_structure": "Lexical strata, place, voice, stridency, complex root nodes and the other source candidate families"}
    rec["summary"] = {
        "deletion+retention": rec["deletion_with_retention"]["minimisers"],
        "deletion-retention": rec["deletion_without_retention"]["minimisers"],
        "coalescence+retention": rec["coalescence_with_retention"]["minimisers"],
        "deletion+current-markedness": rec["deletion_with_current_markedness"]["minimisers"],
        "union+retention": rec["union_with_retention"]["minimisers"],
        "coalescence_selects_hardening_uniquely":
            rec["coalescence_with_retention"]["minimisers"] == ["eke"],
        "retained_term_discharged_under_coalescence":
            all(r["coefficients"]["STRENGTHEN"] == [0, 0]
                for r in rec["coalescence_with_retention"]["rows"])}
    OUT.mkdir(parents=True, exist_ok=True)
    certificate.write("juncture_coalescence.json", rec)
    print(json.dumps(rec["summary"], ensure_ascii=False, indent=1))


if __name__ == "__main__":
    main()
