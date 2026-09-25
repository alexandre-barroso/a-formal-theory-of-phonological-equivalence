from __future__ import annotations
from phonological_requirements import certificate, paths
import json
from pathlib import Path

from .core import ABSENT, FILTERS
FILTERS.setdefault("round", lambda g, x: g.ft(x, "round") is True)
from . import frag_abc as AB
from .evaluate import activation, coefficients, score
from .strictness import zero_contribution_report

OUT = paths.CERTIFICATES


def main():
    sg = AB.make_sigma(); D = AB.DECLS
    ref = AB.build(["o", "t", "u"], scorr_pairs=((0, 2),))
    acts = activation(sg, ref, D)
    cands = []
    for v0 in ("o", "u", "a", ABSENT):
        for v2 in ("o", "u", "a", ABSENT):
            for link in (True, False):
                cands.append(((v0, v2, link),
                              AB.build([v0, "t", v2],
                                       scorr_pairs=(((0, 2),) if link else ()))))

    def run(W):
        rows = [(score(coefficients(sg, ref, c, D, acts), W, AB.LAM), k,
                 AB.observe(sg, c)) for k, c in cands]
        best = min(r[0] for r in rows)
        return {"minimum8": str(best * 8),
                "minimisers": [f"{r[2]}{'[corr]' if r[1][2] else '[nocorr]'}"
                               for r in rows if r[0] == best]}

    B = {"MAX": 20, "IDENT-IO": 4, "IDENT-IO-rd": 60}
    rec = {"candidates": len(cands),
           "reference_coefficients": {k: list(v) for k, v in
                                      coefficients(sg, ref, ref, D, acts).items()},
           "subject_strictness": zero_contribution_report(sg, D),
           "rows": {
             "corr_outranked_w16": run({**B, "CORR": 1, "IDENT-XX": 16}),
             "corr_outranked_w400": run({**B, "CORR": 1, "IDENT-XX": 400}),
             "corr_undominated_w16": run({**B, "CORR": 100, "IDENT-XX": 16}),
             "repair_assimilation": run({"MAX": 20, "IDENT-IO": 4, "IDENT-IO-rd": 60,
                                         "CORR": 100, "IDENT-XX": 16}),
             "repair_deletion": run({"MAX": 2, "IDENT-IO": 40, "IDENT-IO-rd": 60,
                                     "CORR": 100, "IDENT-XX": 16}),
             "repair_deletion_identxx_x56": run({"MAX": 2, "IDENT-IO": 40,
                                                 "IDENT-IO-rd": 60, "CORR": 100,
                                                 "IDENT-XX": 900})}}
    rec["tested_low_corr_minimisers_unchanged"] = (rec["rows"]["corr_outranked_w16"]["minimisers"]
                                   == rec["rows"]["corr_outranked_w400"]["minimisers"])
    rec["tested_deletion_minimisers_unchanged"] = (rec["rows"]["repair_deletion"]["minimisers"]
                                            == rec["rows"]["repair_deletion_identxx_x56"]["minimisers"])
    rec["scope"] = "Schematic three-segment correspondence fragment; comparisons at the displayed weights, not universal ranking or independence claims or a full reduplication analysis."
    OUT.mkdir(parents=True, exist_ok=True)
    certificate.write("agreement_by_correspondence.json", rec)
    for k, v in rec["rows"].items():
        print(f"  {k:28s} {v['minimisers']}  8P={v['minimum8']}")
    print("same minimisers at the two tested low-CORR vectors:", rec["tested_low_corr_minimisers_unchanged"])
    print("same deletion minimisers at the two tested IDENT-XX weights:", rec["tested_deletion_minimisers_unchanged"])


if __name__ == "__main__":
    main()
