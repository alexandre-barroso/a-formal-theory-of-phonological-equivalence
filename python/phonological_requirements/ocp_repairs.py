from __future__ import annotations
from phonological_requirements import certificate, paths
import json
from fractions import Fraction
from pathlib import Path

from . import frag_ocp as O
from .core import ABSENT
from .evaluate import activation, coefficients, score
from .strictness import zero_contribution_report

OUT = paths.CERTIFICATES


def main():
    sg = O.make_sigma(); D = O.DECLS
    ref = O.build(("H", "H"), {0: 0, 1: 1}); acts = activation(sg, ref, D)
    cands = [O.build((t0, t1), {0: l0, 1: l1})
             for t0 in ("H", ABSENT) for t1 in ("H", ABSENT)
             for l0 in (0, 1, None) for l1 in (0, 1, None)]

    def run(W):
        rows = [(score(coefficients(sg, ref, c, D, acts), W, O.LAM), O.describe(c))
                for c in cands]
        m = min(r[0] for r in rows)
        return {"minimum8": str(m * 8),
                "minimisers": sorted({r[1] for r in rows if r[0] == m})}

    rec = {"candidates": len(cands),
           "subject_strictness": zero_contribution_report(sg, D),
           "reference_coefficients": {k: list(v) for k, v in
                                      coefficients(sg, ref, ref, D, acts).items()},
           "rows": {
             "parseT_high": run({"PARSE-T": 30, "PARSE-A": 1, "OCP": 40}),
             "parseA_high": run({"PARSE-T": 1, "PARSE-A": 30, "OCP": 40}),
             "parseT_high_ocp_x100": run({"PARSE-T": 30, "PARSE-A": 1, "OCP": 4000}),
             "parseA_high_ocp_x100": run({"PARSE-T": 1, "PARSE-A": 30, "OCP": 4000})}}
    rec["tested_ocp_weight_invariance"] = (
        rec["rows"]["parseT_high"]["minimisers"] == rec["rows"]["parseT_high_ocp_x100"]["minimisers"]
        and rec["rows"]["parseA_high"]["minimisers"] == rec["rows"]["parseA_high_ocp_x100"]["minimisers"])
    rec["scope"] = "36 containment candidates; two tested above-threshold OCP weights. Exact region is in ocp_region.json; full Myers translation is not established."
    rec["repair_depends_on_parse_weights"] = (
        rec["rows"]["parseT_high"]["minimisers"] != rec["rows"]["parseA_high"]["minimisers"])
    OUT.mkdir(parents=True, exist_ok=True)
    certificate.write("ocp_repairs.json", rec)
    for k, v in rec["rows"].items():
        print(f"  {k:24s} {v['minimisers']}  8P={v['minimum8']}")
    print("same complete minimizers at the two tested OCP weights:", rec["tested_ocp_weight_invariance"])
    print("the repair depends on the PARSE weights:", rec["repair_depends_on_parse_weights"])


if __name__ == "__main__":
    main()
