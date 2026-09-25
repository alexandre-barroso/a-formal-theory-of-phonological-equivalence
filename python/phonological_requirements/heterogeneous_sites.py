from __future__ import annotations
from phonological_requirements import certificate, paths
import itertools, json
from fractions import Fraction as F
from pathlib import Path

from .continuous import objective_x, profile, reach, solve_quadratic

OUT = paths.CERTIFICATES


def main():
    rec = {}
    x = profile(F(5), [F(1)] * 6)
    rec["exact_recovery"] = {"input": "h=5, m=1, N=6",
                             "published": ["1", "3/5", "3/10", "1/10", "0", "0", "0"],
                             "computed": [str(v) for v in x],
                             "matches": [str(v) for v in x] ==
                                        ["1", "3/5", "3/10", "1/10", "0", "0", "0"]}
    het = []
    for m in ([F(1)] * 6, [F(1), F(2), F(1), F(3), F(1), F(1)],
              [F(0), F(2), F(0), F(1), F(4), F(0)]):
        p = profile(F(5), m)
        het.append({"m": [str(v) for v in m], "x": [str(v) for v in p],
                    "nonincreasing": all(p[i] >= p[i + 1] for i in range(len(p) - 1)),
                    "support": sum(1 for v in p if v > 0),
                    "zero_tail": all(v == 0 for v in p[sum(1 for v in p if v > 0):])})
    rec["heterogeneous_nonnegative"] = het
    ext = {}
    for lab, h, N in (("saturated", F(5), 4), ("unsaturated", F(100), 4)):
        base = profile(h, [F(1)] * N)
        rows = []
        for k in (0, 1, 2, 4):
            p = profile(h, [F(1)] * (N + k))
            rows.append({"appended": k, "x": [str(v) for v in p],
                         "prefix_preserved": [str(v) for v in p[:len(base)]] ==
                                             [str(v) for v in base]})
        ext[lab] = {"mass": str(sum(solve_quadratic(h, [F(1)] * N))), "rows": rows}
    rec["extension_stability"] = ext
    h = F(5); m = [F(1), F(1), F(-4), F(1), F(1), F(1)]
    G = [F(k, 8) for k in range(9)]
    best = bestx = None; bmv = bmx = None
    for cand in itertools.product(G, repeat=6):
        xx = [F(1)] + list(cand)
        v = objective_x(h, m, 2, xx)
        if best is None or v < best:
            best, bestx = v, xx
        if all(xx[i] >= xx[i + 1] for i in range(len(xx) - 1)):
            if bmv is None or v < bmv:
                bmv, bmx = v, xx
    rec["obstruction"] = {"m": [str(v) for v in m], "reach": [str(v) for v in reach(m)],
                          "grid_minimiser": [str(v) for v in bestx],
                          "grid_minimum": str(best),
                          "nonincreasing": all(bestx[i] >= bestx[i + 1]
                                               for i in range(len(bestx) - 1)),
                          "best_nonincreasing": [str(v) for v in bmx],
                          "best_nonincreasing_value": str(bmv),
                          "reduction_fails": best < bmv}
    OUT.mkdir(parents=True, exist_ok=True)
    certificate.write("heterogeneous_sites.json", rec)
    print("exact recovery matches:", rec["exact_recovery"]["matches"])
    print("heterogeneous nonnegative: all nonincreasing with a zero tail:",
          all(r["nonincreasing"] and r["zero_tail"] for r in het))
    print("extension stability (saturated):",
          all(r["prefix_preserved"] for r in ext["saturated"]["rows"]))
    print("extension stability (unsaturated):",
          all(r["prefix_preserved"] for r in ext["unsaturated"]["rows"]))
    print("obstruction: reduction fails with one negative site weight:",
          rec["obstruction"]["reduction_fails"])


if __name__ == "__main__":
    main()
