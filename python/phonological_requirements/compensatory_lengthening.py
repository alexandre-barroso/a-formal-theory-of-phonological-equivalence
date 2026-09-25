from __future__ import annotations
from phonological_requirements import certificate, paths
import json
from fractions import Fraction
from pathlib import Path

from . import frag_auto as A
from .core import (ABSENT, And, Decl, Feat, Linked, NodeId, Not, Present,
                   Resolves, Scope, Slot, Struct, TRUE)
from .evaluate import activation, coefficients, score

OUT = paths.CERTIFICATES
SEG = ["t", "i", "k"]
MOR = {1: 0, 2: 1}
A_ANCH = Slot("t", "Or", "subject", kind="anchor")
NCN = Slot("n", "Rel", "trigger", kind="step", relation="succ",
           scope=Scope(same=("word",), label="w"), direction=+1,
           policy="dynamic", filter_mode="stop")
NOCODA = Decl("NOCODA", "Or", (A_ANCH, NCN),
              And((Not(Feat("vocalic", "t", True)), Not(Resolves("n")))),
              Not(Present("t")))
MAXLINKM = Decl("MAXLINK-M", "Mora",
                (A.M, Slot("h", "Or", "subject", kind="assoc", relation="assoc",
                           where="reference")),
                TRUE, Linked("t", "h", where="current"), kind="faithfulness")
D = {"MAX": A.MAXSEG, "NOCODA": NOCODA, "MAX-mora": A.FLOAT_M, "MAXLINK-M": MAXLINKM}
W = {"MAX": 6, "NOCODA": 30, "MAX-mora": 24, "MAXLINK-M": 1}


def build(regime, realis, links):
    if regime not in ("total", "derived"):
        raise ValueError(regime)
    segn = tuple(NodeId("Or", "lex", i) for i in range(3))
    morn = (tuple(NodeId("Mora", "lex", i) for i in range(2)) if regime == "total"
            else tuple(NodeId("Mora", "lex", m) for s, m in sorted(MOR.items())
                       if realis.get(s, SEG[s]) != ABSENT))
    real = {n: realis.get(i, SEG[i]) for i, n in enumerate(segn)}
    real.update({n: "μ" for n in morn})
    dom = {n: {"word": 0} for n in segn + morn}
    assoc = frozenset((NodeId("Mora", "lex", m), NodeId("Or", "lex", s))
                      for m, s in links.items() if NodeId("Mora", "lex", m) in morn)
    corr = {n: (n,) for n in segn + morn} if regime == "derived" else None
    return Struct(order={"seg": segn, "mora": morn}, real=real, dom=dom, assoc=assoc, corr=corr)


def candidates(regime):
    for deleted in (False, True):
        hosts = (None,) if regime == "derived" and deleted else (1, 2, None)
        for host in hosts:
            links = {0: 1}
            if host is not None:
                links[1] = host
            yield deleted, host, build(regime, {2: ABSENT} if deleted else {}, links)


def surface(state):
    vowel = NodeId("Or", "lex", 1)
    long = sum(h == vowel for _, h in state.assoc) == 2
    return "".join(state.real[n] + ("ː" if n == vowel and long else "")
                   for n in state.nodes("seg") if state.real[n] != ABSENT)


def main():
    rec = {}
    for regime in ("total", "derived"):
        sg = A.make_sigma(mora_totality=regime)
        ref = build("total", {}, {0: 1, 1: 2}); acts = activation(sg, ref, D)
        rows = []
        for delk, m1, c in candidates(regime):
            valid, faults = c.well_formed(ref)
            if not valid:
                raise ValueError(faults)
            cf = coefficients(sg, ref, c, D, acts)
            wt = sum(1 for (_m, h) in c.assoc if h == NodeId("Or", "lex", 1))
            rows.append({"coda_deleted": delk, "mu1_host": m1, "moras_on_V": wt,
                         "output": surface(c), "coefficients": cf,
                         "score8": str(score(cf, W, A.LAM) * 8)})
        m = min(Fraction(r["score8"]) for r in rows)
        rec[regime] = {"rows": rows, "canonical_candidates": len(rows),
                       "construction_histories": 6,
                       "minimisers": [r for r in rows if Fraction(r["score8"]) == m],
                       "compensatory_lengthening":
                           all(r["moras_on_V"] == 2 for r in rows
                               if Fraction(r["score8"]) == m)}
    OUT.mkdir(parents=True, exist_ok=True)
    certificate.write("compensatory_lengthening.json", rec)
    for k, v in rec.items():
        print(f"  mora {k:8s} CL={v['compensatory_lengthening']}  "
              f"minimisers={[r['output'] for r in v['minimisers']]}")


if __name__ == "__main__":
    main()
