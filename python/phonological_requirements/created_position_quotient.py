from __future__ import annotations
from phonological_requirements import certificate, paths
import itertools, json, math
from collections import Counter
from fractions import Fraction
from pathlib import Path

from .core import (ABSENT, And, Decl, Feat, Made, NodeId, Not, Or_, Present,
                   RelDecl, Resolves, Scope, Sigma, Slot, SortDecl, Struct, TRUE)
from .evaluate import activation, coefficients, score
from .generate import canonical, insertions

OUT = paths.CERTIFICATES
SEGS = {"a": {"present": True, "vocalic": True},
        "t": {"present": True, "vocalic": False},
        ABSENT: {"present": False, "vocalic": "undefined"}}


def grammar():
    sg = Sigma(sorts={"Or": SortDecl("Or", "total", tier="seg"),
                      "Rel": SortDecl("Rel", "derived", tier="seg")},
               relations={"succ": RelDecl("succ", "succession", "Or", "Or", "Rel")},
               features=SEGS, default_features={"present": True, "vocalic": False},
               domains=("word",))
    A = Slot("t", "Or", "subject", kind="anchor")
    DEP = Decl("DEP", "Or", (A,), Made("t"),
               Or_((Not(Made("t")), Not(Present("t")))), kind="faithfulness")
    MAXD = Decl("MAX", "Or", (A,), TRUE, Present("t"), kind="faithfulness",
                locus_side="reference")
    NEXT = Slot("n", "Rel", "trigger", kind="step", relation="succ",
                scope=Scope(same=("word",), label="w"), direction=+1,
                policy="dynamic", filter_mode="stop")
    HI = Decl("HIATUS", "Or", (A, NEXT),
              And((Feat("vocalic", "t", True), Resolves("n"),
                   Feat("vocalic", "n", True))), Not(Present("t")))
    return sg, {"DEP": DEP, "MAX": MAXD, "HIATUS": HI}, \
        {"DEP": 2, "MAX": 10, "HIATUS": 6}, Fraction(1, 8)


def levels(insert_alphabet, kmax=5):
    sg, D, W, LAM = grammar()
    nodes = tuple(NodeId("Or", "lex", i) for i in range(2))
    ref = Struct(order={"seg": nodes}, real={nodes[0]: "t", nodes[1]: "a"},
                 dom={n: {"word": 0} for n in nodes})
    acts = activation(sg, ref, D)
    out = {}
    for k in range(kmax + 1):
        seen, hist = set(), Counter()
        gen = (insertions(ref, insert_alphabet, k, "seg") if ABSENT not in insert_alphabet
               else _raw_insertions(ref, insert_alphabet, k))
        for base in gen:
            for combo in itertools.product(("a", "t", ABSENT), repeat=len(nodes)):
                s = base
                for p, v in zip(nodes, combo):
                    s = s.with_real(p, v)
                key = canonical(s, "seg")
                if key in seen:
                    continue
                seen.add(key)
                hist[score(coefficients(sg, ref, s, D, acts), W, LAM)] += 1
        out[k] = {"structures": len(seen), "min_score": str(min(hist))}
    return out


def _raw_insertions(ref, alphabet, k):
    base = list(ref.nodes("seg"))
    sites = range(len(base) + 1)
    for places in itertools.combinations_with_replacement(sites, k):
        for vals in itertools.product(alphabet, repeat=k):
            order, real, dom = [], dict(ref.real), dict(ref.dom)
            made = 0
            counts = Counter(places)
            for i in range(len(base) + 1):
                for _ in range(counts.get(i, 0)):
                    nd = NodeId("Or", "made", 10000 + made)
                    order.append(nd); real[nd] = vals[made]
                    dom[nd] = dict(ref.dom.get(base[min(i, len(base) - 1)], {}))
                    made += 1
                if i < len(base):
                    order.append(base[i])
            yield Struct(order={**ref.order, "seg": tuple(order)}, real=real,
                         dom=dom, assoc=ref.assoc, corr=ref.corr)


def main():
    without = levels(("a", "t", ABSENT))
    with_ = levels(("a", "t"))
    m, delta = 2, 2
    crit = delta / math.log(m)
    rec = {"without_quotient": without, "with_quotient": with_,
           "insertion_alphabet_size": m, "delta": delta,
           "critical_temperature": crit,
           "ratio_at": {str(T): m * math.exp(-delta / T)
                        for T in (0.5, 1.0, crit * 0.99, crit * 1.01, 4.0)}}
    OUT.mkdir(parents=True, exist_ok=True)
    certificate.write("created_position_quotient.json", rec)
    print("without the quotient, min score per level:",
          [without[k]["min_score"] for k in sorted(without)])
    print("with    the quotient, min score per level:",
          [with_[k]["min_score"] for k in sorted(with_)])
    print(f"critical temperature delta/log m = {crit:.4f}")
    for T, r in rec["ratio_at"].items():
        print(f"  T={float(T):7.4f}  ratio={r:7.4f}  {'converges' if r < 1 else 'DIVERGES'}")


if __name__ == "__main__":
    main()
