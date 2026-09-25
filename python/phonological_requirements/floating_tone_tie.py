from __future__ import annotations
from phonological_requirements import certificate, paths
import itertools, json
from pathlib import Path

import sympy as sp

from .core import (ABSENT, And, Decl, NodeId, Present, RelDecl, Resolves,
                   Sigma, Slot, SortDecl, Struct, TRUE, read)
from .evaluate import loci

OUT = paths.CERTIFICATES
SEGS = {"a": {"present": True, "bearer": True},
        "H": {"present": True, "bearer": False},
        ABSENT: {"present": False, "bearer": "undefined"}}


def setup():
    sg = Sigma(sorts={"Or": SortDecl("Or", "total", tier="seg"),
                      "Tone": SortDecl("Tone", "total", tier="tone"),
                      "Assoc": SortDecl("Assoc", "derived", tier="seg")},
               relations={"assoc": RelDecl("assoc", "association", "Tone", "Or", "Assoc")},
               features=SEGS, default_features={"present": True, "bearer": False},
               domains=("word",))
    T = Slot("t", "Tone", "subject", kind="anchor")
    HOST = Slot("h", "Or", "subject", kind="assoc", relation="assoc",
                where="current", tier="seg")
    FLOAT = Decl("*FLOAT", "Tone", (T, HOST), Present("t"),
                 And((Resolves("h"), Present("h"))))
    MAXH = Decl("MAX-H", "Tone", (T,), TRUE, Present("t"),
                kind="faithfulness", locus_side="reference")
    return sg, FLOAT, MAXH


def build(parsed, n=3):
    segn = tuple(NodeId("Or", "lex", i) for i in range(n))
    tonn = tuple(NodeId("Tone", "lex", i) for i in range(n))
    real = {x: "a" for x in segn}
    real.update({x: ("H" if parsed[i] else ABSENT) for i, x in enumerate(tonn)})
    dom = {x: {"word": 0} for x in segn + tonn}
    return Struct(order={"seg": segn, "tone": tonn}, real=real, dom=dom,
                  assoc=frozenset())


def main():
    sg, FLOAT, MAXH = setup()
    ref = build((True,) * 3)
    f, mx = sp.symbols("f mx", nonnegative=True)

    def cur(c, d, tier):
        return sum(read(sg, ref, c, d, x, tier).marked for x in loci(c, d, tier, ref))

    rows = []
    for p in itertools.product((True, False), repeat=3):
        c = build(p)
        fl, mh = cur(c, FLOAT, "tone"), cur(c, MAXH, "tone")
        rows.append({"candidate": "".join("H" if x else "-" for x in p),
                     "FLOAT": fl, "MAX_H": mh,
                     "score": str(sp.expand(f * fl + mx * mh))})
    one = [r for r in rows if r["candidate"].count("H") == 2]
    rec = {"input": "Three floating H tones: deletion-only abstraction of the Poko comparison",
           "rows": rows,
           "one_deletion_candidates": [r["candidate"] for r in one],
           "their_scores": [r["score"] for r in one],
           "exactly_tied_for_every_nonnegative_weight_vector":
               len({r["score"] for r in one}) == 1,
           "source": ("mcphersonLamont2026pokoPostlexicalTone: draft2024(63), "
                      "published2026(62), counting floating tones gives tied single deletions"),
           "consequence": ("The two count constraints cannot distinguish these three "
                           "single deletions at any weights. This model omits M tones, "
                           "docking and serial derivations. The source permits a nonlocal "
                           "ALIGN-R alternative; no exclusion of all global evaluators follows.")}
    OUT.mkdir(parents=True, exist_ok=True)
    certificate.write("floating_tone_tie.json", rec)
    for r in rows:
        print(f"  {r['candidate']:5s} *FLOAT={r['FLOAT']} MAX-H={r['MAX_H']}  {r['score']}")
    print("one-deletion candidates exactly tied:",
          rec["exactly_tied_for_every_nonnegative_weight_vector"])


if __name__ == "__main__":
    main()
