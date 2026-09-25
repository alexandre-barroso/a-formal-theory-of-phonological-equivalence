from __future__ import annotations

from dataclasses import replace
from fractions import Fraction
from typing import Mapping, Sequence

from .core import (ABSENT, And, Const, Decl, Feat, Made, NodeId, Not, Or_,
                   Present, RelDecl, SameFeat, SameSeg, Scope, Sigma, Slot,
                   SortDecl, Struct, TRUE, UNSCOPED, read)
from .evaluate import loci, activation, marked_subjects, coefficients, score, subject_tuple

SEGS = {"a": {"present": True, "hi": False, "vocalic": True},
        "i": {"present": True, "hi": True, "vocalic": True},
        "t": {"present": True, "hi": "undefined", "vocalic": False},
        ABSENT: {"present": False, "hi": "undefined", "vocalic": "undefined"}}


def sigma() -> Sigma:
    return Sigma(sorts={"Or": SortDecl("Or", "total", tier="seg"),
                        "Rel": SortDecl("Rel", "derived", tier="seg")},
                 relations={"succ": RelDecl("succ", "succession", "Or", "Or", "Rel")},
                 features=SEGS,
                 default_features={"present": True, "hi": "undefined",
                                   "vocalic": "undefined"},
                 domains=("word",))


ANCHOR = Slot("t", "Or", "subject", kind="anchor")
WORD = Scope(same=("word",), label="same_word")

MAXD = Decl("MAX", "Or", (ANCHOR,), TRUE, Present("t"), kind="faithfulness",
            locus_side="reference")
IDENT = Decl("IDENT", "Or", (ANCHOR,), TRUE,
             SameFeat("hi", ("t", "current"), ("t", "reference")),
             kind="faithfulness", locus_side="reference")
DEP = Decl("DEP", "Or", (ANCHOR,), Made("t"),
           Or_((Not(Made("t")), Not(Present("t")))), kind="faithfulness")
SRC = Slot("n", "Or", "trigger", kind="search", relation="succ", scope=WORD,
           direction=+1, filter="vocalic")
HARM = Decl("HARM", "Or", (ANCHOR, SRC),
            And((Feat("vocalic", "t", True), Present("n"), Feat("hi", "n", True))),
            Feat("hi", "t", True))
DECLS = {"MAX": MAXD, "IDENT": IDENT, "DEP": DEP, "HARM": HARM}
W = {"MAX": 10, "IDENT": 1, "DEP": 6, "HARM": 4}
LAM = Fraction(1, 8)


def ref_struct(segs: Sequence[str]) -> Struct:
    nodes = tuple(NodeId("Or", "lex", i) for i in range(len(segs)))
    return Struct(order={"seg": nodes},
                  real={n: segs[i] for i, n in enumerate(nodes)},
                  dom={n: {"word": 0} for n in nodes})


def containment(ref: Struct, realisations: Mapping[int, str]) -> Struct:
    real = dict(ref.real)
    for i, v in realisations.items():
        real[NodeId("Or", "lex", i)] = v
    return replace(ref, real=real)


def correspondence(ref: Struct, spec: Sequence[tuple[str, tuple[int, ...]]]) -> Struct:
    nodes, real, dom, corr = [], {}, {}, {}
    for k, (v, cs) in enumerate(spec):
        nd = NodeId("Or", "out" if cs else "made", k)
        nodes.append(nd); real[nd] = v; dom[nd] = {"word": 0}
        corr[nd] = tuple(NodeId("Or", "lex", c) for c in cs)
    return Struct(order={"seg": tuple(nodes)}, real=real, dom=dom, corr=corr)


def contributions(ref: Struct, cand: Struct, indexing: str = "locus",
                  decls=None, weights=None, lam=LAM):
    decls = decls or DECLS; weights = weights or W
    sg = sigma()
    acts = activation(sg, ref, decls); subs = marked_subjects(sg, ref, decls)
    cf = coefficients(sg, ref, cand, decls, acts,
                      subjects=(subs if indexing == "subject" else None))
    return cf, score(cf, weights, lam)


def readers_table(ref: Struct, cand: Struct, decls=None):
    decls = decls or DECLS; sg = sigma(); out = {}
    for nm, d in decls.items():
        rows = []
        for nd in loci(cand, d):
            r = read(sg, ref, cand, d, nd)
            rows.append((repr(nd), r.triple(), r.pressure,
                         repr(subject_tuple(sg, ref, cand, d, nd))))
        out[nm] = rows
    return out
