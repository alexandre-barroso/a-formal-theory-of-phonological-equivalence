from __future__ import annotations

from fractions import Fraction

from .core import (ABSENT, And, Const, Decl, Feat, Linked, Made, NodeId, Not,
                   Or_, Present, RelDecl, Readers, Resolves, SameFeat, Scope,
                   Sigma, Slot, SortDecl, Struct, TRUE, UNSCOPED, read)

SEGS = {
    "a": {"present": True, "hi": False, "vocalic": True},
    "e": {"present": True, "hi": False, "vocalic": True},
    "o": {"present": True, "hi": False, "vocalic": True},
    "i": {"present": True, "hi": True, "vocalic": True},
    "u": {"present": True, "hi": True, "vocalic": True},
    "t": {"present": True, "hi": "undefined", "vocalic": False},
    "s": {"present": True, "hi": "undefined", "vocalic": False},
    "l": {"present": True, "hi": "undefined", "vocalic": False},
    ABSENT: {"present": False, "hi": "undefined", "vocalic": "undefined"},
    "H": {"present": True, "hi": "undefined", "vocalic": "undefined"},
    "L": {"present": True, "hi": "undefined", "vocalic": "undefined"},
    "μ": {"present": True, "hi": "undefined", "vocalic": "undefined"},
}


def make_sigma(mora_totality: str = "total") -> Sigma:
    sorts = {
        "Or":   SortDecl("Or", "total", tier="seg"),
        "Tone": SortDecl("Tone", "total", tier="tone",
                         comment="a lexically supplied autosegment"),
        "Mora": SortDecl("Mora", mora_totality, tier="mora",
                         comment="supplied by the lexicon (total) or computed "
                                 "by weight-by-position (derived)"),
        "Rel":  SortDecl("Rel", "derived", tier="seg"),
    }
    rels = {"succ": RelDecl("succ", "succession", "Or", "Or", "Rel"),
            "assoc": RelDecl("assoc", "association", "Tone", "Or", "Rel")}
    return Sigma(sorts=sorts, relations=rels, features=SEGS,
                 default_features={"present": True, "hi": "undefined",
                                   "vocalic": False},
                 domains=("word",))


T = Slot("t", "Tone", "subject", kind="anchor")
M = Slot("t", "Mora", "subject", kind="anchor")
S = Slot("t", "Or", "subject", kind="anchor")
HOST_CUR = Slot("h", "Or", "subject", kind="assoc", relation="assoc", where="current")
HOST_REF = Slot("h", "Or", "subject", kind="assoc", relation="assoc", where="reference")

MAXSEG = Decl("MAX", "Or", (S,), TRUE, Present("t"), kind="faithfulness",
              locus_side="reference")

FLOAT_T = Decl("FLOAT-T", "Tone", (T, HOST_CUR), TRUE,
               And((Resolves("h"), Present("h"))))
FLOAT_M = Decl("FLOAT-M", "Mora", (M, HOST_CUR), TRUE,
               And((Resolves("h"), Present("h"))))
MAXLINK_T = Decl("MAXLINK-T", "Tone", (T, HOST_REF), TRUE,
                 Linked("t", "h", where="current"), kind="faithfulness")
DEPLINK_T = Decl("DEPLINK-T", "Tone", (T, HOST_CUR), TRUE,
                 Or_((Not(Resolves("h")), Linked("t", "h", where="reference"))),
                 kind="faithfulness")

LINKQ = Decl("LINKQ", "Tone", (T, HOST_CUR), TRUE, Feat("hi", "h", True))

DECLS = {"MAX": MAXSEG, "FLOAT-T": FLOAT_T, "MAXLINK-T": MAXLINK_T,
         "DEPLINK-T": DEPLINK_T, "LINKQ": LINKQ}
W = {"MAX": 10, "FLOAT-T": 8, "MAXLINK-T": 1, "DEPLINK-T": 1, "LINKQ": 8}
LAM = Fraction(1, 8)

MORA_DECLS = {"MAX": MAXSEG, "FLOAT-M": FLOAT_M}
MORA_W = {"MAX": 10, "FLOAT-M": 8}


def build(segs, tones=(), moras=(), links=()):
    segn = tuple(NodeId("Or", "lex", i) for i in range(len(segs)))
    tonn = tuple(NodeId("Tone", "lex", i) for i in range(len(tones)))
    morn = tuple(NodeId("Mora", "lex", i) for i in range(len(moras)))
    real = {n: segs[i] for i, n in enumerate(segn)}
    real.update({n: tones[i] for i, n in enumerate(tonn)})
    real.update({n: moras[i] for i, n in enumerate(morn)})
    dom = {n: {"word": 0} for n in segn + tonn + morn}
    assoc = set()
    for tier, i, j in links:
        src = tonn[i] if tier == "tone" else morn[i]
        assoc.add((src, segn[j]))
    return Struct(order={"seg": segn, "tone": tonn, "mora": morn},
                  real=real, dom=dom, assoc=frozenset(assoc))
