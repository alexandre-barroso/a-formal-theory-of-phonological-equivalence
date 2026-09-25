from __future__ import annotations

from fractions import Fraction

from .core import (ABSENT, And, Decl, Feat, Linked, NodeId, Not, Or_, Present,
                   RelDecl, Resolves, SameFeat, Scope, Sigma, Slot, SortDecl,
                   Struct, TRUE)

SEGS = {
    "o": {"present": True, "round": True, "high": False, "vocalic": True},
    "u": {"present": True, "round": True, "high": True, "vocalic": True},
    "a": {"present": True, "round": False, "high": False, "vocalic": True},
    "t": {"present": True, "round": False, "high": "undefined", "vocalic": False},
    ABSENT: {"present": False, "round": "undefined", "high": "undefined",
             "vocalic": "undefined"},
}


def make_sigma() -> Sigma:
    return Sigma(
        sorts={"Or": SortDecl("Or", "total", tier="seg"),
               "SCorr": SortDecl("SCorr", "derived", tier="seg",
                                 comment="a surface correspondence pair")},
        relations={"succ": RelDecl("succ", "succession", "Or", "Or", "Rel"),
                   "scorr": RelDecl("scorr", "correspondence", "Or", "Or", "SCorr")},
        features=SEGS,
        default_features={"present": True, "round": False, "high": "undefined",
                          "vocalic": False},
        domains=("word",))


WORD = Scope(same=("word",), label="word")
ANCHOR = Slot("t", "Or", "subject", kind="anchor")
RNEXT = Slot("n", "Or", "subject", kind="search", relation="succ", scope=WORD,
             direction=+1, filter="round")
PARTNER = Slot("c", "SCorr", "subject", kind="assoc", relation="scorr",
               where="current")

CORR = Decl("CORR", "Or", (ANCHOR, RNEXT),
            And((Feat("round", "t", True), Resolves("n"))),
            Or_((Not(Resolves("n")), Linked("t", "n", where="current"))),
            scope=WORD)

IDENT_XX = Decl("IDENT-XX", "Or", (ANCHOR, PARTNER),
                Feat("round", "t", True),
                SameFeat("high", ("t", "current"), ("c", "current")),
                scope=WORD)

MAXSEG = Decl("MAX", "Or", (ANCHOR,), TRUE, Present("t"),
              kind="faithfulness", locus_side="reference")
IDENT_IO = Decl("IDENT-IO", "Or", (ANCHOR,), TRUE,
                SameFeat("high", ("t", "current"), ("t", "reference")),
                kind="faithfulness", locus_side="reference")

IDENT_IO_RD = Decl("IDENT-IO-rd", "Or", (ANCHOR,), TRUE,
                   SameFeat("round", ("t", "current"), ("t", "reference")),
                   kind="faithfulness", locus_side="reference")

DECLS = {"MAX": MAXSEG, "IDENT-IO": IDENT_IO, "IDENT-IO-rd": IDENT_IO_RD,
         "CORR": CORR, "IDENT-XX": IDENT_XX}
LAM = Fraction(1, 8)


def build(segs, scorr_pairs=()):
    nodes = tuple(NodeId("Or", "lex", i) for i in range(len(segs)))
    assoc = set()
    for a, b in scorr_pairs:
        assoc.add((nodes[a], nodes[b]))
    return Struct(order={"seg": nodes},
                  real={n: segs[i] for i, n in enumerate(nodes)},
                  dom={n: {"word": 0} for n in nodes},
                  assoc=frozenset(assoc))


def observe(sigma, s) -> str:
    return "".join(s.real[n] for n in s.nodes("seg") if sigma.present(s.real[n]))
