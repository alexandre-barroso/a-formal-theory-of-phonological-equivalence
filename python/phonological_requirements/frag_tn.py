from __future__ import annotations

from fractions import Fraction

from .core import (ABSENT, And, Decl, Feat, Made, NodeId, Not, Or_, Present,
                   RelDecl, Resolves, SameFeat, Scope, Sigma, Slot, SortDecl,
                   Struct, TRUE)

SEGS = {
    "ʔ": {"present": True, "cons": True, "cont": False, "glottal": True},
    "x":      {"present": True, "cons": True, "cont": True,  "glottal": False},
    "k":      {"present": True, "cons": True, "cont": False, "glottal": False},
    "e":      {"present": True, "cons": False, "cont": "undefined", "glottal": False},
    ABSENT:   {"present": False, "cons": "undefined", "cont": "undefined",
               "glottal": "undefined"},
}


def make_sigma() -> Sigma:
    return Sigma(sorts={"Or": SortDecl("Or", "total", tier="seg"),
                        "Rel": SortDecl("Rel", "derived", tier="seg")},
                 relations={"succ": RelDecl("succ", "succession", "Or", "Or", "Rel")},
                 features=SEGS,
                 default_features={"present": True, "cons": False,
                                   "cont": "undefined", "glottal": False},
                 domains=("word",))


WORD = Scope(same=("word",), label="word")
ANCHOR = Slot("t", "Or", "subject", kind="anchor")
PREV = Slot("p", "Rel", "trigger", kind="step", relation="succ", scope=WORD,
            direction=-1, policy="dynamic", filter_mode="stop")

STRENGTHEN = Decl("STRENGTHEN", "Or", (ANCHOR, PREV),
                  And((Feat("cons", "t", True), Resolves("p"),
                       Feat("cons", "p", True))),
                  Not(Feat("cont", "t", True)), scope=WORD)

NEXT = Slot("n", "Rel", "trigger", kind="step", relation="succ", scope=WORD,
            direction=+1, policy="dynamic", filter_mode="stop")
NOGLOT = Decl("NOGLOT", "Or", (ANCHOR, NEXT),
              And((Feat("glottal", "t", True), Resolves("n"),
                   Feat("cons", "n", True))),
              Not(Present("t")), scope=WORD)

MAXD = Decl("MAX", "Or", (ANCHOR,), TRUE, Present("t"),
            kind="faithfulness", locus_side="reference")
IDCONT = Decl("IDENT-cont", "Or", (ANCHOR,), TRUE,
              SameFeat("cont", ("t", "current"), ("t", "reference")),
              kind="faithfulness", locus_side="reference")

DECLS = {"MAX": MAXD, "IDENT-cont": IDCONT, "STRENGTHEN": STRENGTHEN,
         "NOGLOT": NOGLOT}
W = {"MAX": 4, "IDENT-cont": 6, "STRENGTHEN": 20, "NOGLOT": 30}
LAM = Fraction(1, 8)

REF = ["e", "ʔ", "x", "e"]


def reference():
    nodes = tuple(NodeId("Or", "lex", i) for i in range(len(REF)))
    return Struct(order={"seg": nodes}, real={n: REF[i] for i, n in enumerate(nodes)},
                  dom={n: {"word": 0} for n in nodes})


def deletion_candidates():
    ref = reference(); nodes = list(ref.nodes("seg"))
    out = []
    for v1 in ("ʔ", ABSENT):
        for v2 in ("x", "k", ABSENT):
            real = dict(ref.real); real[nodes[1]] = v1; real[nodes[2]] = v2
            out.append(((v1, v2), Struct(order=ref.order, real=real, dom=ref.dom)))
    return ref, out


def coalescence_candidates():
    ref = reference()
    out = []
    for v in ("x", "k"):
        nodes = (NodeId("Or", "out", 0), NodeId("Or", "out", 1), NodeId("Or", "out", 2))
        corr = {nodes[0]: (NodeId("Or", "lex", 0),),
                nodes[1]: (NodeId("Or", "lex", 1), NodeId("Or", "lex", 2)),
                nodes[2]: (NodeId("Or", "lex", 3),)}
        real = {nodes[0]: "e", nodes[1]: v, nodes[2]: "e"}
        out.append((("fused", v),
                    Struct(order={"seg": nodes}, real=real,
                           dom={n: {"word": 0} for n in nodes}, corr=corr)))
    return ref, out


def observe(sigma, s):
    return "".join(s.real[n] for n in s.nodes("seg") if sigma.present(s.real[n]))
