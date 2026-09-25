from __future__ import annotations

from fractions import Fraction

from .core import (ABSENT, And, Decl, Feat, Made, NodeId, Not, Or_, Present,
                   RelDecl, Resolves, Scope, Sigma, Slot, SortDecl, Struct, TRUE)

SEGS = {"b": {"present": True, "cons": True, "velar": False, "vocalic": False},
        "e": {"present": True, "cons": False, "velar": False, "vocalic": True},
        "i": {"present": True, "cons": False, "velar": False, "vocalic": True},
        "k": {"present": True, "cons": True, "velar": True, "vocalic": False},
        "n": {"present": True, "cons": True, "velar": False, "vocalic": False},
        ABSENT: {"present": False, "cons": "undefined", "velar": "undefined",
                 "vocalic": "undefined"}}


def make_sigma() -> Sigma:
    return Sigma(sorts={"Or": SortDecl("Or", "total", tier="seg"),
                        "Rel": SortDecl("Rel", "derived", tier="seg")},
                 relations={"succ": RelDecl("succ", "succession", "Or", "Or", "Rel")},
                 features=SEGS,
                 default_features={"present": True, "cons": False,
                                   "velar": False, "vocalic": False},
                 domains=("word",))


WORD = Scope(same=("word",), label="word")
A = Slot("t", "Or", "subject", kind="anchor")
NX = Slot("n", "Rel", "subject", kind="step", relation="succ", scope=WORD,
          direction=+1, policy="dynamic", filter_mode="stop")
PV = Slot("p", "Rel", "trigger", kind="step", relation="succ", scope=WORD,
          direction=-1, policy="dynamic", filter_mode="stop")
NX2 = Slot("n2", "Rel", "trigger", kind="step", relation="succ", scope=WORD,
           direction=+1, policy="dynamic", filter_mode="stop")

NOCC = Decl("*CC#", "Or", (A, NX),
            And((Present("t"), Feat("cons", "t", True), Resolves("n"),
                 Feat("cons", "n", True))),
            Not(Feat("cons", "n", True)), scope=WORD)
VELDEL = Decl("VELDEL", "Or", (A, PV, NX2),
              And((Feat("velar", "t", True), Resolves("p"),
                   Feat("vocalic", "p", True), Resolves("n2"),
                   Feat("vocalic", "n2", True))),
              Not(Present("t")), scope=WORD)
MAXD = Decl("MAX", "Or", (A,), TRUE, Present("t"), kind="faithfulness",
            locus_side="reference")
DEP = Decl("DEP", "Or", (A,), Made("t"),
           Or_((Not(Made("t")), Not(Present("t")))), kind="faithfulness")

DECLS = {"MAX": MAXD, "DEP": DEP, "*CC#": NOCC, "VELDEL": VELDEL}
BASE = ["b", "e", "b", "e", "k", "n"]


def reference():
    nodes = tuple(NodeId("Or", "lex", i) for i in range(6))
    return Struct(order={"seg": nodes},
                  real={n: BASE[i] for i, n in enumerate(nodes)},
                  dom={n: {"word": 0} for n in nodes})


def candidates():
    lex = [NodeId("Or", "lex", i) for i in range(6)]
    out = []
    for kv in ("k", ABSENT):
        for eps in (False, True):
            if eps:
                made = NodeId("Or", "made", 100)
                order = tuple(lex[:5] + [made] + lex[5:])
                real = {n: BASE[i] for i, n in enumerate(lex)}
                real[lex[4]] = kv; real[made] = "i"
            else:
                order = tuple(lex)
                real = {n: BASE[i] for i, n in enumerate(lex)}
                real[lex[4]] = kv
            dom = {n: {"word": 0} for n in order}
            out.append(((kv, eps), Struct(order={"seg": order}, real=real, dom=dom)))
    return out


def observe(sigma, s):
    return "".join(s.real[n] for n in s.nodes("seg") if sigma.present(s.real[n]))
