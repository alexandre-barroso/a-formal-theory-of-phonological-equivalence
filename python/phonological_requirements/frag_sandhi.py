from __future__ import annotations

import itertools

from .core import (ABSENT, And, Decl, Feat, NodeId, Not, Or_, RelDecl, Resolves,
                   SameFeat, Scope, Sigma, Slot, SortDecl, Struct, TRUE)

TONES = ("T1", "T2", "T3", "T4")


REG = {"T1": "H", "T2": "L", "T3": "L", "T4": "H"}
CONT = {"T1": "fall", "T2": "rise", "T3": "low", "T4": "level"}


def features():
    f = {t: dict(present=True, tone=int(t[1]), reg=REG[t], cont=CONT[t]) for t in TONES}
    f[ABSENT] = dict(present=False, tone=None, reg=None, cont=None)
    return f


def sigma() -> Sigma:
    return Sigma(sorts={"Syl": SortDecl("Syl", "total", tier="syll"),
                        "Rel": SortDecl("Rel", "derived", tier="syll")},
                 relations={"succ": RelDecl("succ", "succession", "Syl", "Syl", "Rel")},
                 features=features(), default_features=dict(present=True, tone=None, reg=None, cont=None),
                 domains=("phrase", "word", "pos"))


SG = sigma()
PHRASE = Scope(same=("phrase",), label="phrase")
T = Slot("t", "Syl", "subject", kind="anchor")
N = Slot("n", "Syl", "subject", kind="step", relation="succ", scope=PHRASE, direction=+1,
         filter="present", policy="dynamic")
P = Slot("p", "Syl", "trigger", kind="step", relation="succ", scope=PHRASE, direction=-1,
         filter="present", policy="reference")


def tone(s, k):
    return Feat("tone", s, k)


def sandhi(name, before, out):
    ctx = And((Resolves("n"), tone("n", before)))
    return Decl(name, "Syl", (T, N), And((tone("t", before), ctx)),
                Or_((Not(ctx), tone("t", out))), scope=PHRASE)


def declarations():
    D = {}
    D["S33"] = sandhi("S33", 3, 2)
    D["S11"] = sandhi("S11", 1, 3)
    D["S44"] = sandhi("S44", 4, 3)
    D["IDENT_REG"] = Decl("IDENT_REG", "Syl", (T,), TRUE, SameFeat("reg", ("t", "current"), ("t", "reference")),
                          kind="faithfulness")
    D["IDENT_CONT"] = Decl("IDENT_CONT", "Syl", (T,), TRUE, SameFeat("cont", ("t", "current"), ("t", "reference")),
                           kind="faithfulness")
    D["IDENT_FINAL"] = Decl("IDENT_FINAL", "Syl", (T, N), Not(Resolves("n")),
                            Or_((Resolves("n"), SameFeat("tone", ("t", "current"), ("t", "reference")))),
                            kind="faithfulness")
    D["IDENT_R"] = Decl("IDENT_R", "Syl", (T, P), SameFeat("tone", ("p", "reference"), ("t", "reference")),
                        SameFeat("tone", ("t", "current"), ("t", "reference")), kind="faithfulness")
    return D


def build(tones, phrase=0) -> Struct:
    nodes, real, dom = [], {}, {}
    for i, t in enumerate(tones):
        n = NodeId("Syl", "lex", i)
        nodes.append(n); real[n] = t; dom[n] = {"phrase": phrase, "word": i, "pos": i}
    return Struct(order={"syll": tuple(nodes)}, real=real, dom=dom)


def candidates(ref: Struct):
    nodes = ref.order["syll"]
    for combo in itertools.product(TONES, repeat=len(nodes)):
        real = dict(zip(nodes, combo))
        yield Struct(order=ref.order, real=real, dom=ref.dom)


def surface(s: Struct) -> str:
    return "".join(s.real[n] for n in s.order["syll"])
