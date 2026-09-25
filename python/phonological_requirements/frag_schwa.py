from __future__ import annotations

from .core import (ABSENT, And, Decl, Feat, NodeId, Not, Or_, RelDecl, Resolves, Scope, Sigma, Slot,
                   SortDecl, Struct, Present)

PHRASE = Scope(same=("phrase",), label="phrase")


def make_sigma() -> Sigma:
    f = {"C": dict(present=True, cons=True, nuclear=False, stressed=None, schwa=False),
         "V": dict(present=True, cons=False, nuclear=True, stressed=False, schwa=False),
         "'V": dict(present=True, cons=False, nuclear=True, stressed=True, schwa=False),
         "@": dict(present=True, cons=False, nuclear=True, stressed=False, schwa=True),
         ABSENT: dict(present=False, cons=None, nuclear=None, stressed=None, schwa=None)}
    return Sigma(sorts={"Or": SortDecl("Or", "total", tier="seg"), "Rel": SortDecl("Rel", "derived", tier="seg")},
                 relations={"succ": RelDecl("succ", "succession", "Or", "Or", "Rel")},
                 features=f, default_features={"present": True, "cons": False}, domains=("phrase",))


def build(syms, site: int, kind: str) -> Struct:
    nodes, real, dom = [], {}, {}
    k = 0
    for j, s in enumerate(syms):
        if j == site and kind == "lex":
            n = NodeId("Or", "lex", k); k += 1
            nodes.append(n); real[n] = "@"; dom[n] = {"phrase": 0}
        n = NodeId("Or", "lex", k); k += 1
        nodes.append(n); real[n] = s; dom[n] = {"phrase": 0}
    if site >= len(syms) and kind == "lex":
        n = NodeId("Or", "lex", k); nodes.append(n); real[n] = "@"; dom[n] = {"phrase": 0}
    corr = {n: (n,) for n in nodes}
    return Struct(order={"seg": tuple(nodes)}, real=real, dom=dom, corr=corr)


def candidates(ref: Struct, site: int, kind: str):
    nodes = list(ref.order["seg"])
    if kind == "lex":
        sch = next(n for n in nodes if ref.real[n] == "@")
        yield ref
        r = dict(ref.real); r[sch] = ABSENT
        yield Struct(order=ref.order, real=r, dom=ref.dom, corr=ref.corr)
    else:
        yield ref
        m = NodeId("Or", "made", 0)
        order = tuple(nodes[:site] + [m] + nodes[site:])
        real = dict(ref.real); real[m] = "@"
        dom = dict(ref.dom); dom[m] = {"phrase": 0}
        corr = dict(ref.corr); corr[m] = ()
        yield Struct(order={"seg": order}, real=real, dom=dom, corr=corr)


def surface(s: Struct) -> str:
    return " ".join(s.real[n] for n in s.order["seg"] if s.real[n] is not ABSENT)


T = Slot("t", "Or", "subject", kind="anchor")
N1 = Slot("n1", "Or", "subject", kind="step", relation="succ", scope=PHRASE, direction=+1, filter="present")
N2 = Slot("n2", "Or", "subject", kind="stepof", relation="succ", scope=PHRASE, direction=+1, filter="present", of="n1", tier="seg")
P1 = Slot("p1", "Or", "subject", kind="step", relation="succ", scope=PHRASE, direction=-1, filter="present")
NV = Slot("nv", "Or", "subject", kind="step", relation="succ", scope=PHRASE, direction=+1, filter="nuclear")
cons = lambda s: Feat("cons", s, True)


def declarations() -> dict:
    D = {}
    D["NOSCHWA"] = Decl("NOSCHWA", "Or", (T,), And((Present("t"), Feat("schwa", "t", True))), Not(Present("t")), scope=PHRASE)
    run_start = And((Present("t"), cons("t"), Not(And((Resolves("p1"), cons("p1")))), Resolves("n1"), cons("n1")))
    D["NOCLUSTER"] = Decl("NOCLUSTER", "Or", (T, P1, N1), run_start, Not(And((Resolves("n1"), cons("n1")))), scope=PHRASE)
    triple = And((Present("t"), cons("t"), Resolves("n1"), cons("n1"), Resolves("n2"), cons("n2")))
    D["NOCCC"] = Decl("NOCCC", "Or", (T, N1, N2), triple, Not(And((Resolves("n2"), cons("n2")))), scope=PHRASE)
    clash = And((Present("t"), Feat("stressed", "t", True), Resolves("nv"), Feat("stressed", "nv", True)))
    D["NOCLASH"] = Decl("NOCLASH", "Or", (T, NV), clash, Not(And((Resolves("nv"), Feat("stressed", "nv", True)))), scope=PHRASE)
    D["MAX"] = Decl("MAX", "Or", (T,), Feat("schwa", "t", True, where="reference"), Present("t"), kind="faithfulness",
                    locus_side="reference")
    D["DEP"] = Decl("DEP", "Or", (T,), And((Present("t"), _Made("t"))), Not(Feat("present", "t", True)),
                    kind="faithfulness")
    return D


class _Made:
    def __init__(self, slot): self.slot = slot
    def slots(self): return frozenset({self.slot})
    def eval(self, ctx):
        o = ctx.resolve(self.slot)
        if o is None: return None
        return len(ctx.state.correspondents(o)) == 0
    def depth(self): return 1
