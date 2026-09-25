from __future__ import annotations

from .core import (ABSENT, And, Decl, Feat, NodeId, Not, Or_, Positional, Present,
                   RelDecl, Resolves, Scope, Sigma, Slot, SortDecl, Struct, TRUE)

VOWELS = "aeiou"
STRESSED = {"á": "a", "é": "e", "í": "i", "ó": "o", "ú": "u"}


def features():
    f = {}
    for v in VOWELS:
        f[v] = dict(present=True, nuclear=True, stressed=False)
    for sv in STRESSED:
        f[sv] = dict(present=True, nuclear=True, stressed=True)
    f[ABSENT] = dict(present=False, nuclear=None, stressed=None)
    return f


def sigma() -> Sigma:
    return Sigma(sorts={"Or": SortDecl("Or", "total", tier="seg"),
                        "Rel": SortDecl("Rel", "derived", tier="seg")},
                 relations={"succ": RelDecl("succ", "succession", "Or", "Or", "Rel")},
                 features=features(),
                 default_features=dict(present=True, nuclear=False, stressed=False),
                 domains=("word",))


def struct(segments):
    nodes = [NodeId("Or", "lex", i) for i in range(len(segments))]
    return Struct(order={"seg": tuple(nodes)}, real={nd: s for nd, s in zip(nodes, segments)},
                  dom={nd: {"word": 0} for nd in nodes})


WORD = Scope(same=("word",), label="word")
T = Slot("t", "Or", "subject", kind="anchor")
NEXT_LIVE = Slot("nd", "Or", "trigger", kind="step", relation="succ", scope=WORD,
                 direction=+1, policy="dynamic")
NEXT_ORIGIN = Slot("nr", "Or", "trigger", kind="step", relation="succ", scope=WORD,
                   direction=+1, policy="origin_bound")
NEXT_REF = Slot("nc", "Or", "trigger", kind="step", relation="succ", scope=WORD,
                direction=+1, policy="reference")


def no_unstressed_v() -> Decl:
    return Decl("NO_UNSTR_V", "Or", (T,),
                And((Feat("nuclear", "t", True), Not(Feat("stressed", "t", True)))),
                Not(Present("t")), scope=WORD)


def no_final_c() -> Decl:
    return Decl("NO_FINAL_C", "Or", (T,),
                And((Present("t"), Not(Feat("nuclear", "t", True)),
                     Positional("last_live_of", "t", "word"))),
                Not(Present("t")), scope=WORD)


def max_seg() -> Decl:
    return Decl("MAX", "Or", (T,), TRUE, Present("t"),
                kind="faithfulness", locus_side="reference")


def max_v_initial() -> Decl:
    return Decl("MAX_V_INIT", "Or", (T,),
                And((Feat("nuclear", "t", True, where="reference"),
                     Positional("first_of", "t", "word"))),
                Present("t"), kind="faithfulness", locus_side="reference")


class _RefSuccPresent:
    def __init__(self, slot): self.slot = slot
    def slots(self): return frozenset({self.slot})
    def eval(self, ctx):
        o = ctx.resolve(self.slot)
        if o is None: return None
        order = list(ctx.reference.nodes("seg"))
        if o not in order or order.index(o) + 1 >= len(order): return False
        r = ctx.realisation(order[order.index(o) + 1], "current")
        return None if r is None else ctx.sigma.present(r)
    def depth(self): return 1


def contig() -> Decl:
    return Decl("CONTIG", "Or", (T, NEXT_LIVE),
                And((Present("t"), Resolves("nd"))), _RefSuccPresent("t"),
                kind="faithfulness", locus_side="reference", scope=WORD)


def contig_legacy() -> Decl:
    return Decl("CONTIG", "Or", (T, NEXT_LIVE, NEXT_ORIGIN),
                And((Present("t"), Resolves("nd"))), Resolves("nr"),
                kind="faithfulness", locus_side="reference", scope=WORD)


def max_v_before_c() -> Decl:
    return Decl("MAX_V_BEFORE_C", "Or", (T, NEXT_REF),
                And((Feat("nuclear", "t", True, where="reference"), Resolves("nc"),
                     Not(Feat("nuclear", "nc", True, where="reference")))),
                Present("t"), kind="faithfulness", locus_side="reference", scope=WORD)


def declarations(contextual: bool = False):
    ds = [no_unstressed_v(), no_final_c(), max_seg(), max_v_initial(), contig()]
    if contextual:
        ds.append(max_v_before_c())
    return {d.name: d for d in ds}
