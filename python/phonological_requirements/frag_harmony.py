from __future__ import annotations

from .core import (ABSENT, And, Decl, Feat, Not, Or_, Positional, RelDecl,
                   Resolves, SameFeat, Scope, Sigma, Slot, SortDecl, Struct,
                   NodeId, TRUE)

def _v(high, low, atr, mid=False):
    return dict(present=True, nuclear=True, high=high, low=low, atr=atr, mid=mid)


VOWELS = {
    "i": _v(True, False, True), "I": _v(True, False, False),
    "u": _v(True, False, True), "U": _v(True, False, False),
    "e": _v(False, False, True, mid=True), "E": _v(False, False, False, mid=True),
    "o": _v(False, False, True, mid=True), "O": _v(False, False, False, mid=True),
    "a": _v(False, True, False),
    "i?": _v(True, False, None), "u?": _v(True, False, None),
    "e?": _v(False, False, None, mid=True), "o?": _v(False, False, None, mid=True),
    "a?": _v(False, True, None),
}
VOWELS[ABSENT] = dict(present=False, nuclear=None, high=None, low=None, atr=None, mid=None)
ATR_PAIR = {"i": ("i", "I"), "I": ("i", "I"), "u": ("u", "U"), "U": ("u", "U"),
            "e": ("e", "E"), "E": ("e", "E"), "o": ("o", "O"), "O": ("o", "O"),
            "a": ("e", "a"), "i?": ("i", "I"), "u?": ("u", "U"), "e?": ("e", "E"),
            "o?": ("o", "O"), "a?": ("o", "a")}
HEIGHT_PAIR = {"i": ("i", "e"), "e": ("i", "e"), "u": ("u", "o"), "o": ("u", "o")}


def sigma() -> Sigma:
    return Sigma(sorts={"Or": SortDecl("Or", "total", tier="seg"),
                        "Rel": SortDecl("Rel", "derived", tier="seg")},
                 relations={"succ": RelDecl("succ", "succession", "Or", "Or", "Rel")},
                 features=VOWELS,
                 default_features=dict(present=True, nuclear=True, high=False,
                                       low=False, atr=None, mid=False),
                 domains=("word", "side", "init", "fin"))


def struct(vowels, sides):
    n = len(vowels)
    nodes = [NodeId("Or", "lex", i) for i in range(n)]
    real = {nd: v for nd, v in zip(nodes, vowels)}
    dom = {nd: {"word": 0, "side": sides[i], "init": int(i == 0), "fin": int(i == n - 1)}
           for i, nd in enumerate(nodes)}
    return Struct(order={"seg": tuple(nodes)}, real=real, dom=dom)


WORD = Scope(same=("word",), label="word")
T = Slot("t", "Or", "subject", kind="anchor")
PREV = Slot("z", "Or", "trigger", kind="search", direction=-1, scope=WORD)
NEXT = Slot("z", "Or", "trigger", kind="search", direction=+1, scope=WORD)
PREV_SPEC = Slot("z", "Or", "trigger", kind="search", direction=-1, scope=WORD,
                 filter="atr_specified", where="reference")
NEXT_SPEC = Slot("z", "Or", "trigger", kind="search", direction=+1, scope=WORD,
                 filter="atr_specified", where="reference")
NEXT_SPEC_OR_HIGH = Slot("z", "Or", "trigger", kind="search", direction=+1, scope=WORD,
                         filter="atr_specified_or_high", where="reference")
INITIAL = Slot("z", "Or", "trigger", kind="search", direction=-1,
               scope=Scope(delta={"init": +1}, label="initial"))
FINAL = Slot("f", "Or", "trigger", kind="search", direction=+1,
             scope=Scope(delta={"fin": +1}, label="final"))
ROOT_L = Slot("r", "Or", "subject", kind="search", direction=-1,
              scope=Scope(delta={"side": -1}, label="root"))
NEXT_S = Slot("n", "Or", "subject", kind="search", direction=+1, scope=WORD)
PREV_ROOT = Slot("z", "Or", "trigger", kind="search", direction=-1,
                 scope=Scope(delta={"side": -1}, label="root"))


def spread(name, trigger: Slot, value=None, nonhigh_only=False, side=None) -> Decl:
    act = [Resolves("z")]
    if nonhigh_only:
        act.append(Not(Feat("high", "t", True)))
    if side is not None:
        act.append(_SideIs("t", side))
    if value is None:
        cons = SameFeat("atr", ("t", "current"), ("z", "current"))
    else:
        act.append(Feat("atr", "z", value))
        cons = Feat("atr", "t", value)
    return Decl(name, "Or", (T, trigger), And(tuple(act)), cons, scope=WORD)


def agree_pair() -> Decl:
    return Decl("AGREE_PAIR", "Or", (T, NEXT_S), Resolves("n"),
                SameFeat("atr", ("t", "current"), ("n", "current")), scope=WORD)


def ident(name, feature, side=None, weight_class=None) -> Decl:
    act = TRUE if side is None else _SideIs("t", side)
    return Decl(name, "Or", (T,), act,
                SameFeat(feature, ("t", "current"), ("t", "reference")),
                kind="faithfulness", locus_side="reference")


class _SideIs:
    def __init__(self, slot, value): self.slot, self.value = slot, value
    def slots(self): return frozenset({self.slot})
    def eval(self, ctx):
        o = ctx.resolve(self.slot)
        if o is None: return None
        v = ctx.state.dom[o]["side"]
        return v in self.value if isinstance(self.value, tuple) else v == self.value
    def depth(self): return 1


def block_after_high_initial() -> Decl:
    return Decl("BLOCK_INIT", "Or", (T, INITIAL),
                And((_SideIs("t", -1), Not(Feat("high", "t", True)),
                     Resolves("z"), Feat("high", "z", True))),
                Not(Feat("atr", "t", True)), scope=WORD)


ROOT_R = Slot("z", "Or", "trigger", kind="search", direction=+1,
              scope=Scope(delta={"side": +1}, label="root"))
NEXT_NONHIGH = Slot("b", "Or", "trigger", kind="search", direction=+1, scope=WORD,
                    filter="nonhigh")
INITIAL_Q = Slot("q", "Or", "trigger", kind="search", direction=-1,
                 scope=Scope(delta={"init": +1}, label="initial"))


def spread_with_two_sided_block() -> Decl:
    initial_high = Or_((And((Positional("first_of", "t", "word"), Feat("high", "t", True))),
                        And((Resolves("q"), Feat("high", "q", True)))))
    blocker_ahead = Or_((Not(Feat("high", "t", True)),
                         And((Resolves("b"), _SideIs("b", -1)))))
    return Decl("T1_TARGET", "Or", (T, ROOT_R, NEXT_NONHIGH, INITIAL_Q),
                And((_SideIs("t", -1), Resolves("z"), Feat("atr", "z", True),
                     Not(And((initial_high, blocker_ahead))))),
                Feat("atr", "t", True), scope=WORD)


def two_sided_height() -> Decl:
    return Decl("HEIGHT_2SIDED", "Or", (T, ROOT_L, FINAL),
                And((_SideIs("t", +1), Resolves("r"),
                     Or_((And((Resolves("f"), Feat("mid", "f", True, where="reference"))),
                          And((Not(Resolves("f")), Feat("mid", "t", True, where="reference"))))))),
                SameFeat("mid", ("t", "current"), ("r", "current")), scope=WORD)
