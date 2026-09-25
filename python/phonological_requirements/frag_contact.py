from __future__ import annotations

from .core import (ABSENT, And, Decl, Feat, NodeId, Not, Or_, Positional, Present,
                   RelDecl, Resolves, SameFeat, SameSeg, Scope, Sigma, Slot, SortDecl,
                   Struct, TRUE)

CONS = {
    "t": (1, "cor", False), "p": (1, "lab", False), "k": (1, "dor", False), "q": (1, "uv", False),
    "s": (2, "cor", False), "f": (2, "lab", False), "x": (2, "dor", False), "ʃ": (2, "pal", False),
    "h": (2, "lar", False),
    "d": (3, "cor", True), "b": (3, "lab", True), "g": (3, "dor", True),
    "z": (4, "cor", True), "v": (4, "lab", True), "ɣ": (4, "dor", True), "ʒ": (4, "pal", True),
    "ð": (4, "cor", True),
    "n": (5, "cor", True), "m": (5, "lab", True), "ŋ": (5, "dor", True),
    "l": (6, "cor", True), "ʕ": (6, "phar", True), "ʔ": (1, "lar", False),
    "r": (7, "cor", True), "ɾ": (7, "cor", True),
    "w": (8, "lab", True), "j": (8, "pal", True),
    "ʰp": (1, "lab", False), "ʰt": (1, "cor", False), "ʰk": (1, "dor", False),
}
VOWELS = "aeiouyɯœ"
NUCLEI = list(VOWELS) + [a + b for a in VOWELS for b in VOWELS]


def features():
    f = {}
    for c, (son, pl, vc) in CONS.items():
        f[c] = dict(present=True, nuclear=False, son=son, place=pl, voice=vc, stressed=False, long=False)
        f[c + "ː"] = dict(present=True, nuclear=False, son=son, place=pl, voice=vc, stressed=False, long=True)
    for v in NUCLEI:
        f[v] = dict(present=True, nuclear=True, son=None, place=None, voice=None, stressed=False, long=False)
        f[v + "ː"] = dict(present=True, nuclear=True, son=None, place=None, voice=None, stressed=False, long=True)
        f["'" + v] = dict(present=True, nuclear=True, son=None, place=None, voice=None, stressed=True, long=False)
        f["'" + v + "ː"] = dict(present=True, nuclear=True, son=None, place=None, voice=None, stressed=True, long=True)
    f[ABSENT] = dict(present=False, nuclear=None, son=None, place=None, voice=None, stressed=None, long=None)
    return f


def sigma() -> Sigma:
    return Sigma(sorts={"Or": SortDecl("Or", "total", tier="seg"),
                        "Rel": SortDecl("Rel", "derived", tier="seg")},
                 relations={"succ": RelDecl("succ", "succession", "Or", "Or", "Rel")},
                 features=features(),
                 default_features=dict(present=True, nuclear=False, son=None, place=None,
                                       voice=None, stressed=False, long=False),
                 domains=("word", "syll", "side"))


def struct(segments, sylls, sides, order=None):
    n = len(segments)
    nodes = [NodeId("Or", "lex", i) for i in range(n)]
    real = {nd: s for nd, s in zip(nodes, segments)}
    order = list(range(n)) if order is None else list(order)
    dom = {}
    for pos, i in enumerate(order):
        dom[nodes[i]] = {"word": 0, "syll": sylls[pos], "side": sides[i]}
    return Struct(order={"seg": tuple(nodes[i] for i in order)}, real=real, dom=dom)


WORD = Scope(same=("word",), label="word")
T = Slot("t", "Or", "subject", kind="anchor")
NEXT_SYLL_C = Slot("n", "Or", "subject", kind="step", relation="succ", direction=+1,
                   policy="dynamic", scope=Scope(delta={"syll": +1}, label="next-syllable"),
                   filter="consonantal", filter_mode="stop")
NEXT_SAME_C = Slot("c", "Or", "subject", kind="step", relation="succ", direction=+1,
                   policy="dynamic", scope=Scope(same=("syll",), label="syllable"),
                   filter="consonantal", filter_mode="stop")
NEXT_LIVE = Slot("nd", "Or", "subject", kind="step", relation="succ", direction=+1,
                 policy="dynamic", scope=WORD)
NEXT_REF = Slot("nr", "Or", "trigger", kind="step", relation="succ", direction=+1,
                policy="reference", scope=WORD)
NEXT_ANY_C = Slot("a", "Or", "subject", kind="step", relation="succ", direction=+1,
                  policy="dynamic", scope=WORD, filter="consonantal", filter_mode="stop")

SON = range(1, 9)
CONTACT_ACT = And((Not(Feat("nuclear", "t", True)), Not(Feat("long", "t", True)), Resolves("n")))


def _pairs(pred):
    return Or_(tuple(And((Feat("son", "t", i), Feat("son", "n", j)))
                     for i in SON for j in SON if pred(i, j)))


def contact_threshold(k: int) -> Decl:
    return Decl(f"CONTACT_LE_{k:+d}", "Or", (T, NEXT_SYLL_C), CONTACT_ACT,
                Not(_pairs(lambda i, j: j - i > k)), scope=WORD)


def contact_stratum(x: int) -> Decl:
    return Decl(f"DIST_{x:+d}", "Or", (T, NEXT_SYLL_C), CONTACT_ACT,
                Not(_pairs(lambda i, j: j - i == x)), scope=WORD)


def ident_seg(name="IDENT", side=None) -> Decl:
    act = TRUE if side is None else _SideIs("t", side)
    return Decl(name, "Or", (T,), act, SameSeg(("t", "current"), ("t", "reference")),
                kind="faithfulness", locus_side="reference")


class _SideIs:
    def __init__(self, slot, value): self.slot, self.value = slot, value
    def slots(self): return frozenset({self.slot})
    def eval(self, ctx):
        o = ctx.resolve(self.slot)
        if o is None: return None
        return ctx.state.dom[o]["side"] == self.value
    def depth(self): return 1


def agree_voice(obstruents_only: bool = False) -> Decl:
    act = [Not(Feat("nuclear", "t", True)), Resolves("a")]
    if obstruents_only:
        act += [Or_(tuple(Feat("son", "t", i) for i in (1, 2, 3, 4))),
                Or_(tuple(Feat("son", "a", i) for i in (1, 2, 3, 4)))]
    return Decl("AGREE_VOICE_OBS" if obstruents_only else "AGREE_VOICE", "Or", (T, NEXT_ANY_C),
                And(tuple(act)), SameFeat("voice", ("t", "current"), ("a", "current")), scope=WORD)


def ident_place(obstruents_only: bool = False) -> Decl:
    act = [Not(Feat("nuclear", "t", True, where="reference"))]
    if obstruents_only:
        act.append(Or_(tuple(Feat("son", "t", i, where="reference") for i in (1, 2, 3, 4))))
    return Decl("IDENT_PLACE_OBS" if obstruents_only else "IDENT_PLACE", "Or", (T,), And(tuple(act)),
                SameFeat("place", ("t", "current"), ("t", "reference")),
                kind="faithfulness", locus_side="reference")


def no_geminate() -> Decl:
    return Decl("NO_GEMINATE", "Or", (T,), Not(Feat("nuclear", "t", True)),
                Not(Feat("long", "t", True)), scope=WORD)


def ident_feats(name, feats, side=None) -> Decl:
    act = Not(Feat("nuclear", "t", True, where="reference"))
    if side is not None:
        act = And((act, _SideIs("t", side)))
    return Decl(name, "Or", (T,), act,
                And(tuple(SameFeat(f, ("t", "current"), ("t", "reference")) for f in feats)),
                kind="faithfulness", locus_side="reference")


def ident_son() -> Decl:
    return Decl("IDENT_SON", "Or", (T,), Not(Feat("nuclear", "t", True, where="reference")),
                SameFeat("son", ("t", "current"), ("t", "reference")),
                kind="faithfulness", locus_side="reference")


def max_c() -> Decl:
    return Decl("MAX_C", "Or", (T,), Not(Feat("nuclear", "t", True, where="reference")), Present("t"),
                kind="faithfulness", locus_side="reference")


def linearity() -> Decl:
    from .generator_operations import _RefBefore
    return Decl("LINEARITY", "Or", (T, NEXT_LIVE),
                And((Present("t"), Resolves("nd"))), _RefBefore("t", "nd"),
                kind="faithfulness", locus_side="reference", scope=WORD)


def nasal_place() -> Decl:
    return Decl("NASAL_PLACE", "Or", (T, NEXT_ANY_C),
                And((Feat("son", "t", 5), Resolves("a"),
                     Or_(tuple(Feat("place", "a", pl) for pl in ("lab", "cor", "dor", "pal"))))),
                SameFeat("place", ("t", "current"), ("a", "current")), scope=WORD)


def stress_to_weight() -> Decl:
    return Decl("STRESS_TO_WEIGHT", "Or", (T, NEXT_SAME_C), Feat("stressed", "t", True),
                Or_((Feat("long", "t", True), Resolves("c"))), scope=WORD)


def no_long_v() -> Decl:
    return Decl("NO_LONG_V", "Or", (T,), Feat("nuclear", "t", True),
                Not(Feat("long", "t", True)), scope=WORD)


def ident_length() -> Decl:
    return Decl("IDENT_LENGTH", "Or", (T,), Feat("nuclear", "t", True, where="reference"),
                SameFeat("long", ("t", "current"), ("t", "reference")),
                kind="faithfulness", locus_side="reference")


def no_tl() -> Decl:
    return Decl("NO_TL", "Or", (T, NEXT_SAME_C),
                And((Feat("son", "t", 1), Feat("place", "t", "cor"), Resolves("c"))),
                Not(Feat("son", "c", 6)), scope=WORD)
