from __future__ import annotations

from fractions import Fraction

from .core import (ABSENT, And, Const, Ctx, Decl, Feat, InScope, NodeId, Not,
                   Or_, Positional, Present, RelDecl, Readers, Resolves,
                   SameFeat, SameSeg, Scope, Sigma, Slot, SortDecl, Struct,
                   TRUE, UNSCOPED, read)

ALPHABET = (ABSENT, "a", "ɜ", "ɛ", "e", "ɪ", "i",
            "ɔ", "o", "ʊ", "u", "j", "w")

_RAW = {
    ABSENT:   (False, False, None, None, False),
    "a":      (True,  True,  0,    False, False),
    "ɜ": (True,  True,  0,    True,  False),
    "ɛ": (True,  True,  1,    False, False),
    "e":      (True,  True,  1,    True,  False),
    "ɪ": (True,  True,  2,    False, True),
    "i":      (True,  True,  2,    True,  True),
    "ɔ": (True,  True,  3,    False, False),
    "o":      (True,  True,  3,    True,  False),
    "ʊ": (True,  True,  4,    False, True),
    "u":      (True,  True,  4,    True,  True),
    "j":      (True,  False, 2,    None,  False),
    "w":      (True,  False, 4,    None,  False),
}


def _row(present, nuclear, quality, atr, high, refined=True):
    return {
        "present": present,
        "nuclear": nuclear if (present or not refined) else "undefined",
        "high":    high if (present or not refined) else "undefined",
        "quality": quality if quality is not None else "undefined",
        "atr":     atr if atr is not None else "undefined",
    }


def make_sigma(refined: bool = True) -> Sigma:
    feats = {seg: _row(*vals, refined=refined) for seg, vals in _RAW.items()}
    default = {"present": True, "nuclear": False, "high": False,
               "quality": "undefined", "atr": "undefined"}
    sorts = {
        "Or":  SortDecl("Or", "total", tier="seg",
                        comment="lexical origin; absence is one of its values"),
        "Rel": SortDecl("Rel", "derived", tier="seg",
                        comment="an instance of the succession relation"),
    }
    rels = {"succ": RelDecl("succ", "succession", "Or", "Or", "Rel")}
    return Sigma(sorts=sorts, relations=rels, features=feats,
                 default_features=default, domains=("word", "phrase"))


NEXT_WORD = Scope(same=("phrase",), delta={"word": 1}, label="next_word_same_phrase")
PREV_WORD = Scope(same=("phrase",), delta={"word": -1}, label="prev_word_same_phrase")
PHRASE = Scope(same=("phrase",), label="same_phrase")
LATER_IN_PHRASE = Scope(same=("phrase",), min_delta={"word": 1},
                        label="same_phrase_strictly_later_word")

ANCHOR = Slot("t", "Or", "subject", kind="anchor")


def step(name, sort, scope, direction, filt, policy, role):
    return Slot(name, sort, role, kind="step", relation="succ", scope=scope,
                direction=direction, filter=filt, policy=policy)


def search(name, scope, direction, filt, role="trigger"):
    return Slot(name, "Or", role, kind="search", relation="succ", scope=scope,
                direction=direction, filter=filt)


NUC = Feat("nuclear", "t", True)
NONHIGH = Not(Feat("high", "t", True))

MAX = Decl("MAX", "Or", (ANCHOR,), TRUE, Present("t"), kind="faithfulness")
IDENT_ATR = Decl("IDENT_ATR", "Or", (ANCHOR,), TRUE,
                 SameFeat("atr", ("t", "current"), ("t", "reference")),
                 kind="faithfulness")
IDENT_QUAL = Decl("IDENT_QUAL", "Or", (ANCHOR,), TRUE,
                  SameFeat("quality", ("t", "current"), ("t", "reference")),
                  kind="faithfulness")
IDENT_NUC = Decl("IDENT_NUC", "Or", (ANCHOR,), TRUE,
                 SameFeat("nuclear", ("t", "current"), ("t", "reference")),
                 kind="faithfulness")
INITIAL_FEATURE = Decl(
    "INITIAL_FEATURE", "Or", (ANCHOR,),
    And((Feat("nuclear", "t", True, where="reference"),
         Positional("first_of", "t", "word"))),
    And((SameFeat("quality", ("t", "current"), ("t", "reference")),
         Or_((Not(Feat("nuclear", "t", True)),
              SameFeat("atr", ("t", "current"), ("t", "reference")))))),
    kind="faithfulness")


def harmony():
    src = search("src", LATER_IN_PHRASE, +1, "nuclear", role="trigger")
    return Decl("H", "Or", (ANCHOR, src),
                And((NUC, Positional("last_live_of", "t", "word", "nuclear"),
                     Resolves("src"), InScope("src", LATER_IN_PHRASE),
                     Feat("atr", "src", True))),
                Feat("atr", "t", True), scope=LATER_IN_PHRASE)


def agree_baseline():
    guarded = step("n_guarded", "Rel", NEXT_WORD, +1, None, "dynamic", "trigger")
    free = step("n_free", "Rel", UNSCOPED, +1, None, "dynamic", "subject")
    return Decl("A", "Or", (ANCHOR, guarded, free),
                And((NUC, NONHIGH, Resolves("n_guarded"),
                     Feat("nuclear", "n_guarded", True),
                     Not(Feat("high", "n_guarded", True)))),
                Or_((Not(Present("t")),
                     SameSeg(("t", "current"), ("n_free", "current")))),
                scope=NEXT_WORD, definedness_override=Const(True))


def agree_typed(policy="dynamic", scope=NEXT_WORD, filt=None, filter_mode="skip"):
    partner = Slot("n", "Rel", "subject", kind="step", relation="succ",
                   scope=scope, direction=+1, filter=filt, policy=policy,
                   filter_mode=filter_mode)
    return Decl("A", "Or", (ANCHOR, partner),
                And((NUC, NONHIGH, Resolves("n"),
                     Feat("nuclear", "n", True), Not(Feat("high", "n", True)))),
                Or_((Not(Present("t")),
                     SameSeg(("t", "current"), ("n", "current")))),
                scope=scope)


def glide(policy="dynamic"):
    right = step("nr", "Rel", NEXT_WORD, +1, None, policy, "trigger")
    left = step("nl", "Rel", PREV_WORD, -1, None, policy, "trigger")
    nb = Or_((And((Resolves("nr"), Feat("nuclear", "nr", True),
                   Not(Feat("high", "nr", True)))),
              And((Resolves("nl"), Feat("nuclear", "nl", True),
                   Not(Feat("high", "nl", True))))))
    return Decl("GL", "Or", (ANCHOR, right, left),
                And((NUC, Feat("high", "t", True), nb)),
                Or_((Not(Present("t")), Not(Feat("nuclear", "t", True)))),
                scope=PHRASE)


def deletion(policy="dynamic"):
    left = step("p", "Rel", PREV_WORD, -1, None, policy, "trigger")
    return Decl("D", "Or", (ANCHOR, left),
                And((NUC, Feat("high", "t", True), Resolves("p"),
                     Feat("nuclear", "p", True), Feat("high", "p", True))),
                Not(Present("t")), scope=PREV_WORD)


SCHEMA_ORDER = ("MAX", "IDENT_ATR", "IDENT_QUAL", "IDENT_NUC",
                "H", "A", "GL", "D", "INITIAL_FEATURE")
WEIGHTS = {"MAX": 20, "IDENT_ATR": 1, "IDENT_QUAL": 1, "IDENT_NUC": 2,
           "H": 4, "A": 8, "GL": 8, "D": 24, "INITIAL_FEATURE": 1}
LAMBDA = Fraction(1, 8)


def declarations(a_variant="baseline", policy="dynamic", scope=NEXT_WORD,
                 filt=None, filter_mode="skip"):
    a = (agree_baseline() if a_variant == "baseline"
         else agree_typed(policy, scope, filt, filter_mode))
    gp = "dynamic" if a_variant == "baseline" else policy
    return {"MAX": MAX, "IDENT_ATR": IDENT_ATR, "IDENT_QUAL": IDENT_QUAL,
            "IDENT_NUC": IDENT_NUC, "H": harmony(), "A": a, "GL": glide(gp),
            "D": deletion(gp), "INITIAL_FEATURE": INITIAL_FEATURE}


def struct_from_segments(segments, words, phrase_of_word) -> Struct:
    nodes = tuple(NodeId("Or", "lex", i) for i in range(len(segments)))
    real = {n: segments[i] for i, n in enumerate(nodes)}
    dom = {n: {"word": words[i], "phrase": phrase_of_word[words[i]]}
           for i, n in enumerate(nodes)}
    return Struct(order={"seg": nodes}, real=real, dom=dom)
