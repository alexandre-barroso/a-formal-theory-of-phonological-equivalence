from __future__ import annotations

from typing import Mapping

from .lang import (And, Const, Declaration, Feat, InScope, Not, Or,
                   OriginRecord, Positional, Present, Resolves, SameFeat,
                   SameSeg, Scope, Signature, SlotDecl, UNSCOPED)

NEXT_WORD = Scope(same_phrase=True, word_delta=1, label="next_word_same_phrase")
PREV_WORD = Scope(same_phrase=True, word_delta=-1, label="previous_word_same_phrase")
PHRASE = Scope(same_phrase=True, word_delta=None, label="same_phrase")
LATER_IN_PHRASE = Scope(same_phrase=True, min_word_delta=1,
                        label="same_phrase_strictly_later_word")


def signature_from_spec(spec: Mapping, record: Mapping) -> Signature:
    origins = []
    idx = 0
    for w, word in enumerate(record["words"]):
        phrase = record["phrases"][w]
        for seg in word:
            origins.append(OriginRecord(index=idx, word=w, phrase=phrase, reference=seg))
            idx += 1
    features: dict[str, dict[str, object]] = {}
    for seg, row in spec["features"].items():
        present = bool(row["present"])
        features[seg] = {
            "present": present,
            "nuclear": row["nuclear"] if present else "undefined",
            "high": row["high"] if present else "undefined",
            "quality": row["quality"] if row["quality"] is not None else "undefined",
            "atr": row["atr"] if row["atr"] is not None else "undefined",
        }
    d = spec["default_segment_features"]
    default = {
        "present": bool(d["present"]),
        "nuclear": d["nuclear"],
        "high": d["high"],
        "quality": "undefined",
        "atr": "undefined",
    }
    return Signature(origins=tuple(origins), features=features,
                     default_features=default, absent=spec["alphabet"][0])


ANCHOR = SlotDecl(name="t", kind="anchor", role="subject")


def relatum(name: str, scope: Scope, direction: int, filter: str | None,
            policy: str, role: str = "subject") -> SlotDecl:
    return SlotDecl(name=name, kind="relatum", role=role, scope=scope,
                    direction=direction, filter=filter, policy=policy)


def searched(name: str, scope: Scope, direction: int, filter: str | None,
             role: str = "trigger") -> SlotDecl:
    return SlotDecl(name=name, kind="searched", role=role, scope=scope,
                    direction=direction, filter=filter)


NUC = Feat("nuclear", "t", True)
NONHIGH = Not(Feat("high", "t", True))


MAX = Declaration(
    name="MAX",
    slots=(ANCHOR,),
    activation=Const(True),
    consequence=Present("t"),
)

IDENT_ATR = Declaration(
    name="IDENT_ATR",
    slots=(ANCHOR,),
    activation=Const(True),
    consequence=SameFeat("atr", ("t", "current"), ("t", "reference")),
)

IDENT_QUAL = Declaration(
    name="IDENT_QUAL",
    slots=(ANCHOR,),
    activation=Const(True),
    consequence=SameFeat("quality", ("t", "current"), ("t", "reference")),
)

IDENT_NUC = Declaration(
    name="IDENT_NUC",
    slots=(ANCHOR,),
    activation=Const(True),
    consequence=SameFeat("nuclear", ("t", "current"), ("t", "reference")),
)

INITIAL_FEATURE = Declaration(
    name="INITIAL_FEATURE",
    slots=(ANCHOR,),
    activation=And((Feat("nuclear", "t", True, where="reference"),
                    Positional("first_of_word", "t"))),
    consequence=And((
        SameFeat("quality", ("t", "current"), ("t", "reference")),
        Or((Not(Feat("nuclear", "t", True)),
            SameFeat("atr", ("t", "current"), ("t", "reference")))),
    )),
)


def harmony() -> Declaration:
    src = searched("src", LATER_IN_PHRASE, +1, "nuclear", role="trigger")
    return Declaration(
        name="H",
        slots=(ANCHOR, src),
        scope=LATER_IN_PHRASE,
        activation=And((NUC,
                        Positional("last_nucleus_of_word", "t"),
                        Resolves("src"),
                        InScope("src", LATER_IN_PHRASE),
                        Feat("atr", "src", True))),
        consequence=Feat("atr", "t", True),
    )


def agree_baseline() -> Declaration:
    guarded = relatum("n_guarded", NEXT_WORD, +1, None, "dynamic", role="trigger")
    free = relatum("n_free", UNSCOPED, +1, None, "dynamic", role="subject")
    return Declaration(
        name="A",
        slots=(ANCHOR, guarded, free),
        scope=NEXT_WORD,
        activation=And((NUC, NONHIGH,
                        Resolves("n_guarded"),
                        Feat("nuclear", "n_guarded", True),
                        Not(Feat("high", "n_guarded", True)))),
        consequence=Or((Not(Present("t")),
                        SameSeg(("t", "current"), ("n_free", "current")))),
        definedness_override=Const(True),
    )


def agree_typed(policy: str = "dynamic", scope: Scope = NEXT_WORD,
                filter: str | None = None) -> Declaration:
    partner = relatum("n", scope, +1, filter, policy, role="subject")
    return Declaration(
        name="A",
        slots=(ANCHOR, partner),
        scope=scope,
        activation=And((NUC, NONHIGH,
                        Resolves("n"),
                        Feat("nuclear", "n", True),
                        Not(Feat("high", "n", True)))),
        consequence=Or((Not(Present("t")),
                        SameSeg(("t", "current"), ("n", "current")))),
    )


def glide(policy: str = "dynamic") -> Declaration:
    right = relatum("nr", NEXT_WORD, +1, None, policy, role="trigger")
    left = relatum("nl", PREV_WORD, -1, None, policy, role="trigger")
    neighbour = Or((
        And((Resolves("nr"), Feat("nuclear", "nr", True),
             Not(Feat("high", "nr", True)))),
        And((Resolves("nl"), Feat("nuclear", "nl", True),
             Not(Feat("high", "nl", True)))),
    ))
    return Declaration(
        name="GL",
        slots=(ANCHOR, right, left),
        scope=PHRASE,
        activation=And((NUC, Feat("high", "t", True), neighbour)),
        consequence=Or((Not(Present("t")), Not(Feat("nuclear", "t", True)))),
    )


def deletion(policy: str = "dynamic") -> Declaration:
    left = relatum("p", PREV_WORD, -1, None, policy, role="trigger")
    return Declaration(
        name="D",
        slots=(ANCHOR, left),
        scope=PREV_WORD,
        activation=And((NUC, Feat("high", "t", True),
                        Resolves("p"),
                        Feat("nuclear", "p", True),
                        Feat("high", "p", True))),
        consequence=Not(Present("t")),
    )


SCHEMA_ORDER = ("MAX", "IDENT_ATR", "IDENT_QUAL", "IDENT_NUC",
                "H", "A", "GL", "D", "INITIAL_FEATURE")


def declarations(a_variant: str = "baseline", policy: str = "dynamic",
                 scope: Scope = NEXT_WORD,
                 filter: str | None = None) -> dict[str, Declaration]:
    a = agree_baseline() if a_variant == "baseline" else agree_typed(policy, scope, filter)
    gl_policy = "dynamic" if a_variant == "baseline" else policy
    return {
        "MAX": MAX,
        "IDENT_ATR": IDENT_ATR,
        "IDENT_QUAL": IDENT_QUAL,
        "IDENT_NUC": IDENT_NUC,
        "H": harmony(),
        "A": a,
        "GL": glide(gl_policy),
        "D": deletion(gl_policy),
        "INITIAL_FEATURE": INITIAL_FEATURE,
    }
