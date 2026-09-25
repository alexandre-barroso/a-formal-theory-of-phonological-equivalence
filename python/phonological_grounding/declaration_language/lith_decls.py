from __future__ import annotations

from fractions import Fraction
from typing import Mapping

from .lang import (And, Const, Declaration, Feat, Not, Or, OriginRecord,
                   Present, Readers, Resolves, SameFeat, Scope, Signature,
                   SlotDecl, read)

WORD = Scope(same_phrase=True, word_delta=0, label="same_word")

_CONS = {
    "p": {"present": True, "obstruent": True, "voi": 0, "place": "lab"},
    "b": {"present": True, "obstruent": True, "voi": 1, "place": "lab"},
    "t": {"present": True, "obstruent": True, "voi": 0, "place": "cor"},
    "d": {"present": True, "obstruent": True, "voi": 1, "place": "cor"},
    "k": {"present": True, "obstruent": True, "voi": 0, "place": "dor"},
    "g": {"present": True, "obstruent": True, "voi": 1, "place": "dor"},
    "i": {"present": True, "obstruent": False, "voi": 1, "place": "vowel"},
    "∅": {"present": False, "obstruent": "undefined", "voi": "undefined",
               "place": "undefined"},
}

SIGNATURE = Signature(
    origins=(OriginRecord(0, 0, 0, ""), OriginRecord(1, 0, 0, "∅"),
             OriginRecord(2, 0, 0, "")),
    features=_CONS,
    default_features={"present": True, "obstruent": "undefined",
                      "voi": "undefined", "place": "undefined"},
)

ANCHOR = SlotDecl(name="t", kind="anchor", role="subject")


def _partner(policy: str, filter_mode: str, name: str = "n") -> SlotDecl:
    return SlotDecl(name=name, kind="relatum", role="subject", scope=WORD,
                    direction=1, filter="obstruent", policy=policy,
                    filter_mode=filter_mode)


def agree(policy: str = "witness", filter_mode: str = "stop",
          override=None) -> Declaration:
    return Declaration(
        name="A", slots=(ANCHOR, _partner(policy, filter_mode)), scope=WORD,
        activation=Resolves("n"),
        consequence=SameFeat("voi", ("t", "current"), ("n", "current")),
        definedness_override=override,
    )


def nogem(policy: str = "witness", filter_mode: str = "stop",
          override=None) -> Declaration:
    return Declaration(
        name="N", slots=(ANCHOR, _partner(policy, filter_mode)), scope=WORD,
        activation=Resolves("n"),
        consequence=Not(And((SameFeat("place", ("t", "current"), ("n", "current")),
                             SameFeat("voi", ("t", "current"), ("n", "current"))))),
        definedness_override=override,
    )


def agree_surviving_origins() -> Declaration:
    return Declaration(
        name="A",
        slots=(ANCHOR,
               SlotDecl("n_adj", "relatum", "trigger", WORD, 1, "obstruent",
                        "witness", "stop"),
               _partner("origin_bound", "skip", "n_org")),
        scope=WORD,
        activation=Resolves("n_adj"),
        consequence=SameFeat("voi", ("t", "current"), ("n_org", "current")),
        definedness_override=Const(True),
    )


def nogem_surviving_origins() -> Declaration:
    return Declaration(
        name="N",
        slots=(ANCHOR,
               SlotDecl("n_adj", "relatum", "trigger", WORD, 1, "obstruent",
                        "witness", "stop"),
               _partner("origin_bound", "skip", "n_org")),
        scope=WORD,
        activation=Resolves("n_adj"),
        consequence=Not(And((SameFeat("place", ("t", "current"), ("n_org", "current")),
                             SameFeat("voi", ("t", "current"), ("n_org", "current"))))),
        definedness_override=Const(True),
    )


IDENT_VOI = Declaration(
    name="IDENT", slots=(ANCHOR,), activation=Const(True),
    consequence=SameFeat("voi", ("t", "current"), ("t", "reference")),
)

DEP = Declaration(
    name="DEP", slots=(ANCHOR,), activation=Not(Present("t", where="reference")),
    consequence=Not(Present("t")),
)


def state_of(record: Mapping, j: int) -> tuple[str, ...]:
    x, y, z = j // 4, (j // 2) % 2, j % 2
    return (record["prefix"][x], "i" if z else "∅", record["stem"][y])


def reference_of(record: Mapping) -> tuple[str, ...]:
    x, y, z = record["reference_bits"]
    return (record["prefix"][x], "i" if z else "∅", record["stem"][y])


def readers(record: Mapping, j: int, a_decl: Declaration,
            n_decl: Declaration) -> dict[str, Readers]:
    ref = reference_of(record)
    st = state_of(record, j)
    return {"A": read(SIGNATURE, ref, st, a_decl, 0),
            "N": read(SIGNATURE, ref, st, n_decl, 0)}


def coefficients(record: Mapping, j: int, a_decl: Declaration,
                 n_decl: Declaration) -> tuple[int, int, int, int, int, int, int]:
    ref = reference_of(record)
    st = state_of(record, j)
    cur = readers(record, j, a_decl, n_decl)
    base = readers(record, 4 * record["reference_bits"][0]
                   + 2 * record["reference_bits"][1]
                   + record["reference_bits"][2], a_decl, n_decl)
    c = int(read(SIGNATURE, ref, st, IDENT_VOI, 0).marked)
    r = int(read(SIGNATURE, ref, st, IDENT_VOI, 2).marked)
    d = int(read(SIGNATURE, ref, st, DEP, 1).marked)
    out = [c, r, d]
    for k in ("A", "N"):
        a_ref = base[k].marked
        out.append(cur[k].pressure if a_ref else 0)
        out.append(0 if a_ref else cur[k].marked)
    return tuple(out)


def score(coeffs, weights: Mapping, lam) -> Fraction:
    c, r, d, ao, an, no, nn = coeffs
    lam = Fraction(lam)
    return (Fraction(weights["c"]) * c + Fraction(weights["r"]) * r
            + Fraction(weights["d"]) * d
            + Fraction(weights["a"]) * (ao + lam * an)
            + Fraction(weights["n"]) * (no + lam * nn))


POLICIES = {
    "witness": ("witness", "stop"),
    "dynamic_stop": ("dynamic", "stop"),
    "dynamic_skip": ("dynamic", "skip"),
    "origin_bound": ("origin_bound", "skip"),
}
