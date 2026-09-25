from __future__ import annotations

from fractions import Fraction

from phonological_opacity.fragments.gua import GuaFragment, load_spec

from .guaext import ConstructedInput, fragment, named_fragment
from .sharedactivity import POSTER_WEIGHTS, SharedActivityModel

SPEC = load_spec()


TEBAY_12 = ConstructedInput(
    id="tebay12",
    words=(("t", "ʊ"), ("h", "e")),
    phrases=(0, 0),
    focal=(1, 3),
    note="Tebay (2025) item (12); Obiri-Yeboah & Rasin (12a) 'tU ... he' calabash fall.pst",
)

TEBAY_13 = ConstructedInput(
    id="tebay13",
    words=(("kp", "o"), ("ɛ", "s", "ɛ")),
    phrases=(0, 0),
    focal=(1, 2, 4),
    note="Tebay (2025) item (13); Obiri-Yeboah & Rasin (25) o/E cell 'kpo EsE'",
)


TEBAY_13M = ConstructedInput(
    id="tebay13m",
    words=(("kp", "o"), ("ɛ", "s", "ɛ")),
    phrases=(0, 0),
    focal=(1, 2),
    note="Tebay (2025) item (13) with a junction-matched focal set",
)


def tebay_rows() -> list[dict]:
    out: list[dict] = []

    f12 = fragment(TEBAY_12)
    m12 = SharedActivityModel(f12)
    for label, segs, act, cells, poster in [
        ("12a", ("t", "ʊ", "h", "e"), {1: Fraction(1), 3: Fraction(1)},
         {"MARK_ATR": Fraction(1)}, Fraction(23)),
        ("12b", ("t", "u", "h", "e"), {1: Fraction(1, 2), 3: Fraction(1, 2)},
         {"ID_MINUS_ATR": Fraction(1)}, Fraction(1)),
    ]:
        out.append(_row(m12, label, segs, act, cells, poster))

    f13 = fragment(TEBAY_13)
    m13 = SharedActivityModel(f13)
    out.append(_row(m13, "13a", ("kp", "o", "ɛ", "s", "ɛ"),
                    {1: Fraction(1), 2: Fraction(1, 2), 4: Fraction(1, 2)},
                    {"MARK_HIA": Fraction(1)}, Fraction(22)))
    out.append(_row(m13, "13b", ("kp", "ɛ", "ɛ", "s", "ɛ"),
                    {1: Fraction(1, 3), 2: Fraction(1, 3), 4: Fraction(1, 3)},
                    {"ID_PLUS_ATR_G": Fraction(2, 3)}, Fraction(14),
                    poster_printed=Fraction(7), repair="(13b) prints 1/3 for Id(+A)g; (11) gives 1-1/3"))

    f14 = named_fragment("G34a")
    m14 = SharedActivityModel(f14)
    third = {5: Fraction(1, 3), 8: Fraction(1, 3), 10: Fraction(1, 3)}
    out.append(_row(m14, "14a", _g34a("ɛ", "e", "ɔ"),
                    {0: Fraction(1, 2), 2: Fraction(1, 2), 4: Fraction(1), **third},
                    {"MARK_ATR": Fraction(1), "MARK_HIA": Fraction(1)}, Fraction(45)))
    out.append(_row(m14, "14b", _g34a("e", "e", "ɔ"),
                    {0: Fraction(1), 2: Fraction(1, 2), 4: Fraction(1, 2), **third},
                    {"MARK_HIA": Fraction(1), "ID_MINUS_ATR": Fraction(1)}, Fraction(23)))
    sixth = {q: Fraction(1, 6) for q in (0, 2, 4, 5, 8, 10)}
    out.append(_row(m14, "14c", _g34a("ɛ", "ɔ", "ɔ"), sixth,
                    {"ID_PLUS_ATR_G": Fraction(5, 6)}, Fraction(35, 2)))
    quarter = {4: Fraction(1, 4), 5: Fraction(1, 4), 8: Fraction(1, 4), 10: Fraction(1, 4)}
    out.append(_row(m14, "14d", _g34a("e", "ɔ", "ɔ"),
                    {0: Fraction(1), 2: Fraction(1), **quarter},
                    {"ID_PLUS_ATR_G": Fraction(3, 4), "ID_MINUS_ATR": Fraction(1)}, Fraction(67, 4)))
    return out


def _g34a(x: str, y: str, z: str) -> tuple[str, ...]:
    frag = named_fragment("G34a")
    segs = list(frag.reference)
    for q, s in zip(frag.focal, (x, y, z)):
        segs[q] = s
    return tuple(segs)


def _row(model, label, segs, activities, cells, poster, poster_printed=None, repair=""):
    act = model.activities(segs)
    vio = model.violations(segs)
    from .sharedactivity import CONSTRAINTS as POSTER_COLUMNS
    got = {k: v for k, v in vio.items() if v and k in POSTER_COLUMNS}
    repair_cells = {k: str(v) for k, v in vio.items()
                    if v and k not in POSTER_COLUMNS}
    pen = model.penalty(segs, POSTER_WEIGHTS)
    return {
        "row": label,
        "segments": list(segs),
        "activities_match": all(act.get(q) == v for q, v in activities.items())
        and len(act) == len(activities),
        "activities": {q: str(v) for q, v in sorted(act.items())},
        "cells_match": got == {k: v for k, v in cells.items() if v},
        "cells": {k: str(v) for k, v in sorted(got.items())},
        "repair_cells_not_displayed_by_the_source": repair_cells,
        "penalty": str(pen),
        "poster_abs_H": str(poster),
        "penalty_match": pen == poster,
        "poster_printed_abs_H": None if poster_printed is None else str(poster_printed),
        "repair": repair,
    }


OR_ITEMS = {
    "G34a": "Obiri-Yeboah & Rasin (34a) counterbleeding, assimilation",
    "G34b": "Obiri-Yeboah & Rasin (34b)/(36) countershifting, assimilation",
    "N7": "Obiri-Yeboah & Rasin note 7, transparent harmony across a lexical glide",
    "G37c": "Obiri-Yeboah & Rasin (37c) self-counterfeeding, V2 gliding",
    "C24ei": "Obiri-Yeboah & Rasin (24) e/i cell, glide formation",
    "OR38": "Obiri-Yeboah & Rasin (38a) self-counterfeeding, deletion",
    "C21b": "Obiri-Yeboah & Rasin (21b)/(23), deletion",
    "C23UE": "Obiri-Yeboah & Rasin (23) U/E cell, glide formation",
}


def retained_regression() -> list[dict]:
    out = []
    for iid in OR_ITEMS:
        frag = GuaFragment(SPEC, iid)
        r = frag.evaluate()
        expect = SPEC["expected_regression"]["per_input"][iid]
        out.append({
            "input": iid,
            "source": OR_ITEMS[iid],
            "states": r["states"],
            "fibre": r["fiber"],
            "minima": r["minima"],
            "minimum8": r["minimum8"],
            "exclusively_correct": r["exclusively_correct"],
            "matches_exports": (r["fiber"] == expect["fiber"]
                                 and r["minima"] == expect["minima"]
                                 and r["minimum8"] == expect["minimum8"]),
        })
    return out
