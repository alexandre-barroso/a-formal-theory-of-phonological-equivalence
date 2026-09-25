from __future__ import annotations

from dataclasses import dataclass

from .guaext import ConstructedInput

EXPOSED_CELLS = ("L_ahɛ_te_ɔkpʊkɔ",)

SUBJECTS = {
    "tʊ": (("t", "ʊ"), 1, "Obiri-Yeboah & Rasin (12a) 'tU wa-tCI' calabash, subject"),
    "ahɛ": (("a", "h", "ɛ"), 2, "Obiri-Yeboah & Rasin (34a) 'ahE' knowledge, subject"),
}

VERBS = {
    "te": (("t", "e"), "Obiri-Yeboah & Rasin (34a) 'te' slaughter.pst"),
    "kwe": (("kw", "e"), "Obiri-Yeboah & Rasin (4)/(29) 'kwe' grind.hab"),
}

OBJECTS = {
    "ɔwɛ": (("ɔ", "w", "ɛ"), 2, "Obiri-Yeboah & Rasin (23)/(25) 'OwE' snake"),
    "ɔkɔtɔ": (("ɔ", "k", "ɔ", "t", "ɔ"), 3, "Obiri-Yeboah & Rasin (23)/(25) 'OkOtO' crab"),
    "ɔkpʊkɔ": (("ɔ", "kp", "ʊ", "k", "ɔ"), 3, "Obiri-Yeboah & Rasin (34a) 'OkpUkO' table"),
    "ɛhʊtɔɔ": (("ɛ", "h", "ʊ", "t", "ɔ", "ɔ"), 4, "Obiri-Yeboah & Rasin (12d)/(12e) 'EhUtOO' blood"),
}


_NUCLEI = frozenset("aɜɛeɪiɔoʊu")


def focal_junctions(words) -> tuple[int, ...]:
    starts, i = [], 0
    for w in words:
        starts.append(i)
        i += len(w)
    def last_vowel(k):
        return max(starts[k] + j for j, sg in enumerate(words[k]) if sg in _NUCLEI)
    def first_vowel(k):
        return min(starts[k] + j for j, sg in enumerate(words[k]) if sg in _NUCLEI)
    return (last_vowel(0), last_vowel(1), first_vowel(2))


@dataclass(frozen=True)
class LengthCell:
    subject: str
    verb: str
    obj: str
    v1: int
    v3: int
    inp: ConstructedInput
    opaque: str
    transparent: str


def cell(subject: str, verb: str, obj: str) -> LengthCell:
    s, v1, _ = SUBJECTS[subject]
    v, _ = VERBS[verb]
    o, v3, _ = OBJECTS[obj]
    words = (s, v, o)
    focal = focal_junctions(words)
    ci = ConstructedInput(
        id=f"L_{subject}_{verb}_{obj}",
        words=words,
        phrases=(0, 0, 0),
        focal=focal,
        note="CONSTRUCTED three-word utterance; one phonological phrase by "
             "Obiri-Yeboah & Rasin (18).  Not an attested sentence.",
    )
    plus = {"a": "ɜ", "ɛ": "e", "ɪ": "i", "ɔ": "o", "ʊ": "u"}
    opaque_segs = list(sum(words, ()))
    transparent_segs = list(opaque_segs)
    tgt, trig, first_obj = focal
    opaque_segs[tgt] = plus[opaque_segs[tgt]]
    opaque_segs[trig] = opaque_segs[first_obj]
    transparent_segs[trig] = transparent_segs[first_obj]
    return LengthCell(subject, verb, obj, v1, v3, ci,
                      "".join(opaque_segs), "".join(transparent_segs))


def battery(verb: str = "te") -> list[LengthCell]:
    return [cell(s, verb, o)
            for s in ("tʊ", "ahɛ")
            for o in ("ɔwɛ", "ɔkpʊkɔ", "ɛhʊtɔɔ")]


def prospective_battery(verb: str = "te") -> list[LengthCell]:
    return [c for c in battery(verb) if c.inp.id not in EXPOSED_CELLS]


TRANSPARENT_CONTROLS = {
    "ctrl_survive": ConstructedInput(
        id="ctrl_survive",
        words=(("t", "ʊ"), ("t", "e"), ("s", "i", "s", "i")),
        phrases=(0, 0, 0),
        focal=focal_junctions((("t", "ʊ"), ("t", "e"), ("s", "i", "s", "i"))),
        note="CONSTRUCTED control: the object begins with a consonant, so no "
             "hiatus arises and the [+ATR] trigger survives on the surface. "
             "Harmony must apply transparently and nothing else may change.",
    ),
    "ctrl_notrigger": ConstructedInput(
        id="ctrl_notrigger",
        words=(("t", "ʊ"), ("s", "ɔ"), ("a", "k", "ʊ")),
        phrases=(0, 0, 0),
        focal=focal_junctions((("t", "ʊ"), ("s", "ɔ"), ("a", "k", "ʊ"))),
        note="CONSTRUCTED control: every vowel is [-ATR]; assimilation applies "
             "at the junction and no ATR change may occur anywhere.",
    ),
}
