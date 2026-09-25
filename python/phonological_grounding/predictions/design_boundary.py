from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from itertools import product
from typing import Iterable, Sequence

from phonological_opacity.fragments.gua import GuaFragment

from .guaext import ConstructedInput, fragment
from .ruleserial import RuleSerial, phrasing

POOL: dict[str, tuple[tuple[str, ...], str]] = {
    "anɛ":    (("a", "n", "ɛ"), "O&R (16a-c) 'aNE' man, subject"),
    "a":      (("a",), "O&R (16c)/(17a-b) 'a' determiner"),
    "kubi":   (("k", "u", "b", "i"), "O&R (16c)/(17a) 'kubi' cut.pst"),
    "tei":    (("t", "e", "i"), "O&R (16c) 'teI' food"),
    "kɪtɛ":   (("k", "ɪ", "t", "ɛ"), "O&R (16b)/(17c-d) 'kItE' hold.pst"),
    "bokiti": (("b", "o", "k", "i", "t", "i"), "O&R (16b)/(17c-d) 'bokiti' bucket"),
    "kɔɔ":    (("k", "ɔ", "ɔ"), "O&R (16b)/(17c) 'kOO' red"),
    "mɪ":     (("m", "ɪ"), "O&R (16a) 'mI' 1poss"),
    "sisi":   (("s", "i", "s", "i"), "O&R (16a) 'sisi' sister"),
    "sɔ":     (("s", "ɔ"), "O&R (16a)/(12) 'sO' buy.pst"),
    "atʃɔ":   (("a", "tʃ", "ɔ"), "O&R (16a) 'atCO' hoe"),
    "njɛɛ":   (("n", "j", "ɛ", "ɛ"), "O&R (28b)/(46b)/(47b) 'njEE' 1sg.say.pst"),
    "kpʊtɔ":  (("k", "p", "ʊ", "t", "ɔ"), "O&R (28c-d) 'kpUtO' frog"),
    "akʊ":    (("a", "k", "ʊ"), "O&R (28a-d) 'akU' one"),
    "bɛ":     (("b", "ɛ"), "O&R (28c-d)/(12d-e) 'bE' coming"),
    "atʃɪ":   (("a", "tʃ", "ɪ"), "O&R (46a-c) 'atCI' sponge"),
    "wure":   (("w", "u", "r", "e"), "O&R (46a-c) 'wure' finish.pst"),
    "nte":    (("n", "t", "e"), "O&R (46a,c) 'nte' quickly"),
    "ɔtsʊ":   (("ɔ", "t", "s", "ʊ"), "O&R (47a-c)/(32a,d) 'OtsU' cheek"),
    "seli":   (("s", "e", "l", "i"), "O&R (47a-c) 'seli' peel.pst"),
    "ɪsɛ":    (("ɪ", "s", "ɛ"), "O&R (21b)/(23) 'IsE' grass"),
    "wʊsʊ":   (("w", "ʊ", "s", "ʊ"), "O&R (21b)/(23) 'wUsU' shake"),
    "ɛbɪ":    (("ɛ", "b", "ɪ"), "O&R (23) 'EbI' palm tree"),
    "ohili":  (("o", "h", "i", "l", "i"), "O&R (34b) 'ohili' game"),
    "ibie":   (("i", "b", "i", "e"), "O&R (37c) 'ibie' market"),
    "iku":    (("i", "k", "u"), "O&R (38a) 'iku' group"),
}


@dataclass(frozen=True)
class BoundaryInput:
    id: str
    words: tuple[str, ...]
    inp: ConstructedInput
    phrase1_origins: tuple[int, ...]


def _vowel_positions(word: tuple[str, ...], spec_ft) -> list[int]:
    return [i for i, s in enumerate(word) if spec_ft(s)["nuclear"]]


def build(words: Sequence[str], focal_policy: str = "junctions") -> BoundaryInput:
    segs: list[str] = []
    word_of: list[int] = []
    for w, name in enumerate(words):
        for s in POOL[name][0]:
            segs.append(s)
            word_of.append(w)
    ph = phrasing(len(words))
    probe = fragment(ConstructedInput("probe", tuple(POOL[n][0] for n in words), ph, (0,)))
    nuclear = [q for q in range(len(segs)) if probe.ft(segs[q])["nuclear"]]
    last_of: dict[int, int] = {}
    first_of: dict[int, int] = {}
    for q in nuclear:
        w = word_of[q]
        last_of[w] = q
        first_of.setdefault(w, q)
    focal = set()
    for w in range(len(words) - 1):
        if w in last_of:
            focal.add(last_of[w])
        if (w + 1) in first_of:
            focal.add(first_of[w + 1])
    ci = ConstructedInput(
        id="B_" + "_".join(words),
        words=tuple(POOL[n][0] for n in words),
        phrases=ph,
        focal=tuple(sorted(focal)),
        note="CONSTRUCTED four-word utterance under Obiri-Yeboah & Rasin (18) "
             "(ww)(ww) phrasing.  Not an attested sentence.",
    )
    p1 = tuple(q for q in range(len(segs)) if ph[word_of[q]] == 0)
    return BoundaryInput(ci.id, tuple(words), ci, p1)


def phrase1_projection(frag: GuaFragment, index: int, p1: Sequence[int]) -> str:
    segs = frag.candidate(index)
    return "".join(segs[q] for q in p1 if frag.ft(segs[q])["present"])


def retained_phrase1_outputs(bi: BoundaryInput) -> dict:
    frag = fragment(bi.inp)
    r = frag.evaluate()
    proj = sorted({phrase1_projection(frag, i, bi.phrase1_origins) for i in r["minima"]})
    return {
        "id": bi.id,
        "states": r["states"],
        "minimum8": r["minimum8"],
        "minima": r["minima"][:8],
        "n_minima": len(r["minima"]),
        "phrase1_projections": proj,
        "full_output": sorted({frag.observe(frag.candidate(i)) for i in r["minima"]}),
        "rule_serial": RuleSerial(frag).output(),
    }


def sweep(first_phrase: Sequence[str], second_phrases: Iterable[Sequence[str]]) -> dict:
    rows = []
    for second in second_phrases:
        bi = build(tuple(first_phrase) + tuple(second))
        rows.append(retained_phrase1_outputs(bi))
    projections = {tuple(r["phrase1_projections"]) for r in rows}
    return {
        "first_phrase": list(first_phrase),
        "variants": rows,
        "phrase1_invariant": len(projections) == 1,
        "distinct_phrase1_projections": sorted(list(p) for p in projections),
    }
