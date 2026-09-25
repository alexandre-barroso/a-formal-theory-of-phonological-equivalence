from __future__ import annotations

from dataclasses import dataclass
from typing import Sequence

from phonological_opacity.fragments.gua import GuaFragment

_ATR_PAIR = {0: ("a", "ɜ"), 1: ("ɛ", "e"), 2: ("ɪ", "i"), 3: ("ɔ", "o"), 4: ("ʊ", "u")}
_GLIDE = {2: "j", 4: "w"}

PHRASING_NOTE = (
    "Obiri-Yeboah & Rasin (18): three-word utterances form one phonological "
    "phrase (www); four-word utterances are parsed into two binary phrases "
    "(ww)(ww).  Longer utterances are UNRESOLVED in the source."
)


def phrasing(n_words: int) -> tuple[int, ...]:
    if n_words <= 3:
        return tuple(0 for _ in range(n_words))
    if n_words == 4:
        return (0, 0, 1, 1)
    raise ValueError(PHRASING_NOTE)


@dataclass(frozen=True)
class RuleSerial:

    frag: GuaFragment

    def _f(self, seg: str) -> dict:
        return self.frag.ft(seg)

    def _vowels(self, segs: Sequence[str]) -> list[int]:
        return [q for q in range(self.frag.n)
                if self._f(segs[q])["present"] and self._f(segs[q])["nuclear"]]

    def _present(self, segs: Sequence[str]) -> list[int]:
        return [q for q in range(self.frag.n) if self._f(segs[q])["present"]]

    def harmony(self, segs: Sequence[str]) -> list[str]:
        out = list(segs)
        vs = self._vowels(segs)
        origins = self.frag.origins
        for a, b in zip(vs, vs[1:]):
            if origins[b].word != origins[a].word + 1:
                continue
            if origins[b].phrase != origins[a].phrase:
                continue
            fa, fb = self._f(segs[a]), self._f(segs[b])
            if fb["atr"] is True and fa["atr"] is False and fa["quality"] is not None:
                out[a] = _ATR_PAIR[fa["quality"]][1]
        return out

    def hiatus(self, segs: Sequence[str]) -> list[str]:
        out = list(segs)
        pres = self._present(segs)
        origins = self.frag.origins
        for a, b in zip(pres, pres[1:]):
            if origins[b].word != origins[a].word + 1:
                continue
            if origins[b].phrase != origins[a].phrase:
                continue
            fa, fb = self._f(segs[a]), self._f(segs[b])
            if not (fa["nuclear"] and fb["nuclear"]):
                continue
            ha, hb = bool(fa["high"]), bool(fb["high"])
            if ha and hb:
                out[b] = "∅"
            elif ha and not hb:
                out[a] = _GLIDE[fa["quality"]]
            elif hb and not ha:
                out[b] = _GLIDE[fb["quality"]]
            else:
                out[a] = segs[b]
        return out

    def derive(self, segs: Sequence[str] | None = None) -> list[str]:
        base = list(self.frag.reference) if segs is None else list(segs)
        return self.hiatus(self.harmony(base))

    def output(self, segs: Sequence[str] | None = None) -> str:
        return self.frag.observe(self.derive(segs))
