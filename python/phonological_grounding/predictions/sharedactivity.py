from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import Sequence

from phonological_opacity.fragments.gua import GuaFragment

from .exact import LinForm

CONSTRAINTS = ("MARK_ATR", "MARK_HIA", "ID_INIT_V", "ID_PLUS_ATR_G", "ID_MINUS_ATR")

REPAIR_FAITHFULNESS = ("ID_QUAL", "ID_HIGH", "MAX", "ID_NUC", "ID_PLUS_ATR")
REPAIRED_CONSTRAINTS = CONSTRAINTS + REPAIR_FAITHFULNESS

REPAIR_NOTE = (
    "The poster displays five constraints and eight candidates.  Over a matched "
    "focal product those five select candidates the source never displays, so "
    "the reconstruction cannot reproduce its own source's winner and must be "
    "repaired before any failure of it means anything.  Two gaps, both found by "
    "exhaustive search, not by inspection:\n"
    "  (i) nothing protects the vowel quality of a non-word-initial nucleus, so "
    "      'ahE te ...' -> 'ahE t3 ...' is free;\n"
    "  (ii) `*[-h]i#[-h]j` is satisfied by making the first hiatus member HIGH, "
    "      so 'te' -> 'ti' escapes the constraint while keeping [+ATR] and "
    "      therefore beats the poster's own winner by (3/4)*w_g;\n"
    "  (iii) Id(+A)g charges 1 - x, and an UNSHARED lost [+ATR] vowel has "
    "      x = 1, so losing [+ATR] in isolation is FREE.  In the source's own "
    "      harmony datum (12) the candidate 'tu hE' therefore ties exactly with "
    "      the documented 'tu he', and the model cannot select it exclusively.\n"
    "The repair adds ordinary faithfulness with FREE nonnegative weights and "
    "nothing else: ID_QUAL, MAX and ID_NUC are the dissertation's IDENT_QUAL, "
    "MAX and IDENT_NUC readers verbatim, so the two models are matched; ID_HIGH "
    "is a plain Ident[high].  Every added weight is free, so the repair can only "
    "help the rival, and none of the poster's own displayed cells changes "
    "(no displayed candidate deletes, glides or changes height or quality "
    "except at the assimilation site, where the added constraints charge the "
    "opaque and transparent candidates equally and cancel)."
)

POSTER_WEIGHTS: dict[str, Fraction] = {
    "MARK_ATR": Fraction(23),
    "MARK_HIA": Fraction(22),
    "ID_INIT_V": Fraction(22),
    "ID_PLUS_ATR_G": Fraction(21),
    "ID_MINUS_ATR": Fraction(1),
}

GEN_NOTE = (
    "The poster declares no candidate generator.  This reconstruction gives "
    "SHARED-ACTIVITY the same focal product as the dissertation's fragment so "
    "that both models see identical information, restricted to the ten nuclear "
    "values because the poster supplies no constraint that evaluates absence or "
    "a glide.  Extending GEN to absence/gliding without such a constraint would "
    "hand the rival a free win and is refused."
)

VOWELS = ("a", "ɜ", "ɛ", "e", "ɪ", "i", "ɔ", "o", "ʊ", "u")

DECLARED_DOMAIN = ("G34a", "G34b")


class OutsideDeclaredDomain(Exception):
    pass


@dataclass(frozen=True)
class SharedActivityModel:

    frag: GuaFragment
    phrase_guard: bool = True
    repaired: bool = True
    full_gen: bool = False
    deleted_activity: str = "zero"

    @property
    def constraints(self) -> tuple[str, ...]:
        return REPAIRED_CONSTRAINTS if self.repaired else CONSTRAINTS

    def _tier(self, segments: Sequence[str]) -> list[int]:
        return [q for q in range(self.frag.n)
                if self.frag.ft(segments[q])["present"] and self.frag.ft(segments[q])["nuclear"]]

    def activities(self, segments: Sequence[str]) -> dict[int, Fraction]:
        tier = self._tier(segments)
        out: dict[int, Fraction] = {}
        i = 0
        while i < len(tier):
            j = i
            val = self.frag.ft(segments[tier[i]])["atr"]
            while j + 1 < len(tier) and self.frag.ft(segments[tier[j + 1]])["atr"] == val:
                j += 1
            n = j - i + 1
            for k in range(i, j + 1):
                out[tier[k]] = Fraction(1, n)
            i = j + 1
        return out

    def _check_domain(self, segments: Sequence[str]) -> None:
        if self.full_gen:
            return
        for q in self.frag.focal:
            s = segments[q]
            f = self.frag.ft(s)
            if not (f["present"] and f["nuclear"]):
                raise OutsideDeclaredDomain(
                    f"{self.frag.id}: candidate contains {s!r} at focal origin {q}; "
                    "the poster declares no constraint evaluating absence or a glide")

    def violations(self, segments: Sequence[str]) -> dict[str, Fraction]:
        self._check_domain(segments)
        F = self.frag
        ft = F.ft
        ref = F.reference
        tier = self._tier(segments)
        act = self.activities(segments)
        live = [q for q in range(F.n) if ft(segments[q])["present"]]
        nxt = {a: b for a, b in zip(live, live[1:])}

        def consecutive(p: int, q: int) -> bool:
            if F.origins[q].word != F.origins[p].word + 1:
                return False
            if self.phrase_guard and F.origins[q].phrase != F.origins[p].phrase:
                return False
            return True

        mark_atr = Fraction(0)
        for p, q in zip(tier, tier[1:]):
            if consecutive(p, q) and ft(segments[p])["atr"] is False and ft(segments[q])["atr"] is True:
                mark_atr += 1

        mark_hia = Fraction(0)
        for p in live:
            q = nxt.get(p)
            if q is None or not consecutive(p, q):
                continue
            fp, fq = ft(segments[p]), ft(segments[q])
            if fp["nuclear"] and fq["nuclear"] and not fp["high"] and not fq["high"]:
                if segments[p] != segments[q]:
                    mark_hia += 1

        id_init = Fraction(0)
        id_plus = Fraction(0)
        id_minus = Fraction(0)
        id_qual = Fraction(0)
        id_high = Fraction(0)
        max_v = Fraction(0)
        id_nuc = Fraction(0)
        id_plus_plain = Fraction(0)
        for q in range(F.n):
            r = ft(ref[q])
            f = ft(segments[q])
            word_initial = q == 0 or F.origins[q - 1].word != F.origins[q].word
            if r["nuclear"] and word_initial and segments[q] != ref[q]:
                id_init += 1
            if r["nuclear"] and r["atr"] is True and not (f["nuclear"] and f["atr"] is True):
                if q in act:
                    id_plus += 1 - act[q]
                elif self.deleted_activity == "zero":
                    id_plus += 1
            if r["nuclear"] and r["atr"] is False and f["nuclear"] and f["atr"] is True:
                id_minus += 1
            if r["nuclear"] and r["atr"] is True and not (f["nuclear"] and f["atr"] is True):
                id_plus_plain += 1
            if not f["present"]:
                max_v += 1
            if f["present"] and f["quality"] is not None and r["quality"] is not None:
                if f["quality"] != r["quality"]:
                    id_qual += 1
            if f["present"] and bool(f["high"]) != bool(r["high"]):
                id_high += 1
            if f["present"] and f["nuclear"] != r["nuclear"]:
                id_nuc += 1
        out = {
            "MARK_ATR": mark_atr,
            "MARK_HIA": mark_hia,
            "ID_INIT_V": id_init,
            "ID_PLUS_ATR_G": id_plus,
            "ID_MINUS_ATR": id_minus,
        }
        if self.repaired:
            out.update({"ID_QUAL": id_qual, "ID_HIGH": id_high,
                        "MAX": max_v, "ID_NUC": id_nuc,
                        "ID_PLUS_ATR": id_plus_plain})
        return out

    def penalty(self, segments: Sequence[str], weights: dict[str, Fraction] | None = None) -> Fraction:
        w = dict(POSTER_WEIGHTS) if weights is None else dict(weights)
        v = self.violations(segments)
        return sum((w.get(c, Fraction(0)) * v[c] for c in self.constraints), Fraction(0))

    def symbolic_penalty(self, segments: Sequence[str], prefix: str = "t") -> LinForm:
        v = self.violations(segments)
        out = LinForm.num(0)
        for c in self.constraints:
            if v[c]:
                out = out + LinForm.var(f"{prefix}_{c}") * v[c]
        return out

    def candidates(self) -> list[tuple[int, tuple[str, ...]]]:
        from itertools import product as iproduct

        values = tuple(self.frag.alphabet) if self.full_gen else VOWELS
        out = []
        for combo in iproduct(values, repeat=self.frag.k):
            segs = list(self.frag.reference)
            for q, s in zip(self.frag.focal, combo):
                segs[q] = s
            idx = self.frag.index_of([self.frag.alphabet.index(s) for s in combo])
            out.append((idx, tuple(segs)))
        return out

    def evaluate(self, weights: dict[str, Fraction] | None = None, observation: str | None = None) -> dict:
        target = observation if observation is not None else self.frag.record["observation"]
        vals: dict[int, Fraction] = {}
        obs: dict[int, str] = {}
        for idx, segs in self.candidates():
            vals[idx] = self.penalty(segs, weights)
            obs[idx] = self.frag.observe(segs)
        best = min(vals.values())
        minima = sorted(i for i, v in vals.items() if v == best)
        fibre = sorted(i for i, y in obs.items() if y == target)
        return {
            "id": self.frag.id,
            "states": len(vals),
            "minimum": best,
            "minima": minima,
            "fibre": fibre,
            "exclusively_correct": bool(minima) and set(minima) <= set(fibre),
            "values": vals,
            "observations": obs,
        }
