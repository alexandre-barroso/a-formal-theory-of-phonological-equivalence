from __future__ import annotations

import copy
import json
from dataclasses import dataclass
from fractions import Fraction
from itertools import product
from pathlib import Path
from typing import Callable, Iterable, Sequence

from phonological_opacity.fragments import gua_fragment

ABSENT = "∅"

SCHEMAS = ("MAX", "IDENT_ATR", "IDENT_QUAL", "IDENT_NUC", "H", "A", "GL", "D", "INITIAL_FEATURE")
MARKEDNESS = ("H", "A", "GL", "D")


def load_spec() -> dict:
    return copy.deepcopy(gua_fragment.SPEC)


@dataclass(frozen=True)
class Origin:

    segment: str
    word: int
    phrase: int


class GuaFragment:

    def __init__(self, spec: dict, input_id: str):
        self.spec = spec
        self.record = next(u for u in spec["inputs"] if u["id"] == input_id)
        self.id = input_id
        self.alphabet: list[str] = list(spec["alphabet"])
        self.features: dict = spec["features"]
        self.default_features: dict = spec["default_segment_features"]
        origins: list[Origin] = []
        for w, word in enumerate(self.record["words"]):
            phrase = self.record["phrases"][w]
            for seg in word:
                origins.append(Origin(seg, w, phrase))
        self.origins = tuple(origins)
        self.n = len(self.origins)
        self.focal = tuple(self.record["focal"])
        self.k = len(self.focal)
        self.reference = tuple(o.segment for o in self.origins)
        self.weights = {s: Fraction(spec["weights"][s]) for s in SCHEMAS}
        self.lam = Fraction(spec["lambda"]["num"], spec["lambda"]["den"])
        self.radix = len(self.alphabet)
        self.size = self.radix ** self.k
        self._powers = tuple(self.radix ** i for i in reversed(range(self.k)))
        self._ref_readers = self.readers(self.reference)
        self.reference_index = sum(
            self.alphabet.index(self.origins[q].segment) * p
            for q, p in zip(self.focal, self._powers)
        )

    def ft(self, segment: str) -> dict:
        return self.features.get(segment, self.default_features)

    def candidate(self, index: int) -> tuple[str, ...]:
        if not 0 <= index < self.size:
            raise IndexError(index)
        digits = []
        rest = index
        for p in self._powers:
            digits.append(rest // p)
            rest %= p
        segments = list(self.reference)
        for q, d in zip(self.focal, digits):
            segments[q] = self.alphabet[d]
        return tuple(segments)

    def index_of(self, digits: Sequence[int]) -> int:
        return sum(d * p for d, p in zip(digits, self._powers))

    def observe(self, segments: Sequence[str]) -> str:
        return "".join(s for s in segments if self.ft(s)["present"])

    def all_candidates(self) -> Iterable[tuple[int, tuple[str, ...]]]:
        for i in range(self.size):
            yield i, self.candidate(i)

    def readers(self, segments: Sequence[str]) -> dict[str, list[tuple[bool, bool, bool]]]:
        fs = [self.ft(s) for s in segments]
        rf = [self.ft(s) for s in self.reference]
        live = [q for q in range(self.n) if fs[q]["present"]]
        nxt = {a: b for a, b in zip(live, live[1:])}
        prv = {b: a for a, b in zip(live, live[1:])}
        nuclei = [q for q in live if fs[q]["nuclear"]]
        last_nucleus: dict[int, int] = {}
        for q in nuclei:
            last_nucleus[self.origins[q].word] = q

        out: dict[str, list[tuple[bool, bool, bool]]] = {s: [] for s in SCHEMAS}
        for q in range(self.n):
            f, r = fs[q], rf[q]
            o = self.origins[q]
            nq = nxt.get(q)
            pq = prv.get(q)

            out["MAX"].append((True, True, f["present"]))
            out["IDENT_ATR"].append((True, bool(f["nuclear"] and r["nuclear"]), f["atr"] == r["atr"]))
            out["IDENT_QUAL"].append(
                (True,
                 bool(f["present"] and f["quality"] is not None and r["quality"] is not None),
                 f["quality"] == r["quality"]))
            out["IDENT_NUC"].append((True, bool(f["present"]), f["nuclear"] == r["nuclear"]))

            src = next(
                (j for j in nuclei
                 if j > q and self.origins[j].word > o.word and self.origins[j].phrase == o.phrase),
                None)
            h_context = bool(
                f["nuclear"]
                and last_nucleus.get(o.word) == q
                and src is not None
                and fs[src]["atr"] is True)
            out["H"].append((h_context, bool(f["nuclear"]), f["atr"] is True))

            cross = (nq is not None
                     and self.origins[nq].word == o.word + 1
                     and self.origins[nq].phrase == o.phrase)
            a_context = bool(
                f["nuclear"] and not f["high"] and cross
                and fs[nq]["nuclear"] and not fs[nq]["high"])
            a_good = bool((not f["present"])
                          or (nq is not None and segments[q] == segments[nq]))
            out["A"].append((a_context, True, a_good))

            neighbour = any(
                j is not None
                and abs(self.origins[j].word - o.word) == 1
                and self.origins[j].phrase == o.phrase
                and fs[j]["nuclear"] and not fs[j]["high"]
                for j in (pq, nq))
            gl_context = bool(f["nuclear"] and f["high"] and neighbour)
            out["GL"].append((gl_context, True, not f["nuclear"]))

            d_context = bool(
                f["nuclear"] and f["high"]
                and pq is not None
                and self.origins[pq].word + 1 == o.word
                and self.origins[pq].phrase == o.phrase
                and fs[pq]["nuclear"] and fs[pq]["high"])
            out["D"].append((d_context, True, not f["present"]))

            init_context = bool(r["nuclear"] and (q == 0 or self.origins[q - 1].word != o.word))
            init_defined = bool(f["present"] and f["quality"] is not None)
            init_good = bool(f["quality"] == r["quality"]
                             and ((not f["nuclear"]) or f["atr"] == r["atr"]))
            out["INITIAL_FEATURE"].append((init_context, init_defined, init_good))
        return out

    @staticmethod
    def pressure(triple: tuple[bool, bool, bool]) -> int:
        _c, d, g = triple
        return int(d and not g)

    @staticmethod
    def marked(triple: tuple[bool, bool, bool]) -> int:
        c, d, g = triple
        return int(c and d and not g)

    def locus_terms(self, segments: Sequence[str]) -> dict[str, tuple[int, int]]:
        cur = self.readers(segments)
        ref = self._ref_readers
        out: dict[str, tuple[int, int]] = {}
        for s in SCHEMAS:
            old = new = 0
            for q in range(self.n):
                p = self.pressure(cur[s][q])
                m = self.marked(cur[s][q])
                if s in MARKEDNESS:
                    a = self.marked(ref[s][q])
                    old += p if a else 0
                    new += m if not a else 0
                else:
                    old += m
            out[s] = (old, new)
        return out

    def score(self, segments: Sequence[str]) -> Fraction:
        terms = self.locus_terms(segments)
        total = Fraction(0)
        for s in SCHEMAS:
            old, new = terms[s]
            total += self.weights[s] * (Fraction(old) + self.lam * new)
        return total

    def score8(self, segments: Sequence[str]) -> int:
        v = self.score(segments) * 8
        assert v.denominator == 1, v
        return int(v)

    def evaluate(self, score_fn: Callable[[Sequence[str]], int] | None = None) -> dict:
        score_fn = score_fn or self.score8
        values = []
        observations = []
        for _i, cand in self.all_candidates():
            values.append(score_fn(cand))
            observations.append(self.observe(cand))
        target = self.record["observation"]
        fiber = [i for i, y in enumerate(observations) if y == target]
        best = min(values)
        minima = [i for i, v in enumerate(values) if v == best]
        return {
            "id": self.id,
            "states": self.size,
            "reference_index": self.reference_index,
            "fiber": fiber,
            "minima": minima,
            "minimum8": best,
            "exclusively_correct": bool(minima) and set(minima) <= set(fiber),
            "values": values,
            "observations": observations,
        }


def all_fragments(spec: dict | None = None) -> list[GuaFragment]:
    spec = spec or load_spec()
    return [GuaFragment(spec, u["id"]) for u in spec["inputs"]]


class GuaProbe(GuaFragment):

    def __init__(self, spec: dict, probe_id: str):
        record = next(p for p in spec["probes"] if p["id"] == probe_id)
        shim = dict(record)
        shim["observation"] = ""
        self._probe = record
        object.__setattr__(self, "_probe_record", record)
        spec_shim = dict(spec)
        spec_shim["inputs"] = list(spec["inputs"]) + [shim]
        super().__init__(spec_shim, probe_id)

    def probe_states(self) -> list[list[str]]:
        return [list(s) for s in self._probe["states"]]

    def locus_report(self) -> list[dict]:
        schema = self._probe["locus"]["schema"]
        q = self._probe["locus"]["origin"]
        out = []
        for state in self.probe_states():
            c, dfn, g = self.readers(state)[schema][q]
            ref_marked = self.marked(self._ref_readers[schema][q])
            p = self.pressure((c, dfn, g))
            retained8 = 8 * int(self.weights[schema]) * (p if ref_marked else 0)
            out.append({
                "state": state, "context": bool(c), "defined": bool(dfn), "good": bool(g),
                "reference_marked": bool(ref_marked), "retained8": retained8,
            })
        return out
