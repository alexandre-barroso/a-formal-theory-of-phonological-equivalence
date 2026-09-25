from __future__ import annotations

from fractions import Fraction
from pathlib import Path
from typing import Sequence

from phonological_opacity.fragments.gua import MARKEDNESS, SCHEMAS, GuaFragment, load_spec

from .exact import LinForm


VARIANTS = ("baseline", "def_eq_context", "dynamic_next_word", "dynamic_phrase",
            "dynamic_nucleus", "dynamic_stop_nucleus", "origin_bound",
            "witness", "witness_phrase")


def load_asts() -> dict:
    from phonological_grounding.declaration_language.export_ast import bundle
    return bundle()["gua"]


def a_slot_spec(asts: dict, variant: str) -> dict:
    A = asts[variant]["A"]
    cons = set(A["consequence_slots"])
    relatum = next(s for s in A["slots"] if s["kind"] == "relatum" and s["name"] in cons)
    guarded = [s for s in A["slots"] if s["kind"] == "relatum" and s["name"] not in cons]
    return {"policy": relatum["policy"], "filter": relatum["filter"],
            "mode": relatum["filter_mode"], "scope": relatum["scope"]["label"],
            "definedness_override": A.get("definedness_override"),
            "derived_definedness": A.get("derived_definedness", False),
            "split_relatum": bool(guarded)}


class AResolver:

    def __init__(self, frag: GuaFragment, spec: dict):
        self.f = frag
        self.spec = spec

    def _in_scope(self, q: int, r: int) -> bool:
        o = self.f.origins
        label = self.spec["scope"]
        if label == "unscoped":
            return True
        if label == "same_phrase":
            return o[r].phrase == o[q].phrase
        if label == "next_word_same_phrase":
            return o[r].word == o[q].word + 1 and o[r].phrase == o[q].phrase
        raise ValueError(f"unknown scope {label!r}")

    def _passes_filter(self, segments: Sequence[str], r: int) -> bool:
        flt = self.spec["filter"]
        if flt is None:
            return True
        ft = self.f.ft(segments[r])
        if flt == "nuclear_nonhigh":
            return bool(ft["nuclear"]) and not bool(ft["high"])
        raise ValueError(f"unknown filter {flt!r}")

    def resolve(self, segments: Sequence[str], q: int) -> int | None:
        F = self.f
        present = [i for i in range(F.n) if F.ft(segments[i])["present"]]
        policy = self.spec["policy"]
        if policy == "dynamic":
            forward = [i for i in present if i > q]
            if self.spec["mode"] == "stop":
                if not forward:
                    return None
                r = forward[0]
                return r if self._in_scope(q, r) and self._passes_filter(segments, r) else None
            for r in forward:
                if not self._in_scope(q, r):
                    return None
                if self._passes_filter(segments, r):
                    return r
            return None
        if policy in ("origin_bound", "witness"):
            r = q + 1
            if r >= F.n:
                return None
            if not F.ft(segments[r])["present"]:
                return None
            if not self._in_scope(q, r):
                return None
            if policy == "witness":
                gap = [i for i in range(q + 1, r) if F.ft(segments[i])["present"]]
                if gap:
                    return None
            return r
        raise ValueError(f"unknown policy {policy!r}")

    def triple(self, segments: Sequence[str], q: int) -> tuple[bool, bool, bool]:
        F = self.f
        ft = F.ft
        fq = ft(segments[q])
        r = self.resolve(segments, q)
        t_absent = not fq["present"]
        if self.spec["definedness_override"] is not None:
            ov = self.spec["definedness_override"]
            if ov.get("op") == "const":
                defined = bool(ov["value"])
            else:
                defined = self._activation(segments, q, r)
        else:
            defined = t_absent or (r is not None)
        good = t_absent or (r is not None and segments[q] == segments[r])
        return (self._activation(segments, q, r), defined, good)

    def _activation(self, segments: Sequence[str], q: int, r: int | None) -> bool:
        ft = self.f.ft
        fq = ft(segments[q])
        if not (fq["present"] and fq["nuclear"] and not fq["high"]):
            return False
        if self.spec.get("split_relatum", False):
            F = self.f
            present = [i for i in range(F.n) if F.ft(segments[i])["present"]]
            forward = [i for i in present if i > q]
            g = forward[0] if forward else None
            if g is None:
                return False
            if not (F.origins[g].word == F.origins[q].word + 1
                    and F.origins[g].phrase == F.origins[q].phrase):
                return False
        else:
            g = r
            if g is None:
                return False
        fg = ft(segments[g])
        return bool(fg["nuclear"]) and not bool(fg["high"])


def baseline_spec() -> dict:
    return {"policy": "dynamic", "filter": None, "mode": "skip",
            "scope": "unscoped", "definedness_override": {"op": "const", "value": True},
            "derived_definedness": False, "split_relatum": True}


def locus_terms(frag: GuaFragment, segments: Sequence[str], spec: dict
                ) -> dict[str, tuple[int, int]]:
    cur = frag.readers(segments)
    ref = frag._ref_readers
    res = AResolver(frag, spec)
    cur = dict(cur)
    cur["A"] = [res.triple(segments, q) for q in range(frag.n)]
    ref_A = [res.triple(frag.reference, q) for q in range(frag.n)]
    out: dict[str, tuple[int, int]] = {}
    for s in SCHEMAS:
        old = new = 0
        for q in range(frag.n):
            p = frag.pressure(cur[s][q])
            m = frag.marked(cur[s][q])
            if s in MARKEDNESS:
                a = frag.marked(ref[s][q] if s != "A" else ref_A[q])
                old += p if a else 0
                new += m if not a else 0
            else:
                old += m
        out[s] = (old, new)
    return out


def symbolic(frag: GuaFragment, segments: Sequence[str], spec: dict,
             lam: Fraction = Fraction(1, 8), prefix: str = "w") -> LinForm:
    terms = locus_terms(frag, segments, spec)
    out = LinForm.num(0)
    for s in SCHEMAS:
        old, new = terms[s]
        c = Fraction(old) + lam * Fraction(new)
        if c:
            out = out + LinForm.var(f"{prefix}_{s}") * c
    return out


def score8(frag: GuaFragment, segments: Sequence[str], spec: dict,
           lam: Fraction = Fraction(1, 8)) -> Fraction:
    terms = locus_terms(frag, segments, spec)
    total = Fraction(0)
    for s in SCHEMAS:
        old, new = terms[s]
        total += frag.weights[s] * (Fraction(old) + lam * Fraction(new))
    return total * 8
