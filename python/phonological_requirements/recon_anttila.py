from __future__ import annotations

import itertools
import random
import unicodedata
from fractions import Fraction as F

HIGH, MID, LOW = set("iuy"), set("eoö"), set("aä")
VOW = HIGH | MID | LOW


def _syll(s: str):
    out = []
    for syl in s.split("."):
        d = unicodedata.normalize("NFD", syl)
        stressed = "́" in d or "̀" in d
        base = "".join(ch for ch in d if not unicodedata.combining(ch))
        vowels = [ch for ch in base if ch in VOW]
        heavy = len(vowels) >= 2 or (base[-1] not in VOW)
        first = vowels[0]
        height = "I" if first in HIGH else "O" if first in MID else "A"
        out.append([stressed, heavy, height, len(vowels) >= 2])
    return out


def violations(form: str, stem_vowel: str, strong: bool):
    S = _syll(form)
    if strong:
        for i, syl in enumerate(S):
            if syl[3] and i == len(S) - 2:
                syl[2] = {"i": "I", "u": "I", "e": "O", "o": "O", "a": "A"}[stem_vowel]
    v = {}
    st = lambda s: s[0]; hv = lambda s: s[1]; ht = lambda s: s[2]
    v["*'X.'X"] = sum(1 for a, b in zip(S, S[1:]) if st(a) and st(b))
    v["*H"] = sum(1 for s in S if hv(s) and not st(s))
    v["*'L"] = sum(1 for s in S if st(s) and not hv(s))
    v["*L.L"] = sum(1 for a, b in zip(S, S[1:]) if not hv(a) and not hv(b))
    v["*H/I"] = sum(1 for s in S if hv(s) and ht(s) == "I")
    v["*'I"] = sum(1 for s in S if st(s) and ht(s) == "I")
    v["*L/A"] = sum(1 for s in S if not hv(s) and ht(s) == "A")
    v["*H/O"] = sum(1 for s in S if hv(s) and ht(s) == "O")
    v["*'O"] = sum(1 for s in S if st(s) and ht(s) == "O")
    v["*H.H"] = sum(1 for a, b in zip(S, S[1:]) if hv(a) and hv(b))
    v["*X.X"] = sum(1 for a, b in zip(S, S[1:]) if not st(a) and not st(b))
    v["*'H"] = sum(1 for s in S if st(s) and hv(s))
    return v


STRATA = [["*'X.'X"], ["*H", "*'L"], ["*L.L", "*H/I", "*'I"],
          ["*L/A", "*H/O", "*'O", "*H.H", "*X.X", "*'H"]]


def linear_extensions(strata=STRATA):
    for perms in itertools.product(*[itertools.permutations(s) for s in strata]):
        yield [c for p in perms for c in p]


def ot_winner(order, va, vb):
    for c in order:
        if va[c] != vb[c]:
            return "a" if va[c] < vb[c] else "b"
    return "tie"


def count_law(va, vb, strata=STRATA):
    n = {"a": 0, "b": 0, "tie": 0}; tot = 0
    for order in linear_extensions(strata):
        n[ot_winner(order, va, vb)] += 1; tot += 1
    return {k: F(v, tot) for k, v in n.items()}


def volume_law(va, vb, strata=STRATA, samples=200000, seed=1):
    rng = random.Random(seed)
    for s in strata:
        d = [va[c] - vb[c] for c in s]
        if any(d):
            wins = {"a": 0, "b": 0, "tie": 0}
            for _ in range(samples):
                w = [rng.expovariate(1.0) for _ in s]
                x = sum(wi * di for wi, di in zip(w, d))
                wins["a" if x < 0 else "b" if x > 0 else "tie"] += 1
            return {k: F(v, samples) for k, v in wins.items()}, s
    return {"a": F(0), "b": F(0), "tie": F(1)}, None
