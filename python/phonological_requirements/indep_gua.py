from __future__ import annotations

from fractions import Fraction
from itertools import product
from typing import Optional, Sequence

ABSENT = "∅"
ALPHABET = (ABSENT, "a", "ɜ", "ɛ", "e", "ɪ", "i",
            "ɔ", "o", "ʊ", "u", "j", "w")

_FT = {
    ABSENT:     (False, False, None, None, False),
    "a":        (True,  True,  0,    False, False),
    "ɜ":   (True,  True,  0,    True,  False),
    "ɛ":   (True,  True,  1,    False, False),
    "e":        (True,  True,  1,    True,  False),
    "ɪ":   (True,  True,  2,    False, True),
    "i":        (True,  True,  2,    True,  True),
    "ɔ":   (True,  True,  3,    False, False),
    "o":        (True,  True,  3,    True,  False),
    "ʊ":   (True,  True,  4,    False, True),
    "u":        (True,  True,  4,    True,  True),
    "j":        (True,  False, 2,    None,  False),
    "w":        (True,  False, 4,    None,  False),
}
_DEFAULT = (True, False, None, None, False)


def ft(seg: str):
    return _FT.get(seg, _DEFAULT)


def present(seg):  return ft(seg)[0]
def nuclear(seg):  return ft(seg)[1]
def quality(seg):  return ft(seg)[2]
def atr(seg):      return ft(seg)[3]
def high(seg):     return ft(seg)[4]


SCHEMATA = ("MAX", "IDENT_ATR", "IDENT_QUAL", "IDENT_NUC",
            "H", "A", "GL", "D", "INITIAL_FEATURE")
MARKEDNESS = (4, 5, 6, 7)
WEIGHTS = (20, 1, 1, 2, 4, 8, 8, 24, 1)
LAMBDA = Fraction(1, 8)


class Product:

    def __init__(self, ident: str, segments: Sequence[str],
                 words: Sequence[int], phrase_of_word: Sequence[int],
                 focal: Sequence[int]):
        self.id = ident
        self.reference = tuple(segments)
        self.words = tuple(words)
        self.phrase_of_word = tuple(phrase_of_word)
        self.focal = tuple(focal)
        self.n = len(self.reference)

    def phrase(self, origin: int) -> int:
        return self.phrase_of_word[self.words[origin]]

    def states(self):
        for coords in product(range(len(ALPHABET)), repeat=len(self.focal)):
            s = list(self.reference)
            for q, k in zip(self.focal, coords):
                s[q] = ALPHABET[k]
            yield coords, tuple(s)

    def index_of(self, coords) -> int:
        i = 0
        for c in coords:
            i = i * len(ALPHABET) + c
        return i

    def live(self, s):
        return [q for q in range(self.n) if present(s[q])]

    def readers(self, s):
        live = self.live(s)
        pos_in_live = {q: i for i, q in enumerate(live)}
        nxt = {live[i]: live[i + 1] for i in range(len(live) - 1)}
        prv = {live[i + 1]: live[i] for i in range(len(live) - 1)}
        nuclei = [q for q in live if nuclear(s[q])]
        last_nuc = {}
        for q in nuclei:
            last_nuc[self.words[q]] = q

        C = [[False] * self.n for _ in SCHEMATA]
        D = [[False] * self.n for _ in SCHEMATA]
        G = [[False] * self.n for _ in SCHEMATA]

        for q in range(self.n):
            cur, ref = s[q], self.reference[q]
            w = self.words[q]
            ph = self.phrase(q)
            n = nxt.get(q)
            v = prv.get(q)

            C[0][q] = True; D[0][q] = True; G[0][q] = present(cur)
            C[1][q] = True
            D[1][q] = nuclear(cur) and nuclear(ref)
            G[1][q] = atr(cur) == atr(ref)
            C[2][q] = True
            D[2][q] = present(cur) and quality(cur) is not None and quality(ref) is not None
            G[2][q] = quality(cur) == quality(ref)
            C[3][q] = True
            D[3][q] = present(cur)
            G[3][q] = nuclear(cur) == nuclear(ref)
            src = None
            for j in nuclei:
                if j > q and self.words[j] > w and self.phrase(j) == ph:
                    src = j
                    break
            C[4][q] = (nuclear(cur) and last_nuc.get(w) == q
                       and src is not None and atr(s[src]) is True)
            D[4][q] = nuclear(cur)
            G[4][q] = atr(cur) is True
            cross = (n is not None and self.words[n] == w + 1
                     and self.phrase(n) == ph)
            C[5][q] = (nuclear(cur) and not high(cur) and cross
                       and nuclear(s[n]) and not high(s[n]))
            D[5][q] = True
            G[5][q] = (not present(cur)) or (n is not None and cur == s[n])
            nb = any(j is not None and abs(self.words[j] - w) == 1
                     and self.phrase(j) == ph
                     and nuclear(s[j]) and not high(s[j])
                     for j in (v, n))
            C[6][q] = nuclear(cur) and high(cur) and nb
            D[6][q] = True
            G[6][q] = not nuclear(cur)
            C[7][q] = (nuclear(cur) and high(cur) and v is not None
                       and self.words[v] + 1 == w and self.phrase(v) == ph
                       and nuclear(s[v]) and high(s[v]))
            D[7][q] = True
            G[7][q] = not present(cur)
            C[8][q] = nuclear(ref) and (q == 0 or self.words[q - 1] != w)
            D[8][q] = present(cur) and quality(cur) is not None
            G[8][q] = (quality(cur) == quality(ref)
                       and ((not nuclear(cur)) or atr(cur) == atr(ref)))
        return C, D, G

    def activation_bits(self):
        C, D, G = self.readers(self.reference)
        return [[bool(C[k][q] and D[k][q] and not G[k][q]) for q in range(self.n)]
                for k in range(len(SCHEMATA))]

    def coefficients(self, s, a):
        C, D, G = self.readers(s)
        out = []
        for k in range(len(SCHEMATA)):
            p = [D[k][q] and not G[k][q] for q in range(self.n)]
            if k in MARKEDNESS:
                old = sum(1 for q in range(self.n) if p[q] and a[k][q])
                new = sum(1 for q in range(self.n) if p[q] and not a[k][q] and C[k][q])
            else:
                old = sum(1 for q in range(self.n) if p[q] and C[k][q])
                new = 0
            out.append((old, new))
        return out

    def score(self, coeffs, weights=WEIGHTS, lam=LAMBDA) -> Fraction:
        return sum(Fraction(w) * (Fraction(o) + lam * Fraction(nn))
                   for w, (o, nn) in zip(weights, coeffs))

    def observe(self, s) -> str:
        return "".join(x for x in s if present(x))


def evaluate(prod: Product, weights=WEIGHTS, lam=LAMBDA):
    a = prod.activation_bits()
    recs = []
    for coords, s in prod.states():
        cs = prod.coefficients(s, a)
        recs.append({
            "i": prod.index_of(coords),
            "coords": coords,
            "state": s,
            "obs": prod.observe(s),
            "coeffs": cs,
            "score": prod.score(cs, weights, lam),
        })
    best = min(r["score"] for r in recs)
    minima = [r["i"] for r in recs if r["score"] == best]
    return recs, best, minima
