from __future__ import annotations

from .indep_gua import Product

C = "t"


def _mk(ident, words, phrases_of_word):
    segs, wix = [], []
    for w, block in enumerate(words):
        for s in block:
            segs.append(s)
            wix.append(w)
    return Product(ident, segs, wix, phrases_of_word, focal=())


def ml_h(vowels, phrases=None):
    n = len(vowels)
    words = [[C, v] for v in vowels]
    return _mk(f"MLH{n}-" + "".join(vowels), words,
               phrases if phrases is not None else [0] * n)


def ml_h_twonuc(vowels_per_word, phrases=None):
    words = [[C] + [x for v in vs for x in (v, C)][:-1] if len(vs) > 1 else [C, vs[0]]
             for vs in vowels_per_word]
    n = len(words)
    return _mk("MLH2-" + "_".join("".join(v) for v in vowels_per_word), words,
               phrases if phrases is not None else [0] * n)


def ml_a(pairs, phrases=None):
    words = []
    for i, (a, b) in enumerate(pairs):
        block = []
        if a is not None:
            block.append(a)
        block.append(C)
        if b is not None:
            block.append(b)
        words.append(block)
    n = len(words)
    return _mk("MLA-" + "_".join(f"{a or ''}{b or ''}" for a, b in pairs), words,
               phrases if phrases is not None else [0] * n)


def ml_hiatus(pairs, phrases=None):
    return ml_a(pairs, phrases)


REGISTRY = {
    "H2viol": lambda: ml_h_twonuc([["ɛ"], ["e", "ɛ"], ["e"]]),
    "Hmixed": lambda: ml_h(["ɛ", "e", "e"]),
    "H3viol": lambda: ml_h_twonuc([["ɛ"], ["e", "ɛ"], ["e", "ɛ"], ["e"]]),
    "A2viol": lambda: ml_a([(None, "ɛ"), ("a", "ɔ"), ("e", None)]),
    "Amixed": lambda: ml_a([(None, "ɛ"), ("a", "ɔ"), ("ɔ", None)]),
    "GL2viol": lambda: ml_a([(None, "ɪ"), ("e", "ʊ"), ("o", None)]),
    "D2viol": lambda: ml_a([(None, "ɪ"), ("ʊ", "ɪ"), ("ʊ", None)]),
    "A2phrase": lambda: ml_a([(None, "ɛ"), ("a", None), (None, "ɔ"), ("e", None)],
                             phrases=[0, 0, 1, 1]),
}
