from __future__ import annotations
import itertools

VOICELESS = "ptksfčţxʂʃ"
VOICED = "bdgzvǰʣɣʐʒ"
PAIR = dict(zip(VOICELESS, VOICED)) | dict(zip(VOICED, VOICELESS))
AFFRICATES = set("čǰţʣ")


def obstruent(c): return c in VOICELESS or c in VOICED
def voiced(c): return c in VOICED


def candidates(inp: str):
    pos = [i for i, c in enumerate(inp) if obstruent(c)]
    for combo in itertools.product([0, 1], repeat=len(pos)):
        s = list(inp)
        for i, v in zip(pos, combo):
            base = s[i]
            s[i] = base if v == (1 if voiced(base) else 0) else PAIR[base]
        yield "".join(s)


def presonorant(s: str, i: int) -> bool:
    return i + 1 < len(s) and s[i + 1] != " " and not obstruent(s[i + 1])


CONSTRAINTS = {
    "*ObsVoice": lambda u, s: sum(1 for c in s if voiced(c)),
    "Ident": lambda u, s: sum(1 for a, b in zip(u, s) if obstruent(a) and voiced(a) != voiced(b)),
    "Id-pson": lambda u, s: sum(1 for i, (a, b) in enumerate(zip(u, s))
                                if obstruent(a) and voiced(a) != voiced(b) and presonorant(u, i)),
    "Agree": lambda u, s: sum(1 for a, b in zip(s.replace(" ", ""), s.replace(" ", "")[1:])
                              if obstruent(a) and obstruent(b) and voiced(a) != voiced(b)),
    "*VcdAff": lambda u, s: sum(1 for c in s if c in AFFRICATES and voiced(c)),
    "NoVcdPWdCoda": lambda u, s: sum(1 for i, c in enumerate(s)
                                     if voiced(c) and (i + 1 == len(s) or s[i + 1] == " ")),
}


def profile(u, s, names):
    return tuple(CONSTRAINTS[n](u, s) for n in names)


def ot_winners(u: str, order: tuple[str, ...]):
    cands = list(dict.fromkeys(candidates(u)))
    best = min(profile(u, s, order) for s in cands)
    return sorted(s for s in cands if profile(u, s, order) == best)


def factorial_typology(inputs, names=("Agree", "Id-pson", "*ObsVoice", "Ident")):
    patterns = {}
    for order in itertools.permutations(names):
        pat = tuple(tuple(ot_winners(u, order)) for u in inputs)
        patterns.setdefault(pat, []).append(" >> ".join(order))
    return patterns


def stratified_orders(strata):
    for parts in itertools.product(*[itertools.permutations(st) for st in strata]):
        yield tuple(c for st in parts for c in st)
