from __future__ import annotations

import sys
from fractions import Fraction
from itertools import product

from phonological_opacity.fragments.gua import GuaFragment, GuaProbe, load_spec
from phonological_opacity.fragments import lithuanian as lit

RESULTS: list[tuple[str, bool, str]] = []


def check(label: str, ok: bool, detail: str = "") -> None:
    RESULTS.append((label, bool(ok), detail))


spec = load_spec()
frag = {u["id"]: GuaFragment(spec, u["id"]) for u in spec["inputs"]}
ev = {k: v.evaluate() for k, v in frag.items()}

TABLE_9 = {
    "G34a": (13 ** 3, Fraction(3)), "G34b": (13 ** 3, Fraction(5, 2)),
    "N7": (13 ** 2, Fraction(1)), "G37c": (13 ** 3, Fraction(7, 2)),
    "C24ei": (13 ** 2, Fraction(2)), "OR38": (13 ** 3, Fraction(43, 2)),
    "C21b": (13 ** 2, Fraction(20)), "C23UE": (13 ** 2, Fraction(2)),
}
for key, (states, minimum) in TABLE_9.items():
    e = ev[key]
    check(f"tab:opacity-gua-selection {key}: {states} candidates, min = {minimum}",
          e["states"] == states and Fraction(e["minimum8"], 8) == minimum,
          f"got states={e['states']} min={Fraction(e['minimum8'], 8)}")

check("opacity: 9,464 candidates in the eight products",
      sum(e["states"] for e in ev.values()) == 9464,
      str(sum(e["states"] for e in ev.values())))

check("thm:opacity-gua-selection: unique minimiser in each product",
      all(len(e["minima"]) == 1 for e in ev.values()),
      str({k: len(e["minima"]) for k, e in ev.items()}))

check("thm:opacity-gua-selection: each minimiser realises the table's observation",
      all(set(e["minima"]) <= set(e["fiber"]) for e in ev.values()))

f = frag["G34a"]
ALPHA = spec["alphabet"]


def g34a_index(triple: tuple[str, str, str]) -> int:
    return f.index_of([ALPHA.index(x) for x in triple])


rows = {"reference": ("ɛ", "e", "ɔ"), "selected": ("e", "ɔ", "ɔ"), "rival": ("ɛ", "ɔ", "ɔ")}
totals = {}
for name, triple in rows.items():
    segs = f.candidate(g34a_index(triple))
    terms = f.locus_terms(segs)
    faith = sum(f.weights[s] * (terms[s][0] + f.lam * terms[s][1])
                for s in ("MAX", "IDENT_ATR", "IDENT_QUAL", "IDENT_NUC", "INITIAL_FEATURE"))
    retained_h = f.weights["H"] * (terms["H"][0] + f.lam * terms["H"][1])
    retained_a = f.weights["A"] * (terms["A"][0] + f.lam * terms["A"][1])
    other = sum(f.weights[s] * (terms[s][0] + f.lam * terms[s][1]) for s in ("GL", "D"))
    totals[name] = (faith, retained_h, retained_a, other, f.score(segs))

EXPECTED_CRITICAL = {
    "reference": (0, 4, 8, 0, 12),
    "selected": (3, 0, 0, 0, 3),
    "rival": (2, 4, 0, 0, 6),
}
for name, want in EXPECTED_CRITICAL.items():
    got = tuple(totals[name])
    check(f"tab:opacity-gua-critical row '{name}' = {want}",
          got == tuple(Fraction(v) for v in want), f"got {got}")

g = frag["G34b"]
sel = g.candidate(ev["G34b"]["minima"][0])
alt = list(sel)
alt[g.focal[0]] = "i"
check("opacity G34b: keeping ɪ leaves exactly one new H violation costing 1/2",
      g.locus_terms(sel)["H"] == (0, 1)
      and g.weights["H"] * g.lam == Fraction(1, 2),
      f"H terms {g.locus_terms(sel)['H']}")
check("opacity G34b: changing that ATR costs 1 more than the selected candidate",
      g.score(tuple(alt)) - g.score(sel) == Fraction(1, 2),
      f"delta {g.score(tuple(alt)) - g.score(sel)}")

check("opacity: a focal absence costs at least 20 (w_Max = 20)",
      f.weights["MAX"] == 20)

COST_ROW = {"a": 4, "ɜ": 4, "ɛ": 3, "e": 3, "ɪ": 4, "i": 4,
            "ɔ": 2, "o": 3, "ʊ": 4, "u": 4, "j": 7, "w": 7}
faith_only = ("MAX", "IDENT_ATR", "IDENT_QUAL", "IDENT_NUC", "INITIAL_FEATURE")
base = f.candidate(g34a_index(("ɛ", "e", "ɔ")))
for v, want in COST_ROW.items():
    segs = list(base)
    segs[f.focal[1]] = v
    segs[f.focal[2]] = v
    t = f.locus_terms(tuple(segs))
    cost = sum(f.weights[s] * (t[s][0] + f.lam * t[s][1]) for s in faith_only)
    check(f"tab:appg-equal-vowels v = {v} costs {want}", cost == want, f"got {cost}")

check("opacity: OR38 fibre {1189, 1261} with scores 89/2 and 43/2",
      ev["OR38"]["fiber"] == [1189, 1261]
      and Fraction(ev["OR38"]["values"][1189], 8) == Fraction(89, 2)
      and Fraction(ev["OR38"]["values"][1261], 8) == Fraction(43, 2))
check("opacity: C21b fibre {9, 117} with scores 46 and 20",
      ev["C21b"]["fiber"] == [9, 117]
      and Fraction(ev["C21b"]["values"][9], 8) == 46
      and Fraction(ev["C21b"]["values"][117], 8) == 20)
check("opacity: C23UE fibre {159} with score 2",
      ev["C23UE"]["fiber"] == [159] and Fraction(ev["C23UE"]["values"][159], 8) == 2)
check("opacity eq:appg-certificate: the three (J, e) pairs are ({1261},172), ({117},160), ({159},16)",
      (ev["OR38"]["minima"], ev["OR38"]["minimum8"]) == ([1261], 172)
      and (ev["C21b"]["minima"], ev["C21b"]["minimum8"]) == ([117], 160)
      and (ev["C23UE"]["minima"], ev["C23UE"]["minimum8"]) == ([159], 16))
check("opacity: 1189 = (ɔ,∅,i) and 1261 = (ɔ,i,∅)",
      tuple(frag["OR38"].candidate(1189)[q] for q in frag["OR38"].focal) == ("ɔ", "∅", "i")
      and tuple(frag["OR38"].candidate(1261)[q] for q in frag["OR38"].focal) == ("ɔ", "i", "∅"))
check("opacity: 9 = (∅,ʊ), 117 = (ʊ,∅), 159 = (w,ɛ)",
      tuple(frag["C21b"].candidate(9)[q] for q in frag["C21b"].focal) == ("∅", "ʊ")
      and tuple(frag["C21b"].candidate(117)[q] for q in frag["C21b"].focal) == ("ʊ", "∅")
      and tuple(frag["C23UE"].candidate(159)[q] for q in frag["C23UE"].focal) == ("w", "ɛ"))

def faith_vector(fragment: GuaFragment, index: int) -> list[int]:
    t = fragment.locus_terms(fragment.candidate(index))
    return [t[s][0] for s in ("MAX", "IDENT_ATR", "IDENT_QUAL", "IDENT_NUC", "INITIAL_FEATURE")]


T = g34a_index(("e", "ɔ", "ɔ"))
Z = g34a_index(("ɛ", "ɔ", "ɔ"))
U = g34a_index(("ɛ", "e", "ɔ"))
check("opacity sec:appg-current-bound: faithfulness of T is (0,2,1,0,0)", faith_vector(f, T) == [0, 2, 1, 0, 0], str(faith_vector(f, T)))
check("opacity sec:appg-current-bound: faithfulness of Z is (0,1,1,0,0)", faith_vector(f, Z) == [0, 1, 1, 0, 0], str(faith_vector(f, Z)))


def current_markedness(fragment: GuaFragment, index: int) -> dict[str, int]:
    segs = fragment.candidate(index)
    readers = fragment.readers(segs)
    return {s: sum(fragment.marked(readers[s][q]) for q in range(fragment.n))
            for s in ("H", "A", "GL", "D")}


check("opacity: every current markedness locus is zero in T and in Z",
      all(v == 0 for v in current_markedness(f, T).values())
      and all(v == 0 for v in current_markedness(f, Z).values()),
      f"T={current_markedness(f, T)} Z={current_markedness(f, Z)}")
check("opacity eq:opacity-current-bound: P(T) = 2f + q and P(Z) = f + q, so P(Z) <= P(T) for all f,q >= 0",
      faith_vector(f, T) == [0, 2, 1, 0, 0] and faith_vector(f, Z) == [0, 1, 1, 0, 0])
check("opacity: the correct fibre of G34a is exactly {T}", ev["G34a"]["fiber"] == [T], str(ev["G34a"]["fiber"]))
check("opacity: Z is a unary neighbour of U but T is not",
      sum(a != b for a, b in zip(f.candidate(U), f.candidate(Z))) == 1
      and sum(a != b for a, b in zip(f.candidate(U), f.candidate(T))) == 2)

def score_without_D(fragment: GuaFragment, index: int, policy: str) -> Fraction:
    segs = fragment.candidate(index)
    terms = fragment.locus_terms(segs)
    total = Fraction(0)
    for s, (old, new) in terms.items():
        if s == "D":
            if policy == "D0":
                continue
            readers = fragment.readers(segs)
            ref = fragment._ref_readers
            cur_old = sum(fragment.marked(readers["D"][q]) for q in range(fragment.n)
                          if fragment.marked(ref["D"][q]))
            cur_new = sum(fragment.marked(readers["D"][q]) for q in range(fragment.n)
                          if not fragment.marked(ref["D"][q]))
            total += fragment.weights["D"] * (cur_old + fragment.lam * cur_new)
            continue
        total += fragment.weights[s] * (old + fragment.lam * new)
    return total


c23, c21 = frag["C23UE"], frag["C21b"]
i_wE = c23.index_of([ALPHA.index("w"), ALPHA.index("ɛ")])
i_0E = c23.index_of([ALPHA.index("∅"), ALPHA.index("ɛ")])
i_wI = c21.index_of([ALPHA.index("w"), ALPHA.index("ɪ")])
i_U0 = c21.index_of([ALPHA.index("ʊ"), ALPHA.index("∅")])
i_0U = c21.index_of([ALPHA.index("∅"), ALPHA.index("ʊ")])
m, n_, q_, b_ = (frag["C23UE"].weights[s] for s in ("MAX", "IDENT_NUC", "IDENT_QUAL", "INITIAL_FEATURE"))
WANT = [
    ("C23UE (w,ɛ) correct", c23, i_wE, n_),
    ("C23UE (∅,ɛ) rival", c23, i_0E, m),
    ("C21b (w,ɪ) rival", c21, i_wI, n_),
    ("C21b (ʊ,∅) correct", c21, i_U0, m),
    ("C21b (∅,ʊ) correct", c21, i_0U, m + q_ + b_),
]
for policy in ("D0", "Dcurrent"):
    for label, fr, idx, want in WANT:
        got = score_without_D(fr, idx, policy)
        check(f"tab:opacity-deletion-bound [{policy}] {label} = {want}", got == want, f"got {got}")
check("thm:opacity-deletion-bound: n < m is required by C23UE but C21b's whole fibre costs >= m > n",
      n_ < m and min(score_without_D(c21, i, "D0") for i in (i_U0, i_0U)) >= m
      and score_without_D(c21, i_wI, "D0") == n_)

probe = GuaProbe(spec, "constructed_A_locality")
report = probe.locus_report()
check("sec:appg-domain: retained A contributes 0 in s and 8 in t",
      [r["retained8"] // 8 for r in report] == [0, 8],
      str([r["retained8"] for r in report]))
check("sec:appg-domain: both candidates have a false current context and the same next present origin",
      all(not r["context"] for r in report))

lspec = lit.load_spec()
lweights, llam = lit.reference_weights(lspec)
check("opacity: the vector (1,4,2,16,16,1/8) selects the three Lithuanian outputs, costs 1, 2, 2",
      all(lit.evaluate(rec, "RR", lweights, llam)["exclusively_correct"] for rec in lspec["inputs"])
      and [Fraction(lit.evaluate(rec, "RR", lweights, llam)["minimum8"], 8) for rec in lspec["inputs"]]
      == [Fraction(1), Fraction(2), Fraction(2)])

SYMBOLIC = {
    "PG": {0: "r", 1: "r+d", 2: "a", 3: "d", 4: "c+r+a", 5: "c+r+d", 6: "c", 7: "c+d"},
    "PB": {0: "r+Ln", 1: "r+d", 2: "a", 3: "d", 4: "c+r+a", 5: "c+r+d", 6: "c+Ln", 7: "c+d"},
    "TT": {0: "n", 1: "d", 2: "r+La", 3: "r+d", 4: "c+La", 5: "c+d", 6: "c+r+n", 7: "c+r+d"},
}
NAMES = ("c", "r", "d", "a_old", "a_new", "n_old", "n_new")


def symbolic_to_vector(expr: str) -> tuple[int, ...]:
    slot = {"c": 0, "r": 1, "d": 2, "a": 3, "La": 4, "n": 5, "Ln": 6}
    vec = [0] * 7
    for term in expr.split("+"):
        vec[slot[term]] += 1
    return tuple(vec)


for rec in lspec["inputs"]:
    for j, expr in SYMBOLIC[rec["id"]].items():
        got = lit.coefficient_vector(rec, "RR", j)
        check(f"tab:appg-lt-scores {rec['id']} j={j} = {expr}",
              got == symbolic_to_vector(expr), f"got {dict(zip(NAMES, got))}")

def region_holds(c, r, d, a, n, lam):
    return (0 < c and c < d and c < r and d < a and d < n
            and d < c + lam * n and d < c + lam * a)


def selects_all(c, r, d, a, n, lam):
    w = {"c": c, "r": r, "d": d, "a": a, "n": n}
    return all(lit.evaluate(rec, "RR", w, lam)["exclusively_correct"] for rec in lspec["inputs"])


VALUES = [Fraction(x) for x in (0, 1, 2, 3, 5)]
LAMS = [Fraction(0), Fraction(1, 8), Fraction(1, 2), Fraction(1), Fraction(2)]
mismatch = []
for c, r, d, a, n, lam in product(VALUES, VALUES, VALUES, VALUES, VALUES, LAMS):
    if region_holds(c, r, d, a, n, lam) != selects_all(c, r, d, a, n, lam):
        mismatch.append((c, r, d, a, n, lam))
check(f"thm:opacity-lt-region: region <=> joint selection over {len(VALUES)**5 * len(LAMS)} exact rational points",
      not mismatch, f"{len(mismatch)} mismatches, first {mismatch[:3]}")

for config in ("SR", "RS", "SS"):
    bad = [(c, r, d, a, n, lam) for c, r, d, a, n, lam
           in product(VALUES, VALUES, VALUES, VALUES, VALUES, LAMS)
           if all(lit.evaluate(rec, config, {"c": c, "r": r, "d": d, "a": a, "n": n}, lam)["exclusively_correct"]
                  for rec in lspec["inputs"])]
    check(f"thm:opacity-lt-region: {config} admits no jointly correct selection (sampled)",
          not bad, f"witness {bad[:1]}")

bad0 = [(c, r, d, a, n) for c, r, d, a, n in product(VALUES, VALUES, VALUES, VALUES, VALUES)
        if all(lit.evaluate(rec, "RR", {"c": c, "r": r, "d": d, "a": a, "n": n}, Fraction(0))["exclusively_correct"]
               for rec in lspec["inputs"])]
check("thm:opacity-lt-region: RR with lambda = 0 admits no jointly correct selection (sampled)",
      not bad0, f"witness {bad0[:1]}")

check("opacity: in RR the last two inequalities follow from the first five",
      all((not (0 < c and c < d and c < r and d < a and d < n))
          or (d < c + Fraction(1) * n and d < c + Fraction(1) * a)
          for c, r, d, a, n in product(VALUES, VALUES, VALUES, VALUES, VALUES)))

check("opacity: RR at lambda = 1 reproduces every ordinary score in the product",
      all(lit.evaluate(rec, "RR", lweights, Fraction(1))["scores8"]
          == lit.evaluate(rec, "O", lweights, None)["scores8"] for rec in lspec["inputs"]))

check("opacity: all four factorisations preserve C*p in all 24 candidates",
      all(lit.reader(rec["h"], mode, k, j)[4] == lit.markedness(rec["h"], j)[0 if k == "A" else 1]
          for rec in lspec["inputs"] for mode in ("R", "S") for k in ("A", "N") for j in range(8)))


def main() -> int:
    failed = [row for row in RESULTS if not row[1]]
    for label, ok, detail in RESULTS:
        if not ok:
            print(f"FAIL  {label}   [{detail}]")
    print(f"\n{len(RESULTS) - len(failed)}/{len(RESULTS)} opacity product claims verified")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
