from __future__ import annotations

import sys
from decimal import Decimal, getcontext
from fractions import Fraction as Q
from itertools import permutations

getcontext().prec = 50
RESULTS: list[tuple[str, bool, str]] = []


def check(label: str, ok: bool, detail: str = "") -> None:
    RESULTS.append((label, bool(ok), detail))


def assim(x: Q) -> Q:
    return 1 + 20 * x


def faith(y: Q) -> Q:
    return 2 + 20 * y


ACTIVITIES = [Q(7, 10), Q(8, 10), Q(9, 10)]
check("eq:app-walker-source-penalty: with (w, s) = (1, 20) and (2, 20), "
      "assimilation beats faithfulness iff y - x > -1/20",
      all((assim(x) < faith(y)) == (y - x > Q(-1, 20))
          for x in (Q(k, 100) for k in range(60, 101))
          for y in (Q(k, 100) for k in range(60, 101))))
six = [(x, y) for x, y in permutations(ACTIVITIES, 2)]
check("application: there are six printed .7/.8/.9 cells with distinct target and trigger",
      len(six) == 6)
check("application: on all six printed cells the affine criterion agrees with 'trigger exceeds target'",
      all((assim(x) < faith(y)) == (y > x) for x, y in six),
      str([(str(x), str(y), assim(x) < faith(y), y > x) for x, y in six]))
check("application: the published levels are separated by 1/10, which exceeds the 1/20 offset",
      min(abs(x - y) for x, y in six) == Q(1, 10) > Q(1, 20))
check("application: the interior witness x = .80, y = .78 lies in the open strip and assimilates",
      Q(-1, 20) < Q(78, 100) - Q(80, 100) < 0 and assim(Q(80, 100)) < faith(Q(78, 100)))
check("application: the boundary witness x = .80, y = .75 gives the exact tie 17 = 17",
      assim(Q(80, 100)) == 17 == faith(Q(75, 100)), f"{assim(Q(80, 100))}, {faith(Q(75, 100))}")

def fibre_probability(scores: list[Q], masses: list[Q], target: list[bool], t: Decimal) -> Decimal:
    num = sum((Decimal(m.numerator) / Decimal(m.denominator)
               * (t * Decimal(s.numerator) / Decimal(s.denominator)).exp()
               for s, m, keep in zip(scores, masses, target) if keep), Decimal(0))
    den = sum((Decimal(m.numerator) / Decimal(m.denominator)
               * (t * Decimal(s.numerator) / Decimal(s.denominator)).exp()
               for s, m in zip(scores, masses)), Decimal(0))
    return num / den


CASES = [
    ("all maximisers in the target fibre", [Q(0), Q(0), Q(1)], [True, True, True], True),
    ("a maximiser outside the target fibre", [Q(0), Q(0), Q(1)], [True, True, False], False),
    ("tied maximisers, all inside", [Q(2), Q(2), Q(1)], [True, True, False], True),
    ("tied maximisers, one outside", [Q(2), Q(2), Q(1)], [True, False, True], False),
]
for label, scores, target, want in CASES:
    masses = [Q(1)] * len(scores)
    limit_high = fibre_probability(scores, masses, target, Decimal(200))
    goes_to_one = limit_high > Decimal("0.999999")
    maxima = max(scores)
    condition = all(keep for s, keep in zip(scores, target) if s == maxima)
    check(f"eq:app-pater-scaling: {label} — the limit is one exactly when every global "
          "maximiser lies in the target fibre",
          goes_to_one == want == condition, f"limit {limit_high}, condition {condition}")

scores = [Q(0), Q(0), Q(0), Q(1)]
target = [True, True, True, False]
masses = [Q(1)] * 4
for t_expr, want in ((Decimal(2).ln(), Q(3, 5)), (Decimal(3).ln(), Q(1, 2))):
    got = fibre_probability(scores, masses, target, t_expr)
    check(f"application: P_t(target) = 3/(3 + e^t); at t = log{'2' if want == Q(3, 5) else '3'} it is {want}",
          abs(got - Decimal(want.numerator) / Decimal(want.denominator)) < Decimal("1e-30"), str(got))
check("application: the four-parse example tends to zero, not one, because the unique global "
      "maximiser is in the wrong fibre",
      fibre_probability(scores, masses, target, Decimal(200)) < Decimal("1e-40"))
check("application: at t = log 2 the target fibre nevertheless wins the aggregate comparison",
      fibre_probability(scores, masses, target, Decimal(2).ln()) > Decimal("0.5"))

def binary_probe(m: Q, p: Q, n: int) -> Decimal:
    exponent = (Decimal(m.numerator) / Decimal(m.denominator) * n
                - Decimal(p.numerator) / Decimal(p.denominator))
    return 1 / (1 + exponent.exp())


def one_shot(m: Q, K: int) -> list[Decimal]:
    weights = [(-Decimal(m.numerator) / Decimal(m.denominator) * n).exp() for n in range(K + 1)]
    total = sum(weights, Decimal(0))
    return [w / total for w in weights]


m, p = Q(1, 2), Q(3, 2)
q = one_shot(m, 8)
ratios = [q[n + 1] / q[n] for n in range(len(q) - 1)]
expected = (-Decimal(1) / 2).exp()
check("eq:app-cabrera-one-shot: every adjacent one-shot ratio equals e^{-m}, "
      "independently of the normaliser and of K",
      all(abs(r - expected) < Decimal("1e-30") for r in ratios), str(ratios[:3]))
check("application: m is recovered as -log(q_{n+1}/q_n) = 1/2",
      abs(-ratios[0].ln() - Decimal("0.5")) < Decimal("1e-30"))
def one_shot_architecture(m: Q, p_value: Q, K: int) -> list[Decimal]:
    del p_value
    return one_shot(m, K)


check("eq:app-cabrera-one-shot: distinct MParse weights give the identical one-shot law, "
      "so p is unidentifiable from that consumer however much data it supplies",
      all(a == b for a, b in zip(one_shot_architecture(m, Q(1, 4), 8),
                                 one_shot_architecture(m, Q(9), 8)))
      and one_shot_architecture(m, Q(1, 4), 8) != one_shot(Q(1, 3), 8))
check("application: the same two MParse weights give different binary responses, "
      "so the separate structural-versus-null consumer does identify p",
      abs(binary_probe(m, Q(1, 4), 3) - binary_probe(m, Q(9), 3)) > Decimal("0.4"))
q8, q12 = one_shot(m, 8), one_shot(m, 12)
check("application: changing K changes the one-shot law's normaliser but not its adjacent ratios",
      all(abs(q12[n + 1] / q12[n] - expected) < Decimal("1e-30") for n in range(12)))


def binary(m: Q, p: Q, n: int) -> Decimal:
    exponent = Decimal(m.numerator) / Decimal(m.denominator) * n - Decimal(p.numerator) / Decimal(p.denominator)
    return 1 / (1 + exponent.exp())


check("eq:app-cabrera-binary: r_n = 1/(1 + e^{mn - p}) and its log odds are p - mn",
      all(abs(((r := binary(m, p, n)) / (1 - r)).ln()
              - (Decimal(p.numerator) / Decimal(p.denominator)
                 - Decimal(m.numerator) / Decimal(m.denominator) * n)) < Decimal("1e-30")
          for n in range(0, 8)))
check("application: with m = 1/2 and p = 3/2 the binary response at n = 3 is exactly 1/2",
      abs(binary(m, p, 3) - Decimal("0.5")) < Decimal("1e-40"), str(binary(m, p, 3)))
r3 = binary(m, p, 3)
recovered = Decimal(m.numerator) / Decimal(m.denominator) * 3 + (r3 / (1 - r3)).ln()
check("eq:app-cabrera-p: p = mn + log(r_n/(1-r_n)) recovers p = 3m = 3/2",
      abs(recovered - Decimal("1.5")) < Decimal("1e-30"), str(recovered))
check("application: the binary response crosses one half exactly at p = mn",
      abs(binary(m, p, 3) - Decimal("0.5")) < Decimal("1e-40")
      and binary(m, p, 2) > Decimal("0.5") and binary(m, p, 4) < Decimal("0.5"))


def main() -> int:
    failed = [r for r in RESULTS if not r[1]]
    for label, ok, detail in RESULTS:
        if not ok:
            print(f"FAIL  {label}   [{detail}]")
    print(f"\n{len(RESULTS) - len(failed)}/{len(RESULTS)} completion claims verified")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
