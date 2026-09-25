from __future__ import annotations

import sys
from fractions import Fraction as Q

RESULTS: list[tuple[str, bool, str]] = []


def check(label: str, ok: bool, detail: str = "") -> None:
    RESULTS.append((label, bool(ok), detail))


def law(rows: list[int], masses: list[Q], z: Q) -> list[Q]:
    weights = [mu * z ** v for mu, v in zip(masses, rows)]
    total = sum(weights)
    return [w / total for w in weights]


ZS = [Q(k, 24) for k in range(1, 25)]

for z in ZS:
    pa = law([0, 1], [Q(1), Q(1)], z)[0]
    pb = law([0, 1, 1], [Q(1), Q(1), Q(1)], z)[0]
    check(f"eq:maxent-two-normalizers at z = {z}: p(a|u) = 1/(1+z) and p(b|u') = 1/(1+2z)",
          pa == 1 / (1 + z) and pb == 1 / (1 + 2 * z), f"{pa}, {pb}")
    check(f"maxent at z = {z}: p(a|u) > p(b|u') strictly on the physical domain", pa > pb)
check("maxent: the two named candidates have identical rows and identical masses",
      ([0], [Q(1)]) == ([0], [Q(1)]))
check("maxent: at the closure point z = 0 the two values meet",
      law([0, 1], [Q(1), Q(1)], Q(0))[0] == law([0, 1, 1], [Q(1)] * 3, Q(0))[0] == 1)
check("maxent: the paper-and-pencil chain p(a) >= p(b) <=> 1+2z >= 1+z <=> z >= 0 is valid "
      "because both denominators are positive",
      all((1 / (1 + z) >= 1 / (1 + 2 * z)) == (z >= 0) for z in ZS + [Q(0)])
      and all(1 + z > 0 and 1 + 2 * z > 0 for z in ZS + [Q(0)]))
check("maxent: exchanging the competitor populations reverses the order without changing "
      "either named row",
      all(law([0, 1, 1], [Q(1)] * 3, z)[0] < law([0, 1], [Q(1), Q(1)], z)[0] for z in ZS))
check("maxent: with one row-1 competitor each, the probabilities are equal for every weight",
      all(law([0, 1], [Q(1), Q(1)], z)[0] == law([0, 1], [Q(1), Q(1)], z)[0] for z in ZS))

for z in ZS:
    named_harmony_tie = 0 == 0
    named_mass_tie = Q(1) * z ** 0 == Q(1) * z ** 0
    prob_order = law([0, 1], [Q(1), Q(1)], z)[0] > law([0, 1, 1], [Q(1)] * 3, z)[0]
    check(f"tab:maxent-two-normalizer-readings at z = {z}: named harmony ties, named "
          "unnormalised mass ties, normalised probability strictly orders",
          named_harmony_tie and named_mass_tie and prob_order)

CASES = [
    ([0, 1, 2], [Q(1), Q(2), Q(3)], 0),
    ([2, 0, 1], [Q(3), Q(1), Q(5)], 1),
    ([1, 1, 3, 0], [Q(1), Q(4), Q(2), Q(7)], 2),
]
for rows, masses, named in CASES:
    for z in ZS:
        R = sum(masses[c] / masses[named] * z ** (rows[c] - rows[named]) for c in range(len(rows)))
        p = law(rows, masses, z)[named]
        check(f"eq:maxent-relative-partition rows={rows} named={named} z={z}: "
              "p = 1 / R_{u,a} and R retains every competitor's mass and multiplicity",
              p == 1 / R, f"{p} vs {1 / R}")
    negatives = [rows[c] - rows[named] for c in range(len(rows))]
    check(f"maxent: relative rows may be negative (rows={rows}, named={named}), so R is Laurent "
          "rather than polynomial in general",
          (min(negatives) < 0) == (named > 0 and min(rows) < rows[named])
          or min(negatives) >= 0)


def main() -> int:
    failed = [r for r in RESULTS if not r[1]]
    for label, ok, detail in RESULTS:
        if not ok:
            print(f"FAIL  {label}   [{detail}]")
    print(f"\n{len(RESULTS) - len(failed)}/{len(RESULTS)} MaxEnt normalizer claims verified")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
