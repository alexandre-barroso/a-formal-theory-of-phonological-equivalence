from __future__ import annotations

import sys
from fractions import Fraction as Q
from itertools import product

RESULTS: list[tuple[str, bool, str]] = []


def check(label: str, ok: bool, detail: str = "") -> None:
    RESULTS.append((label, bool(ok), detail))


def mean_range(rows: list[int], samples: int = 40) -> tuple[Q, Q]:
    lo, hi = min(rows), max(rows)
    seen = []
    for weights in product(range(1, 5), repeat=len(rows)):
        total = sum(weights)
        seen.append(Q(sum(w * r for w, r in zip(weights, rows)), total))
    return min(seen + [Q(lo)]), max(seen + [Q(hi)])


check("maxent: a one-constraint fibre with rows {0,1,2} has closed conditional-mean range [0,2]",
      mean_range([0, 1, 2]) == (Q(0), Q(2)), str(mean_range([0, 1, 2])))
check("maxent: removing the interior row 1 leaves the same interval, because 0 and 2 generate it",
      mean_range([0, 2]) == (Q(0), Q(2)), str(mean_range([0, 2])))
check("maxent: under fixed unit masses the mass function nevertheless changes from "
      "1 + z + z^2 to 1 + z^2",
      all(1 + z + z * z != 1 + z * z for z in (Q(k, 8) for k in range(1, 9))))
check("maxent: so convex-hull reduction is exact for the arbitrary-mass envelope "
      "and inexact for the fixed-mass law",
      mean_range([0, 1, 2]) == mean_range([0, 2])
      and any(Q(1, 1 + z + z * z) != Q(1, 1 + z * z) for z in (Q(k, 8) for k in range(1, 9))))

def envelope(rows_a: list[int], rows_b: list[int]) -> tuple[Q, Q]:
    la, ha = Q(min(rows_a)), Q(max(rows_a))
    lb, hb = Q(min(rows_b)), Q(max(rows_b))
    return lb - ha, hb - la


check("eq:maxent-response-envelope: for one constraint the closed envelope is the "
      "Minkowski difference of the two row intervals",
      envelope([0, 1, 2], [1, 3]) == (Q(-1), Q(3)), str(envelope([0, 1, 2], [1, 3])))
check("maxent: the envelope forgets interior row multiplicity",
      envelope([0, 1, 1, 1, 2], [1, 3]) == envelope([0, 2], [1, 3]))

def fixed_mass_law(rows: list[int], z: Q) -> list[Q]:
    weights = [z ** r for r in rows]
    total = sum(weights)
    return [w / total for w in weights]


ZS = [Q(k, 8) for k in range(1, 9)]
A, B = [0, 1, 2], [0, 2]
check("thm:max-g9: the envelope does not determine the fixed-mass law — two fibres with "
      "the same closed envelope have different laws",
      mean_range(A) == mean_range(B)
      and any(fixed_mass_law(A, z)[0] != fixed_mass_law(B, z)[0] for z in ZS))
SHIFTED_A, SHIFTED_B = [0, 2], [1, 3]
check("thm:max-g9: the fixed-mass law does not determine the arbitrary-mass envelope — "
      "shifting every row by a constant leaves the law identical at every weight while "
      "moving the envelope",
      all(fixed_mass_law(SHIFTED_A, z) == fixed_mass_law(SHIFTED_B, z) for z in ZS)
      and mean_range(SHIFTED_A) != mean_range(SHIFTED_B),
      f"{mean_range(SHIFTED_A)} vs {mean_range(SHIFTED_B)}")
check("thm:max-g9: neither consumer factors through the other, so they are incomparable",
      (mean_range(A) == mean_range(B)
       and any(fixed_mass_law(A, z) != fixed_mass_law(B, z) for z in ZS))
      and (all(fixed_mass_law(SHIFTED_A, z) == fixed_mass_law(SHIFTED_B, z) for z in ZS)
           and mean_range(SHIFTED_A) != mean_range(SHIFTED_B)))

check("maxent: deterministic HG rescaling H_{cw} = c H_w preserves every strict order and tie",
      all((Q(c) * (Q(3) * 1 + Q(5) * 2) > Q(c) * (Q(3) * 2 + Q(5) * 0))
          == ((Q(3) * 1 + Q(5) * 2) > (Q(3) * 2 + Q(5) * 0))
          for c in (1, 2, 7)))
z = Q(1, 2)
check("maxent: for unit-mass rows 0 and 1 at z = 1/2 the row-0 probability is 1/(1+z) = 2/3",
      fixed_mass_law([0, 1], z)[0] == Q(2, 3), str(fixed_mass_law([0, 1], z)[0]))
check("maxent: doubling every weight replaces z by z^2 = 1/4 and gives 1/(1+z^2) = 4/5",
      fixed_mass_law([0, 1], z * z)[0] == Q(4, 5), str(fixed_mass_law([0, 1], z * z)[0]))
check("maxent: the winner and the same-input order survive the rescaling while the "
      "probability changes from 2/3 to 4/5",
      fixed_mass_law([0, 1], z)[0] > fixed_mass_law([0, 1], z)[1]
      and fixed_mass_law([0, 1], z * z)[0] > fixed_mass_law([0, 1], z * z)[1]
      and fixed_mass_law([0, 1], z)[0] != fixed_mass_law([0, 1], z * z)[0])
def activity(w: Q, temperature: Q) -> Q:
    return w / temperature


check("maxent: rescaling the weights alone changes the activity, hence the law",
      all(activity(Q(c) * Q(1), Q(1)) != activity(Q(1), Q(1)) for c in (2, 3, 5)))
check("maxent: scaling weights and temperature by the same factor leaves w/T, hence z, "
      "hence the whole law, fixed",
      all(activity(Q(c) * Q(1), Q(c) * Q(1)) == activity(Q(1), Q(1)) for c in (2, 3, 5)))
check("maxent: so 'the weights were rescaled' omits the compensating operation and does not "
      "license probability-law equivalence",
      activity(Q(2), Q(1)) != activity(Q(1), Q(1)) == activity(Q(2), Q(2)))


def main() -> int:
    failed = [r for r in RESULTS if not r[1]]
    for label, ok, detail in RESULTS:
        if not ok:
            print(f"FAIL  {label}   [{detail}]")
    print(f"\n{len(RESULTS) - len(failed)}/{len(RESULTS)} MaxEnt mass and scaling claims verified")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
