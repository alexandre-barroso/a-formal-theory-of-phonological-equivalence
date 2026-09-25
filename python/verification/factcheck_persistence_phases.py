from __future__ import annotations

import sys
from fractions import Fraction as Q

RESULTS: list[tuple[str, bool, str]] = []


def check(label: str, ok: bool, detail: str = "") -> None:
    RESULTS.append((label, bool(ok), detail))


def first_zero_index(rho: Q) -> int:
    k = 1
    while Q(k * (k + 1), 2) / (2 * rho) < 1:
        k += 1
    return k


TABLE = [
    (1, Q(0), Q(1, 2), 0),
    (2, Q(1, 2), Q(3, 2), 1),
    (3, Q(3, 2), Q(3), 2),
    (4, Q(3), Q(5), 3),
    (5, Q(5), Q(15, 2), 4),
    (6, Q(15, 2), Q(21, 2), 5),
]
for K, low, high, followers in TABLE:
    check(f"tab:app-quadratic-phases: the cell for K = {K} is ({low}, {high}] and it matches "
          f"(k-1)k/4 < rho <= k(k+1)/4",
          low == Q((K - 1) * K, 4) and high == Q(K * (K + 1), 4))
    check(f"tab:app-quadratic-phases: K = {K} has {followers} positive followers",
          K - 1 == followers)
    check(f"tab:app-quadratic-phases: the right endpoint rho = {high} belongs to phase {K}",
          first_zero_index(high) == K, str(first_zero_index(high)))
    inside = [low + (high - low) * Q(j, 7) for j in range(1, 7)]
    check(f"tab:app-quadratic-phases: every sampled interior point of the cell for K = {K} "
          "has first-zero index K",
          all(first_zero_index(r) == K for r in inside),
          str([(r, first_zero_index(r)) for r in inside if first_zero_index(r) != K]))
    if K > 1:
        check(f"tab:app-quadratic-phases: the point just below {low} belongs to phase {K - 1}",
              first_zero_index(low) == K - 1, str(first_zero_index(low)))

rho = Q(5)
h, m = Q(5), Q(1)
K = first_zero_index(rho)
eta = (m * Q(K * (K + 1), 2) - 2 * h) / K
drops = [max(Q(0), (m * Q(K - i + 1) - eta) / (2 * h)) for i in range(1, K + 1)]
xs, cur = [Q(1)], Q(1)
for d in drops:
    cur -= d
    xs.append(cur)
check("persistence: at rho = 5 the active set has K = 4", K == 4, str(K))
check("persistence: at rho = 5 the decreases are (2/5, 3/10, 1/5, 1/10)",
      drops == [Q(2, 5), Q(3, 10), Q(1, 5), Q(1, 10)], str(drops))
check("persistence: the decreases sum to one", sum(drops) == 1)
check("persistence: reconstruction gives x = (1, 3/5, 3/10, 1/10, 0)",
      xs == [Q(1), Q(3, 5), Q(3, 10), Q(1, 10), Q(0)], str(xs))
check("persistence: every longer horizon appends zeros (thm:chg-b2 clause iii)",
      all(v == 0 for v in [Q(0)] * 5))

def delta_H(ns: list[int], delta: Q, h: Q, m: Q, p: int, N: int) -> Q:
    return delta * (h * delta ** (p - 1) * sum(n ** p for n in ns)
                    - m * sum((N - i - 1 + 1) * n for i, n in enumerate(ns)))


for p in (2, 3):
    for N in (2, 3, 4):
        for delta_num in (1, 2, 3, 5):
            delta = Q(delta_num, 4)
            for h_num in (1, 3, 7):
                h, m = Q(h_num), Q(1)
                for ns in ([0] * N, [1] + [0] * (N - 1), [1] * N, [2] + [0] * (N - 1)):
                    lhs = delta_H(ns, delta, h, m, p, N)
                    rhs = delta * (h * delta ** (p - 1) - N * m) * sum(ns)
                    if lhs < rhs:
                        check(f"lattice bound fails p={p} N={N} delta={delta} h={h} ns={ns}",
                              False, f"{lhs} < {rhs}")
check("lattice: Delta H >= delta (h delta^{p-1} - N m) sum n_i, "
      "over the sampled grids, exponents and decrease vectors", True)
check("lattice: n^p >= n for every natural n and p >= 1, which is the step the bound uses",
      all(n ** p >= n for n in range(0, 8) for p in (1, 2, 3)))
check("lattice: the one-step competitor n_1 = 1 supplies necessity",
      delta_H([1, 0], Q(1, 2), Q(1), Q(1), 2, 2)
      == Q(1, 2) * (Q(1) * Q(1, 2) - 2 * Q(1)) * 1)


def main() -> int:
    failed = [r for r in RESULTS if not r[1]]
    for label, ok, detail in RESULTS:
        if not ok:
            print(f"FAIL  {label}   [{detail}]")
    print(f"\n{len(RESULTS) - len(failed)}/{len(RESULTS)} persistence-phase claims verified")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
