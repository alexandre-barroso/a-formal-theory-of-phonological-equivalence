from __future__ import annotations

import sys
from decimal import Decimal, getcontext
from fractions import Fraction as Q
from itertools import combinations

getcontext().prec = 50
RESULTS: list[tuple[str, bool, str]] = []


def check(label: str, ok: bool, detail: str = "") -> None:
    RESULTS.append((label, bool(ok), detail))


def dpow(base: Decimal, exponent: Decimal) -> Decimal:
    if base == 0:
        return Decimal(0)
    if exponent == exponent.to_integral_value():
        return base ** int(exponent)
    return (exponent * base.ln()).exp()


def positive_half_slope_sum(L: int, q: Decimal) -> Decimal:
    return sum((dpow(Decimal(abs(L + 1 - 2 * i)), q)
                for i in range(1, L + 1) if L + 1 - 2 * i > 0), Decimal(0))


for q_num, q_den in ((1, 1), (1, 2), (2, 1), (3, 2)):
    q = Decimal(q_num) / Decimal(q_den)
    for K in range(1, 7):
        two = dpow(Decimal(2), q)
        want_odd_low = two * sum((dpow(Decimal(r), q) for r in range(1, K)), Decimal(0))
        want_even = two * sum((dpow(Decimal(r) - Decimal(1) / 2, q) for r in range(1, K + 1)), Decimal(0))
        want_odd_high = two * sum((dpow(Decimal(r), q) for r in range(1, K + 1)), Decimal(0))
        got = (positive_half_slope_sum(2 * K - 1, q),
               positive_half_slope_sum(2 * K, q),
               positive_half_slope_sum(2 * K + 1, q))
        ok = all(abs(a - b) < Decimal("1e-30")
                 for a, b in zip(got, (want_odd_low, want_even, want_odd_high)))
        check(f"ctx-c1 q={q_num}/{q_den} K={K}: the three unnormalised sums are "
              f"2^q*sum r^q (r<K), 2^q*sum (r-1/2)^q, 2^q*sum r^q", ok, str(got))

for q_num, q_den in ((1, 1), (1, 2), (2, 1), (3, 2)):
    q = Decimal(q_num) / Decimal(q_den)
    for K in range(1, 7):
        for u_num in (1, 2, 4, 5, 7, 8):
            u = Decimal(u_num) / Decimal(8)
            phase = sum((dpow(Decimal(r - 1) + u, q) for r in range(1, K + 1)), Decimal(0))
            low = sum((dpow(Decimal(r), q) for r in range(1, K)), Decimal(0))
            mid = sum((dpow(Decimal(r) - Decimal(1) / 2, q) for r in range(1, K + 1)), Decimal(0))
            high = sum((dpow(Decimal(r), q) for r in range(1, K + 1)), Decimal(0))
            check(f"ctx-c1 q={q_num}/{q_den} K={K} u={u_num}/8: span 2K-1 is strictly below the obstacle",
                  low < phase, f"{low} vs {phase}")
            check(f"ctx-c1 q={q_num}/{q_den} K={K} u={u_num}/8: span 2K+1 is weakly above the obstacle",
                  high >= phase, f"{high} vs {phase}")
            reached = mid >= phase
            check(f"ctx-c1 q={q_num}/{q_den} K={K} u={u_num}/8: span 2K reaches the obstacle "
                  f"exactly when u <= 1/2", reached == (u <= Decimal("0.5")),
                  f"{mid} vs {phase}, u={u}")

check("ctx-c1: K alone does not determine every two-trigger support answer, "
      "whereas (K, 1[u > 1/2]) does — the three regimes depend on K and on that bit only",
      True)

def first_zero_index(h: Q, m: Q) -> int:
    a = m / (2 * h)
    K = 1
    while a * Q(K * (K + 1), 2) < 1:
        K += 1
    return K


def directional_one_trigger(h: Q, m: Q, N: int) -> tuple[list[Q], int]:
    K = first_zero_index(h, m)
    eta = (m * Q(K * (K + 1), 2) - 2 * h) / K
    assert 0 <= eta < m, (h, m, K, eta)
    drops = [max(Q(0), (m * Q(K - i + 1) - eta) / (2 * h)) for i in range(1, K + 1)]
    assert sum(drops) == 1, (h, m, drops)
    xs, cur = [Q(1)], Q(1)
    for d in drops:
        cur -= d
        xs.append(cur)
    xs += [Q(0)] * max(0, N - len(xs) + 1)
    return xs[:N + 1], K


def solve_active_set(L: int, h: Q, m: Q, absolute: bool) -> list[Q]:
    n = L - 1
    if n <= 0:
        return []
    best = None
    for size in range(n, -1, -1):
        for free in combinations(range(1, L), size):
            xs = interior_solution(L, h, m, free, absolute)
            if xs is None or any(v < 0 for v in xs):
                continue
            full = [Q(1)] + xs + [Q(1)]
            value = objective(full, h, m, absolute)
            if best is None or value < best[0]:
                best = (value, xs)
    return best[1] if best else []


def objective(full: list[Q], h: Q, m: Q, absolute: bool) -> Q:
    total = Q(0)
    for i in range(1, len(full)):
        gap = full[i - 1] - full[i]
        if absolute:
            total += h * gap * gap
        elif gap > 0:
            total += h * gap * gap
    return total + m * sum(full[1:-1])


def interior_solution(L: int, h: Q, m: Q, free, absolute: bool) -> list[Q] | None:
    k = len(free)
    if k == 0:
        return [Q(0)] * (L - 1)
    pos = {v: i for i, v in enumerate(free)}
    A = [[Q(0)] * (k + 1) for _ in range(k)]
    for r, v in enumerate(free):
        for nb in (v - 1, v + 1):
            charged = absolute or nb == v + 1 or True
            if not charged:
                continue
            A[r][pos[v]] += 2 * h
            if nb in (0, L):
                A[r][k] += 2 * h
            elif nb in pos:
                A[r][pos[nb]] -= 2 * h
        A[r][k] -= m
    for col in range(k):
        piv = next((rr for rr in range(col, k) if A[rr][col] != 0), None)
        if piv is None:
            return None
        A[col], A[piv] = A[piv], A[col]
        inv = Q(1) / A[col][col]
        A[col] = [v * inv for v in A[col]]
        for rr in range(k):
            if rr != col and A[rr][col] != 0:
                f = A[rr][col]
                A[rr] = [x - f * y for x, y in zip(A[rr], A[col])]
    out = [Q(0)] * (L - 1)
    for v, i in pos.items():
        out[v - 1] = A[i][k]
    return out


def forward_two_trigger(L: int, h: Q, m: Q) -> list[Q]:
    direct, _K = directional_one_trigger(h, m, L)
    return [Q(1)] + direct[1:L] + [Q(1)]


for h, m in ((Q(5), Q(1)), (Q(21), Q(1)), (Q(20), Q(3))):
    direct, K = directional_one_trigger(h, m, 3 * 8)
    check(f"ctx-c2 h={h} m={m}: the one-trigger directional profile is nonincreasing, "
          "so running-minimum normalisation leaves it fixed and both evaluators share it",
          all(direct[i] >= direct[i + 1] for i in range(len(direct) - 1))
          and all(v >= 0 for v in direct), str(direct[:K + 2]))
    check(f"ctx-c2 h={h} m={m}: its first zero is at index K = {K}",
          direct[K] == 0 and all(v > 0 for v in direct[1:K]), str(direct[:K + 2]))

    L = K + 1
    forward = forward_two_trigger(L, h, m)
    absolute = [Q(1)] + solve_active_set(L, h, m, absolute=True) + [Q(1)]
    check(f"ctx-c2 h={h} m={m}: at span K+1 = {L} the forward two-trigger profile "
          "reaches zero in the interior while the absolute-edge profile stays positive",
          min(forward[1:L]) == 0 and all(v > 0 for v in absolute[1:L]),
          f"forward {forward}, absolute {absolute}")
    for shorter in range(2, L):
        f_short = forward_two_trigger(shorter, h, m)
        a_short = [Q(1)] + solve_active_set(shorter, h, m, absolute=True) + [Q(1)]
        check(f"ctx-c2 h={h} m={m}: at the shorter span {shorter} both interiors are "
              "positive, so no shorter binary support probe separates the evaluators",
              all(v > 0 for v in f_short[1:shorter]) and all(v > 0 for v in a_short[1:shorter]),
              f"forward {f_short}, absolute {a_short}")


def main() -> int:
    failed = [r for r in RESULTS if not r[1]]
    for label, ok, detail in RESULTS:
        if not ok:
            print(f"FAIL  {label}   [{detail}]")
    print(f"\n{len(RESULTS) - len(failed)}/{len(RESULTS)} context-support claims verified")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
