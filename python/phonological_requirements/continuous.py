from __future__ import annotations

from fractions import Fraction
from typing import Sequence


def reach(m: Sequence[Fraction]) -> list[Fraction]:
    out, acc = [], Fraction(0)
    for v in reversed(list(m)):
        acc += v
        out.append(acc)
    return list(reversed(out))


def solve_quadratic(h: Fraction, m: Sequence[Fraction]) -> list[Fraction]:
    M = reach(m)
    N = len(M)
    free = [max(Fraction(0), M[i]) / (2 * h) for i in range(N)]
    if sum(free) <= 1:
        return free
    order = sorted(range(N), key=lambda i: -M[i])
    for k in range(1, N + 1):
        act = order[:k]
        mu = (sum(M[i] for i in act) - 2 * h) / k
        if mu < 0:
            continue
        d = [max(Fraction(0), (M[i] - mu) / (2 * h)) for i in range(N)]
        if sum(1 for x in d if x > 0) == k and abs(sum(d) - 1) == 0:
            return d
    raise RuntimeError("no KKT point found")


def profile(h: Fraction, m: Sequence[Fraction]) -> list[Fraction]:
    d = solve_quadratic(h, m)
    x = [Fraction(1)]
    acc = Fraction(0)
    for v in d:
        acc += v
        x.append(Fraction(1) - acc)
    return x


def objective_x(h: Fraction, m: Sequence[Fraction], p: int, x: Sequence[Fraction]) -> Fraction:
    tot = Fraction(0)
    for i in range(1, len(x)):
        diff = x[i - 1] - x[i]
        if diff > 0:
            tot += h * diff ** p
    for i in range(1, len(x)):
        tot += m[i - 1] * x[i]
    return tot
