from __future__ import annotations

import sys
from decimal import Decimal, getcontext
from fractions import Fraction

getcontext().prec = 60
TOL = Decimal("1e-30")
RESULTS: list[tuple[str, bool, str]] = []


def check(label: str, ok: bool, detail: str = "") -> None:
    RESULTS.append((label, bool(ok), detail))


def dpow(base: Decimal, exponent: Decimal) -> Decimal:
    if base == 0:
        return Decimal(0)
    if exponent == exponent.to_integral_value():
        return base ** int(exponent)
    return (exponent * base.ln()).exp()


def threshold(h: Decimal, m: Decimal, p: Decimal) -> tuple[int, Decimal, Decimal]:
    q = Decimal(1) / (p - 1)
    a = dpow(m / (p * h), q)
    total = Decimal(0)
    k = 0
    while True:
        k += 1
        total += dpow(Decimal(k), q)
        if a * total >= 1:
            return k, q, a


def objective(xs: list[Decimal], h: Decimal, m: Decimal, p: Decimal) -> Decimal:
    prev = Decimal(1)
    total = Decimal(0)
    for x in xs:
        gap = prev - x
        if gap > 0:
            total += h * dpow(gap, p)
        total += m * x
        prev = x
    return total


def solve_boundary_eta(K: int, h: Decimal, m: Decimal, p: Decimal, q: Decimal) -> Decimal:
    def mass(eta: Decimal) -> Decimal:
        s = Decimal(0)
        for i in range(1, K + 1):
            num = m * Decimal(K - i + 1) - eta
            if num > 0:
                s += dpow(num / (p * h), q)
        return s
    lo, hi = Decimal(0), m
    for _ in range(400):
        mid = (lo + hi) / 2
        if mass(mid) > 1:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


CASES = [
    (Decimal(1), Decimal(1), Decimal(2)),
    (Decimal(5), Decimal(1), Decimal(2)),
    (Decimal(3), Decimal(2), Decimal(3)),
    (Decimal(1), Decimal("0.3"), Decimal("1.5")),
    (Decimal(2), Decimal(7), Decimal(4)),
]

for h, m, p in CASES:
    K, q, a = threshold(h, m, p)
    label = f"h={h} m={m} p={p}"

    left = a * sum((dpow(Decimal(r), q) for r in range(1, K)), Decimal(0))
    right = a * sum((dpow(Decimal(r), q) for r in range(1, K + 1)), Decimal(0))
    check(f"eq:chg-threshold-pair [{label}] strict below, weak at K",
          left < 1 <= right, f"{left} .. {right}")

    if K >= 2:
        N = K - 1
        d = [a * dpow(Decimal(N - i + 1), q) for i in range(1, N + 1)]
        xs, cur = [], Decimal(1)
        for di in d:
            cur -= di
            xs.append(cur)
        check(f"thm:chg-b2(i) [{label}] sum of decreases < 1", sum(d) < 1, str(sum(d)))
        check(f"thm:chg-b2(i) [{label}] every follower activity is positive",
              all(x > 0 for x in xs), str(xs[-1]))
        worse = True
        for idx in range(N):
            for eps in (Decimal("1e-8"), Decimal("-1e-8")):
                cand = list(xs)
                cand[idx] = min(Decimal(1), max(Decimal(0), cand[idx] + eps))
                if objective(cand, h, m, p) < objective(xs, h, m, p) - TOL:
                    worse = False
        check(f"thm:chg-b2(i) [{label}] the claimed optimizer beats coordinate perturbations", worse)

    eta = solve_boundary_eta(K, h, m, p, q)
    d = []
    for i in range(1, K + 1):
        num = m * Decimal(K - i + 1) - eta
        d.append(dpow(num / (p * h), q) if num > 0 else Decimal(0))
    xs, cur = [], Decimal(1)
    for di in d:
        cur -= di
        xs.append(cur)
    check(f"thm:chg-b2(ii) [{label}] eta lies in [0, m)", 0 <= eta < m, str(eta))
    check(f"thm:chg-b2(ii) [{label}] decreases sum to 1", abs(sum(d) - 1) < Decimal("1e-25"), str(sum(d)))
    check(f"thm:chg-b2(ii) [{label}] x_i > 0 iff i < K, and x_K = 0",
          all(x > Decimal("1e-25") for x in xs[:-1]) and abs(xs[-1]) < Decimal("1e-25"),
          str(xs))

    for R in (1, 3):
        etaR = eta + m * Decimal(R)
        dR = []
        for i in range(1, K + R + 1):
            num = m * Decimal(K + R - i + 1) - etaR
            dR.append(dpow(num / (p * h), q) if num > 0 else Decimal(0))
        check(f"thm:chg-b2(iii) [{label}] R={R} keeps the first K decreases",
              all(abs(dR[i] - d[i]) < Decimal("1e-25") for i in range(K)))
        check(f"thm:chg-b2(iii) [{label}] R={R} appends exactly R zero decreases",
              all(abs(x) < Decimal("1e-25") for x in dR[K:]) and len(dR) == K + R)

def two_trigger_profile(L: int, h: Fraction, m: Fraction) -> list[Fraction]:
    n = L - 1
    if n == 0:
        return []
    from itertools import combinations

    def solve_free(free: list[int]) -> list[Fraction] | None:
        k = len(free)
        if k == 0:
            return [Fraction(0)] * n
        pos = {v: i for i, v in enumerate(free)}
        A = [[Fraction(0)] * (k + 1) for _ in range(k)]
        for r, v in enumerate(free):
            A[r][pos[v]] += 4 * h
            A[r][k] -= m
            for nb in (v - 1, v + 1):
                if nb == 0 or nb == L:
                    A[r][k] += 2 * h
                elif nb in pos:
                    A[r][pos[nb]] -= 2 * h
        for col in range(k):
            piv = next((r for r in range(col, k) if A[r][col] != 0), None)
            if piv is None:
                return None
            A[col], A[piv] = A[piv], A[col]
            inv = Fraction(1) / A[col][col]
            A[col] = [v * inv for v in A[col]]
            for r in range(k):
                if r != col and A[r][col] != 0:
                    f = A[r][col]
                    A[r] = [a - f * b for a, b in zip(A[r], A[col])]
        sol = [Fraction(0)] * n
        for v, i in pos.items():
            sol[v - 1] = A[i][k]
        return sol

    best = None
    for size in range(n, -1, -1):
        for free in combinations(range(1, L), size):
            sol = solve_free(list(free))
            if sol is None or any(v < 0 for v in sol):
                continue
            xs = [Fraction(1)] + sol + [Fraction(1)]
            value = (h * sum((xs[i] - xs[i - 1]) ** 2 for i in range(1, L + 1))
                     + m * sum(sol))
            if best is None or value < best[0]:
                best = (value, sol)
    return best[1] if best else []


def phase_of(h: Fraction, m: Fraction) -> tuple[int, Fraction]:
    target = 2 * h / m
    K = 1
    while True:
        base = Fraction(K * (K - 1), 2)
        u = (target - base) / K
        if 0 < u <= 1:
            return K, u
        if u <= 0:
            raise ValueError("no phase found")
        K += 1


for want_K, want_u, centre in ((4, Fraction(1, 4), Fraction(0)), (4, Fraction(3, 4), Fraction(1, 9))):
    m = Fraction(2)
    h = m * (Fraction(want_K * (want_K - 1), 2) + want_K * want_u) / 2
    K, u = phase_of(h, m)
    check(f"eq:ctx-phase p=2 recovers (K,u) = ({want_K},{want_u})",
          (K, u) == (want_K, want_u), f"got ({K},{u}) for h={h} m={m}")
    prof = two_trigger_profile(2 * K, h, m)
    got_centre = prof[K - 1]
    check(f"sec:chg-context: at span L = 2K = {2 * K}, (K,u) = ({want_K},{want_u}) has centre activity {centre}",
          got_centre == centre, f"got {got_centre} (profile {prof})")
    check(f"sec:chg-context: L = 2K support law — min x = 0 iff u <= 1/2  [(K,u)=({want_K},{want_u})]",
          (min(prof) == 0) == (u <= Fraction(1, 2)), f"min {min(prof)}, u {u}")

for want_K, want_u in ((4, Fraction(1, 4)), (4, Fraction(3, 4)), (3, Fraction(1, 2)), (2, Fraction(1))):
    m = Fraction(2)
    h = m * (Fraction(want_K * (want_K - 1), 2) + want_K * want_u) / 2
    K, u = phase_of(h, m)
    for L in range(2, 2 * K + 3):
        prof = two_trigger_profile(L, h, m)
        if not prof:
            continue
        positive = all(v > 0 for v in prof)
        if L <= 2 * K - 1:
            check(f"eq:ctx-support-law L={L} <= 2K-1 with (K,u)=({K},{u}): every interior activity positive",
                  positive, f"profile {prof}")
        elif L == 2 * K:
            check(f"eq:ctx-support-law L=2K={L} with (K,u)=({K},{u}): min = 0 iff u <= 1/2",
                  (min(prof) == 0) == (u <= Fraction(1, 2)), f"min {min(prof)}")
        else:
            check(f"eq:ctx-support-law L={L} >= 2K+1 with (K,u)=({K},{u}): min = 0",
                  min(prof) == 0, f"min {min(prof)}")

def one_trigger_K(h: Fraction, m: Fraction) -> int:
    a = Fraction(m, 2 * h)
    k = 0
    while True:
        k += 1
        if a * Fraction(k * (k + 1), 2) >= 1:
            return k


pts = []
for want_u in (Fraction(1, 4), Fraction(3, 4)):
    m = Fraction(2)
    h = m * (Fraction(4 * 3, 2) + 4 * want_u) / 2
    pts.append((one_trigger_K(h, m), want_u, two_trigger_profile(8, h, m)))
check("sec:chg-context: (4,1/4) and (4,3/4) share a one-trigger support boundary but differ at L = 8",
      pts[0][0] == pts[1][0] and min(pts[0][2]) != min(pts[1][2]),
      f"K's {pts[0][0]},{pts[1][0]}; centres {pts[0][2][3]},{pts[1][2][3]}")


def main() -> int:
    failed = [r for r in RESULTS if not r[1]]
    for label, ok, detail in RESULTS:
        if not ok:
            print(f"FAIL  {label}   [{detail}]")
    print(f"\n{len(RESULTS) - len(failed)}/{len(RESULTS)} continuous HG claims verified")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
