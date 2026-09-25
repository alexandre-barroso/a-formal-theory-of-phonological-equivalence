import itertools
import random
import sys
from fractions import Fraction as F
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

RESULTS = []


def check(label, ok, detail=""):
    RESULTS.append((label, bool(ok), detail))


def mass(mu, row, z):
    m = mu
    for v, zi in zip(row, z):
        m *= zi ** v
    return m


def random_ledger(rng, k):
    cands = rng.randint(2, 4)
    return [(F(rng.randint(1, 5), rng.choice((1, 2, 3))), tuple(rng.randint(0, 3) for _ in range(k))) for _ in range(cands)]


def stress_cross_product(rng, trials):
    bad = 0
    for _ in range(trials):
        k = rng.randint(1, 3)
        u, u2 = random_ledger(rng, k), random_ledger(rng, k)
        A = [i for i in range(len(u)) if rng.random() < 0.5] or [0]
        B = [i for i in range(len(u2)) if rng.random() < 0.5] or [0]
        for _ in range(8):
            z = [F(rng.randint(1, 8), 8) for _ in range(k)]
            Zu = sum(mass(mu, row, z) for mu, row in u)
            Zu2 = sum(mass(mu, row, z) for mu, row in u2)
            FA = sum(mass(u[i][0], u[i][1], z) for i in A)
            FB = sum(mass(u2[i][0], u2[i][1], z) for i in B)
            if (FA / Zu >= FB / Zu2) != (FA * Zu2 - FB * Zu >= 0):
                bad += 1
    check("cross-input order equals the sign of the cleared cross-product numerator at random activities", bad == 0, f"{bad} failures over {trials} ledger pairs")


def stress_same_input_cells(rng, trials):
    bad = 0
    for _ in range(trials):
        k = rng.randint(1, 3)
        ra, rb = tuple(rng.randint(0, 3) for _ in range(k)), tuple(rng.randint(0, 3) for _ in range(k))
        dominated = all(a >= b for a, b in zip(ra, rb))
        holds = True
        for z in itertools.product([F(1, 4), F(1, 2), F(3, 4), F(1)], repeat=k):
            if mass(F(1), ra, z) > mass(F(1), rb, z):
                holds = False
        if dominated != holds:
            bad += 1
    check("same-input weak order for every weight iff coordinatewise row domination (unit masses, grid of activities)", bad == 0, f"{bad} failures over {trials} row pairs")


def stress_normalization(rng, trials):
    bad = 0
    for _ in range(trials):
        k = rng.randint(1, 3)
        u = random_ledger(rng, k)
        z = [F(rng.randint(1, 8), 8) for _ in range(k)]
        Z = sum(mass(mu, row, z) for mu, row in u)
        probs = [mass(mu, row, z) / Z for mu, row in u]
        if sum(probs) != 1 or any(p <= 0 for p in probs):
            bad += 1
        s = F(rng.randint(2, 5))
        Z2 = sum(mass(s * mu, row, z) for mu, row in u)
        probs2 = [mass(s * mu, row, z) / Z2 for mu, row in u]
        if probs2 != probs:
            bad += 1
    check("finite laws normalize exactly, are strictly positive, and forget a common positive mass scale", bad == 0, f"{bad} failures over {trials} ledgers")


def stress_temperature_ratio(rng, trials):
    import math
    bad = 0
    for _ in range(trials):
        m = rng.randint(2, 6)
        delta = F(rng.randint(1, 6), rng.choice((1, 2)))
        crit = float(delta) / math.log(m)
        for T in (crit * 0.9, crit * 0.99, crit * 1.01, crit * 1.2):
            r = m * math.exp(-float(delta) / T)
            if (r < 1) != (T < crit):
                bad += 1
    check("maximum temperature: the level ratio m*exp(-delta/T) crosses 1 exactly at delta/log m", bad == 0, f"{bad} failures over {trials} grammars")


def main():
    rng = random.Random(20260918)
    stress_cross_product(rng, 400)
    stress_same_input_cells(rng, 400)
    stress_normalization(rng, 400)
    stress_temperature_ratio(rng, 100)
    failed = [r for r in RESULTS if not r[1]]
    for label, ok, detail in RESULTS:
        print(f"[{'PASS' if ok else 'FAIL'}] {label}  {detail}")
    print(f"{len(RESULTS) - len(failed)}/{len(RESULTS)} MaxEnt stress suites verified")
    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main())
