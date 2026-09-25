import random
import sys
from fractions import Fraction as F
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from phonological_equivalence.application_model import QuadraticProfile, QuadraticSupportIndex

RESULTS = []


def check(label, ok, detail=""):
    RESULTS.append((label, bool(ok), detail))


def energy(x, h, sites, p=2):
    total = F(0)
    prev = F(1)
    for i, xi in enumerate(x):
        d = prev - xi
        if d > 0:
            total += h * d ** p
        total += sites[i] * xi
        prev = xi
    return total


def running_min(x):
    out, cur = [], F(1)
    for xi in x:
        cur = min(cur, xi)
        out.append(cur)
    return out


def stress_quadratic_profile(rng, trials):
    bad = 0
    for _ in range(trials):
        h, m = F(rng.randint(1, 40), rng.choice((1, 2, 4))), F(rng.randint(1, 12), rng.choice((1, 2, 4)))
        K = QuadraticSupportIndex(h, m)
        N = K + rng.randint(0, 4)
        x = QuadraticProfile(h, m, N)[1:]
        sites = [m] * N
        if any(a < b for a, b in zip(x, x[1:])):
            bad += 1
        if any(v < 0 for v in x) or x[0] > 1:
            bad += 1
        positives = sum(1 for v in x if v > 0)
        if positives != K - 1 and N >= K - 1:
            bad += 1
        base = energy(x, h, sites)
        for _ in range(30):
            y = [max(F(0), min(F(1), v + F(rng.randint(-3, 3), rng.choice((5, 7, 9, 11))))) for v in x]
            y = running_min(y)
            if energy(y, h, sites) < base:
                bad += 1
        longer = QuadraticProfile(h, m, N + 3)[1:]
        if longer[:N] != x or any(v != 0 for v in longer[N:]) and N >= K:
            bad += 1
    check("quadratic persistence: nonincreasing profile, K-1 positive followers, no better perturbation, exact zero tail (random h, m)", bad == 0, f"{bad} failures over {trials} weight pairs")


def stress_running_minimum(rng, trials):
    bad = 0
    for _ in range(trials):
        N = rng.randint(2, 9)
        h = F(rng.randint(1, 20))
        sites = [F(rng.randint(0, 9)) for _ in range(N)]
        x = [F(rng.randint(0, 8), 8) for _ in range(N)]
        y = running_min(x)
        if energy(y, h, sites) > energy(x, h, sites):
            bad += 1
        if sum(a * b for a, b in zip(sites, y)) > sum(a * b for a, b in zip(sites, x)):
            bad += 1
    check("nonnegative sites: running-minimum normalization weakly lowers the objective and every site term (random heterogeneous weights)", bad == 0, f"{bad} failures over {trials} profiles")


def stress_negative_site(rng, trials):
    found = 0
    for _ in range(trials):
        N = rng.randint(3, 7)
        h = F(rng.randint(1, 8))
        sites = [F(rng.randint(0, 3)) for _ in range(N)]
        sites[rng.randint(1, N - 1)] = F(-rng.randint(2, 8))
        grid = [F(k, 4) for k in range(5)]
        best_mono, best_any = None, None
        import itertools
        for x in itertools.product(grid, repeat=N):
            e = energy(list(x), h, sites)
            if best_any is None or e < best_any:
                best_any = e
            if all(a >= b for a, b in zip(x, x[1:])) and (best_mono is None or e < best_mono):
                best_mono = e
        if best_any < best_mono:
            found += 1
    check("one negative site: the grid minimum over all profiles beats the best nonincreasing profile in a majority of random instances", found > trials // 2, f"{found} of {trials} instances")


def stress_witness():
    h, sites = F(5), [F(1), F(1), F(-4), F(1), F(1), F(1)]
    x = [F(3, 4), F(5, 8), F(1), F(3, 4), F(1, 2), F(3, 8)]
    mono = [F(7, 8), F(7, 8), F(7, 8), F(5, 8), F(3, 8), F(1, 4)]
    import itertools
    grid = [F(k, 8) for k in range(9)]
    best_mono = min(energy(list(y), h, sites) for y in itertools.product(grid, repeat=6) if all(a >= b for a, b in zip((F(1),) + y, y)))
    check("obstruction witness: h = 5, m = (1,1,-4,1,1,1): the non-monotone profile scores 3/32 and the best nonincreasing grid profile 9/32", energy(x, h, sites) == F(3, 32) and energy(mono, h, sites) == F(9, 32) and best_mono == F(9, 32), f"{energy(x, h, sites)} {energy(mono, h, sites)} {best_mono}")


def main():
    rng = random.Random(20260918)
    stress_quadratic_profile(rng, 200)
    stress_running_minimum(rng, 2000)
    stress_negative_site(rng, 12)
    stress_witness()
    failed = [r for r in RESULTS if not r[1]]
    for label, ok, detail in RESULTS:
        print(f"[{'PASS' if ok else 'FAIL'}] {label}  {detail}")
    print(f"{len(RESULTS) - len(failed)}/{len(RESULTS)} continuous HG stress suites verified")
    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main())
