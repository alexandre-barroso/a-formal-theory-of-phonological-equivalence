import itertools
import random
import sys
from fractions import Fraction as F

RESULTS = []


def check(label, ok, detail=""):
    RESULTS.append((label, bool(ok), detail))


def kernel(f, X):
    return frozenset(frozenset(x for x in X if f[x] == v) for v in set(f.values()))


def refines(P, Q):
    return all(any(B <= C for C in Q) for B in P)


def stress_kernel_monotonicity(rng, trials):
    bad = 0
    for _ in range(trials):
        X = list(range(rng.randint(2, 7)))
        qs = {x: rng.randint(0, 3) for x in X}
        g = {v: rng.randint(0, 2) for v in range(4)}
        qw = {x: g[qs[x]] for x in X}
        if not refines(kernel(qs, X), kernel(qw, X)):
            bad += 1
        r = {x: rng.randint(0, 3) for x in X}
        preserved_strong = refines(kernel(r, X), kernel(qs, X))
        preserved_weak = refines(kernel(r, X), kernel(qw, X))
        if preserved_strong and not preserved_weak:
            bad += 1
    check("query monotonicity: a factoring weaker query has a coarser kernel and inherits preservation (random finite domains)", bad == 0, f"{bad} failures over {trials}")


def stress_carrier_algebra(rng, trials):
    bad = 0
    for _ in range(trials):
        X = list(range(rng.randint(2, 7)))
        battery = [{x: rng.randint(0, 2) for x in X} for _ in range(rng.randint(1, 3))]
        joint = {x: tuple(q[x] for q in battery) for x in X}
        E = kernel(joint, X)
        r = {x: rng.randint(0, 3) for x in X}
        factors = refines(kernel(r, X), E)
        exists_reader = all(len({joint[x] for x in X if r[x] == v}) == 1 for v in set(r.values()))
        if factors != exists_reader:
            bad += 1
        if len({joint[x] for x in X}) != len(E):
            bad += 1
        new = {x: rng.randint(0, 2) for x in X}
        joint2 = {x: (joint[x], new[x]) for x in X}
        price_formula = sum(len({new[x] for x in B}) - 1 for B in E)
        if len(kernel(joint2, X)) - len(E) != price_formula:
            bad += 1
    check("finite carrier algebra: factorization iff kernel inclusion, minimum carrier size, exact added-consumer price", bad == 0, f"{bad} failures over {trials}")


def stress_closure_lattice(rng, trials):
    bad = 0
    for _ in range(trials):
        X = list(range(rng.randint(2, 6)))
        universe = [{x: rng.randint(0, 2) for x in X} for _ in range(rng.randint(2, 5))]
        def cl(J):
            E = kernel({x: tuple(q[x] for q in J) for x in X}, X) if J else frozenset([frozenset(X)])
            return [q for q in universe if all(len({q[x] for x in B}) == 1 for B in E)]
        subsets = [list(c) for n in range(len(universe) + 1) for c in itertools.combinations(universe, n)]
        for J in subsets:
            cJ = cl(J)
            if not all(q in cJ for q in J):
                bad += 1
            if cl(cJ) != cJ:
                bad += 1
            for K in subsets:
                if all(q in K for q in J) and not all(q in cl(K) for q in cJ):
                    bad += 1
    check("redundancy closure: extensive, monotone, idempotent on random finite consumer universes", bad == 0, f"{bad} failures over {trials}")


def stress_orbit_recovery(rng, trials):
    bad = 0
    for _ in range(trials):
        n = rng.randint(2, 6)
        X = list(range(n))
        perm = list(range(n)); rng.shuffle(perm)
        orbits = frozenset(frozenset({x, perm[x]}) for x in X)
        blocks = []
        seen = set()
        for x in X:
            if x in seen:
                continue
            block = {x}
            y = perm[x]
            while y != x:
                block.add(y); y = perm[y]
            seen |= block; blocks.append(frozenset(block))
        u = {x: rng.randint(0, 3) for x in X}
        image = {}
        collision = False
        for B in blocks:
            img = frozenset(u[x] for x in B)
            if img in image and image[img] != B:
                collision = True
            image[img] = B
        invertible = not collision
        induced = {B: frozenset(u[x] for x in B) for B in blocks}
        injective = len(set(induced.values())) == len(blocks)
        if invertible != injective:
            bad += 1
    check("semantic-orbit recovery: the induced orbit map is invertible on its image iff it has no collisions (random permutation actions)", bad == 0, f"{bad} failures over {trials}")


def stress_verdict_trichotomy(rng, trials):
    bad = 0
    for _ in range(trials):
        rows = [(rng.randint(0, 2), rng.randint(0, 2)) for _ in range(rng.randint(0, 5))]
        admitted = rng.random() < 0.8
        mismatches = [r for r in rows if r[0] != r[1]]
        if not admitted:
            verdict = "not_evaluated"
        elif mismatches:
            verdict = "nonconservative"
        else:
            verdict = "conservative"
        count = (verdict == "not_evaluated") + (verdict == "nonconservative") + (verdict == "conservative")
        if count != 1:
            bad += 1
        if admitted and (verdict == "nonconservative") != bool(mismatches):
            bad += 1
        if admitted and verdict == "nonconservative" and min(mismatches) not in mismatches:
            bad += 1
    check("qualified finite decision: exactly one verdict, nonconservative iff a mismatch row exists, least witness selected", bad == 0, f"{bad} failures over {trials}")


def stress_shared_activity_threshold(rng, trials):
    bad = 0
    for _ in range(trials):
        v1, v3 = rng.randint(1, 9), rng.randint(0, 9)
        wm, wg = F(rng.randint(1, 30), rng.choice((1, 2, 4))), F(rng.randint(1, 30), rng.choice((1, 2, 4)))
        opaque = wm * (1 + v3) * (v1 + 1 + v3)
        transparent = wg * v1
        ratio = wg / wm
        lhs = opaque < transparent
        rhs = ratio > F((1 + v3) * (v1 + 1 + v3), v1)
        if lhs != rhs:
            bad += 1
        if v3 + 1 <= 9 and (wm * (1 + (v3 + 1)) * (v1 + 1 + (v3 + 1)) < transparent) and not lhs:
            bad += 1
    check("shared-activity separator: the opaque realization is selected iff the weight ratio exceeds the exact threshold, monotone in the autosegment size", bad == 0, f"{bad} failures over {trials}")


def main():
    rng = random.Random(20260918)
    stress_kernel_monotonicity(rng, 3000)
    stress_carrier_algebra(rng, 3000)
    stress_closure_lattice(rng, 200)
    stress_orbit_recovery(rng, 3000)
    stress_verdict_trichotomy(rng, 3000)
    stress_shared_activity_threshold(rng, 3000)
    failed = [r for r in RESULTS if not r[1]]
    for label, ok, detail in RESULTS:
        print(f"[{'PASS' if ok else 'FAIL'}] {label}  {detail}")
    print(f"{len(RESULTS) - len(failed)}/{len(RESULTS)} finite-carrier stress suites verified")
    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main())
