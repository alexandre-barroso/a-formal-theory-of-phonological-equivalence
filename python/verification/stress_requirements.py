import itertools
import random
import sys
from fractions import Fraction as F
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

RESULTS = []


def check(label, ok, detail=""):
    RESULTS.append((label, bool(ok), detail))


def rat(rng, lo=0, hi=20, den=(1, 2, 3, 4, 5, 8)):
    return F(rng.randint(lo, hi), rng.choice(den))


def stress_modes(rng, trials):
    bad = 0
    for _ in range(trials):
        rA, rB, wA, wB = (rat(rng) for _ in range(4))
        for cA, cB in itertools.product((False, True), repeat=2):
            neither = wA + wB
            aonly = rA + (0 if cB else wB)
            bonly = rB + (0 if cA else wA)
            both = rA + rB
            best = min(neither, aonly, bonly, both)
            both_unique = both == best and all(x > both for x in (neither, aonly, bonly))
            predicted = (not cA) and (not cB) and rA < wA and rB < wB
            if both_unique != predicted:
                bad += 1
            if not cA and (both < bonly) != (rA < wA):
                bad += 1
            if cA and both < bonly:
                bad += 1
    check("modes: mutual both-apply selected exclusively iff no carried side and both isolated inequalities", bad == 0, f"{bad} failures")


def stress_feeding(rng, trials):
    bad = 0
    for _ in range(trials):
        n = rng.randint(2, 12)
        wI, w, lam = rat(rng, 1, 10), rat(rng, 1, 40), F(rng.randint(0, 8), 8)
        if not (wI + lam * w < w):
            continue
        cost = {0: w}
        for k in range(1, n + 1):
            cost[k] = k * wI + (lam * w if k < n else 0)
        best = min(cost.values())
        argmin = sorted(k for k in cost if cost[k] == best)
        runs = n * wI <= wI + lam * w
        if runs and n not in argmin:
            bad += 1
        if not runs and argmin != [1]:
            bad += 1
        if runs and n * wI < wI + lam * w and argmin != [n]:
            bad += 1
    check("feeding chain: runs to the end iff n*wI <= wI + lambda*w, otherwise stops after the first locus", bad == 0, f"{bad} failures")


def covering_cost(wI, w, dels):
    total = 0
    prev = False
    for d in dels:
        total += wI if d else (0 if prev else w)
        prev = d
    return total


def stress_covering(rng, trials):
    bad = 0
    counts_ok = True
    for n in range(1, 13):
        wI, w = F(1), F(rng.randint(2, 9))
        sets = list(itertools.product((False, True), repeat=n))
        costs = {s: covering_cost(wI, w, s) for s in sets}
        best = min(costs.values())
        mins = [s for s in sets if costs[s] == best]
        if best != wI * ((n + 1) // 2):
            bad += 1
        expected_count = 1 if n % 2 == 0 else (n + 1) // 2
        if len(mins) != expected_count:
            counts_ok = False
        for s in mins:
            prev = False
            for d in s:
                if not d and not prev:
                    bad += 1
                prev = d
            if sum(s) != (n + 1) // 2:
                bad += 1
        lam = F(rng.randint(1, 7), 8)
        costs2 = {s: costs[s] + lam * w * sum(1 for a, b in zip((False,) + s, s) if a and b) for s in sets}
        best2 = min(costs2.values())
        mins2 = [s for s in sets if costs2[s] == best2]
        if mins2 != [tuple(k % 2 == 0 for k in range(n))]:
            bad += 1
    check("directional deletion: minimum ceil(n/2), minimisers are the left covers, parity unique under the cluster ban (n <= 12)", bad == 0 and counts_ok, f"{bad} failures, counts {'match' if counts_ok else 'differ'}")


def stress_cycles(rng, trials):
    bad = 0
    for k in range(2, 13):
        r, w = F(1), F(rng.randint(2, 9))
        best_seen = None
        mins = []
        for s in itertools.product((False, True), repeat=k):
            cost = r * sum(s) + w * sum(1 for j in range(k) if not s[j] and not s[j - 1])
            if best_seen is None or cost < best_seen:
                best_seen, mins = cost, [s]
            elif cost == best_seen:
                mins.append(s)
        if best_seen != r * ((k + 1) // 2):
            bad += 1
        if len(mins) != (k if k % 2 else 2):
            bad += 1
        for s in mins:
            if sum(s) != (k + 1) // 2 or any(not s[j] and not s[j - 1] for j in range(k)):
                bad += 1
    check("destruction cycles: minimum ceil(k/2)*r, k or 2 minimisers with independent complement (k <= 12)", bad == 0, f"{bad} failures")


def stress_indexation(rng, trials):
    bad = 0
    for _ in range(trials):
        m = rng.randint(2, 9)
        w, c, Fb = rat(rng, 1, 20), rat(rng, 1, 9), rat(rng)
        for j in range(1, m):
            if not (w * min(m, 1) + Fb < w * min(m - j, 1) + Fb + j * c):
                bad += 1
    check("indexation ablation: a partial repair of a saturated schema is never selected", bad == 0, f"{bad} failures")


def stress_gauge(rng, trials):
    from phonological_requirements.indep_gua import MARKEDNESS, SCHEMATA, evaluate
    from phonological_requirements.products import gua_products
    bad = 0
    prods = gua_products()
    for _ in range(trials):
        lam = F(rng.randint(1, 16), 16)
        wts = tuple(rat(rng, 0, 12) for _ in SCHEMATA)
        _, prod = rng.choice(prods)
        recs, _, _ = evaluate(prod, weights=wts, lam=lam)
        for r in recs:
            uniform = sum(w * (F(o) + lam * F(n)) if k in MARKEDNESS else w * lam * (F(o) + F(n)) for k, (w, (o, n)) in enumerate(zip(wts, r["coeffs"])))
            exempt_rescaled = sum(w * (F(o) + lam * F(n)) if k in MARKEDNESS else (lam * w) * (F(o) + F(n)) for k, (w, (o, n)) in enumerate(zip(wts, r["coeffs"])))
            if uniform != exempt_rescaled:
                bad += 1
    check("gauge: the uniform theory at (w_F, w_M, lambda) scores every Gua candidate as the exempt theory at (lambda w_F, w_M, lambda)", bad == 0, f"{bad} failures")


def stress_dominance(rng, trials):
    from phonological_requirements.indep_gua import SCHEMATA, evaluate
    from phonological_requirements.products import gua_products
    bad = 0
    prods = gua_products()
    for _ in range(trials):
        lam = F(rng.randint(0, 16), 16)
        wts = tuple(rat(rng, 0, 12) for _ in SCHEMATA)
        _, prod = rng.choice(prods)
        recs, best, minima = evaluate(prod, weights=wts, lam=lam)
        rows = {r["i"]: r["coeffs"] for r in recs}
        for i in minima:
            for j, cj in rows.items():
                if j == i:
                    continue
                dom = all(cj[k][0] <= rows[i][k][0] and cj[k][1] <= rows[i][k][1] for k in range(len(SCHEMATA)))
                strict = any(wts[k] > 0 and (cj[k][0] < rows[i][k][0] or (cj[k][1] < rows[i][k][1] and lam > 0)) for k in range(len(SCHEMATA)))
                if dom and strict:
                    bad += 1
    check("dominance: no Gua minimiser is dominated strictly at a positive-weight coordinate", bad == 0, f"{bad} failures")


def stress_attenuation_monotone(rng, trials):
    from phonological_requirements.attenuation_region import exact_region_certificate, exact_instance
    proof, records = exact_region_certificate()
    pts = sorted({F(0),F(1,2),F(1)} | {F(rng.randint(0,100),100) for _ in range(trials)})
    flags = [exact_instance(l, proof, records)[0] for l in pts]
    bad = sum(flag is not (l < F(1,2)) for l,flag in zip(pts,flags))
    check("attenuation: full minimizer fibers agree with the exact projected interval on rational instances",
          bad == 0 and proof["candidates"] == 9464, f"{bad} failures over {len(pts)} points in two reader variants")


def stress_schwa(rng, trials):
    from phonological_requirements.schwa_attenuation import cells, logit_diff
    C = cells(); comparisons = 0; bad = 0
    for i in range(trials):
        lam = F(i % 17,16)
        w = {k:rat(rng) for k in ("NOSCHWA","NOCCC","NOCLASH","MAX","DEP","NOCLUSTER")}
        for key,cell in C.items():
            x = int(key in (3,4,7,8)); y = int(key % 2 == 0)
            marking = w["NOCLUSTER"]*(1-x)+w["NOCCC"]*x+w["NOCLASH"]*y
            expected = marking-lam*w["NOSCHWA"]-w["DEP"] if key<=4 else lam*marking+w["MAX"]-w["NOSCHWA"]
            comparisons += 1
            bad += logit_diff(cell,w,lam) != expected
    check("schwa: complete reader contrasts match the two-context retained law including zero and unit attenuation",
          comparisons==8*trials and comparisons>0 and bad==0,f"{comparisons} comparisons, {bad} failures")


def main():
    rng = random.Random(20260918)
    stress_modes(rng, 400)
    stress_feeding(rng, 400)
    stress_covering(rng, 1)
    stress_cycles(rng, 1)
    stress_indexation(rng, 200)
    stress_gauge(rng, 12)
    stress_dominance(rng, 12)
    stress_attenuation_monotone(rng, 24)
    stress_schwa(rng, 400)
    failed = [r for r in RESULTS if not r[1]]
    for label, ok, detail in RESULTS:
        print(f"[{'PASS' if ok else 'FAIL'}] {label}  {detail}")
    print(f"{len(RESULTS) - len(failed)}/{len(RESULTS)} requirements stress suites verified")
    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main())
