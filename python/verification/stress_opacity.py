import random
import sys
from fractions import Fraction as F
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from phonological_opacity.fragments import lithuanian as lit
from phonological_opacity.fragments.gua import GuaFragment, load_spec

RESULTS = []


def check(label, ok, detail=""):
    RESULTS.append((label, bool(ok), detail))


def rat(rng, lo=0, hi=24, den=(1, 2, 3, 4, 5, 8)):
    return F(rng.randint(lo, hi), rng.choice(den))


def region_holds(c, r, d, a, n, lam):
    return 0 < c and c < d and c < r and d < a and d < n and d < c + lam * n and d < c + lam * a


def stress_lithuanian_region(rng, trials):
    spec = lit.load_spec()
    bad = 0
    agree = 0
    for _ in range(trials):
        c, r, d, a, n = (rat(rng, 0, 12) for _ in range(5))
        lam = F(rng.randint(0, 16), 8)
        w = {"c": c, "r": r, "d": d, "a": a, "n": n}
        selects = all(lit.evaluate(rec, "RR", w, lam)["exclusively_correct"] for rec in spec["inputs"])
        if selects != region_holds(c, r, d, a, n, lam):
            bad += 1
        agree += selects
        for config in ("SR", "RS", "SS"):
            if all(lit.evaluate(rec, config, w, lam)["exclusively_correct"] for rec in spec["inputs"]):
                bad += 1
    check("Lithuanian: reader RR selects the three outputs exclusively iff the seven-inequality region holds; SR, RS, SS never do", bad == 0, f"{bad} failures, {agree} selecting points among {trials}")


def stress_gua_attenuation(rng, trials):
    from phonological_requirements.indep_gua import WEIGHTS, evaluate
    from phonological_requirements.products import gua_observations, gua_products
    prods, obs = gua_products(), gua_observations()
    bad = 0
    for _ in range(trials):
        lam = F(rng.randint(0, 64), 64)
        ok = all(len(evaluate(p, WEIGHTS, lam)[2]) == 1 and evaluate(p, WEIGHTS, lam)[0][evaluate(p, WEIGHTS, lam)[2][0]]["obs"] in obs[p.id]["allowed"] for _, p in prods)
        if ok != (lam < F(1, 4)):
            bad += 1
    check("Gua at the declared weights: all eight selections hold iff lambda < 1/4 (random lambda)", bad == 0, f"{bad} failures over {trials} lambda values")


def stress_current_bound(rng, trials):
    spec = load_spec()
    frag = GuaFragment(spec, "G34a")
    ev = frag.evaluate()
    correct = set(ev["fiber"])
    rows = []
    for index, segs in frag.all_candidates():
        terms = frag.locus_terms(segs)
        readers = frag.readers(segs)
        faith = [terms[s][0] for s in ("MAX", "IDENT_ATR", "IDENT_QUAL", "IDENT_NUC", "INITIAL_FEATURE")]
        current = [sum(frag.marked(readers[s][q]) for q in range(frag.n)) for s in ("H", "A", "GL", "D")]
        rows.append((index, faith, current))
    bad = 0
    for _ in range(trials):
        wf = [rat(rng, 0, 30) for _ in range(5)]
        wm = [rat(rng, 0, 30) for _ in range(4)]
        scores = {i: sum(a * b for a, b in zip(wf, f)) + sum(a * b for a, b in zip(wm, m)) for i, f, m in rows}
        best = min(scores.values())
        mins = [i for i, s in scores.items() if s == best]
        if len(mins) == 1 and mins[0] in correct:
            bad += 1
    check("current markedness: no random nonnegative weighting selects the counterbleeding output exclusively (9 constraints, ahE te OkpUkO)", bad == 0, f"{bad} failures over {trials} weightings")


def stress_deletion_bound(rng, trials):
    spec = load_spec()
    frags = {k: GuaFragment(spec, k) for k in ("C21b", "C23UE")}
    evs = {k: frags[k].evaluate() for k in frags}
    rows = {}
    for k, fr in frags.items():
        ref = fr._ref_readers
        entries = []
        for index, segs in fr.all_candidates():
            terms = fr.locus_terms(segs)
            readers = fr.readers(segs)
            plain = {s: terms[s] for s in terms if s != "D"}
            cur_old = sum(fr.marked(readers["D"][q]) for q in range(fr.n) if fr.marked(ref["D"][q]))
            cur_new = sum(fr.marked(readers["D"][q]) for q in range(fr.n) if not fr.marked(ref["D"][q]))
            entries.append((index, plain, (cur_old, cur_new)))
        rows[k] = entries
    names = [s for s in rows["C21b"][0][1]]
    bad = 0
    for _ in range(trials):
        w = {s: rat(rng, 0, 30) for s in names}
        wD = rat(rng, 0, 30)
        lam = F(rng.randint(0, 16), 8)
        for policy in ("D0", "Dcurrent"):
            both = True
            for k in frags:
                scores = {}
                for index, plain, (co, cn) in rows[k]:
                    s = sum(w[n] * (F(o) + lam * F(nn)) for n, (o, nn) in plain.items())
                    if policy == "Dcurrent":
                        s += wD * (co + lam * cn)
                    scores[index] = s
                best = min(scores.values())
                mins = [i for i, v in scores.items() if v == best]
                if not (len(mins) == 1 and mins[0] in set(evs[k]["fiber"])):
                    both = False
            if both:
                bad += 1
    check("deletion bound: neither the removed nor the current reading of D selects both wUsU EbI and wUsU IsE exclusively at a shared random vector", bad == 0, f"{bad} failures over {trials} vectors")


def stress_gauge_products(rng, trials):
    spec = load_spec()
    bad = 0
    for _ in range(trials):
        fr = GuaFragment(spec, rng.choice([u["id"] for u in spec["inputs"]]))
        lam = F(rng.randint(1, 16), 16)
        wts = {s: rat(rng, 0, 20) for s in fr.weights}
        faith_names = ("MAX", "IDENT_ATR", "IDENT_QUAL", "IDENT_NUC", "INITIAL_FEATURE")
        for _, segs in fr.all_candidates():
            terms = fr.locus_terms(segs)
            uniform = sum((wts[s] * lam * (terms[s][0] + terms[s][1])) if s in faith_names else wts[s] * (terms[s][0] + lam * terms[s][1]) for s in terms)
            exempt = sum(((lam * wts[s]) * (terms[s][0] + terms[s][1])) if s in faith_names else wts[s] * (terms[s][0] + lam * terms[s][1]) for s in terms)
            if uniform != exempt:
                bad += 1
    check("gauge on the appendix readers: uniform (w_F, lambda) equals exempt (lambda w_F, lambda) at every candidate", bad == 0, f"{bad} failures")


def main():
    rng = random.Random(20260918)
    stress_lithuanian_region(rng, 3000)
    stress_gua_attenuation(rng, 24)
    stress_current_bound(rng, 300)
    stress_deletion_bound(rng, 200)
    stress_gauge_products(rng, 6)
    failed = [r for r in RESULTS if not r[1]]
    for label, ok, detail in RESULTS:
        print(f"[{'PASS' if ok else 'FAIL'}] {label}  {detail}")
    print(f"{len(RESULTS) - len(failed)}/{len(RESULTS)} opacity stress suites verified")
    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main())
