from __future__ import annotations

import itertools
from fractions import Fraction as F

from phonological_requirements import certificate
from phonological_requirements.indep_gua import SCHEMATA, evaluate
from phonological_requirements.interaction_typology import lp_strict, pareto
from phonological_requirements.products import gua_observations, gua_products

POINTS = [F(0), F(1, 16), F(1, 8), F(1, 4), F(3, 10), F(2, 5), F(21, 50), F(11, 25), F(9, 20), F(23, 50), F(47, 100), F(12, 25), F(49, 100),
          F(1, 2), F(3, 5), F(31, 50), F(7, 10), F(3, 4), F(9, 10), F(1)]


def rows_at(lam, prods, obs, cache):
    per = []
    for _, prod in prods:
        if prod.id not in cache:
            recs, _, _ = evaluate(prod, lam=F(1, 8))
            cache[prod.id] = [(r["obs"], r["coeffs"]) for r in recs]
        allowed = set(obs[prod.id]["allowed"])
        rows = [(sf, [F(o) + lam * F(n) for (o, n) in co]) for sf, co in cache[prod.id]]
        per.append((prod.id, [r for sf, r in rows if sf in allowed], pareto([r for sf, r in rows if sf not in allowed])))
    return per


def feasible(lam, prods, obs, cache):
    per = rows_at(lam, prods, obs, cache)
    refutations = []
    unresolved = False
    for choice in itertools.product(*[range(len(tg)) for _, tg, _ in per]):
        strict = []
        for (_, tg, others), j in zip(per, choice):
            for o in others:
                strict.append([p - q for p, q in zip(o, tg[j])])
        ok, cert = lp_strict(strict, len(SCHEMATA))
        if ok:
            return True, {k: str(v) for k, v in zip(SCHEMATA, cert)}, None
        unresolved |= ok is None
        refutations.append({" ".join(str(x) for x in row): str(mult) for row, mult in cert.items()} if cert else None)
    return (None if unresolved else False), None, refutations


PARAMETRIC_WEIGHTS = ((3, -4), (1, 0), (1, -2), (2, -2), (2, 0),
                      (4, 0), (4, 0), (4, 0), (4, 0))


def region_weights(lam):
    if not 0 <= lam < F(1, 2):
        raise ValueError("the witness requires 0 <= lambda < 1/2")
    return [F(a) + lam*b for a, b in PARAMETRIC_WEIGHTS]


def difference_polynomial(rival, goal):
    out = [0, 0, 0]
    for (ro, rn), (go, gn), (a, b) in zip(rival, goal, PARAMETRIC_WEIGHTS):
        old, new = ro-go, rn-gn
        out[0] += old*a
        out[1] += old*b + new*a
        out[2] += new*b
    return tuple(out)


def positive_on_half_interval(poly):
    a, b, c = poly
    return a > 0 and 4*a+b >= 0 and 4*a+2*b+c >= 0


def exact_region_certificate():
    from . import frag_gua as fg
    from .evaluate import activation, marked_subjects, coefficients
    prods, obs = gua_products(), gua_observations()
    sigma = fg.make_sigma()
    declarations = fg.declarations("typed", "dynamic", fg.NEXT_WORD, None, "stop")
    records = {}
    fibers = {}
    chosen = {}
    margins = {}
    changes = {}
    total = 0
    for _, prod in prods:
        baseline, _, _ = evaluate(prod)
        reference = fg.struct_from_segments(prod.reference, prod.words, prod.phrase_of_word)
        acts = activation(sigma, reference, declarations)
        subjects = marked_subjects(sigma, reference, declarations)
        rows = []
        for record in baseline:
            state = fg.struct_from_segments(record["state"], prod.words, prod.phrase_of_word)
            cf = coefficients(sigma, reference, state, declarations, acts, subjects=subjects)
            rows.append({"i": record["i"], "surface": record["obs"],
                         "baseline": record["coeffs"], "subject": [cf[n] for n in SCHEMATA]})
        allowed = set(obs[prod.id]["allowed"])
        good = [r for r in rows if r["surface"] in allowed]
        wrong = [r for r in rows if r["surface"] not in allowed]
        if not good or not wrong:
            raise ValueError(f"{prod.id}: empty correct or incorrect fiber")
        fibers[prod.id] = [r["i"] for r in good]
        changes[prod.id] = sum(r["baseline"] != r["subject"] for r in rows)
        successful = []
        for goal in good:
            polynomials = [difference_polynomial(r[k], goal[k])
                           for k in ("baseline", "subject") for r in wrong]
            if all(positive_on_half_interval(p) for p in polynomials):
                successful.append((goal, polynomials))
        if not successful:
            raise ValueError(f"{prod.id}: parametric witness not verified")
        goal, polynomials = successful[0]
        chosen[prod.id] = goal["i"]
        margins[prod.id] = {"comparisons": len(polynomials),
                           "distinct_polynomials": [list(p) for p in sorted(set(polynomials))]}
        total += len(rows)
        records[prod.id] = rows
    if set(records) != {"G34a", "G34b", "N7", "G37c", "C24ei", "OR38", "C21b", "C23UE"} or total != 9464:
        raise ValueError("the eight focal products changed")
    critical = (("G34b", 957, 1126), ("G37c", 1584, 1571))
    deltas = []
    for ident, good, rival in critical:
        rows = {r["i"]: r for r in records[ident]}
        if fibers[ident] != [good] or rival in fibers[ident]:
            raise ValueError("the critical singleton fibers changed")
        pair = None
        for variant in ("baseline", "subject"):
            delta = tuple((ro-go, rn-gn) for (ro, rn), (go, gn)
                          in zip(rows[rival][variant], rows[good][variant]))
            if pair is not None and delta != pair:
                raise ValueError("critical reader variants disagree")
            pair = delta
        deltas.append(pair)
    expected_b = ((0,0),(1,0),(0,0),(0,0),(0,-1),(0,0),(0,0),(0,0),(0,0))
    expected_c = ((0,0),(-1,0),(0,0),(0,0),(1,-1),(0,0),(0,0),(0,0),(0,0))
    if deltas != [expected_b, expected_c]:
        raise ValueError("the exact upper-bound comparisons changed")
    rec = {"lower": "0", "upper": "1/2", "lower_included": True, "upper_included": False,
           "weight_polynomials": {k: list(v) for k, v in zip(SCHEMATA, PARAMETRIC_WEIGHTS)},
           "candidates": total, "correct_fibers": fibers, "witness_representatives": chosen,
           "subject_coefficient_changes": changes, "strict_margin_certificates": margins,
           "critical_comparisons": [{"product": k, "correct_index": g, "rival_index": r,
                                     "difference": [list(x) for x in delta]}
                                    for (k,g,r),delta in zip(critical,deltas)],
           "upper_bound_sum": {"H": [1,-2]}}
    return rec, records


def exact_instance(lam, proof, records):
    if lam < 0:
        raise ValueError("attenuation must be nonnegative")
    if lam >= F(1,2):
        return False, None
    ws = region_weights(lam)
    for ident, rows in records.items():
        good = set(proof["correct_fibers"][ident])
        for variant in ("baseline", "subject"):
            values = [sum(w*(F(a)+lam*b) for w,(a,b) in zip(ws,r[variant])) for r in rows]
            best = min(values)
            if any(r["i"] not in good for r,v in zip(rows,values) if v == best):
                raise ValueError("the exact witness has an incorrect minimizer")
    return True, {k: str(v) for k,v in zip(SCHEMATA, ws)}


def main() -> int:
    proof, records = exact_region_certificate()
    rec = {"declarations": list(SCHEMATA), "products": list(records),
           "candidates": proof["candidates"], "exact_region": proof,
           "feasible": {}, "witness": {}}
    for lam in POINTS:
        ok, ws = exact_instance(lam, proof, records)
        rec["feasible"][str(lam)] = ok
        if ok:
            rec["witness"][str(lam)] = ws
        print(lam, ok)
    certificate.write("attenuation_region.json", rec)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
