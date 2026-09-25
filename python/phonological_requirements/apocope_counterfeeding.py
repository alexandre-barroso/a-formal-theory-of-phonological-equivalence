from __future__ import annotations
from phonological_requirements import certificate, paths

import itertools
import json
import math
from fractions import Fraction as F
from pathlib import Path

from .core import ABSENT
from .evaluate import activation, coefficients, score
from .frag_apocope import declarations, sigma, struct

OUT = paths.CERTIFICATES
LAM = F(1, 8)
W_POINTS = {
    "A": dict(NO_UNSTR_V=3, NO_FINAL_C=4, MAX=2, MAX_V_INIT=100, CONTIG=100, MAX_V_BEFORE_C=0),
    "B": dict(NO_UNSTR_V=1, NO_FINAL_C=1, MAX=2, MAX_V_INIT=100, CONTIG=100, MAX_V_BEFORE_C=0),
    "C": dict(NO_UNSTR_V=1, NO_FINAL_C=10, MAX=2, MAX_V_INIT=100, CONTIG=100, MAX_V_BEFORE_C=0),
    "D": dict(NO_UNSTR_V=3, NO_FINAL_C=1, MAX=2, MAX_V_INIT=100, CONTIG=100, MAX_V_BEFORE_C=0),
    "E": dict(NO_UNSTR_V=5, NO_FINAL_C=10, MAX=2, MAX_V_INIT=100, CONTIG=100, MAX_V_BEFORE_C=10),
}


def parse(form):
    return form.split()


def render(s):
    return "".join(str(s.real[n]) for n in s.order["seg"] if s.real[n] != ABSENT)


def evaluate(form, W, contextual, lam=LAM):
    segs = parse(form)
    sg = sigma(); ref = struct(segs); nodes = ref.order["seg"]
    D = declarations(contextual)
    acts = activation(sg, ref, D)
    dele = [i for i, s in enumerate(segs) if s not in "áéíóú"]
    rows = []
    for combo in itertools.product([0, 1], repeat=len(dele)):
        s = ref
        for i, k in zip(dele, combo):
            if k:
                s = s.with_real(nodes[i], ABSENT)
        cf = coefficients(sg, ref, s, D, acts)
        deleted = tuple(i for i, k in zip(dele, combo) if k)
        rows.append((render(s), cf, score(cf, {k: W.get(k, 0) for k in D}, lam), deleted))
    lo = min(r[2] for r in rows)
    return {"winners": sorted({r[0] for r in rows if r[2] == lo}), "rows": rows, "n": len(segs)}


def final_deletion_row(e, target):
    n = e["n"]
    for r in e["rows"]:
        if r[0] == target and r[3] == tuple(range(n - len(r[3]), n)):
            return r
    raise SystemExit(f"{target!r} is not a final-deletion candidate")


def variants_at_points():
    from .observations import GCS_VARIANTS, GCS_WORDS
    out = {}
    for v, (exp_c, exp_v) in GCS_VARIANTS.items():
        W = W_POINTS[v]
        row, expected = {}, {}
        for word, (vf, cf) in GCS_WORDS.items():
            e_v = evaluate(vf, W, contextual=(v == "E"))["winners"]
            e_c = evaluate(cf, W, contextual=(v == "E"))["winners"]
            row[word] = {"V_final": e_v, "C_final": e_c}
            bv, bc = "".join(parse(vf)), "".join(parse(cf))
            expected[word] = {"V_final": [bv[:-1] if v in ("A", "D", "E") else bv],
                              "C_final": [bc[:-2] if v == "A" else bc[:-1] if v in ("C", "E") else bc]}
        out[v] = {"weights": W, "outputs": row,
                  "expected": expected, "all_words_agree": row == expected,
                  "paso_agrees": row["paso"] == {"V_final": [exp_v], "C_final": [exp_c]}}
    return out


def cost_vec(cf, names, lam):
    return [F(cf[k][0]) + lam * F(cf[k][1]) for k in names]


def region(form_targets, contextual, lam=LAM):
    import numpy as np
    from scipy.optimize import linprog
    sg = sigma()
    names = sorted(declarations(contextual))
    ineqs = []
    representative_dominates = True
    for form, target in form_targets:
        e = evaluate(form, {n: 1 for n in names}, contextual, lam)
        tgt = final_deletion_row(e, target)
        ct = cost_vec(tgt[1], names, lam)
        for c, cf, _, deleted in e["rows"]:
            if c == target:
                representative_dominates &= all(a >= b for a, b in zip(cost_vec(cf, names, lam), ct))
                continue
            d = [a - b for a, b in zip(cost_vec(cf, names, lam), ct)]
            if all(x == 0 for x in d):
                ineqs.append(d)
                continue
            ineqs.append(d)
    if representative_dominates:
        for i, row in enumerate(ineqs):
            for indices in ([i], *([j, i] for j in range(i))):
                total = [sum(ineqs[j][k] for j in indices) for k in range(len(names))]
                if all(value <= 0 for value in total):
                    return {"feasible": False, "status": "exact_nonnegative_weight_obstruction",
                            "names": names, "positive_multiplier_rows": [[str(x) for x in ineqs[j]] for j in indices],
                            "row_sum": [str(x) for x in total], "representative_dominates_correct_fiber": True,
                            "n_inequalities": len(ineqs)}
    A = np.array([[float(x) for x in d] for d in ineqs])
    n = len(names)
    c = np.zeros(n + 1); c[-1] = -1.0
    res = linprog(c, A_ub=np.hstack([-A, np.ones((len(ineqs), 1))]), b_ub=np.zeros(len(ineqs)),
                  bounds=[(0, 1000)] * n + [(None, 1.0)], method="highs")
    if res.status != 0 or res.x[-1] <= 1e-9:
        return {"feasible": None, "status": "numerical_search_without_exact_certificate",
                "solver_status": int(res.status),
                "slack": float(res.x[-1]) if res.status == 0 else None,
                "n_inequalities": len(ineqs)}
    w = {k: F(str(round(float(v), 6))) for k, v in zip(names, res.x[:-1])}
    exact = all(sum(w[k] * d for k, d in zip(names, dd)) > 0 for dd in ineqs)
    return {"feasible": True if exact else None, "slack": float(res.x[-1]), "witness": {k: str(v) for k, v in w.items()},
            "witness_exact": exact, "n_inequalities": len(ineqs)}


def variant_regions():
    from .observations import GCS_VARIANTS, GCS_WORDS
    out = {}
    for v, (exp_c, exp_v) in GCS_VARIANTS.items():
        vf, cf = GCS_WORDS["paso"]
        targets = [(vf, exp_v), (cf, exp_c)]
        out[v] = {"without_contextual": region(targets, False), "with_contextual": region(targets, True)}
    for v in ("A", "E"):
        targets = []
        for word, (vf, cf) in GCS_WORDS.items():
            segs_v, segs_c = parse(vf), parse(cf)
            def app(segs, variant_out):
                base = "".join(segs)
                if variant_out.endswith("os") or variant_out.endswith("as"):
                    return base
                if variant_out == "páso":
                    return base[:-1] if base.endswith("s") else base
                b = base[:-1] if base.endswith("s") else base
                return b[:-1]
            targets += [(vf, app(segs_v, GCS_VARIANTS[v][1])), (cf, app(segs_c, GCS_VARIANTS[v][0]))]
        out[f"{v}_all_words"] = {"targets": targets, "without_contextual": region(targets, False),
                                 "with_contextual": region(targets, True)}
    return out


def counterfeeding_bound():
    rows = {}
    for lam in (F(0), F(1, 16), F(1, 8), F(1, 5), F(1, 4), F(1, 2), F(1)):
        W = dict(NO_UNSTR_V=20, NO_FINAL_C=10, MAX=2, MAX_V_INIT=100, CONTIG=100)
        rows[str(lam)] = {"páso": evaluate("p á s o", W, False, lam)["winners"],
                          "pásos": evaluate("p á s o s", W, False, lam)["winners"]}
    return {"by_lambda_at_w_FC_10_w_MAX_2": rows, "bound": "lambda < w_MAX / w_FC = 1/5"}


def coupling():
    from .observations import GCS_TABLE_1 as T1
    sg = sigma(); names = sorted(declarations(False))
    diffs = {}
    for form in ("p á s o", "p á s o s"):
        e = evaluate(form, {n: 1 for n in names}, False)
        a = cost_vec(final_deletion_row(e, "pás")[1], names, LAM)
        b = cost_vec(final_deletion_row(e, "páso")[1], names, LAM)
        diffs[form] = {k: str(x - y) for k, x, y in zip(names, a, b)}
    p1, n1 = T1["V_final_apocope"] / T1["V_final_contexts"], T1["V_final_contexts"]
    p2, n2 = 22 / 56, 56
    p = (T1["V_final_apocope"] + 22) / (n1 + n2)
    z = (p1 - p2) / math.sqrt(p * (1 - p) * (1 / n1 + 1 / n2))
    return {"cost_differences_pas_minus_paso": diffs, "identical": diffs["p á s o"] == diffs["p á s o s"],
            "scope": "Suffix-deletion representatives. Complete C-final pas fiber contains a second correspondence.",
            "complete_fiber_log_odds_V": "w_U - w_MAX - lambda*w_FC",
            "complete_fiber_log_odds_C": "w_U - w_MAX - lambda*w_FC - w_MAX_V_BEFORE_C + log(1+exp(-w_CONTIG-(1-lambda)*w_FC))",
            "without_contextual_faithfulness": "C-final apocope odds are at least V-final apocope odds in this declared fragment.",
            "observed_conditional_rates": {"V_final": round(p1, 3), "C_final_given_C_deletion": round(p2, 3)},
            "z": round(z, 2),
            "z_scope": "Descriptive pooled independent-binomial calculation; speaker clustering and lexical sampling are not modeled. No inferential p-value is asserted."}


def maxent_fit(contextual: bool):
    import numpy as np
    from scipy.optimize import minimize
    from scipy.special import logsumexp
    from .observations import GCS_TABLE_6, GCS_WORDS
    names = sorted(declarations(contextual))
    data = []
    for word, (vf, cf) in GCS_WORDS.items():
        for form, key in ((vf, "V_final"), (cf, "C_final")):
            e = evaluate(form, {n: 1 for n in names}, contextual)
            costs, surfaces = [], []
            for c, cf_, _, deleted in e["rows"]:
                costs.append([float(x) for x in cost_vec(cf_, names, LAM)])
                surfaces.append(c)
            base = "".join(parse(form))
            b = base[:-1] if base.endswith("s") else base
            obs = {}
            for out, freq in GCS_TABLE_6[key].items():
                target = {"pásos": base, "páso": b, "pás": b[:-1]}[out]
                obs[target] = freq
            fibers = {surface: np.flatnonzero(np.asarray(surfaces) == surface) for surface in set(surfaces)}
            if any(not len(fibers.get(surface, ())) for surface in obs):
                raise ValueError("Observation outside candidate surface support")
            data.append((np.asarray(costs), fibers, obs))
    def objective(w):
        total = 0.0
        gradient = np.zeros(len(names))
        for matrix, fibers, obs in data:
            logits = -matrix @ w
            log_z = logsumexp(logits)
            expected = np.exp(logits - log_z) @ matrix
            for surface, frequency in obs.items():
                indices = fibers[surface]
                log_mass = logsumexp(logits[indices])
                total += frequency * (log_z - log_mass)
                conditional = np.exp(logits[indices] - log_mass) @ matrix[indices]
                gradient += frequency * (conditional - expected)
        return total, gradient
    x0 = np.array([{"MAX": 6.0, "MAX_V_INIT": 10.0, "CONTIG": 10.0}.get(n, 5.0) for n in names])
    rng = np.random.default_rng(260920)
    starts = [x0, np.zeros(len(names)), *[rng.uniform(1, 15, len(names)) for _ in range(4)]]
    fits = [minimize(objective, start, jac=True, bounds=[(0, None)] * len(names),
                     method="L-BFGS-B", options={"ftol": 1e-13, "gtol": 1e-7, "maxiter": 10000})
            for start in starts]
    finite = [r for r in fits if np.isfinite(r.fun) and np.all(np.isfinite(r.x))]
    if not finite:
        raise RuntimeError("No finite MaxEnt fit")
    res = min(finite, key=lambda r: r.fun)
    wv = res.x
    pred, mae = {}, []
    for (matrix, fibers, obs), (word, key) in zip(data, [(w, k) for w in GCS_WORDS for k in ("V_final", "C_final")]):
        logits = -matrix @ wv
        probability = np.exp(logits - logsumexp(logits))
        law = {surface: 100 * float(probability[indices].sum()) for surface, indices in fibers.items()}
        attested = {surface: law[surface] for surface in obs}
        other = sum(p for surface, p in law.items() if surface not in obs)
        pred[f"{word} {key}"] = {"attested": attested, "observed": obs, "other": other}
        mae += [abs(attested[k] - obs[k]) for k in obs] + [other]
    return {"weights": {n: float(v) for n, v in zip(names, wv)}, "nll": float(res.fun),
            "predictions": pred, "MAE_over_attested_and_other": sum(mae) / len(mae),
            "observation": "Surface law summed over every correspondence in each fiber.",
            "training": "Source Table 6 rounded percentage weights replicated across four schematic word pairs; not 800 independent observations.",
            "fit_status": "Finite numerical fit, not a certified global maximum or an identified parameter estimate.",
            "optimization_runs": [{"success": bool(r.success), "status": int(r.status), "nll": float(r.fun), "iterations": int(r.nit)} for r in fits]}


def transparent_bound():
    upper = -math.expm1(math.log(0.05) / 80)
    return {"zero_count": 0, "trials": 80, "one_sided_confidence": 0.95,
            "exact_binomial_upper": upper, "rule_of_three_upper": 3 / 80,
            "binary_logit_gap_lower": math.log((1 - upper) / upper),
            "scope": "Conditional two-candidate iid benchmark. It does not identify a grammar parameter from clustered speech tokens or an unconditional full-candidate probability."}


def appendix_2():
    from .observations import GCS_APPENDIX_2 as A
    vd1, cd, vd2 = A["VD1"], A["CD"], A["VD2"]
    return {"pasos": {"pás": round(cd * vd2, 3), "páso": round(cd * (1 - vd2), 3), "pásos": round(1 - cd, 3)},
            "paso": {"pás": round(vd1 + (1 - vd1) * vd2, 3), "páso": round((1 - vd1) * (1 - vd2), 3)}}


def main():
    rec = {"variants_at_points": (vp := variants_at_points()), "variant_regions": (vr := variant_regions()),
           "counterfeeding_bound": counterfeeding_bound(), "coupling": (cp := coupling()),
           "maxent_without_contextual": (m0 := maxent_fit(False)), "maxent_with_contextual": (m1 := maxent_fit(True)),
           "transparent_bound": transparent_bound(), "appendix_2_products": appendix_2(), "lambda": str(LAM)}
    OUT.mkdir(parents=True, exist_ok=True)
    certificate.write("apocope_counterfeeding.json", rec)
    print("1. variants at points:", {v: r["paso_agrees"] for v, r in vp.items()})
    for v, r in vp.items():
        print(f"   {v}: " + "; ".join(f"{w}: {o['V_final']}/{o['C_final']}" for w, o in r["outputs"].items()))
    print("2. regions (paso/pasos):")
    for v, r in vr.items():
        print(f"   {v:12s} without contextual: {r['without_contextual'].get('feasible')}   with: {r['with_contextual'].get('feasible')}")
    print("3. counterfeeding bound:", rec["counterfeeding_bound"])
    print("4. coupling:", cp)
    print("5. MaxEnt without contextual: MAE", m0["MAE_over_attested_and_other"], m0["weights"])
    for k, v in m0["predictions"].items():
        if k.startswith("paso"): print("     ", k, v)
    print("   MaxEnt with contextual: MAE", m1["MAE_over_attested_and_other"], m1["weights"])
    for k, v in m1["predictions"].items():
        if k.startswith("paso"): print("     ", k, v)
    print("6. transparent bound:", rec["transparent_bound"])
    print("7. appendix 2:", rec["appendix_2_products"])
    if not all(r["all_words_agree"] for r in vp.values()):
        raise SystemExit("F04-1: a variant failed at its weight point")


if __name__ == "__main__":
    main()
