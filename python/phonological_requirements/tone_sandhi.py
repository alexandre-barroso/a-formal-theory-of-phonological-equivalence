from __future__ import annotations
from phonological_requirements import certificate, paths

import json
import math
import sys
import time
from fractions import Fraction as F
from pathlib import Path

import numpy as np

from .evaluate import activation, coefficients, score
from .frag_sandhi import SG, TONES, build, candidates, declarations, surface

OUT = paths.CERTIFICATES
LAM = F(1, 8)
DECLS = declarations()
NAMES = sorted(DECLS)


def toks(seq):
    return [seq[i:i + 2] for i in range(0, len(seq), 2)] if isinstance(seq, str) else list(seq)


def rows(tones):
    ref = build(tones); acts = activation(SG, ref, DECLS)
    return [(surface(c), coefficients(SG, ref, c, DECLS, acts)) for c in candidates(ref)]


def coef_matrix(tones, lam):
    return [(sf, np.array([float(co[k][0]) + float(lam) * float(co[k][1]) for k in NAMES])) for sf, co in rows(tones)]


def maxent(tones, w, lam):
    M = coef_matrix(tones, lam)
    wv = np.array([w[k] for k in NAMES])
    h = np.array([-(r @ wv) for _, r in M])
    p = np.exp(h - h.max()); p /= p.sum()
    return {sf: float(x) for (sf, _), x in zip(M, p)}


def categorical(tones, w, lam=LAM):
    M = coef_matrix(tones, lam)
    wv = np.array([w[k] for k in NAMES])
    cost = [r @ wv for _, r in M]
    best = min(cost)
    return sorted({sf for (sf, _), c in zip(M, cost) if abs(c - best) < 1e-9})


def loglik(table, w, lam, cache):
    ll = 0.0
    for ur, srs in table.items():
        if (ur, lam) not in cache:
            cache[(ur, lam)] = coef_matrix(list(ur), lam)
        M = cache[(ur, lam)]
        wv = np.array([w[k] for k in NAMES])
        h = np.array([-(r @ wv) for _, r in M]); h -= h.max()
        logZ = math.log(np.exp(h).sum())
        idx = {sf: i for i, (sf, _) in enumerate(M)}
        for sr, n in srs.items():
            ll += n * (h[idx[sr]] - logZ)
    return ll


def fit(table, lam, free=None, x0=None):
    from scipy.optimize import minimize
    free = free or NAMES
    cache = {}
    def f(x):
        w = {k: 0.0 for k in NAMES}; w["IDENT_R"] = 60.0; w["IDENT_FINAL"] = 60.0; w.update(dict(zip(free, x)))
        return -loglik(table, w, lam, cache)
    x0 = x0 or [1.0] * len(free)
    res = minimize(f, x0, method="L-BFGS-B", bounds=[(0, 60)] * len(free))
    w = {k: 0.0 for k in NAMES}; w["IDENT_R"] = 60.0; w["IDENT_FINAL"] = 60.0; w.update(dict(zip(free, [float(v) for v in res.x])))
    return w, -float(res.fun)


def fit_lambda(table, free=None):
    best = None
    for lam in [i / 40 for i in range(0, 41)]:
        w, ll = fit(table, F(lam).limit_denominator(1000), free)
        if best is None or ll > best[1] + 1e-9:
            best = (lam, ll, w)
    return best


def fit_continuous(tables, free_by_experiment, shared=True):
    from scipy.optimize import minimize
    from scipy.special import logsumexp
    names = list(tables)
    widths = [len(free_by_experiment[n]) for n in names]
    offsets = np.cumsum([0]+widths)
    prepared = []
    for name in names:
        blocks = []
        for ur, observed in tables[name].items():
            candidates_ = rows(list(ur))
            surfaces = [s for s,_ in candidates_]
            if len(set(surfaces)) != len(surfaces):
                raise ValueError("Tonal candidate surfaces must be injective for this likelihood")
            old = np.array([[co[k][0] for k in NAMES] for _,co in candidates_],dtype=float)
            new = np.array([[co[k][1] for k in NAMES] for _,co in candidates_],dtype=float)
            counts = np.array([observed.get(sf,0) for sf in surfaces],dtype=float)
            if set(observed)-set(surfaces) or counts.sum()<=0:
                raise ValueError("Observed tonal fiber missing or empty")
            blocks.append((old,new,counts))
        prepared.append(blocks)
    def objective(theta):
        loss = 0.0; gradient = np.zeros_like(theta)
        for i,name in enumerate(names):
            cols = [NAMES.index(n) for n in free_by_experiment[name]]
            weights = np.zeros(len(NAMES)); weights[NAMES.index("IDENT_R")]=60;weights[NAMES.index("IDENT_FINAL")]=60
            weights[cols]=theta[offsets[i]:offsets[i+1]]
            li = offsets[-1]+(0 if shared else i); lam=theta[li]
            for old,new,counts in prepared[i]:
                matrix=old+lam*new; logits=-(matrix@weights); logz=logsumexp(logits)
                loss += counts.sum()*logz-counts@logits
                residual=counts-counts.sum()*np.exp(logits-logz)
                gradient[offsets[i]:offsets[i+1]] += residual@matrix[:,cols]
                gradient[li] += residual@(new@weights)
        return float(loss),gradient
    trials=[]
    for attenuation in (0.125,0.5,0.875):
        initial=[4.0]*int(offsets[-1])+[attenuation]*(1 if shared else len(names))
        trials.append(minimize(objective,initial,jac=True,method="L-BFGS-B",
            bounds=[(0,60)]*int(offsets[-1])+[(0,1)]*(1 if shared else len(names)),
            options={"ftol":1e-14,"gtol":1e-8,"maxiter":6000,"maxls":80,"maxcor":30}))
    successful=[r for r in trials if r.success and np.isfinite(r.fun)]
    if not successful:
        raise RuntimeError("No continuous tonal optimization converged")
    best=min(successful,key=lambda r:r.fun)
    return {"loglik":-float(best.fun), "lambda":[float(x) for x in best.x[offsets[-1]:]],
            "weights":{name:dict(zip(free_by_experiment[name],map(float,best.x[offsets[i]:offsets[i+1]]))) for i,name in enumerate(names)},
            "fixed_weights":{"IDENT_R":60,"IDENT_FINAL":60},"free_weight_bounds":[0,60],
            "shared_attenuation":shared,"candidate_counts":[[len(b[2]) for b in bs] for bs in prepared],
            "optimization":{"starts":len(trials),"converged_starts":len(successful),"messages":[str(r.message) for r in trials]},
            "scope":"Numerical minimum found on [0,1], full candidate laws; aggregate likelihood, not an identified process/task/speaker partition."}


def predicted(table, w, lam):
    out = {}
    for ur, srs in table.items():
        p = maxent(list(ur), w, lam)
        n = sum(srs.values())
        out["".join(ur)] = {sr: {"observed": c, "observed_rate": round(c / n, 3), "predicted_rate": round(p[sr], 3)} for sr, c in srs.items()}
        out["".join(ur)]["_other_mass"] = round(1 - sum(p[sr] for sr in srs), 4)
    return out


def rates(table, w, lam, first, second, third):
    p_u = maxent([first, "T3", third], w, lam)
    p_d = maxent([first, second, third], w, lam)
    ru = p_u["T2T3" + third] / (p_u["T2T3" + third] + p_u["T3T3" + third])
    rd = p_d["T2T3" + third] / (p_d["T2T3" + third] + p_d["T3T3" + third])
    return {"underlying": round(ru, 4), "derived": round(rd, 4)}


def main():
    from .observations import SANDHI
    t0 = time.time()
    rec = {"lambda": str(LAM)}
    dump = lambda: certificate.write("tone_sandhi.json", rec)
    W = dict(S33=40, S11=6, S44=6, IDENT_REG=3, IDENT_CONT=3, IDENT_R=60, IDENT_FINAL=60)
    rec["weights_categorical"] = W
    rec["categorical"] = {ur: categorical(toks(ur), W) for exp in SANDHI.values() for ur in exp["table"]}
    print("1. categorical winners:", rec["categorical"])
    rec["fits"] = {}
    for name, exp in SANDHI.items():
        table = {tuple(toks(ur)): srs for ur, srs in exp["table"].items()}
        free = ["S33", "IDENT_REG", "IDENT_CONT", exp["feeding"]]
        w, ll = fit(table, LAM, free)
        prof = {}
        for lam in (0, F(1, 16), F(1, 8), F(1, 4), F(3, 10), F(2, 5), F(1, 2), F(3, 4), 1):
            wl, lll = fit(table, F(lam), free)
            prof[str(lam)] = {"loglik": round(lll, 3), "weights": {k: round(v, 3) for k, v in wl.items() if k in free},
                              "rates": rates(table, wl, F(lam), "T3", exp["second"], exp["third"])}
        lam_best, ll_best, w_best = fit_lambda(table, free)
        rec["fits"][name] = {
            "n_tokens": sum(sum(s.values()) for s in table.values()),
            "at_lambda_1_8": {"weights": {k: round(v, 3) for k, v in w.items() if k in free}, "loglik": round(ll, 3),
                              "predicted": predicted(table, w, LAM),
                              "rates": rates(table, w, LAM, "T3", exp["second"], exp["third"])},
            "profile_over_lambda": prof,
            "lambda_grid_best": {"lambda": lam_best, "loglik": round(ll_best, 3), "weights": {k: round(v, 3) for k, v in w_best.items() if k in free},
                           "rates": rates(table, w_best, F(lam_best).limit_denominator(1000), "T3", exp["second"], exp["third"])},
            "observed_rates": exp["observed_rates"],
        }
        print(f"2. {name}: lambda=1/8 loglik {ll:.2f} weights {rec['fits'][name]['at_lambda_1_8']['weights']} rates {rec['fits'][name]['at_lambda_1_8']['rates']}; "
              f"lambda grid best {lam_best} loglik {ll_best:.2f} rates {rec['fits'][name]['lambda_grid_best']['rates']}")
    tables = {name: {tuple(toks(ur)): srs for ur, srs in exp["table"].items()} for name, exp in SANDHI.items()}
    rec["continuous_separate"] = fit_continuous(tables, {name:["S33","IDENT_REG","IDENT_CONT",exp["feeding"]] for name,exp in SANDHI.items()}, shared=False)
    def joint_ll(x, lam):
        w = dict(S33=x[0], IDENT_REG=x[1], IDENT_CONT=x[4], S11=x[2], S44=x[3], IDENT_R=60.0, IDENT_FINAL=60.0)
        cache = {}
        return sum(loglik(tb, w, lam, cache) for tb in tables.values())
    from scipy.optimize import minimize
    joint = {}
    for lam in (F(1, 8), F(1, 4), F(1, 2), 1):
        res = minimize(lambda x: -joint_ll(x, lam), [5, 2, 2, 2, 2], method="L-BFGS-B", bounds=[(0, 60)] * 5)
        joint[str(lam)] = {"loglik": round(-float(res.fun), 3), "weights": dict(zip(("S33", "IDENT_REG", "S11", "S44", "IDENT_CONT"), [round(float(v), 3) for v in res.x]))}
    sep = sum(rec["fits"][n]["at_lambda_1_8"]["loglik"] for n in SANDHI)
    rec["joint_fit"] = {"shared_S33_IDENT": joint, "separate_fits_loglik_at_1_8": round(sep, 3),
                        "deviance_shared_vs_separate_at_1_8": round(2 * (sep - joint[str(F(1, 8))]["loglik"]), 3)}
    print(f"2. joint fit (shared S33, IDENT): {joint}; separate {sep:.2f}; deviance at 1/8: {rec['joint_fit']['deviance_shared_vs_separate_at_1_8']}")
    cf = {}
    for name, exp in SANDHI.items():
        pu, pd = exp["observed_rates"]["underlying"], exp["observed_rates"]["derived"]
        lu, ld = math.log(pu / (1 - pu)), math.log(pd / (1 - pd))
        cf[name] = {"logit_underlying": round(lu, 3), "logit_derived": round(ld, 3),
                    "lambda_as_function_of_wI": {str(wI): round((ld + wI) / (lu + wI), 3) for wI in (0, 1, 2, 3, 5, 8)},
                    "lambda_lower_bound_at_wI_0": (round(ld / lu, 3) if ld > 0 else 0.0),
                    "wI_needed_for_lambda_1_8": round((ld - lu / 8) / (1 / 8 - 1), 3)}
    rec["closed_form"] = cf
    print("2. closed form:", cf)
    w = rec["fits"]["experiment_1"]["at_lambda_1_8"]["weights"]; w = {k: w.get(k, 0.0) for k in NAMES}; w["IDENT_R"] = 60.0; w["IDENT_FINAL"] = 60.0
    ctrl = {}
    for third in TONES:
        p = maxent(["T3", "T1", third], w, LAM)
        ctrl["T3T1" + third] = {sf: round(x, 3) for sf, x in p.items() if x > 0.01}
    rec["control_third_syllable"] = ctrl
    print("3. control:", ctrl)
    rec["seconds"] = round(time.time() - t0, 1)
    dump()
    print(f"certificate written in {rec['seconds']} s")


if __name__ == "__main__":
    main()
