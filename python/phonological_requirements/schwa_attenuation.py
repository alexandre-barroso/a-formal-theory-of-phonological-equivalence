from __future__ import annotations
from phonological_requirements import certificate, paths

import json
import sys
import time
from fractions import Fraction as F
from math import log, exp, sqrt, erf
from pathlib import Path

import numpy as np
from scipy.optimize import minimize, brentq
from scipy.special import expit, xlogy
from scipy.stats import norm

from .evaluate import activation, coefficients
from .frag_schwa import build, candidates, declarations, make_sigma, surface
from .observations import SCHWA

OUT = paths.CERTIFICATES
SG = make_sigma()
D = declarations()
NAMES = sorted(D)

CONTEXTS = {
 1: ("word C -ss", ["C", "'V", "C", "C", "V", "C", "'V", "C"], 3, "made"),
 2: ("word C -s", ["C", "'V", "C", "C", "'V", "C"], 3, "made"),
 3: ("word CC -ss", ["C", "'V", "C", "C", "C", "V", "C", "'V", "C"], 4, "made"),
 4: ("word CC -s", ["C", "'V", "C", "C", "C", "'V", "C"], 4, "made"),
 5: ("clitic C -ss", ["V", "C", "'V", "C", "C", "V", "'V"], 4, "lex"),
 6: ("clitic C -s", ["V", "C", "'V", "C", "C", "'V", "C"], 4, "lex"),
 7: ("clitic CC -ss", ["C", "V", "C", "'V", "C", "C", "C", "V", "'V"], 6, "lex"),
 8: ("clitic CC -s", ["C", "V", "C", "'V", "C", "C", "C", "'V", "C"], 6, "lex"),
}


def cells():
    out = {}
    for k, (label, syms, site, kind) in CONTEXTS.items():
        ref = build(syms, site, kind)
        acts = activation(SG, ref, D)
        rows = {}
        for c in candidates(ref, site, kind):
            co = coefficients(SG, ref, c, D, acts)
            has = "@" in surface(c)
            rows["schwa" if has else "zero"] = {n: co[n] for n in NAMES}
        out[k] = {"label": label, **rows}
    return out


def logit_diff(cell, w, lam):
    def P(row):
        return sum(w[n] * (row[n][0] + lam * row[n][1]) for n in NAMES)
    return P(cell["zero"]) - P(cell["schwa"])


def deviance(pred, data):
    dv = 0.0
    for k, (y, n) in data.items():
        p = min(max(pred[k], 1e-12), 1 - 1e-12); ph = y / n
        ll = y * log(p) + (n - y) * log(1 - p)
        ls = (y * log(ph) if y else 0) + ((n - y) * log(1 - ph) if n - y else 0)
        dv += -2 * (ll - ls)
    return dv


def fit_core(C, data, lam=None, free=None, fixed0=()):
    idx = list(free) if free is not None else [n for n in NAMES if n not in fixed0]
    if not idx or not set(idx) <= set(NAMES) or set(idx) & set(fixed0):
        raise ValueError("invalid free/fixed weight partition")
    if lam is not None and not 0 <= lam <= 1:
        raise ValueError("attenuation must lie in [0, 1]")
    keys = sorted(C)
    old = np.array([[C[k]["zero"][n][0]-C[k]["schwa"][n][0] for n in idx] for k in keys], dtype=float)
    new = np.array([[C[k]["zero"][n][1]-C[k]["schwa"][n][1] for n in idx] for k in keys], dtype=float)
    counts = np.array([data[k][0] for k in keys], dtype=float)
    totals = np.array([data[k][1] for k in keys], dtype=float)
    saturated = float(np.sum(xlogy(counts, counts/totals)+xlogy(totals-counts, (totals-counts)/totals)))
    def nll(theta):
        w = theta[:len(idx)]; l = theta[-1] if lam is None else lam
        matrix = old+l*new; eta = matrix@w
        residual = totals*expit(eta)-counts
        gradient = list(residual@matrix)
        if lam is None:
            gradient.append(float(residual@(new@w)))
        return float(np.sum(totals*np.logaddexp(0, eta)-counts*eta)), np.array(gradient)
    fits = []
    for scale in (1.0, 4.0, 15.0):
        start = [scale]*len(idx)+([0.5] if lam is None else [])
        fits.append(minimize(nll, start, jac=True, method="L-BFGS-B",
            bounds=[(0, None)]*len(idx)+([(0, 1)] if lam is None else []),
            options={"ftol":1e-14,"gtol":1e-9,"maxiter":6000,"maxls":80,"maxcor":20}))
    successful = [r for r in fits if r.success and np.isfinite(r.fun)]
    if not successful:
        raise RuntimeError("No French likelihood optimization converged")
    best = min(successful, key=lambda r:r.fun)
    l = float(best.x[-1]) if lam is None else float(lam)
    predictions = expit((old+l*new)@best.x[:len(idx)])
    return {"deviance":float(2*(best.fun+saturated)), "weights":dict(zip(idx,map(float,best.x[:len(idx)]))),
            "lambda":l, "pred":dict(zip(keys,map(float,predictions))),
            "optimization":{"method":"bounded L-BFGS-B, analytic gradient", "starts":len(fits),
                            "converged_starts":len(successful), "messages":[str(r.message) for r in fits]},
            "fixed_zero_weights":[n for n in NAMES if n not in idx]}


def fit_logistic(X, data):
    keys = sorted(data)
    def nll(b):
        pred = {k: 1 / (1 + exp(-sum(bi * xi for bi, xi in zip(b, X[k])))) for k in keys}
        return deviance(pred, data)
    r = minimize(nll, [0.0] * len(X[keys[0]]), method="BFGS")
    r2 = minimize(nll, r.x, method="Nelder-Mead", options={"xatol": 1e-10, "fatol": 1e-12, "maxiter": 40000})
    b = r2.x
    pred = {k: 1 / (1 + exp(-sum(bi * xi for bi, xi in zip(b, X[k])))) for k in keys}
    return {"deviance": r2.fun, "coef": list(map(float, b)), "pred": pred}


def fit_nhg(V, data, free):
    keys = sorted(data)
    def nll(w):
        if any(v < 0 for v in w):
            return 1e9
        pred = {}
        for k in keys:
            d = V[k]
            h = sum(wi * d[n] for wi, n in zip(w, free))
            sd = sqrt(sum(d[n] ** 2 for n in d))
            pred[k] = norm.cdf(h / sd)
        return deviance(pred, data)
    best = None
    for x0 in ([1.0] * len(free), [2.0, 3.0, 0.5, 2.0, 0.0, 0.0][:len(free)]):
        r = minimize(nll, x0, method="Nelder-Mead", options={"xatol": 1e-9, "fatol": 1e-10, "maxiter": 40000})
        if best is None or r.fun < best.fun:
            best = r
    return {"deviance": best.fun, "weights": dict(zip(free, map(float, best.x)))}


def main():
    t0 = time.time()
    C = cells()
    data = {k: (SCHWA["counts"][k], SCHWA["n"]) for k in CONTEXTS}
    obs = {k: y / n for k, (y, n) in data.items()}
    rec = {"data": {"counts": SCHWA["counts"], "n": SCHWA["n"], "note": SCHWA["note"]},
           "cells": {k: {"label": v["label"], "schwa": {n: list(v["schwa"][n]) for n in NAMES}, "zero": {n: list(v["zero"][n]) for n in NAMES}} for k, v in C.items()}}
    rec["data"]["lineage"] = "Counts reconstructed as round(162*p) in Flemming2021 supplementary schwa_models.R from Smith and Pater2020 Table14p24; not individual trial data."
    print("cells (old,new):")
    for k, v in C.items():
        print(f"  {k} {v['label']:14s} schwa {{{', '.join(f'{n}:{v['schwa'][n]}' for n in NAMES if v['schwa'][n] != (0,0))}}}  zero {{{', '.join(f'{n}:{v['zero'][n]}' for n in NAMES if v['zero'][n] != (0,0))}}}")
    m1 = fit_core(C, data, lam=1.0)
    rec["source_maxent_lambda1"] = m1
    print(f"source MaxEnt (lambda = 1): deviance {m1['deviance']:.2f}  weights {m1['weights']}  (the source: 14.6)")
    mf = fit_core(C, data, lam=None)
    rec["core_lambda_free"] = mf
    rec["restricted_zero_DEP_CLUSTER"] = fit_core(C, data, fixed0=("DEP", "NOCLUSTER"))
    rec["core_lambda_zero"] = fit_core(C, data, lam=0.0)
    rec["statistical_scope"] = "Aggregate independent-binomial reference over reconstructed counts; repeated speaker/item dependence and pooling are not modeled. Profile intervals and chi-square values are conditional reference calculations, not calibrated population inference."
    print(f"core, lambda free: deviance {mf['deviance']:.2f}  lambda {mf['lambda']:.3f}  weights {mf['weights']}")
    m8 = fit_core(C, data, lam=0.125)
    rec["core_lambda_1_8"] = m8
    print(f"core, lambda = 1/8: deviance {m8['deviance']:.2f}  weights {m8['weights']}")
    prof = {}
    for l in (0.05, 0.125, 0.25, 0.4, 0.5, 0.6, 0.65, 0.7, 0.8, 0.9, 1.0):
        prof[str(l)] = fit_core(C, data, lam=l)["deviance"]
    rec["profile"] = prof
    print("profile:", {k: round(v, 2) for k, v in prof.items()})
    X_aug = {k: [1.0, float(C[k]["zero"]["NOCCC"][0] + C[k]["zero"]["NOCCC"][1]), float((C[k]["zero"]["NOCCC"][0] + C[k]["zero"]["NOCCC"][1]) * (k <= 4)),
                 float(C[k]["zero"]["NOCLASH"][0] + C[k]["zero"]["NOCLASH"][1]), float(k >= 5)] for k in C}
    ma = fit_logistic(X_aug, data)
    rec["source_maxent_augmented"] = ma
    print(f"source MaxEnt + *CCC/iP: deviance {ma['deviance']:.2f}  coef {[round(c, 2) for c in ma['coef']]}  (the source: 2.2)")
    X6 = {k: [float(k <= 4), float(k >= 5), float((C[k]["zero"]["NOCCC"][0] + C[k]["zero"]["NOCCC"][1]) * (k <= 4)), float((C[k]["zero"]["NOCCC"][0] + C[k]["zero"]["NOCCC"][1]) * (k >= 5)),
              float((C[k]["zero"]["NOCLASH"][0] + C[k]["zero"]["NOCLASH"][1]) * (k <= 4)), float((C[k]["zero"]["NOCLASH"][0] + C[k]["zero"]["NOCLASH"][1]) * (k >= 5))] for k in C}
    m6 = fit_logistic(X6, data)
    rec["free_ratio_model"] = m6
    b = m6["coef"]
    rec["free_ratio_model"]["ratios"] = {"CCC clitic/word": b[3] / b[2] if b[2] else None, "Clash clitic/word": b[5] / b[4] if b[4] else None}
    print(f"free-ratio model (6 params): deviance {m6['deviance']:.2f}  CCC word {b[2]:.2f} clitic {b[3]:.2f} (ratio {b[3]/b[2]:.2f}); Clash word {b[4]:.2f} clitic {b[5]:.2f} (ratio {b[5]/b[4]:.2f})")
    V = {}
    for k in C:
        d = {}
        for n in NAMES:
            d[n] = (C[k]["schwa"][n][0] + C[k]["schwa"][n][1]) - (C[k]["zero"][n][0] + C[k]["zero"][n][1])
            d[n] = -float(d[n])
        V[k] = d
    nh = fit_nhg(V, data, ["NOSCHWA", "NOCCC", "NOCLASH", "MAX"])
    rec["nhg_normal"] = nh; print(f"normal NHG: deviance {nh['deviance']:.2f}  weights", {k: round(v, 2) for k, v in nh['weights'].items()}, "(the source: 26.0)")
    for k in C:
        V[k]["CCC_iP"] = V[k]["NOCCC"] if k <= 4 else 0.0
    nh2 = fit_nhg(V, data, ["NOSCHWA", "NOCCC", "CCC_iP", "NOCLASH", "MAX"])
    rec["nhg_normal_augmented"] = nh2; print(f"normal NHG + *CCC/iP: deviance {nh2['deviance']:.2f}  (the source: 6.7)")
    lg = {k: log(obs[k] / (1 - obs[k])) for k in obs}
    ccc_w = ((lg[3] - lg[1]) + (lg[4] - lg[2])) / 2; ccc_c = ((lg[7] - lg[5]) + (lg[8] - lg[6])) / 2
    cl_w = ((lg[2] - lg[1]) + (lg[4] - lg[3])) / 2; cl_c = ((lg[6] - lg[5]) + (lg[8] - lg[7])) / 2
    rec["closed_form"] = {"logits": lg, "CCC_effect_word": ccc_w, "CCC_effect_clitic": ccc_c, "lambda_from_CCC": ccc_c / ccc_w,
                          "Clash_effect_word": cl_w, "Clash_effect_clitic": cl_c, "lambda_from_Clash": cl_c / cl_w}
    print(f"closed form: *CCC effect words {ccc_w:.2f}, clitics {ccc_c:.2f} -> lambda {ccc_c/ccc_w:.2f}; *Clash words {cl_w:.2f}, clitics {cl_c:.2f} -> lambda {cl_c/cl_w:.2f}")
    from scipy.stats import chi2
    rec["lack_of_fit"] = {"source_maxent (4 params)": {"deviance": m1["deviance"], "p": float(chi2.sf(m1["deviance"], 4))},
                          "core lambda free (5 params)": {"deviance": mf["deviance"], "p": float(chi2.sf(mf["deviance"], 3))},
                          "source augmented (5 params)": {"deviance": ma["deviance"], "p": float(chi2.sf(ma["deviance"], 3))},
                          "core lambda 1/8 (4 params)": {"deviance": m8["deviance"], "p": float(chi2.sf(m8["deviance"], 4))}}
    print("lack of fit:", {k: (round(v["deviance"], 2), round(v["p"], 3)) for k, v in rec["lack_of_fit"].items()})
    target = mf["deviance"]+chi2.ppf(0.95,1)
    profile_difference = lambda l: fit_core(C,data,lam=l)["deviance"]-target
    rec["lambda_profile_interval_95"] = [float(brentq(profile_difference,0,mf["lambda"],xtol=1e-9)),
                                        float(brentq(profile_difference,mf["lambda"],1,xtol=1e-9))]
    rec["aic"] = {"source_maxent (4)": m1["deviance"] + 8, "core lambda free (5)": mf["deviance"] + 10, "source augmented (5)": ma["deviance"] + 10,
                  "free-ratio (6)": m6["deviance"] + 12, "normal NHG (4)": nh["deviance"] + 8, "normal NHG augmented (5)": nh2["deviance"] + 10}
    rec["equal_ratio_test"] = {"deviance_core_minus_free_ratio": mf["deviance"] - m6["deviance"], "df": 1, "p": float(chi2.sf(max(mf["deviance"] - m6["deviance"], 0.0), 1))}
    def dev_at(w, law):
        pred = {}
        for k in C:
            d = {n: -float((C[k]["schwa"][n][0] + C[k]["schwa"][n][1]) - (C[k]["zero"][n][0] + C[k]["zero"][n][1])) for n in NAMES}
            h = sum(w.get(n, 0.0) * d[n] for n in NAMES)
            pred[k] = 1 / (1 + exp(-h)) if law == "logit" else norm.cdf(h / sqrt(sum(v * v for v in d.values())))
        return deviance(pred, data), {k: round(v, 3) for k, v in pred.items()}
    rec["at_source_weights"] = {"maxent": dev_at({"NOSCHWA": 2.08, "NOCCC": 2.84, "NOCLASH": 0.48, "MAX": 2.14}, "logit"),
                                "nhg": dev_at({"NOSCHWA": 2.20, "NOCCC": 2.98, "NOCLASH": 0.57, "MAX": 2.21}, "probit")}
    print("lambda 95% profile interval:", rec["lambda_profile_interval_95"], " AIC:", {k: round(v, 1) for k, v in rec["aic"].items()})
    print("equal-ratio test:", {k: (round(v, 3) if isinstance(v, float) else v) for k, v in rec["equal_ratio_test"].items()})
    rec["seconds"] = round(time.time() - t0, 1)
    certificate.write("schwa_attenuation.json", rec)
    print(f"certificate written in {rec['seconds']} s")


if __name__ == "__main__":
    main()
