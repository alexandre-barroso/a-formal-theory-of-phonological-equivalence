from __future__ import annotations
from phonological_requirements import certificate, paths

import itertools
import json
import sys
import time
from fractions import Fraction as F
from pathlib import Path

import numpy as np

from .core import ABSENT, Ctx
from .evaluate import activation, coefficients, loci, tier_of
from .interaction_typology import lp_strict, pareto
from .frag_redup import FLAGS, build, candidates, declarations, info, make_sigma, surface, is_v
from .stratal_syncope import inward_audit, listed_slots
from .core import read


def decl_flags(d, flags):
    out = {k for sl in d.slots for k, v in sl.coord if k in flags}
    def walk(t):
        if getattr(t, "coord", None) in flags and hasattr(t, "slot"):
            out.add(t.coord)
        for p in getattr(t, "parts", ()):
            walk(p)
        if hasattr(t, "a") and not isinstance(getattr(t, "a"), str):
            walk(t.a)
    walk(d.activation); walk(d.consequence)
    return out


def inward_audit_active(sigma, ref, cand, decls, flags, key):
    out = []
    for name, d in decls.items():
        ls = listed_slots(d, flags)
        fl = decl_flags(d, flags)
        if not ls or not fl:
            continue
        dt = tier_of(sigma, d, "seg")
        for locus in loci(cand, d, dt, ref):
            ctx = Ctx(sigma, ref, cand, d, locus, dt)
            res = {s.name: ctx.resolve(s.name) for s in d.slots}
            def cyc(nd):
                return None if nd is None else cand.dom.get(nd, ref.dom.get(nd, {})).get(key)
            def carries(nd):
                return nd is not None and any(cand.dom.get(nd, ref.dom.get(nd, {})).get(f) == 1 for f in fl)
            act = bool(read(sigma, ref, cand, d, locus, dt).context)
            if not act and not carries(locus):
                continue
            for f in fl:
                def carries_f(nd, f=f):
                    return nd is not None and cand.dom.get(nd, ref.dom.get(nd, {})).get(f) == 1
                lic = [cyc(res[s]) for s in ls if carries_f(res.get(s)) and cyc(res[s]) is not None]
                if not lic:
                    continue
                cmax = max(lic)
                for s, nd in res.items():
                    cv = cyc(nd)
                    if cv is not None and cv > cmax:
                        out.append({"declaration": name, "flag": f, "locus": repr(locus), "slot": s, "cycle": cv, "licensing_cycle": cmax,
                                    "activated": act, "surface": None})
    return out


OUT = paths.CERTIFICATES
SG = make_sigma()

ITEMS = [
 ("N1", [("kaana", "stem"), ("o?", "suf")], "kaːno?", ("h", "h"), {}),
 ("N2", [("nes", "pre"), ("kaana", "stem"), ("o?", "suf")], "neskaːno?", ("h", "h", "h"), {}),
 ("N3", [("xa", "pre"), ("kaana", "stem"), ("o?", "suf")], "xakano?", ("h", "w", "h"), {}),
 ("N4", [("yaaloona", "stem"), ("o?", "suf")], "yaːloːno?", ("h", "h", "h"), {}),
 ("N5", [("ke", "pre"), ("yaaloona", "stem"), ("o?", "suf")], "keyaloːno?", ("h", "w", "h", "h"), {}),
 ("N6", [("notoxo", "stem"), ("o?", "suf")], "notxo?", ("h", "h"), {}),
 ("N7", [("we", "pre"), ("notoxo", "stem"), ("o?", "suf")], "wentoxo?", ("h", "w", "h"), {}),
 ("N8", [("yamaxa", "stem"), ("o?", "suf")], "yamxo?", ("h", "h"), {}),
 ("N9", [("he", "pre"), ("yakapa", "stem"), ("o?s", "suf")], "heykapo?s", ("h", "w", "h"), {}),
 ("N10", [("ke", "pre"), ("netale", "stem"), ("o?s", "suf")], "kentalo?s", ("h", "w", "h"), {}),
 ("N11", [("wo", "pre"), ("komo", "stem"), ("o?s", "suf")], "wokmo?s", ("h", "h"), {}),
 ("N12", [("taa", "pre"), ("notoso", "stem"), ("o?s", "suf")], "taːnotso?s", ("h", "h", "h"), {}),
 ("N13", [("ke", "pre"), ("taa", "pre"), ("notoso", "stem"), ("o?s", "suf")], "ketanotso?s", ("h", "w", "h", "h"), {}),
 ("R1", [("RED", "red"), ("topo", "stem"), ("o?s", "suf")], "totopo?s", ("h", "w", "h"), {}),
 ("R2", [("RED", "red"), ("komo", "stem"), ("o?s", "suf")], "kokomo?s", ("h", "w", "h"), {}),
 ("R3", [("RED", "red"), ("salke", "stem"), ("n", "suf"), ("o?s", "suf")], "sasalkeno?s", None, {}),
 ("R4", [("RED", "red"), ("xeyco", "stem"), ("o?s", "suf")], "xexeyco?s", None, {}),
 ("R5", [("RED", "red"), ("naato", "stem"), ("o?s", "suf")], "nanato?s", ("h", "w", "h"), {}),
 ("R6", [("he", "pre"), ("RED", "red"), ("yaace", "stem"), ("w", "suf"), ("o?", "suf")], "heyayacewo?", ("h", "w", "h", "w", "h"), {}),
 ("R7", [("RED", "red"), ("maaka", "stem"), ("n", "suf"), ("o?s", "suf")], "mamakano?s", None, {}),
 ("R8", [("RED", "red"), ("soopko", "stem"), ("o?s", "suf")], "sosopko?s", None, {}),
 ("R9", [("RED", "red"), ("cool'o", "stem"), ("o?", "suf")], "cocol'o?", None, {}),
 ("R10", [("he", "pre"), ("RED", "red"), ("m'eyca", "stem"), ("o?s", "suf")], "hem'em'eyco?s", None, {}),
 ("R11", [("RED", "red"), ("yapece", "stem", ("L",)), ("o?s", "suf")], "yaypeco?s", ("h", "w", "h"), {}),
 ("R12", [("RED", "red"), ("yakawa", "stem", ("L",)), ("o?s", "suf")], "yaykawo?s", ("h", "w", "h"), {}),
 ("R13", [("we", "pre"), ("na", "pre"), ("RED", "red"), ("wel", "stem"), ("o?s", "suf")], "wenwewelo?s", None, {}),
 ("R16", [("RED", "red"), ("qeta", "stem"), ("w", "suf"), ("o?s", "suf")], "qeqetawo?s", None, {}),
 ("R14", [("RED", "red"), ("notoo", "stem"), ("n", "suf"), ("o?s", "suf")], "nonotoːno?s", None, {}),
 ("R15", [("he", "pre"), ("na", "pre"), ("RED", "red"), ("tayoo", "stem"), ("n", "suf"), ("o?", "suf")], "hentatayoːno?", None, {}),
 ("U1", [("yapece", "stem", ("L",)), ("o?s", "suf")], "yapco?s", None, {}),
]
KH = ("KH", [("RED", "red"), ("pataka", "stem")], "papa", None, {"truncate": True})
KH0 = ("KH0", [("pataka", "stem")], "pataka", None, {"truncate": True})
EXC = [("E1", [("he", "pre"), ("RED", "red"), ("maake", "stem"), ("w", "suf"), ("o?", "suf")], "hemamaːkewo?", None, {}),
       ("E2", [("he", "pre"), ("RED", "red"), ("naate", "stem"), ("w", "suf"), ("o?", "suf")], "henanaːtewo?", None, {})]
BOUND = ("MAX_C", "PARSE")
UBOUND = 10**3


def stress_pattern(c):
    return tuple({"'": "h", ".": "w", "_": "u"}[c.real[n][0]] for n in c.order["seg"]
                 if c.real[n] is not ABSENT and is_v(c.real[n]))


def rows_for(item, D, keying="unique", made_cycle="own", lam=F(1, 8), extra=()):
    name, morphs, seg, pat, opts = item
    if dict(extra).get("hl_feet") is False:
        pat = None
    ref = build(morphs)
    acts = activation(SG, ref, D)
    names = sorted(D)
    target, rivals, all_rows = [], [], []
    for c in candidates(ref, morphs, made_cycle=made_cycle, **opts, **dict(extra)):
        co = coefficients(SG, ref, c, D, acts, keying=keying)
        row = [F(co[k][0]) + lam * F(co[k][1]) for k in names]
        pair = [(F(co[k][0]), F(co[k][1])) for k in names]
        hit = surface(c, False) == seg and (pat is None or stress_pattern(c) == pat)
        (target if hit else rivals).append((surface(c), row, pair))
        all_rows.append((surface(c), pair))
    return names, target, rivals, all_rows


def _solve(systems, names, choice, fixed_idx, ids=None):
    n = len(names)
    ids = ids or list(range(len(systems)))
    strict, label, weak = [], [], []
    for i, (tg, rv) in enumerate(systems):
        x = tg[choice[i]][1]
        for sf, r in rv:
            strict.append([p - q for p, q in zip(r, x)]); label.append((ids[i], sf))
        for j, (sf, r) in enumerate(tg):
            if j != choice[i]:
                weak.append([p - q for p, q in zip(r, x)])
    BIG = F(10**6)
    s2 = [([r[j] for j in range(n) if j not in fixed_idx], sum(r[j] * BIG for j in fixed_idx)) for r in strict]
    w2 = [([r[j] for j in range(n) if j not in fixed_idx], sum(r[j] * BIG for j in fixed_idx)) for r in weak]
    ok, cert = lp_strict_const(s2, n - len(fixed_idx), weak=w2)
    if ok:
        w, k = {}, 0
        for j, nm in enumerate(names):
            if j in fixed_idx:
                w[nm] = BIG
            else:
                w[nm] = cert[k]; k += 1
        return True, w, None
    if ok is None:
        return None, None, {"inconclusive": cert}
    by_reduced = {}
    for (rr, cc), lb in zip(s2, label):
        by_reduced.setdefault(tuple(rr), []).append((f"{lb[0]}:{lb[1]}", cc))
    refuted, consts = [], []
    for r in cert:
        labs = by_reduced.get(tuple(r), [("?", None)])
        cmin = min(cc for _, cc in labs)
        refuted.append([l for l, cc in labs if cc == cmin]); consts.append(str(cmin))
    return False, None, {"rows": [x[0] for x in refuted], "all_labels": refuted, "constants": consts, "y": [str(v) for v in cert.values()]}


def joint_feasible(systems, names, fixed=BOUND, rounds=12, ids=None):
    fixed_idx = [names.index(k) for k in fixed if k in names]
    ids = ids or list(range(len(systems)))
    w = {k: (F(10**6) if k in fixed else F(1)) for k in names}
    for k in ("WSP", "SWP", "NOLONGV_RED", "NOCODA_RED", "AFFIX_SYL_RED", "DEP_BR"):
        if k in w and k not in fixed:
            w[k] = F(100)
    choice = {i: 0 for i in range(len(systems))}
    tried, last, first = set(), None, None
    order_of = {}
    for i, (tg, _) in enumerate(systems):
        order_of[i] = sorted(range(len(tg)), key=lambda j: (sum(F(w[k]) * v for k, v in zip(names, tg[j][1])), j))
        choice[i] = order_of[i][0]
    for _ in range(rounds):
        key = tuple(sorted(choice.items()))
        if key in tried:
            break
        tried.add(key)
        ok, w2, cert = _solve(systems, names, choice, fixed_idx, ids)
        if ok:
            return {"feasible": True, "witness": {k: str(v) for k, v in w2.items()}}, w2
        if ok is None:
            return {"feasible": None, "evidence": cert}, None
        last = cert
        first = first or cert
        named = {r.split(":")[0] for r in cert["rows"]}
        moved = False
        for i in range(len(systems)):
            if str(ids[i]) in named and len(systems[i][0]) > 1:
                o = order_of[i]; k = o.index(choice[i])
                if k + 1 < len(o):
                    choice[i] = o[k + 1]; moved = True
        if not moved:
            break
    return {"feasible": None, "farkas": first, "farkas_last": last,
            "status": "UNRESOLVED_BRANCH_ALTERNATION", "conclusive": False,
            "stage": "selected target branches only; full fiber feasibility unresolved"}, None


def systems_key(i, systems, choice):
    return (i, choice[i])


def lp_strict_const(rows, n, weak=()):
    from scipy.optimize import linprog
    if not rows:
        if not weak:
            return True, [F(1)] * n
        return lp_strict_const([([F(0)] * n, F(1))], n, weak=weak)
    A = np.array([[float(x) for x in r] for r, _ in rows]); cvec = np.array([float(c) for _, c in rows]); m = len(rows)
    weak = list(weak)
    B = np.array([[float(x) for x in r] for r, _ in weak]) if weak else np.zeros((0, n)); dvec = np.array([float(c) for _, c in weak]) if weak else np.zeros(0)
    c = np.zeros(n + 1); c[-1] = -1.0
    Aub = np.vstack([np.hstack([-A, np.ones((m, 1))]), np.hstack([-B, np.zeros((len(weak), 1))])]) if weak else np.hstack([-A, np.ones((m, 1))])
    bub = np.concatenate([cvec, dvec]) if weak else cvec
    res = linprog(c, A_ub=Aub, b_ub=bub, bounds=[(0, None)] * n + [(None, 1.0)], method="highs")
    tstar = float(res.x[-1]) if res.status == 0 else None
    if res.status == 0 and res.x[-1] > 1e-7:
        for k in (6, 9, 12):
            w = [F(x).limit_denominator(10**k) for x in res.x[:-1]]
            if all(x >= 0 for x in w) and all(sum(a * x for a, x in zip(r, w)) + cc > 0 for r, cc in rows) \
               and all(sum(a * x for a, x in zip(r, w)) + cc >= 0 for r, cc in weak):
                return True, w
    M = np.vstack([A, B]) if weak else A; cd = np.concatenate([cvec, dvec]) if weak else cvec; mm = m + len(weak)
    res2 = linprog(np.zeros(mm), A_ub=np.vstack([M.T, cd.reshape(1, -1)]), b_ub=np.zeros(n + 1),
                   A_eq=np.concatenate([np.ones(m), np.zeros(len(weak))]).reshape(1, -1), b_eq=[1.0],
                   bounds=[(0, None)] * mm, method="highs")
    if res2.status == 0:
        ys = [float(v) for v in res2.x]
        allrows = rows + weak
        for k in (1, 2, 3, 4, 6, 8, 10, 12):
            y = [F(v).limit_denominator(10**k) if v > 1e-12 else F(0) for v in ys]
            if sum(y[:m]) > 0 and all(sum(yi * r[j] for yi, (r, _) in zip(y, allrows)) <= 0 for j in range(n)) \
               and sum(yi * cc for yi, (_, cc) in zip(y, allrows)) <= 0:
                if any(yi > 0 for yi in y[m:]):
                    return None, {"branch_dual_uses_weak_rows": True,
                                  "reason": "full weak-row certificate required"}
                cert = {}
                for yi, (r, _) in zip(y[:m], rows):
                    if yi > 0:
                        cert[tuple(r)] = cert.get(tuple(r), F(0)) + yi
                return False, cert
        sup = [i for i, v in enumerate(ys) if v > 1e-9]
        if len(sup) <= 12 and all(i < m for i in sup):
            y = _exact_farkas([rows[i] for i in sup], n)
            if y is not None:
                cert = {}
                for i, yi in zip(sup, y):
                    if yi > 0:
                        key = tuple(rows[i][0])
                        cert[key] = cert.get(key, F(0)) + yi
                return False, cert
    return None, {"t_star": tstar, "farkas_status": int(res2.status), "support": int(sum(1 for v in (res2.x if res2.status == 0 else []) if v > 1e-9))}


def _exact_farkas(rows, n):
    from scipy.optimize import linprog
    m = len(rows)
    A = np.array([[float(x) for x in r] for r, _ in rows]); cvec = np.array([float(c) for _, c in rows])
    obj = np.zeros(m + 1); obj[-1] = -1.0
    Aub = np.hstack([np.vstack([A.T, cvec.reshape(1, -1)]), np.ones((n + 1, 1))])
    res = linprog(obj, A_ub=Aub, b_ub=np.zeros(n + 1), A_eq=np.hstack([np.ones((1, m)), np.zeros((1, 1))]), b_eq=[1.0],
                  bounds=[(0, None)] * m + [(None, None)], method="highs")
    if res.status != 0:
        return None
    for k in (2, 3, 4, 6, 8, 10, 12):
        y = [F(v).limit_denominator(10**k) if v > 1e-12 else F(0) for v in res.x[:-1]]
        if sum(y) > 0 and all(sum(yi * r[j] for yi, (r, _) in zip(y, rows)) <= 0 for j in range(n)) \
           and sum(yi * cc for yi, (_, cc) in zip(y, rows)) <= 0:
            return y
    return None


def run_items(items, D, lam=F(1, 8), keying="unique", made_cycle="own", extra=()):
    systems, names, counts, allrows = [], None, {}, {}
    for it in items:
        nm, tg, rv, rows = rows_for(it, D, keying=keying, made_cycle=made_cycle, lam=lam, extra=extra)
        names = nm
        counts[it[0]] = {"candidates": len(tg) + len(rv), "target_fibre": len(tg)}
        if not tg:
            return None, names, counts, allrows, f"{it[0]}: the expected output is not a candidate"
        rv2 = [(sf, r) for sf, r, _ in rv]
        rows_only = pareto([r for _, r in rv2])
        keep = {tuple(r) for r in rows_only}
        rv3 = [(sf, r) for sf, r in rv2 if tuple(r) in keep]
        systems.append(([(sf, r) for sf, r, _ in tg], rv3))
        allrows[it[0]] = rows
    return systems, names, counts, allrows, None


def check(items, D, lam=F(1, 8), keying="unique", made_cycle="own", extra=()):
    systems, names, counts, allrows, err = run_items(items, D, lam, keying, made_cycle, extra)
    if err:
        return {"feasible": False, "reason": err, "counts": counts}, names, allrows
    res, w = joint_feasible(systems, names, ids=[it[0] for it in items])
    res["counts"] = counts
    return res, names, allrows


def winners(items, D, w, lam=F(1, 8), keying="unique", made_cycle="own", extra=()):
    out = {}
    for it in items:
        name, morphs, seg, pat, opts = it
        ref = build(morphs); acts = activation(SG, ref, D); names = sorted(D)
        best, arg = None, []
        for c in candidates(ref, morphs, made_cycle=made_cycle, **opts, **dict(extra)):
            co = coefficients(SG, ref, c, D, acts, keying=keying)
            v = sum(F(w[k]) * (F(co[k][0]) + lam * F(co[k][1])) for k in names)
            if best is None or v < best:
                best, arg = v, [surface(c)]
            elif v == best:
                arg.append(surface(c))
        out[name] = arg
    return out


def pipeline(rec, key, D, extra=(), items=ITEMS):
    res, names, allrows = check(items, D, extra=extra)
    rec[key] = {"feasible": res["feasible"], "farkas": res.get("farkas"), "evidence": res.get("evidence"), "counts": res["counts"]}
    print(f"{key}: feasible {res['feasible']}", ((res.get("farkas") or {}).get("all_labels") or [])[:4])
    return res, allrows


def variant_pipeline(rec, key, D, extra=(), exceptional="dep_exempt"):
    V = rec[key] = {"exceptional_statement_of_main": exceptional}
    res, allrows = pipeline(V, "main", D, extra)
    if not res["feasible"]:
        return
    w = {k: F(v) for k, v in res["witness"].items()}
    V["main"]["witness"] = res["witness"]
    V["main"]["winners"] = winners(ITEMS + EXC, D, w, extra=extra)
    print("  exceptions at the witness:", {k: v for k, v in V["main"]["winners"].items() if k in ("E1", "E2")})
    V["grid"] = {}
    for lam in ("0", "1/16", "1/8", "1/2", "1"):
        r, _, _ = check(ITEMS, D, lam=F(lam), extra=extra)
        V["grid"][lam] = r["feasible"]
    print("  grid:", V["grid"])
    r, _, _ = check(ITEMS, D, keying="self", extra=extra)
    V["keying_self"] = r["feasible"]; print("  keying self:", r["feasible"])
    D2 = declarations(ident_br_side="base", foot_hl="FOOT_HL" in D, superheavy="NO_3MU" in D, exceptional=exceptional)
    same = True
    for it in ITEMS:
        _, _, _, rows2, _ = run_items([it], D2, extra=extra)
        r1 = {sf: dict(zip(sorted(D), pr)) for sf, pr in allrows[it[0]]}
        r2 = {sf: dict(zip(sorted(D2), pr)) for sf, pr in rows2[it[0]]}
        for sf in r1:
            if r1[sf]["IDENT_BR_LEN"] != r2[sf]["IDENT_BR_LEN"]:
                same = False
    V["ident_br_side_identical_rows"] = same; print("  IDENT_BR_LEN copy-side and base-side rows identical:", same)
    V["exceptional"] = {}
    for exc in ("swp_listed", "sync_listed", "dep_exempt"):
        Dx = declarations(exceptional=exc, foot_hl="FOOT_HL" in D, superheavy="NO_3MU" in D)
        if exc == "sync_listed":
            Dr = declarations(exceptional="sync_listed_retained", foot_hl="FOOT_HL" in D, superheavy="NO_3MU" in D)
            rr, _, _ = check(ITEMS, Dr, extra=extra)
            V["exceptional_sync_listed_retained"] = {"feasible": rr["feasible"], "farkas": rr.get("farkas")}
            print("  exceptional sync_listed with the retained consequence:", rr["feasible"], ((rr.get("farkas") or {}).get("all_labels") or [])[:3])
        r, _, _ = check(ITEMS, Dx, extra=extra)
        aud = {}
        for mc in ("own", "copy"):
            viol = []
            for it in ITEMS:
                ref = build(it[1])
                for c in candidates(ref, it[1], made_cycle=mc, **dict(extra)):
                    for v in inward_audit_active(SG, ref, c, Dx, ("red", "L"), "cycle"):
                        v["surface"] = surface(c); viol.append(v)
            byd = {}
            for v in viol:
                byd.setdefault(v["declaration"], []).append(v)
            aud[mc] = {"violations": len(viol), "by_declaration": {k: {"count": len(v), "activated": sum(1 for x in v if x["activated"]), "example": v[0]} for k, v in byd.items()}}
        V["exceptional"][exc] = {"feasible": r["feasible"], "farkas": r.get("farkas"), "inward": aud}
        print(f"  exceptional {exc}: feasible {r['feasible']}", ((r.get("farkas") or {}).get("all_labels") or [])[:3])
        for mc in ("own", "copy"):
            print(f"     inward ({mc}):", {k: (v["count"], v["activated"], v["example"]["slot"], v["example"]["surface"]) for k, v in aud[mc]["by_declaration"].items()})
    Dplain = declarations(exceptional="none", foot_hl="FOOT_HL" in D, superheavy="NO_3MU" in D)
    for drop, k2 in ((("NOCODA_RED", "NOLONGV_RED", "AFFIX_SYL_RED", "SWP_L"), "no_listed"), (("NOCODA_RED",), "no_nocoda_red"),
                     (("NOLONGV_RED",), "no_nolongv_red"), (("SWP_L",), "no_swp_l"), (("AFFIX_SYL_RED",), "no_affix_syl_red"),
                     (("DEP_BR",), "no_dep_br"), (("IDENT_BR_LEN",), "no_ident_br_len"), (("MAX_BR",), "no_max_br"),
                     (("FOOT_HL", "NO_3MU"), "no_completion")):
        base = Dplain if k2 in ("no_listed", "no_swp_l") else D
        Dd = {k: v for k, v in base.items() if k not in drop}
        r, _, _ = check(ITEMS, Dd, extra=extra)
        V[k2] = {"dropped": list(drop), "feasible": r["feasible"], "farkas": r.get("farkas")}
        print(f"  {k2}: feasible {r['feasible']}", ((r.get("farkas") or {}).get("all_labels") or [])[:4])
    r, _, _ = check([KH0, KH], D, extra=extra)
    V["kager_hamilton_hypothetical"] = {"feasible": r["feasible"], "witness": r.get("witness"), "farkas": r.get("farkas")}
    print("  Kager-Hamilton hypothetical (pataka; RED-pataka -> papa):", r["feasible"], ((r.get("farkas") or {}).get("all_labels") or [])[:3])
    r, _, _ = check(ITEMS, D, extra=extra + (("truncate", True),))
    V["tonkawa_with_truncation_candidates"] = r["feasible"]; print("  Tonkawa with truncation candidates:", r["feasible"])


def main(full=False):
    t0 = time.time()
    rec = {"items": [it[0] for it in ITEMS]}
    pipeline(rec, "source_inventory", declarations())
    pipeline(rec, "no_hl_feet", declarations(), (("hl_feet", False),))
    variant_pipeline(rec, "foot_hl", declarations(foot_hl=True, exceptional="dep_exempt"))
    variant_pipeline(rec, "no_3mu", declarations(superheavy=True, exceptional="dep_exempt"))
    rec["seconds"] = round(time.time() - t0, 1)
    certificate.write("reduplication_template.json", rec)
    print(f"certificate written in {rec['seconds']} s")


if __name__ == "__main__":
    main(full="--full" in sys.argv)
