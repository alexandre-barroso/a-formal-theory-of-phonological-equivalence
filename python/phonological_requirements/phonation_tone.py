from __future__ import annotations
from phonological_requirements import certificate, paths

import itertools
import json
from fractions import Fraction as F
from pathlib import Path

from .core import ABSENT, NodeId, Struct
from .evaluate import activation, coefficients, score
from .frag_nuer import build, candidates, declarations, sigma, surface

OUT = paths.CERTIFICATES
LAM = F(1, 8)
SG = sigma()
DECLS = declarations()
NAMES = sorted(DECLS)

W = {n: 0 for n in NAMES}
W.update(dict(CROWD=1000000, DEP_T=625, FALL_MODAL=1000000, FINAL_LOW=8000, IDENT_T=2000, LINEARITY_T=1000000, MAX_FIRST_T=1000000, MAX_T=5000, NOFALL_BREATHY=1000000, NORISE_FINAL=1000000, NO_CONTOUR=3000, NO_FALL_AFTER_HIGH=1000000, NO_L_AFTER_RISE_FINAL=1000000, NO_M_AFTER_HIGH=1000000, NO_M_BEFORE_FALL=1000000, NO_M_CONTOUR=1000000, NO_RISE_AFTER_LOW=1000000, NO_RISE_BEFORE_LOW=1000000, NO_RISE_RISE=1000000, OCP_SYL=1000000, TONED=1000000, STAR_M=0))


_ROWS = {}


def _key(ref, decls):
    syls = ref.order["syll"]
    return (tuple((ref.real[s], ref.dom[s]["fin"], tuple(ref.real[n] for n in ref.order["tone"] if (n, s) in ref.assoc))
                  for s in syls), id(decls))


def evaluated(ref, decls=DECLS):
    k = _key(ref, decls)
    if k not in _ROWS:
        acts = activation(SG, ref, decls)
        _ROWS[k] = [(surface(c), coefficients(SG, ref, c, decls, acts), c) for c in candidates(ref)]
    return _ROWS[k]


def evaluate(ref, Wt=W, decls=DECLS, lam=LAM, rows_only=False):
    rows = [(sf, co, score(co, Wt, lam)) for sf, co, _ in evaluated(ref, decls)]
    if rows_only:
        return rows
    best = min(r[2] for r in rows)
    return {"winners": sorted({r[0] for r in rows if r[2] == best}), "best": best, "n": len(rows)}


def vec(co, names=NAMES, lam=LAM):
    return [F(co[k][0]) + lam * F(co[k][1]) for k in names]


def run_items(items):
    out = {}
    for key, (spec, expected, loc) in items.items():
        ref = build(spec)
        e = evaluate(ref)
        out[key] = {"input": surface(ref), "winners": e["winners"], "expected": sorted(expected), "locator": loc,
                    "winner_in_expected": all(w in expected for w in e["winners"]),
                    "candidates": e["n"]}
    return out


def pareto(rows):
    rows = [list(r) for r in dict.fromkeys(tuple(r) for r in rows)]
    if len(rows) <= 1:
        return rows
    import numpy as np
    R = np.array([[float(x) for x in r] for r in rows])
    keep = []
    for i in np.argsort(R.sum(axis=1), kind="stable"):
        r = R[i]
        if not any(np.all(R[j] <= r) for j in keep):
            keep.append(int(i))
    return [rows[i] for i in keep]


def blocks(items, names=NAMES, decls=DECLS):
    B = {}
    for key, (spec, expected, _) in items.items():
        rows = evaluate(build(spec), rows_only=True, decls=decls)
        listed = {v: pareto([vec(co, names=names) for sf, co, _ in rows if sf == v]) for v in expected}
        unlisted = pareto([vec(co, names=names) for sf, co, _ in rows if sf not in expected])
        B[key] = (listed, unlisted)
    return B


def _lp(A_ub, b_ub, A_eq, b_eq, n, bounds=None):
    import numpy as np
    from scipy.optimize import linprog
    c = np.zeros(n + 1); c[-1] = -1.0
    kw = {}
    rhs_ub = list(b_ub) if len(b_ub) else [F(0)] * len(A_ub)
    rhs_eq = list(b_eq) if len(b_eq) else [F(0)] * len(A_eq)
    if A_ub:
        kw["A_ub"] = np.hstack([-np.array(A_ub, dtype=float), np.ones((len(A_ub), 1))])
        kw["b_ub"] = -np.array(rhs_ub, dtype=float)
    if A_eq:
        kw["A_eq"] = np.hstack([np.array(A_eq, dtype=float), np.zeros((len(A_eq), 1))])
        kw["b_eq"] = np.array(rhs_eq, dtype=float)
    bd = bounds if bounds is not None else [(0, None)] * n
    res = linprog(c, bounds=bd + [(None, 1.0)], method="highs", **kw)
    if res.status != 0 or res.x[-1] <= 1e-9:
        return False, None, None
    x = [F(str(float(v))).limit_denominator(10**9) for v in res.x[:-1]]
    inside = all((lo is None or v >= F(lo)) and (hi is None or v <= F(hi))
                 for v, (lo, hi) in zip(x, bd))
    equal = all(sum(F(a)*b for a,b in zip(row,x)) == F(rhs) for row,rhs in zip(A_eq,rhs_eq))
    margins = [sum(F(a)*b for a,b in zip(row,x))-F(rhs) for row,rhs in zip(A_ub,rhs_ub)]
    if inside and equal and all(v > 0 for v in margins):
        return True, x, min(margins, default=F(1))
    return False, None, None


def _witness(names, values):
    return {k: str(v) for k,v in zip(names,values) if v}


def _full_fiber(B, weights, all_variants=False):
    for listed, unlisted, *extra in B.values():
        minima = [min((sum(a*b for a,b in zip(row,weights)) for row in rows), default=None)
                  for rows in listed.values()]
        present = [v for v in minima if v is not None]
        if not present or (all_variants and (None in minima or len(set(minima)) != 1)):
            return False
        best = min(present)
        if any(sum(a*b for a,b in zip(row,weights)) <= best for row in unlisted):
            return False
    return True

def exact_tie_region(items, names=NAMES, B=None):
    B = blocks(items, names) if B is None else B
    w0 = [F(W[k]) for k in names]
    A_ub, A_eq = [], []
    for key, (listed, unlisted) in B.items():
        if not listed or any(not rs for rs in listed.values()):
            return {"feasible": False, "status": "TARGET_ABSENT_FROM_DECLARED_GEN", "item": key}
        reps = [min(rs, key=lambda r: sum(a*b for a,b in zip(w0,r))) for rs in listed.values()]
        base = reps[0]
        for r in reps[1:]: A_eq.append([x-y for x,y in zip(r,base)])
        for row in unlisted: A_ub.append([x-y for x,y in zip(row,base)])
    ok, x, slack = _lp(A_ub, [], A_eq, [], len(names))
    if ok and _full_fiber(B, x, all_variants=True):
        return {"feasible": True, "status": "EXACT_FULL_FIBER_TIE_WITNESS", "slack": str(slack), "witness": _witness(names,x)}
    return {"feasible": None, "status": "UNRESOLVED_SELECTED_REPRESENTATIVE_SEARCH", "conclusive": False, "witness": None}

def exact_tie_pairs(items, names=NAMES):
    B = blocks(items, names)
    keys = list(B)
    bad = []
    for a, b in itertools.combinations(keys, 2):
        feas = False
        for choice in itertools.product(*[itertools.product(*[range(len(rs)) for rs in B[k][0].values()]) for k in (a, b)]):
            A_ub, A_eq = [], []
            for k, ch in zip((a, b), choice):
                listed, unlisted = B[k]
                reps = [rs[j] for rs, j in zip(listed.values(), ch)]
                base = reps[0]
                for r in reps[1:]:
                    A_eq.append([x - y for x, y in zip(r, base)])
                for l in unlisted:
                    A_ub.append([x - y for x, y in zip(l, base)])
            ok, witness, _ = _lp(A_ub, [], A_eq, [], len(names))
            if ok and _full_fiber({k: B[k] for k in (a,b)}, witness, all_variants=True):
                feas = True
                break
        if not feas:
            bad.append({"pair": [a,b], "status": "UNRESOLVED_NUMERICAL_BRANCH_SEARCH"})
    return bad


def variation_region(items, names=NAMES, B=None, restarts=0, seed=0, only=None):
    import random
    B = B or blocks(items, names)
    w0 = [F(W[k]) for k in names]
    rng = random.Random(seed)
    out = {}
    for key, (listed, unlisted) in B.items():
        for v, rs in listed.items():
            if only is not None and f"{key}:{v}" not in only:
                continue
            found = None
            starts = [w0] + [[F(rng.randint(0, 1000)) for _ in names] for _ in range(restarts)]
            for r_v, w_start in ((r, ws) for ws in starts for r in rs):
                if found:
                    break
                w = w_start
                for _ in range(5):
                    weak, strict = [], []
                    for v2, rs2 in listed.items():
                        for r2 in rs2:
                            if r2 is r_v:
                                continue
                            d = [x - y for x, y in zip(r2, r_v)]
                            if any(abs(z) > 1e-12 for z in d):
                                weak.append(d)
                    for l in unlisted:
                        strict.append([x - y for x, y in zip(l, r_v)])
                    for k2, (l2, u2) in B.items():
                        if k2 == key:
                            continue
                        cheapest = min((r for rs2 in l2.values() for r in rs2),
                                       key=lambda r: sum(a * b for a, b in zip(w, r)))
                        for l in u2:
                            strict.append([x - y for x, y in zip(l, cheapest)])
                    ok, x = _lp_weak(weak, strict, len(names))
                    if ok:
                        found = _witness(names, x)
                        break
                    if x is None:
                        break
                    w = list(x)
                if found:
                    break
            out[f"{key}:{v}"] = {"feasible": True if found is not None else None, "status": "EXACT_VARIANT_WITNESS" if found is not None else "UNRESOLVED_NUMERICAL_BRANCH_SEARCH", "witness": found}
    return out


def _lp_weak(weak, strict, n):
    import numpy as np
    from scipy.optimize import linprog
    if not strict:
        return True, [F(0)] * n
    rows = weak + strict
    A = np.array(rows, dtype=float)
    c = np.zeros(n + 1); c[-1] = -1.0
    slack_col = np.array([[0.0]] * len(weak) + [[1.0]] * len(strict))
    res = linprog(c, A_ub=np.hstack([-A, slack_col]), b_ub=np.zeros(len(rows)),
                  bounds=[(0, None)] * n + [(None, 1.0)], method="highs")
    if res.status != 0 or res.x[-1] <= 1e-9:
        return False, None
    x = [F(str(float(v))).limit_denominator(10**9) for v in res.x[:-1]]
    dot = lambda row: sum(F(a)*b for a,b in zip(row,x))
    if all(v >= 0 for v in x) and all(dot(row) >= 0 for row in weak) and all(dot(row) > 0 for row in strict):
        return True, x
    return False, None

def four_contour_invariance(items):
    out, changed = {}, []
    for key, (spec, expected, _) in items.items():
        cont = spec[-1] == "+"
        body = [x for x in spec if x != "+"]
        highs = [i for i, (ph, mel) in enumerate(body) if mel == "H"]
        base = evaluate(build(spec))["winners"]
        rows = {}
        for assign in itertools.product(("H", "HL"), repeat=len(highs)):
            alt = list(body)
            for i, mel in zip(highs, assign):
                alt[i] = (alt[i][0], mel)
            e = evaluate(build(alt + (["+"] if cont else [])))
            rows["".join(assign) or "-"] = e["winners"]
            if e["winners"] != base:
                changed.append((key, assign, e["winners"], base))
        out[key] = rows
    return {"rows": out, "changed": changed}


def primitive_mid_region(items, names=NAMES):
    from .frag_nuer import build_m, candidates_m
    B = {}
    for key, (spec, expected, _) in items.items():
        ref = build_m(spec)
        acts = activation(SG, ref, DECLS)
        rows = [(surface(c), coefficients(SG, ref, c, DECLS, acts)) for c in candidates_m(ref)]
        listed = {v: pareto([vec(co, names=names) for sf, co in rows if sf == v]) for v in expected}
        unlisted = pareto([vec(co, names=names) for sf, co in rows if sf not in expected])
        missing = [v for v, rs in listed.items() if not rs]
        B[key] = (listed, unlisted, missing)
    return B


def region_from_blocks(B, names=NAMES, w0=None):
    w = w0 or [F(W[k]) for k in names]
    seen = set()
    for _ in range(8):
        strict, choice = [], []
        for key, (listed, unlisted, missing) in B.items():
            rows = [r for rs in listed.values() for r in rs]
            if not rows:
                return {"feasible": False, "status": "TARGET_ABSENT_FROM_DECLARED_GEN", "item": key}
            cheapest = min(rows, key=lambda r: sum(a*b for a,b in zip(w,r)))
            choice.append(rows.index(cheapest))
            strict.extend([[x-y for x,y in zip(row,cheapest)] for row in unlisted])
        if tuple(choice) in seen: break
        seen.add(tuple(choice))
        ok, x = _lp_weak([], strict, len(names))
        if ok and _full_fiber(B,x):
            return {"feasible": True, "status": "EXACT_FULL_FIBER_WITNESS", "witness": _witness(names,x)}
        if x is None: break
        w = x
    return {"feasible": None, "status": "UNRESOLVED_NUMERICAL_BRANCH_SEARCH", "conclusive": False}

def pair_conflicts_blocks(B, names=NAMES):
    keys = list(B)
    bad = []
    for a, b in itertools.combinations(keys, 2):
        feas = False
        ra = [r for rs in B[a][0].values() for r in rs]; rb = [r for rs in B[b][0].values() for r in rs]
        for x in ra:
            for y in rb:
                strict = [[p - q for p, q in zip(l, x)] for l in B[a][1]] + \
                         [[p - q for p, q in zip(l, y)] for l in B[b][1]]
                if _lp_weak([], strict, len(names))[0]:
                    feas = True
                    break
            if feas:
                break
        if not feas:
            bad.append({"pair": [a,b], "status": "UNRESOLVED_NUMERICAL_BRANCH_SEARCH"})
    return bad


def syllable_contrib(ref, cand, acts, i, decls=DECLS, Wt=W, lam=LAM):
    from .core import read
    from .evaluate import loci, tier_of, _keys
    total = F(0)
    for name, d in decls.items():
        dt = tier_of(SG, d, "seg")
        for n in loci(cand, d, dt, ref):
            src = ref if (d.locus_side == "reference") else cand
            if src.dom[n].get("syll") != i:
                continue
            r = read(SG, ref, cand, d, n, dt)
            p, c = r.pressure, r.context
            ks = _keys(cand, n, "unique")
            a = any(acts[name].get(k, False) for k in ks)
            if d.kind == "faithfulness":
                old = int(p and c); new = 0
            else:
                old = int(p and a); new = int(p and (not a) and c)
            total += F(Wt[name]) * (F(old) + lam * F(new))
    return total


HARD = ("TONED", "CROWD", "OCP_SYL", "NOFALL_BREATHY", "FALL_MODAL", "MAX_FIRST_T", "NORISE_FINAL", "NO_M_CONTOUR")
_OPT_CACHE = {}


def syllable_options(ph, mel, fin=0):
    from .frag_nuer import syllable_realisations, assemble
    key = (ph, mel, fin)
    if key in _OPT_CACHE:
        return _OPT_CACHE[key]
    ref = build([(ph, mel)] + ([] if fin else ["+"]))
    hard = {n: DECLS[n] for n in HARD if W.get(n, 0) >= 1000000}
    keep = []
    for opt in syllable_realisations(mel):
        cand = assemble(ref, [opt])
        acts = activation(SG, ref, hard)
        co = coefficients(SG, ref, cand, hard, acts)
        if all(v == (0, 0) for v in co.values()):
            keep.append(opt)
    _OPT_CACHE[key] = keep
    return keep


def realise(spec_body, cont, choice):
    from .frag_nuer import assemble
    ref = build(spec_body + (["+"] if cont else []))
    return ref, assemble(ref, list(choice))


def window_cost(body, cont, i, prev_opt, opt, next_opt, cache):
    lo, hi = max(0, i - 1), min(len(body) - 1, i + 1)
    wbody = body[lo:hi + 1]
    wcont = cont or (hi < len(body) - 1)
    choice = [c for c in (prev_opt if i > 0 else None, opt, next_opt if i < len(body) - 1 else None) if c is not None]
    key = (tuple(wbody), wcont, i - lo, tuple(choice))
    if key not in cache:
        ref, cand = realise(list(wbody), wcont, choice)
        acts = activation(SG, ref, DECLS)
        cache[key] = syllable_contrib(ref, cand, acts, i - lo)
    return cache[key]


def dp_winners(spec):
    cont = spec[-1] == "+"
    body = [x for x in spec if x != "+"]
    opts = [syllable_options(ph, mel, fin=(0 if (cont or i < len(body) - 1) else 1)) for i, (ph, mel) in enumerate(body)]
    cache = {}
    n = len(body)
    if n == 1:
        best = None; wins = []
        for o in opts[0]:
            c = window_cost(body, cont, 0, None, o, None, cache)
            if best is None or c < best: best, wins = c, [(o,)]
            elif c == best: wins.append((o,))
        return best, wins, cache
    table = {}
    for a in opts[0]:
        for b in opts[1]:
            table[(a, b)] = (window_cost(body, cont, 0, None, a, b, cache), [(a, b)])
    for i in range(1, n):
        new = {}
        for (a, b), (c0, paths) in table.items():
            nxts = opts[i + 1] if i + 1 < n else [None]
            for nx in nxts:
                c = c0 + window_cost(body, cont, i, a, b, nx, cache)
                key = (b, nx)
                if key not in new or c < new[key][0]:
                    new[key] = (c, [p + ((nx,) if nx is not None else ()) for p in paths])
                elif c == new[key][0]:
                    new[key][1].extend(p + ((nx,) if nx is not None else ()) for p in paths)
        table = new
    best = min(v[0] for v in table.values())
    wins = [p for v in table.values() if v[0] == best for p in v[1]]
    return best, wins, cache


def evaluate_pruned(spec):
    cont = spec[-1] == "+"; body = [x for x in spec if x != "+"]
    per = [syllable_options(ph, mel, 0 if (cont or i < len(body) - 1) else 1) for i, (ph, mel) in enumerate(body)]
    ref = build(spec); acts = activation(SG, ref, DECLS)
    rows = []
    for choice in itertools.product(*per):
        _, cand = realise(body, cont, list(choice))
        co = coefficients(SG, ref, cand, DECLS, acts)
        rows.append((surface(cand), score(co, W, LAM)))
    best = min(r[1] for r in rows)
    return {"winners": sorted({r[0] for r in rows if r[1] == best}), "best": best, "n": len(rows)}


def dp_check(items, extra=(), pruned=False):
    out = {}
    for key, spec in list((k, v[0]) for k, v in items.items()) + list(extra):
        cont = spec[-1] == "+"; body = [x for x in spec if x != "+"]
        best, wins, _ = dp_winners(spec)
        dp_surf = sorted({surface(realise(body, cont, list(w))[1]) for w in wins})
        e = evaluate_pruned(spec) if pruned else evaluate(build(spec))
        out[key] = {"dp_best": str(best), "enum_best": str(e["best"]), "dp_winners": dp_surf, "enum_winners": e["winners"],
                    "agree": best == e["best"] and dp_surf == e["winners"]}
    return out


def predictions(max_n=4):
    out = {}
    for ph in ("b", "m"):
        for n in range(2, max_n + 1):
            for fin in (False, True):
                spec = [(ph, "LH")] * n + ([] if fin else ["+"])
                best, wins, _ = dp_winners(spec)
                cont = not fin
                out[f"{ph}:LH^{n}{'#' if fin else '+'}"] = {"cost": str(best),
                    "winners": sorted({surface(realise([x for x in spec if x != '+'], cont, list(w))[1]) for w in wins})}
    return out


def fall_bounding(items):
    out = {}
    for key, (spec, expected, _) in items.items():
        body = [x for x in spec if x != "+"]
        if not any(ph == "m" and mel == "LH" for ph, mel in body):
            continue
        ref = build(spec)
        rows = []
        for _, co, c in evaluated(ref):
            by_syl = {}
            for n in c.order["tone"]:
                s_ = next(sy for sy in c.order["syll"] if (n, sy) in c.assoc)
                by_syl.setdefault(s_, []).append(n)
            ins_fall = False
            for sy, ns in by_syl.items():
                lex = [n for n in ref.order["tone"] if (n, sy) in ref.assoc]
                if [ref.real[n] for n in lex] != ["L", "H"]:
                    continue
                reals = [c.real[n] for n in ns]; kinds = [n.kind for n in ns]
                if reals == ["H", "L"] and kinds == ["out", "made"] and c.corr[ns[0]] == (lex[1],):
                    ins_fall = True
            rows.append((surface(c), vec(co), ins_fall))
        bounded, unbounded = 0, []
        for sf, r, f in rows:
            if not f:
                continue
            dom = any(all(a <= b for a, b in zip(r2, r)) and any(a < b for a, b in zip(r2, r)) for sf2, r2, f2 in rows if not f2)
            if dom:
                bounded += 1
            else:
                unbounded.append(sf)
        out[key] = {"insertion_falls": bounded + len(unbounded), "dominated": bounded, "not_dominated": unbounded}
    return out


def main():
    import sys, time
    from .observations import NUER
    OUT.mkdir(parents=True, exist_ok=True)
    full = "--full" in sys.argv
    t0 = time.time()
    rec = {"lambda": str(LAM), "weights": {k: v for k, v in W.items() if v}}
    two = {k: v for k, v in NUER.items() if len([x for x in v[0] if x != "+"]) <= 2}
    if full:
        rec["what"] = "the pairwise exact-tie search over every realisation choice (two-syllable contexts), the primitive-mid pair conflicts, the per-variant region search with random restarts over all contexts, the four-syllable DP check and the longer predictions; finite positive certificates and unresolved search outcomes are distinguished"
        Ball = blocks(NUER)
        vr0 = rec["variation_region_all"] = variation_region(NUER, B=Ball)
        failed = [k for k, v in vr0.items() if not v["feasible"]]
        print(f"1. per-variant regions over all contexts: {len(vr0) - len(failed)}/{len(vr0)}; none found for {failed}")
        rec["variation_region_restarts"] = variation_region(NUER, B=Ball, restarts=20, only=failed)
        infeasible = [k for k, v in rec["variation_region_restarts"].items() if not v["feasible"]]
        print(f"1. those cells with 20 random restarts: none found for {infeasible}")
        pairs = rec["exact_tie_pairs"] = exact_tie_pairs(two)
        print(f"1. two-syllable contexts without an exactly checked joint tie witness: {pairs[:10]} ({len(pairs)} of {len(two) * (len(two) - 1) // 2} pairs)")
        Bm = primitive_mid_region(NUER)
        Bm2 = {k: v for k, v in Bm.items() if k in two}
        rec["primitive_mid_pair_conflicts"] = pair_conflicts_blocks(Bm2)
        print(f"2. primitive mid: pairs of two-syllable contexts without an exactly checked weighting: {rec['primitive_mid_pair_conflicts'][:8]}")
        extra4 = [("R4b", [("b", "LH"), ("m", "H"), ("b", "L"), ("m", "LH"), "+"]), ("R4f", [("m", "LH"), ("b", "LH"), ("b", "L"), ("b", "LH")])]
        rec["dp_check_four"] = dp_check({}, extra4, pruned=True)
        print(f"3. dynamic programme against enumeration on four-syllable phrases: {[(k, v['agree']) for k, v in rec['dp_check_four'].items()]}")
        rec["predictions_long"] = predictions(6)
        def alone(Bk, cell):
            key, v = cell.split(":")
            listed, unlisted = Bk[key][0], Bk[key][1]
            for r_v in listed.get(v, []):
                weak = [[x - y for x, y in zip(r2, r_v)] for v2, rs2 in listed.items() for r2 in rs2 if r2 is not r_v]
                weak = [d for d in weak if any(abs(z) > 1e-12 for z in d)]
                strict = [[x - y for x, y in zip(l, r_v)] for l in unlisted]
                if _lp_weak(weak, strict, len(NAMES))[0]:
                    return True
            return None
        rec["cells_alone"] = {c: alone(Ball, c) for c in failed}
        print(f"1. exactly checked positive own-context witnesses (null means unresolved): {rec['cells_alone']}")
        from .frag_nuer import declarations as _decl
        Bm_all = primitive_mid_region(NUER)
        rec["primitive_mid_alone"] = {k: any(_lp_weak([], [[x - y for x, y in zip(l, r_v)] for l in v[1]], len(NAMES))[0]
                                             for rs in v[0].values() for r_v in rs) or None for k, v in Bm_all.items()}
        print(f"2. primitive mid, each context alone: unresolved for {[k for k, f in rec['primitive_mid_alone'].items() if not f]}")
        Dv = _decl(rise_after_fall=False)
        itv = {}
        for key, (spec, expected, loc) in NUER.items():
            e = evaluate(build(spec), decls=Dv)
            itv[key] = {"winners": e["winners"], "in_expected": all(w in expected for w in e["winners"])}
        Bv = blocks(NUER, decls=Dv)
        regv = region_from_blocks({k: (v[0], v[1], []) for k, v in Bv.items()})
        vrv = variation_region(NUER, B=Bv)
        failed_v = [k for k, v in vrv.items() if not v["feasible"]]
        rec["narrow_after_low"] = {"items_in_expected": sum(v["in_expected"] for v in itv.values()), "n": len(itv),
                                  "mismatches": [k for k, v in itv.items() if not v["in_expected"]],
                                  "joint_region": regv, "cells_without_a_region": failed_v,
                                  "cells_alone": {c: alone(Bv, c) for c in failed_v}}
        print(f"1. the narrower reading (a fall not a Low for the after-Low ban): {rec['narrow_after_low']}")
        print("3. predictions to six rising tonemes:", {k: v["winners"] for k, v in rec["predictions_long"].items() if "^6" in k})
        rec["seconds"] = round(time.time() - t0, 1)
        certificate.write("phonation_tone_pairs.json", rec)
        print("wrote phonation_tone_pairs.json")
        return
    dump = lambda: certificate.write("phonation_tone.json", rec)
    it = rec["items"] = run_items(NUER)
    bad = [k for k, v in it.items() if not v["winner_in_expected"]]
    print(f"1. {len(it) - len(bad)}/{len(it)} contexts: the winner(s) at the displayed vector lie in the listed set"
          + (f"  OUTSIDE: {[(k, it[k]['winners'], it[k]['expected']) for k in bad]}" if bad else ""))
    single = [k for k, v in it.items() if len(v["expected"]) == 1]
    rec["single_variant_cells_unique"] = [k for k in single if it[k]["winners"] == it[k]["expected"]]
    print(f"1. single-variant cells reproduced uniquely: {len(rec['single_variant_cells_unique'])}/{len(single)}")
    Bq = blocks(NUER)
    exact = rec["exact_ties"] = exact_tie_region(NUER, B=Bq)
    print(f"1. exact-tie reading of the variation: {exact}")
    dump()
    B2 = {k: v for k, v in Bq.items() if k in two}
    vr = rec["variation_region"] = variation_region(two, B=B2)
    infeasible = [k for k, v in vr.items() if not v["feasible"]]
    print(f"1. multiple-grammars reading: {len(vr) - len(infeasible)}/{len(vr)} (context, variant) pairs have a weighting"
          + (f"; none found for {infeasible}" if infeasible else ""))
    Bf = {k: (v[0], v[1], []) for k, v in Bq.items()}
    regf = rec["fusion_region"] = region_from_blocks(Bf)
    print(f"2. fusion inventory, the joint region (some listed variant beats every unlisted, everywhere): {regf.get('feasible')}")
    dump()
    inv = rec["four_contour"] = four_contour_invariance(NUER)
    print(f"2. four-contour lexicon: winners changed in {len(inv['changed'])} (item, assignment) cases {inv['changed'][:4]}")
    Bm = primitive_mid_region(NUER)
    missing = {k: v[2] for k, v in Bm.items() if v[2]}
    reg = region_from_blocks(Bm)
    rec["primitive_mid"] = {"listed_variants_without_realisation": missing, "region": reg}
    print(f"2. primitive mid: variants without any realisation {missing}; joint region: {reg.get('feasible')}")
    dump()
    extra = [("R3a", [("b", "LH"), ("m", "H"), ("m", "LH"), "+"]), ("R3b", [("m", "LH"), ("b", "L"), ("b", "LH")])]
    dc = rec["dp_check"] = dp_check({k: NUER[k] for k in NUER if k in two or k in ("C1", "C2", "C3", "E1")}, extra)
    badd = [k for k, v in dc.items() if not v["agree"]]
    print(f"3. dynamic programme against enumeration: {len(dc) - len(badd)}/{len(dc)} phrases agree" + (f"; disagree {badd}" if badd else ""))
    dump()
    fb = rec["fall_bounding"] = fall_bounding(NUER)
    print(f"2. the fall by insertion is harmonically bounded: {sum(v['dominated'] for v in fb.values())}/{sum(v['insertion_falls'] for v in fb.values())} realisations; not dominated in {[k for k, v in fb.items() if v['not_dominated']]}")
    pr = rec["predictions"] = predictions(4)
    print("3. predictions for sequences of rising tonemes:", {k: v["winners"] for k, v in pr.items()})
    rec["seconds"] = round(time.time() - t0, 1)
    certificate.write("phonation_tone.json", rec)
    print(f"certificate written in {rec['seconds']} s")


if __name__ == "__main__":
    main()
