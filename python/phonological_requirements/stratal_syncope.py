from __future__ import annotations
from phonological_requirements import certificate, paths

import itertools
import json
import random
import sys
import time
from fractions import Fraction as F
from pathlib import Path

from .core import ABSENT, Ctx, NodeId, Struct
from .evaluate import activation, coefficients, loci, score, tier_of
from .frag_stratal import (CONS, FLAGS, FLOAT, LONG, SG, VOWELS, build, candidates, declarations,
                           listed_declarations, surface, unstressed)

OUT = paths.CERTIFICATES
LAM = F(1, 8)
BOUND = 10 ** 6

W0 = dict(SYNCOPE=6000, SHORTEN=3000, ONSET=BOUND, NOCC_INIT=BOUND, CODA_SSP=BOUND, VVCC=BOUND,
          RR_GLOT=BOUND, CODA2=800, ACC_STRESS=400000, RIGHTMOST_DOM=500000, LEFTMOST_ACC=300000,
          NONFIN=60000, PENULT=40000, MAX_V=4000, MAX_VV=20000, MAX_ACC=BOUND, MAX_C=BOUND, MAX_FLOAT=8000,
          DEP_X=1500, IDENT_LONG=500, IDENT_LONG_S=5000, IDENT_NUC=500, IDENT_NAS=400, IDENT_FRONT=2000,
          DEP_C=700, UNIF=400, UNIF2=2500, SEL_SISTER=BOUND, SEL_ANY=BOUND, ALLO_OUT=BOUND, DEP_X_FINAL=BOUND)
HARD = tuple(k for k, v in W0.items() if v == BOUND)


def bridge(s: Struct) -> str:
    real = dict(s.real)
    for n in s.order["seg"]:
        if real[n] in LONG:
            real[n] = real[n][0]
    return surface(Struct(order=s.order, real=real, dom=s.dom, corr=s.corr))


def _feat(x):
    u = unstressed(x)
    return SG.features[u] if u in SG.features else SG.features[x]


def hard_ok(ref: Struct, c: Struct, sel: str = "SEL_SISTER", final_ban: bool = True) -> bool:
    order = list(c.order["seg"])
    seq = [c.real[n] for n in order]
    feats = [_feat(x) for x in seq]
    n = len(seq)
    for i, f in enumerate(feats):
        if f["nuclear"]:
            if i == 0 or not feats[i - 1]["cons"]:
                return False
            if f["long"] and i + 2 < n and feats[i + 1]["cons"] and feats[i + 2]["cons"] \
               and (i + 3 >= n or feats[i + 3]["cons"]):
                return False
        else:
            if i == 0 and n > 1 and feats[1]["cons"]:
                return False
            if i + 1 < n and feats[i + 1]["cons"] and (i + 2 >= n or feats[i + 2]["cons"]) and f["son"] < feats[i + 1]["son"]:
                return False
            if f["sonc"] and i + 1 < n and feats[i + 1]["sonc"] and feats[i + 1]["glot"]:
                return False
    last = order[-1]
    cs_last = c.correspondents(last)
    if final_ban and len(cs_last) == 1 and ref.real[cs_last[0]] == FLOAT:
        return False
    realised = {r for m in order for r in c.correspondents(m)}
    rorder = list(ref.order["seg"])
    for k, r in enumerate(rorder):
        v = ref.real[r]
        if r not in realised:
            if v in VOWELS and ref.dom[r]["acc"]:
                return False
            if v in CONS:
                return False
        elif v in VOWELS and ref.dom[r]["alt"] and sel:
            img = [m for m in order if r in c.correspondents(m)]
            if len(img) == 1 and len(c.correspondents(img[0])) == 1:
                out = _feat(c.real[img[0]])
                if sel == "SEL_SISTER":
                    want = any(ref.dom[x].get("cycle") == 1 and _feat(ref.real[x])["nuclear"]
                               for x in rorder[k + 1:k + 2])
                else:
                    want = None
                if want is not None and out["front"] != want:
                    return False
    return True


def evaluate(ref, Wt, decls, prune=True, rows_only=False, obs=bridge, keep=False):
    acts = activation(SG, ref, decls)
    sel = "SEL_SISTER" if "SEL_SISTER" in decls else None
    fb = "DEP_X_FINAL" in decls
    rows, proposed = [], []
    for c in candidates(ref):
        co = coefficients(SG, ref, c, decls, acts)
        rows.append((obs(c), co, score(co, Wt, LAM)) + ((c,) if keep else ()))
        proposed.append(prune and not hard_ok(ref, c, sel, fb))
    if rows_only:
        return rows
    best = min(r[2] for r in rows)
    pruned = sum(p and r[2] > best for p, r in zip(proposed, rows))
    rows = [r for p, r in zip(proposed, rows) if not p or r[2] <= best]
    out = {"winners": sorted({r[0] for r in rows if r[2] == best}), "best": best, "n": len(rows), "pruned": pruned}
    if keep:
        out["structs"] = [r[3] for r in rows if r[2] == best]
    return out


def run_items(items, Wt, decls, **kw):
    out = {}
    for key, (spec, expected, loc) in items.items():
        ref = build(spec)
        e = evaluate(ref, Wt, decls, **kw)
        out[key] = {"input": surface(ref), "winners": e["winners"], "expected": sorted(expected), "locator": loc,
                    "winner_in_expected": all(w in expected for w in e["winners"]),
                    "candidates": e["n"], "pruned": e["pruned"]}
    return out


def weights(decls, base=W0):
    return {k: base.get(k, 0) for k in decls}


def mism(res):
    return sorted(k for k, v in res.items() if not v["winner_in_expected"])


def vec(co, names):
    return [F(co[k][0]) + LAM * F(co[k][1]) for k in names]


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


def blocks(items, Wt, decls, names, rows_by_key=None):
    B = {}
    for key, (spec, expected, _) in items.items():
        rows = rows_by_key[key] if rows_by_key else evaluate(build(spec), Wt, decls, rows_only=True)
        listed = {v: pareto([vec(co, names) for sf, co, _ in rows if sf == v]) for v in expected}
        listed = {v: rs for v, rs in listed.items() if rs}
        unlisted = pareto([vec(co, names) for sf, co, _ in rows if sf not in expected])
        B[key] = (listed, unlisted)
    return B


def run_set(items, Wt, decls, names):
    rows_by_key, out = {}, {}
    for key, (spec, expected, loc) in items.items():
        ref = build(spec)
        rows = evaluate(ref, Wt, decls, rows_only=True)
        rows_by_key[key] = rows
        best = min(r[2] for r in rows)
        winners = sorted({r[0] for r in rows if r[2] == best})
        out[key] = {"input": surface(ref), "winners": winners, "expected": sorted(expected), "locator": loc,
                    "winner_in_expected": all(w in expected for w in winners), "candidates": len(rows)}
    return out, blocks(items, Wt, decls, names, rows_by_key)


def lp_weak(weak, strict, n, fixed=()):
    import numpy as np
    from scipy.optimize import linprog
    rows = weak + strict
    if not strict:
        return True, [F(1000) if i in fixed else F(0) for i in range(n)]
    A = np.array(rows, dtype=float)
    c = np.zeros(n + 1); c[-1] = -1.0
    slack_col = np.array([[0.0]] * len(weak) + [[1.0]] * len(strict))
    bounds = [(1000, 1000) if i in fixed else (0, None) for i in range(n)] + [(None, 1.0)]
    res = linprog(c, A_ub=np.hstack([-A, slack_col]), b_ub=np.zeros(len(rows)), bounds=bounds, method="highs")
    if res.status == 0 and res.x[-1] > 1e-9:
        x = [F(str(float(v))).limit_denominator(10**9) for v in res.x[:-1]]
        dot = lambda row: sum(F(a) * b for a, b in zip(row, x))
        if (all(v >= 0 for v in x) and all(x[i] == 1000 for i in fixed)
                and all(dot(row) >= 0 for row in weak) and all(dot(row) > 0 for row in strict)):
            return True, x
    return False, None


def region(B, names, w0, fixed=(), rows_extra=()):
    w = list(w0)
    seen = set()
    for _ in range(10):
        strict, choice = [list(e) for e in rows_extra], []
        for key, (listed, unlisted) in B.items():
            rows = [r for rs in listed.values() for r in rs]
            if not rows:
                return {"feasible": False, "status": "TARGET_ABSENT_FROM_DECLARED_GEN", "reason": f"no realisation of a listed variant in {key}"}
            cheapest = min(rows, key=lambda r: sum(a * b for a, b in zip(w, r)))
            choice.append(rows.index(cheapest))
            for l in unlisted:
                strict.append([x - y for x, y in zip(l, cheapest)])
        if tuple(choice) in seen:
            break
        seen.add(tuple(choice))
        ok, x = lp_weak([], strict, len(names), fixed)
        if ok:
            return {"feasible": True, "status": "EXACT_DECLARED_DOMAIN_WITNESS", "witness": {k: str(v) for k, v in zip(names, x) if v > 0}}
        if x is None:
            break
        w = x
    return {"feasible": None, "status": "UNRESOLVED_NUMERICAL_BRANCH_SEARCH", "conclusive": False}


def pair_conflicts(B, names, fixed=()):
    bad = []
    for a, b in itertools.combinations(list(B), 2):
        feas = False
        ra = [r for rs in B[a][0].values() for r in rs]; rb = [r for rs in B[b][0].values() for r in rs]
        for x in ra:
            for y in rb:
                strict = [[p - q for p, q in zip(l, x)] for l in B[a][1]] + \
                         [[p - q for p, q in zip(l, y)] for l in B[b][1]]
                if lp_weak([], strict, len(names), fixed)[0]:
                    feas = True; break
            if feas:
                break
        if not feas:
            bad.append({"pair": [a, b], "status": "UNRESOLVED_NUMERICAL_BRANCH_SEARCH"})
    return bad


def two_pass(spec, D1, W1, D2, W2, persist=False):
    stem = [m for m in spec if m[1] == 0]
    ref1 = build(stem)
    e1 = evaluate(ref1, W1, D1, keep=True)
    full = build(spec)
    wins = set()
    for w1 in e1["structs"]:
        nodes, real, dom = [], {}, {}
        k = 0
        for n in ref1.order["seg"]:
            imgs = [m for m in w1.order["seg"] if n in w1.correspondents(m)]
            if imgs:
                m = imgs[0]
                if w1.correspondents(m)[0] != n:
                    continue
                v = unstressed(w1.real[m])
            elif persist and ref1.real[n] == FLOAT:
                v = FLOAT
            else:
                continue
            nn = NodeId("Or", "lex", k); k += 1
            nodes.append(nn); real[nn] = v; dom[nn] = dict(w1.dom[m] if imgs else ref1.dom[n])
            dom[nn]["alt"] = 0 if imgs and v != ref1.real[n] else dom[nn]["alt"]
        for n in full.order["seg"]:
            if full.dom[n]["level"] == 1:
                nn = NodeId("Or", "lex", k); k += 1
                nodes.append(nn); real[nn] = full.real[n]; dom[nn] = dict(full.dom[n])
        ref2 = Struct(order={"seg": tuple(nodes)}, real=real, dom=dom, corr={n: (n,) for n in nodes})
        e2 = evaluate(ref2, W2, D2)
        wins |= set(e2["winners"])
    return sorted(wins), sorted(e1["winners"])


def listed_slots(decl, flags):
    ls = {s.name for s in decl.slots if any(k in flags for k, v in s.coord)}
    def walk(t):
        if getattr(t, "coord", None) in flags and hasattr(t, "slot"):
            ls.add(t.slot)
        for p in getattr(t, "parts", ()):
            walk(p)
        if hasattr(t, "a") and not isinstance(getattr(t, "a"), str):
            walk(t.a)
    walk(decl.activation); walk(decl.consequence)
    return ls


def inward_audit(sigma, ref, cand, decls, flags, key):
    out = []
    for name, d in decls.items():
        ls = listed_slots(d, flags)
        if not ls:
            continue
        dt = tier_of(sigma, d, "seg")
        for locus in loci(cand, d, dt, ref):
            ctx = Ctx(sigma, ref, cand, d, locus, dt)
            res = {s.name: ctx.resolve(s.name) for s in d.slots}
            def cyc(nd):
                if nd is None:
                    return None
                return cand.dom.get(nd, ref.dom.get(nd, {})).get(key)
            lc = [cyc(res[s]) for s in ls if res.get(s) is not None and cyc(res[s]) is not None]
            if not lc:
                continue
            cmax = max(lc)
            for s, nd in res.items():
                cv = cyc(nd)
                if cv is not None and cv > cmax:
                    out.append({"declaration": name, "locus": repr(locus), "slot": s, "cycle": cv, "listed_cycle": cmax})
    return out


def audit_this(items, decls, flags=FLAGS, key="cycle"):
    n_struct, viol = 0, []
    for k, (spec, _, _) in items.items():
        ref = build(spec)
        for c in candidates(ref):
            n_struct += 1
            v = inward_audit(SG, ref, c, decls, flags, key)
            if v:
                viol.append((k, bridge(c), v[:3]))
    return n_struct, viol


def audit_accent():
    from . import morphological_accent as R6
    from .frag_morphaccent import FLAGS as AFLAGS, anti_declarations, build as abuild, sigma as asigma
    sg = asigma(); decls = anti_declarations()
    n_struct, viol = 0, []
    for lang, items in (("jp", R6.ITEMS_JP), ("ru", R6.ITEMS_RU), ("cu", R6.ITEMS_CU)):
        for k, spec in items.items():
            ref = abuild(spec)
            for c in R6.candidates(ref):
                n_struct += 1
                v = inward_audit(sg, ref, c, decls, AFLAGS, "rank")
                if v:
                    viol.append((lang, k, v[:3]))
    return n_struct, viol


def exchange(c, ref, v):
    realised = {r for m in c.order["seg"] for r in c.correspondents(m)}
    if v in realised:
        return None
    order = list(ref.order["seg"]); iv = order.index(v)
    nodes, real, dom, corr = [], {}, {}, {}
    ins = [NodeId("Or", "out", 900)]
    def put(m, r, d, cs):
        nodes.append(m); real[m] = r; dom[m] = d; corr[m] = cs
    done = False
    seq = list(c.order["seg"])
    for k, m in enumerate(seq):
        cs = c.correspondents(m)
        pos = order.index(cs[0]) if cs else None
        if not done and pos is not None and pos > iv:
            prev_nuc = k > 0 and _feat(c.real[seq[k - 1]])["nuclear"]
            if prev_nuc:
                put(NodeId("Or", "made", 901), "y", dict(ref.dom[v]), ())
            put(ins[0], ref.real[v][0], dict(ref.dom[v]), (v,))
            if _feat(c.real[m])["nuclear"]:
                put(NodeId("Or", "made", 902), "y", dict(ref.dom[v]), ())
            done = True
        put(m, c.real[m], c.dom[m], cs)
    if not done:
        if seq and _feat(c.real[seq[-1]])["nuclear"]:
            put(NodeId("Or", "made", 901), "y", dict(ref.dom[v]), ())
        put(ins[0], ref.real[v][0], dict(ref.dom[v]), (v,))
    return Struct(order={"seg": tuple(nodes)}, real=real, dom=dom, corr=corr)


def exchange_certificate(items, decls, names):
    changes, n, excluded = {}, 0, 0
    for key, (spec, _, _) in items.items():
        ref = build(spec); acts = activation(SG, ref, decls)
        longs = [r for r in ref.order["seg"] if ref.real[r] in LONG]
        if not longs:
            continue
        for c in candidates(ref):
            if not hard_ok(ref, c):
                continue
            for v in longs:
                c2 = exchange(c, ref, v)
                if c2 is None:
                    continue
                n += 1
                co1 = coefficients(SG, ref, c, decls, acts); co2 = coefficients(SG, ref, c2, decls, acts)
                if not hard_ok(ref, c2) or co2["VVCC"] != co1["VVCC"] and (co2["VVCC"][0] > co1["VVCC"][0] or co2["VVCC"][1] > co1["VVCC"][1]):
                    excluded += 1
                    continue
                for k in names:
                    d = F(co2[k][0] - co1[k][0]) + LAM * F(co2[k][1] - co1[k][1])
                    if d:
                        changes.setdefault(k, set()).add(str(d))
    return {"exchanges": n, "excluded_by_a_bound_requirement": excluded,
            "changes": {k: sorted(v) for k, v in changes.items()}}


def schematic(n_words, seed=0):
    rng = random.Random(seed)
    C = ["p", "t", "k", "q", "s", "h", "m", "n", "l", "w", "y", "c", "k’", "t’", "n’"]
    Vs = ["a", "e", "i", "o", "u"]
    def syl(acc_ok=True):
        v = rng.choice(Vs)
        if rng.random() < 0.35:
            v = v + v
        if acc_ok and rng.random() < 0.3:
            v = v[0] + "́" + v[1:]
        return rng.choice(C) + v
    out = []
    for _ in range(n_words):
        pre = [("hi", 0, 2)] if rng.random() < 0.5 else ([("pée", 0, 2)] if rng.random() < 0.5 else [])
        root = "".join(syl() for _ in range(rng.randint(1, 3))) + (FLOAT if rng.random() < 0.3 else "")
        suf = []
        if rng.random() < 0.6:
            suf.append(("én’i", 0, 1, ("app2",)))
        asp = rng.choice([("see", 0, 1), ("uu’", 0, 1), ("t", 0, 1), ("siix", 0, 1), ("", 0, 1), ("qaa", 0, 1)])
        suf.append(asp)
        if rng.random() < 0.5 and asp[0] in ("see", "", "qaa"):
            suf += rng.choice([[("m", 1, 1), ("qa", 1, 1)], [("e", 1, 1)], [("kik", 1, 1), ("e", 1, 1)], [("ne", 1, 1)]])
        out.append(pre + [(root, 0, 0)] + suf)
    return out


def schematic_checks(specs, Wt, decls):
    long_deleted, allo, n, none = 0, {"short_before_stem_CV": 0, "long_elsewhere": 0, "counter": []}, 0, 0
    for spec in specs:
        ref = build(spec)
        try:
            e = evaluate(ref, Wt, decls, keep=True)
        except (AssertionError, ValueError):
            none += 1
            continue
        n += 1
        for c in e["structs"]:
            realised = {r for m in c.order["seg"] for r in c.correspondents(m)}
            for r in ref.order["seg"]:
                if ref.real[r] in LONG and r not in realised:
                    long_deleted += 1
            app = [r for r in ref.order["seg"] if ref.dom[r]["app2"] and ref.real[r] in VOWELS]
            if app:
                r = app[0]
                order = list(ref.order["seg"]); i = order.index(r)
                nxt = [x for x in order[i + 1:] if ref.real[x] != ABSENT]
                stem_cv = (len(nxt) >= 2 and _feat(ref.real[nxt[0]])["cons"] and _feat(ref.real[nxt[1]])["nuclear"]
                           and ref.dom[nxt[1]]["level"] == 0)
                before_v = bool(nxt) and _feat(ref.real[nxt[0]])["nuclear"]
                img = [m for m in c.order["seg"] if r in c.correspondents(m)]
                nuclear = bool(img) and _feat(c.real[img[0]])["nuclear"] and len(c.correspondents(img[0])) == 1
                if before_v:
                    continue
                if stem_cv and not nuclear:
                    allo["short_before_stem_CV"] += 1
                elif not stem_cv and nuclear:
                    allo["long_elsewhere"] += 1
                else:
                    allo["counter"].append((surface(ref), bridge(c)))
    return {"words": n, "without_admissible_candidate": none, "long_nuclei_unrealised": long_deleted, "alternation": allo}


def main():
    from .observations import NEZ, NEZ_RESIDUE
    t0 = time.time()
    rec = {"lambda": str(LAM)}
    only = sys.argv[1].split(",") if len(sys.argv) > 1 and sys.argv[1] not in ("all", "--full") else None
    items = {k: NEZ[k] for k in (only or NEZ)}
    full = "--full" in sys.argv
    dump = lambda: certificate.write(("stratal_syncope_full.json" if full else "stratal_syncope.json"), rec)

    MAIN = declarations(shorten=True, ref_weight=True, env="all", level_scoped=True)
    NAMES = sorted(MAIN)
    Wm = weights(MAIN)
    rec["weights"] = {k: v for k, v in Wm.items() if v}
    it, B = run_set(items, Wm, MAIN, NAMES)
    rec["items"] = it
    print(f"1. {sum(v['winner_in_expected'] for v in it.values())}/{len(it)} contexts at the displayed vector"
          + (f"; outside: {mism(it)}" if mism(it) else ""))
    variants = {
        "surface_weight": (dict(shorten=True, ref_weight=False), {}),
        "realisational_shortening": (dict(shorten=False, ref_weight=False), {"IDENT_LONG": BOUND}),
        "env_open": (dict(shorten=True, ref_weight=True, env="open"), {}),
        "unscoped": (dict(shorten=True, ref_weight=True, level_scoped=False), {}),
    }
    rec["ablations"] = {}
    for name, (kw, over) in variants.items():
        D = declarations(**kw)
        Wv = {**weights(D), **{k: v for k, v in over.items() if k in D}}
        nm = sorted(D)
        r, Bv = run_set(items, Wv, D, nm)
        rec["ablations"][name] = {"mismatches": mism(r), "winners_at_mismatches": {k: r[k]["winners"] for k in mism(r)}}
        print(f"1. ablation {name}: {len(r) - len(mism(r))}/{len(r)}; mismatches {mism(r)}")
        if mism(r):
            fx = tuple(i for i, k in enumerate(nm) if k in HARD or over.get(k) == BOUND)
            rec["ablations"][name]["region"] = region(Bv, nm, [F(Wv[k]) for k in nm], fx)
            print(f"1.    its region: {rec['ablations'][name]['region'].get('feasible')} {rec['ablations'][name]['region'].get('reason', '')}")
            if full and not rec["ablations"][name]["region"].get("feasible"):
                sub = {k: v for k, v in Bv.items() if k in mism(r) or k.startswith(("K", "S"))}
                rec["ablations"][name]["pair_conflicts"] = pair_conflicts(sub, nm, fx)
                print(f"1.    unresolved pair searches: {rec['ablations'][name]['pair_conflicts'][:12]}")
                import random
                rng = random.Random(1)
                ex = []
                if "SHORTEN" in D:
                    e = [0.0] * len(nm); e[nm.index("SHORTEN")] = 1.0; e[nm.index("IDENT_LONG")] = -1.0; ex = [e]
                out = {"plain": None, "shortening_effective": None}
                for mode, rows_extra in (("plain", []), ("shortening_effective", ex)):
                    if mode == "shortening_effective" and not ex:
                        continue
                    for t in range(40):
                        w0 = [F(Wv[k]) for k in nm] if t == 0 else [F(rng.randint(0, 1000)) for _ in nm]
                        res = region(Bv, nm, w0, fx, rows_extra)
                        if res.get("feasible"):
                            out[mode] = {"restart": t, "witness": res["witness"]}; break
                rec["ablations"][name]["restarts"] = out
                print(f"1.    restarts: plain {'found' if out['plain'] else 'none in 40'}; shortening effective {'found' if out['shortening_effective'] else ('none in 40' if ex else 'n/a')}")
    res = rec["residue"] = run_items(NEZ_RESIDUE, Wm, MAIN)
    print(f"1. the residue (not fitted): {[(k, v['winners'], v['expected']) for k, v in res.items()]}")
    dump()
    fixed = tuple(i for i, k in enumerate(NAMES) if k in HARD)
    w0 = [F(Wm[k]) for k in NAMES]
    reg = rec["region"] = region(B, NAMES, w0, fixed)
    print(f"1. joint region (bound requirements fixed): {reg.get('feasible')} {reg.get('witness')}")
    if reg.get("feasible"):
        Wr = {k: F(v) for k, v in reg["witness"].items()}
        Wr = {k: Wr.get(k, 0) for k in NAMES}
        itw = run_items(items, Wr, MAIN)
        rec["items_at_witness"] = {"agree": sum(v["winner_in_expected"] for v in itw.values()), "n": len(itw), "mismatches": mism(itw)}
        print(f"1. at the exact witness: {rec['items_at_witness']}")
    else:
        rec["pair_conflicts"] = pair_conflicts(B, NAMES, fixed)
        print(f"1. unresolved pair searches: {rec['pair_conflicts'][:10]}")
    dump()

    L = listed_declarations()
    Dallo = {k: v for k, v in MAIN.items() if k != "SYNCOPE"}; Dallo["ALLO_OUT"] = L["ALLO_OUT"]
    r = run_items(items, weights(Dallo), Dallo)
    rec["allo_out"] = {"mismatches": mism(r), "winners_at_mismatches": {k: r[k]["winners"] for k in mism(r)}}
    print(f"2. the listed outward statement in place of syncope: {len(r) - len(mism(r))}/{len(r)}; mismatches {mism(r)}")
    Dany = dict(MAIN); del Dany["SEL_SISTER"]; Dany["SEL_ANY"] = L["SEL_ANY"]
    r = run_items(items, weights(Dany), Dany, prune=False) if len(items) <= 6 else run_items(
        {k: v for k, v in items.items() if k.startswith(("K", "R"))}, weights(Dany), Dany, prune=False)
    rec["sel_any"] = {"mismatches": mism(r), "n": len(r)}
    print(f"2. selection by any later stem morpheme: {len(r) - len(mism(r))}/{len(r)}; mismatches {mism(r)}")
    CX1 = [("kuu", 0, 0, ("alt",)), ("táayN", 0, 1), ("én’i", 0, 1, ("app2",)), ("see", 0, 1)]
    rec["constructed_selection"] = {"input": surface(build(CX1)),
                                    "sister": evaluate(build(CX1), Wm, MAIN)["winners"],
                                    "any": evaluate(build(CX1), weights(Dany), Dany, prune=False)["winners"]}
    print(f"2. constructed context {rec['constructed_selection']}")
    dump()

    D1 = declarations(shorten=False, ref_weight=False)
    W1 = {**weights(D1), "IDENT_LONG": BOUND}
    D2 = {k: v for k, v in declarations(shorten=True, ref_weight=False).items() if k != "SYNCOPE"}
    W2 = weights(D2)
    D1w = {k: v for k, v in D1.items() if k != "DEP_X_FINAL"}; W1w = {k: v for k, v in W1.items() if k != "DEP_X_FINAL"}
    tp = rec["two_level"] = {}
    for key, (spec, expected, _) in items.items():
        for persist in (False, True):
            w2, w1 = two_pass(spec, D1, W1, D2, W2, persist)
            tp.setdefault(key, {})["persist" if persist else "no_persist"] = {"stem_level": w1, "word_level": w2,
                                                                              "in_expected": all(x in expected for x in w2)}
        w2, w1 = two_pass(spec, D1w, W1w, D2, W2, False)
        tp[key]["final_ban_word_level"] = {"stem_level": w1, "word_level": w2, "in_expected": all(x in expected for x in w2)}
    bad = {p: [k for k, v in tp.items() if not v[p]["in_expected"]] for p in ("no_persist", "persist", "final_ban_word_level")}
    rec["two_level_mismatches"] = bad
    print(f"3. two-level evaluation: mismatches without persistence {bad['no_persist']}, with {bad['persist']}, final ban word-level {bad['final_ban_word_level']}")
    CX2 = [("hi", 0, 2), ("c’ákN", 0, 0), ("", 0, 1), ("e", 1, 1)]
    rec["constructed_floating"] = {"input": surface(build(CX2)), "fixed_reference": evaluate(build(CX2), Wm, MAIN)["winners"],
                                   "two_level_no_persist": two_pass(CX2, D1, W1, D2, W2, False)[0],
                                   "two_level_persist": two_pass(CX2, D1, W1, D2, W2, True)[0],
                                   "two_level_final_ban_word_level": two_pass(CX2, D1w, W1w, D2, W2, False)[0]}
    print(f"3. constructed context {rec['constructed_floating']}")
    dump()

    Daud = dict(MAIN); Daud.update(L)
    n1, v1 = audit_this(items, Daud)
    per = {}
    for _, _, vs in v1:
        for v in vs:
            per[v["declaration"]] = per.get(v["declaration"], 0) + 1
    rec["inward_audit"] = {"coverage": "Resolved-slot accesses only; custom reference terms require separate semantic inspection. Zero slot violations does not certify all information access.",
                           "this_fragment": {"structures": n1, "structures_with_a_violation": len(v1),
                                             "violations_by_declaration": per, "examples": v1[:5]},
                           "term_access": {"SEL_SISTER": "the reference's next present node after the root's vowel: its sister, cycle 1 (inward)",
                                           "SEL_ANY": "any later vowel-initial morpheme of the stem in the reference (outward: excluded by the restriction)"}}
    print(f"4. inward audit, this fragment: {n1} structures, {len(v1)} with a violation, by declaration {per}")
    n2, v2 = audit_accent()
    rec["inward_audit"]["accent_fragment"] = {"structures": n2, "violations": v2[:20], "n_violations": len(v2)}
    print(f"4. inward audit, accent fragment: {n2} structures, {len(v2)} violations {v2[:3]}")
    dump()

    rk = {k: ([(m[0].replace("én’i", "én’y"),) + tuple(m[1:]) for m in spec], exp, loc)
          for k, (spec, exp, loc) in items.items() if any(m[0] == "én’i" for m in spec)}
    r = run_items(rk, Wm, MAIN)
    rec["recoding_glide"] = {"n": len(r), "mismatches": mism(r), "winners_at_mismatches": {k: r[k]["winners"] for k in mism(r)}}
    print(f"5. the suffix's final segment a glide: {len(r) - len(mism(r))}/{len(r)}; mismatches {mism(r)}")
    if rk:
        Bk = blocks(rk, Wm, MAIN, NAMES)
        rec["recoding_region"] = region(Bk, NAMES, w0, fixed)
        print(f"5. its region: {rec['recoding_region'].get('feasible')}")
    dump()

    rec["exchange"] = exchange_certificate(items, MAIN, NAMES)
    print(f"6. exchanges for lexically long nuclei: {rec['exchange']}")
    idx = {k: i for i, k in enumerate(NAMES)}
    row = [F(0)] * len(NAMES)
    for k, a in (("MAX_V", 1), ("MAX_VV", 1), ("IDENT_LONG", -1), ("DEP_C", -2), ("SYNCOPE", -(1 + LAM)), ("PENULT", -LAM)):
        row[idx[k]] = a
    B2 = {k: (v[0], v[1] + [[]]) for k, v in B.items()}
    strict_extra = [row]
    w = list(w0); ok_sub = None
    for _ in range(10):
        strict = list(strict_extra)
        for key, (listed, unlisted) in B.items():
            rows = [r for rs in listed.values() for r in rs]
            cheapest = min(rows, key=lambda r: sum(a * b for a, b in zip(w, r)))
            for l in unlisted:
                strict.append([x - y for x, y in zip(l, cheapest)])
        ok, x = lp_weak([], strict, len(NAMES), fixed)
        if ok:
            ok_sub = {k: str(v) for k, v in zip(NAMES, x) if v > 0}; break
        if x is None:
            break
        w = x
    rec["exchange_subregion"] = {"feasible": True if ok_sub is not None else None,
                                 "status": "EXACT_DECLARED_DOMAIN_WITNESS" if ok_sub is not None else "UNRESOLVED_NUMERICAL_BRANCH_SEARCH", "witness": ok_sub,
                                 "inequality": "MAX_V + MAX_VV > IDENT_LONG + 2 DEP_C + (1+lambda) SYNCOPE + lambda PENULT"}
    print(f"6. the sub-region where the exchange closes meets the data's region: {rec['exchange_subregion']['feasible']}")
    dump()

    specs = schematic(120 if not full else 300, seed=0)
    rec["schematic"] = schematic_checks(specs, Wm, MAIN)
    print(f"7. schematic words: {rec['schematic']}")
    rec["seconds"] = round(time.time() - t0, 1)
    dump()
    print(f"certificate written in {rec['seconds']} s")


if __name__ == "__main__":
    main()
