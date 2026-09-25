from __future__ import annotations
from phonological_requirements import certificate, paths

import itertools
import json
from fractions import Fraction as F
from pathlib import Path

from .core import ABSENT
from .evaluate import activation, coefficients, score
from .frag_morphaccent import (build, declarations, nuclei, relink, sigma,
                               surface, well_formed, with_made)

OUT = paths.CERTIFICATES
LAM = F(1, 8)
SG = sigma()
DECLS = declarations()
NAMES = sorted(DECLS)

def M(segs, side=2, rank=1, acc=None, flags=(), pwd=0):
    return {"segs": list(segs), "side": side, "rank": rank, "acc": acc,
            "flags": tuple(flags), "pwd": pwd}


def R(segs, acc=None):
    return M(segs, side=0, rank=0, acc=acc)


ITEMS_JP = {
    "hasi_1": [R("h a s i".split(), 1)], "hasi_2": [R("h a s i".split(), 3)],
    "hasi_0": [R("h a s i".split())],
    "inoti": [R("i n o t i".split(), 0)], "kokoro": [R("k o k o r o".split(), 3)],
    "atama": [R("a t a m a".split(), 4)], "miyako": [R("m i y a k o".split())],
    "yom_tara": [R("y o m".split(), 1), M("t a r a".split(), acc=1)],
    "yob_tara": [R("y o b".split()), M("t a r a".split(), acc=1)],
    "abura_ppo": [R("a b u r a".split()), M("p p o".split(), acc=2, flags=("dele",)), M(["i"], rank=2)],
    "ada_ppo": [R("a d a".split(), 2), M("p p o".split(), acc=2, flags=("dele",)), M(["i"], rank=2)],
    "kiza_ppo": [R("k i z a".split(), 1), M("p p o".split(), acc=2, flags=("dele",)), M(["i"], rank=2)],
    "edo_kko": [R("e d o".split()), M("k k o".split(), flags=("dele",))],
    "koobe_kko": [R("k oo b e".split(), 1), M("k k o".split(), flags=("dele",))],
    "nyuuyooku_kko": [R("n y uu y oo k u".split(), 4), M("k k o".split(), flags=("dele",))],
    "yosida_ke": [R("y o s i d a".split()), M("k e".split(), flags=("prea",))],
    "nisimura_ke": [R("n i s i m u r a".split(), 3), M("k e".split(), flags=("prea",))],
    "andoo_ke": [R("a n d oo".split(), 0), M("k e".split(), flags=("prea",))],
    "yosida_si": [R("y o s i d a".split()), M("s i".split(), flags=("preb",))],
    "nisimura_si": [R("n i s i m u r a".split(), 3), M("s i".split(), flags=("preb",))],
    "satoo_si": [R("s a t oo".split(), 1), M("s i".split(), flags=("preb",))],
    "ma_futatu": [M("m a".split(), rank=1, flags=("prea",)), R("f u t a t u".split())],
    "ma_yonaka": [M("m a".split(), rank=1, flags=("prea",)), R("y o n a k a".split(), 5)],
    "kaki_mono": [R("k a k i".split(), 1), M("m o n o".split(), flags=("shf",), pwd=1)],
    "yomi_mono": [R("y o m i".split(), 1), M("m o n o".split(), flags=("shf",), pwd=1)],
    "nori_mono": [R("n o r i".split()), M("m o n o".split(), flags=("shf",), pwd=1)],
    "wasure_mono": [R("w a s u r e".split()), M("m o n o".split(), flags=("shf",), pwd=1)],
    "kuzu_ya": [R("k u z u".split(), 1), M("y a".split(), flags=("shf",), pwd=1)],
    "kona_ya": [R("k o n a".split(), 3), M("y a".split(), flags=("shf",), pwd=1)],
    "toma_ya": [R("t o m a".split()), M("y a".split(), flags=("shf",), pwd=1)],
    "kaki_te": [R("k a k i".split(), 1), M("t e".split(), flags=("exp",), pwd=1)],
    "katari_te": [R("k a t a r i".split()), M("t e".split(), flags=("exp",), pwd=1)],
    "inoti_nagara": [R("i n o t i".split(), 0), M("n a g a r a".split(), flags=("exp",), pwd=1)],
    "miyako_nagara": [R("m i y a k o".split()), M("n a g a r a".split(), flags=("exp",), pwd=1)],
    "kawa_no": [R("k a w a".split(), 3), M("n o".split(), flags=("delx",))],
    "atama_no": [R("a t a m a".split(), 4), M("n o".split(), flags=("delx",))],
    "umi_no": [R("u m i".split(), 0), M("n o".split(), flags=("delx",))],
    "utiwa_no": [R("u t i w a".split(), 2), M("n o".split(), flags=("delx",))],
    "ehon_no": [R("e h o N".split(), 2), M("n o".split(), flags=("delx",))],
    "hon_no": [R("h o N".split(), 1), M("n o".split(), flags=("delx",))],
    "hukoo_no": [R("h u k oo".split(), 3), M("n o".split(), flags=("delx",))],
    "ha_no": [R("h a".split(), 1), M("n o".split(), flags=("delx",))],
    "kyoo_no": [R("k y oo".split(), 2), M("n o".split(), flags=("delx",))],
}

ITEMS_RU = {
    "rak_u": [R("r a k".split(), 1), M(["u"])], "rak_ami": [R("r a k".split(), 1), M("a m i".split())],
    "rak_i_acc": [R("r a k".split(), 1), M(["i"], acc=0)],
    "stol_u": [R("s t o l".split()), M(["u"])], "stol_ami": [R("s t o l".split()), M("a m i".split())],
    "stol_i_acc": [R("s t o l".split()), M(["i"], acc=0)],
    "topor_0": [R("t o p o r".split())], "topor_u": [R("t o p o r".split()), M(["u"])],
    "komnat_i": [R("k o m n a t".split(), 1), M(["i"])], "tetrad_i": [R("t e t r a d".split(), 4), M(["i"])],
    "luz_ic_a": [R("l u ž".split(), 1), M("i c".split(), side=1, rank=1, acc=0), M(["a"], rank=2)],
    "cast_ic_a": [R("č a s t".split()), M("i c".split(), side=1, rank=1, acc=0), M(["a"], rank=2)],
    "siv_ux_a": [R("s i v".split(), 1), M("u x".split(), side=1, rank=1, acc=0, flags=("dele",)), M(["a"], rank=2)],
    "skak_ux_a": [R("s k a k".split()), M("u x".split(), side=1, rank=1, acc=0, flags=("dele",)), M(["a"], rank=2)],
    "puz_ac_u": [R("p u z".split(), 1), M("a č".split(), side=1, rank=1, flags=("dele",)), M(["u"], rank=2)],
    "izb_ac_u": [R("i z b".split()), M("a č".split(), side=1, rank=1, flags=("dele",)), M(["u"], rank=2)],
    "borod_ac_u": [R("b o r o d".split()), M("a č".split(), side=1, rank=1, flags=("dele",)), M(["u"], rank=2)],
    "rukav_a": [R("r u k a v".split(), 3), M(["a"], flags=("dele",))],
    "master_a": [R("m a s t e r".split(), 1), M(["a"], flags=("dele",))],
    "promysl_i": [R("p r o m ɨ s l".split(), 2), M(["i"])],
    "kolokol_u": [R("k o l o k o l".split(), 1), M(["u"])],
    "kolokol_am": [R("k o l o k o l".split(), 1), M("a m".split(), flags=("dele",))],
    "kolbas_e": [R("k o l b a s".split()), M(["e"])],
    "kolbas_am": [R("k o l b a s".split()), M("a m".split(), flags=("preb",))],
    "vi_pisat": [M("v i".split(), rank=1, acc=1, flags=("dele",)), R("p' i s a".split(), 3), M(["t'"], rank=2)],
}

ITEMS_CU = {
    "pe_yax": [M("p e".split(), rank=1, acc=1), R("y a x".split())],
    "ne_yax": [M("n e".split(), rank=1, acc=1), R("y a x".split())],
    "pe_yax_qal": [M("p e".split(), rank=1, acc=1), R("y a x".split()), M("q a l".split(), rank=2, acc=1)],
    "yax_qal_i": [R("y a x".split()), M("q a l".split(), rank=1, acc=1), M(["i"], rank=2, acc=0)],
    "ne_wen_qal": [M("n e".split(), rank=1, acc=1), R("w e n".split()), M("q a l".split(), rank=2, acc=1)],
    "yax_em": [R("y a x".split()), M("e m".split())], "max_em": [R("m a x".split()), M("e m".split())],
    "mi_ne_tew": [M("m i".split(), rank=2), M("n e".split(), rank=1, acc=1), R("t e w".split())],
    "pe_miaw_lu": [M("p e".split(), rank=1, acc=1), R("m i ʔ a w".split(), 1), M("l u".split(), rank=2)],
    "ayu_qa": [R("ʔ a y u".split(), 1), M("q a".split(), acc=1)],
    "pe_tul_qa": [M("p e".split(), rank=1, acc=1), R("t u l".split(), 1), M("q a".split(), rank=2, acc=1)],
    "pe_pulin_qal": [M("p e".split(), rank=1, acc=1), R("p u l i n".split(), 3), M("q a l".split(), rank=2, acc=1)],
    "ne_ngiy_qal_i_pe": [M("n e".split(), rank=1, acc=1), R("ŋ i y".split(), 1), M("q a l".split(), rank=2, acc=1),
                         M(["i"], rank=3, acc=0), M("p e".split(), rank=4)],
    "wena_nuk": [R("w e n a".split()), M("n u k".split(), flags=("preb",))],
    "ne_ma_ci": [M("n e".split(), rank=1, acc=1), R("m a".split()), M("č i".split(), rank=2, flags=("preb",))],
    "pe_tama_nga": [M("p e".split(), rank=1, acc=1), R("t a m a".split()), M("ŋ a".split(), rank=2, flags=("preb",))],
    "meme_yke": [R("m e m e".split(), 1), M("y k e".split(), flags=("preb",))],
    "tivie_maa_le": [R("t i v i ʔ e".split(), 1), M("m aa".split(), flags=("preb",)), M("l e".split(), rank=2)],
    "yax_i_qa_te": [R("y a x".split()), M(["i"], side=1, rank=1, acc=0), M("q a".split(), rank=2, acc=1), M("t e".split(), rank=3)],
    "kwa_i_qa_te": [R("k w a".split()), M(["i"], side=1, rank=1, acc=0), M("q a".split(), rank=2, acc=1), M("t e".split(), rank=3)],
    "pacike_i_ce": [R("p a č i k e".split(), 1), M(["i"], side=1, rank=1, acc=0), M("č e".split(), rank=2)],
    "wiwe_i_ce": [R("w i w e".split(), 1), M(["i"], side=1, rank=1, acc=0), M("č e".split(), rank=2)],
    "ne_max_i_ve_ngax": [M("n e".split(), rank=1, acc=1), R("m a x".split()), M(["i"], side=1, rank=2, acc=0),
                         M("v e".split(), rank=3), M("ŋ a x".split(), rank=4, flags=("preb",))],
}

ZERO = {n: 0 for n in NAMES}
W_JP = dict(ZERO, CULM=200, DEP=10, MAX_R=45, MAX_A=10, MAX_INIT=30, MAXLINK_R=25, MAXLINK_X=4, LOCAL=10,
            NONFINAL=2, ALIGN_R_PWD=1, ALIGN_L_PWD=1, ANTI_DEL=80, ANTI_DEL_ADJ=60, ANTI_PRE_A=80,
            ANTI_PRE_B=20, ANTI_SHIFT=60, ANTI_EXPEL=60)
W_RU = dict(ZERO, CULM=200, HEAD=200, DEP=4, MAX_R=60, MAX_S=30, MAX_A=20, MAXLINK_R=60, MAXLINK_X=30,
            LOCAL=30, PSP=12, ALIGN_R_ALL=1, ANTI_DEL=100, ANTI_PRE_B=20)
W_CU = dict(ZERO, CULM=200, HEAD=200, DEP=4, MAX_R=60, MAX_S=30, MAX_A=12, MAXLINK_R=60, MAXLINK_X=12,
            LOCAL=12, INIT=8, ALIGN_R=1, ANTI_PRE_B=20)
LANGS = {"jp": (ITEMS_JP, W_JP), "ru": (ITEMS_RU, W_RU), "cu": (ITEMS_CU, W_CU)}


def candidates(ref):
    nuc = nuclei(ref)
    accs = list(ref.order["acc"])
    for combo in itertools.product([None] + nuc, repeat=len(accs)):
        hosts = [h for h in combo if h is not None]
        if len(hosts) != len(set(hosts)):
            continue
        s = ref
        for a, h in zip(accs, combo):
            s = relink(s, a, h)
        yield s
        for n in nuc:
            if n not in hosts:
                yield with_made(s, n)


def evaluate(ref, W, decls=DECLS, lam=LAM, cands=None):
    acts = activation(SG, ref, decls)
    rows = []
    for c in (cands if cands is not None else candidates(ref)):
        assert well_formed(c)
        co = coefficients(SG, ref, c, decls, acts)
        rows.append((surface(c), co, score(co, W, lam)))
    best = min(r[2] for r in rows)
    winners = sorted({r[0] for r in rows if r[2] == best})
    return {"rows": rows, "winners": winners, "best": best}


def run_languages():
    from .observations import ALDERETE_CU, ALDERETE_JP, ALDERETE_RU
    obs = {"jp": ALDERETE_JP, "ru": ALDERETE_RU, "cu": ALDERETE_CU}
    out = {}
    for lang, (items, W) in LANGS.items():
        res = {}
        for key, spec in items.items():
            ref = build(spec)
            e = evaluate(ref, W)
            exp, loc = obs[lang][key]
            res[key] = {"input": surface(ref), "winners": e["winners"], "expected": exp,
                        "locator": loc, "agrees": e["winners"] == [exp],
                        "candidates": len(e["rows"])}
        out[lang] = res
    return out


def inequalities(lang, items=None, decls=DECLS, lam=LAM):
    from .observations import ALDERETE_CU, ALDERETE_JP, ALDERETE_RU
    obs = {"jp": ALDERETE_JP, "ru": ALDERETE_RU, "cu": ALDERETE_CU}[lang]
    items = items or LANGS[lang][0]
    names = sorted(decls)
    ineqs, ties = [], []
    for key, spec in items.items():
        ref = build(spec)
        e = evaluate(ref, {n: 1 for n in names}, decls, lam)
        exp = obs[key][0]
        tgt = [r for r in e["rows"] if r[0] == exp]
        assert tgt, (key, exp, sorted({r[0] for r in e["rows"]})[:8])
        vec = lambda co: [F(co[k][0]) + lam * F(co[k][1]) for k in names]
        losers = [r for r in e["rows"] if r[0] != exp]
        ineqs.append((key, [vec(t[1]) for t in tgt], [vec(l[1]) for l in losers]))
    return names, ineqs


def region(lang, decls=DECLS, lam=LAM, fixed=None, W=None, pre=None):
    import numpy as np
    from scipy.optimize import linprog
    names, ineqs = pre if pre is not None else inequalities(lang, decls=decls, lam=lam)
    W = W or LANGS[lang][1]
    wv = [F(W.get(k, 0)) for k in names]
    cost = lambda row: sum(a * b for a, b in zip(wv, row))
    n = len(names)
    rows, aliases = [], []
    for key, tg, ls in ineqs:
        t = min(tg, key=cost)
        for l in ls:
            d = [float(x - y) for x, y in zip(l, t)]
            if all(abs(x) < 1e-12 for x in d):
                aliases.append(key)
                continue
            rows.append(d)
    if aliases:
        return {"feasible": None, "status": "UNRESOLVED_SELECTED_BRANCH_ALIAS",
                "conclusive": False, "aliases": sorted(set(aliases))}
    A = np.array(rows)
    c = np.zeros(n + 1); c[-1] = -1.0
    A_ub = np.hstack([-A, np.ones((len(rows), 1))]); b_ub = np.zeros(len(rows))
    bounds = [(0, None)] * n + [(None, 1.0)]
    if fixed:
        for k, v in fixed.items():
            bounds[names.index(k)] = (v, v)
    res = linprog(c, A_ub=A_ub, b_ub=b_ub, bounds=bounds, method="highs")
    if res.status == 0 and res.x[-1] > 1e-9:
        witness = [F(str(float(v))) for v in res.x[:-1]]
        bounds_ok = all((lo is None or v >= F(str(lo))) and (hi is None or v <= F(str(hi)))
                        for v, (lo, hi) in zip(witness, bounds[:-1]))
        exact_cost = lambda row: sum(a * b for a, b in zip(witness, row))
        margins = [min(map(exact_cost, ls)) - min(map(exact_cost, tg)) for _, tg, ls in ineqs]
        if bounds_ok and min(margins) > 0:
            return {"feasible": True, "status": "EXACT_FULL_FIBER_WITNESS",
                    "slack": str(min(margins)),
                    "witness": {k: str(v) for k, v in zip(names, witness) if v},
                    "n_inequalities": len(rows)}
    return {"feasible": None, "status": "UNRESOLVED_NUMERICAL_SEARCH", "conclusive": False,
            "solver_status": int(res.status), "n_inequalities": len(rows)}


def necessary(lang, decls=DECLS, lam=LAM):
    W = LANGS[lang][1]
    used = [n for n in sorted(decls) if W.get(n, 0) > 0]
    unused = {n: 0 for n in sorted(decls) if W.get(n, 0) == 0}
    pre = inequalities(lang, decls=decls, lam=lam)
    base = region(lang, decls, lam, fixed=unused, pre=pre)
    out = {}
    for name in used:
        r = region(lang, decls, lam, fixed=dict(unused, **{name: 0}), pre=pre)
        out[name] = "dispensable" if r["feasible"] is True else "unresolved"
    return {"used": used, "region_of_used": base, "by_declaration": out}


CLASSES = {"rec0": dict(acc=None, flags=()), "rec1": dict(acc=1, flags=()),
           "dom0": dict(acc=None, flags=("dele",)), "dom1": dict(acc=1, flags=("dele",)),
           "prea": dict(acc=None, flags=("prea",)), "preb": dict(acc=None, flags=("preb",))}
ROOTS = {"r0": None, "r1": 1, "r2": 3}
SUFFIX = ["k", "a"]


def family_item(root, classes):
    morphs = [R("t a t a".split(), ROOTS[root])]
    for i, c in enumerate(classes, 1):
        morphs.append(M(list(SUFFIX), side=2, rank=i, **CLASSES[c]))
    return morphs


def family(max_len):
    for n in range(max_len + 1):
        for classes in itertools.product(sorted(CLASSES), repeat=n):
            for root in sorted(ROOTS):
                yield (root,) + classes


def analysis(ref, c):
    kept, made = [], None
    for a, b in c.assoc:
        if c.real.get(a) != "A":
            continue
        if a.kind == "made":
            made = c.dom[b]["morph"]
        else:
            kept.append(c.dom[a]["morph"])
    return tuple(sorted(kept)), made


def outermost_dominance(item, W, decls=DECLS):
    spec = [dict(m) for m in item]
    ref = build(spec)
    e = evaluate(ref, W, decls)
    dele = [i for i, m in enumerate(spec) if "dele" in m["flags"]]
    k = max(dele) if dele else None
    best = e["best"]
    wins = [(surface(c), analysis(ref, c)) for c in candidates(ref)
            if score(coefficients(SG, ref, c, decls, activation(SG, ref, decls)), W, LAM) == best]
    rec = {"k": k, "winners": sorted({w[0] for w in wins}), "kept": sorted({w[1][0] for w in wins}),
           "made": sorted({w[1][1] for w in wins}, key=lambda x: (x is None, x))}
    if k is None:
        return rec
    rec["L1"] = all(all(i >= k for i in kept) for _, (kept, _) in wins)
    red = [dict(m) for m in spec]
    for i in range(k):
        red[i]["acc"] = None
    e2 = evaluate(build(red), W, decls)
    rec["reduced_winners"] = e2["winners"]
    rec["L3"] = e2["winners"] == rec["winners"]
    return rec


def exchange_lemma(max_len, grammars=("jp", "ru")):
    def routes(c, acc):
        host = next(b for a, b in c.assoc if a == acc)
        unreal = relink(c, acc, None)
        out = [unreal]
        if not any(a.kind == "made" for a, b in unreal.assoc if unreal.real.get(a) == "A"):
            out.append(with_made(unreal, host))
        return out

    def premise(ref, W, acc, c):
        side = ref.dom[acc]["side"]
        wmax = {0: W["MAX_R"], 1: W["MAX_S"], 2: W["MAX_A"]}[side]
        ref_host = next(b for a, b in ref.assoc if a == acc)
        nuc = nuclei(ref)
        own = [n for n in nuc if ref.dom[n]["morph"] == ref.dom[acc]["morph"]]
        root_initial = side == 0 and ref_host == own[0]
        host = next(b for a, b in c.assoc if a == acc)
        only = sum(1 for a, b in c.assoc if c.real.get(a) == "A") == 1
        swap = W["DEP"] + LAM * W["INIT"] * (host != nuc[0])
        unreal = LAM * W["HEAD"] * only + LAM * (W["ANTI_PRE_A"] + W["ANTI_PRE_B"])
        return W["ANTI_DEL"] > wmax + W["MAX_INIT"] * root_initial + min(swap, unreal)

    out = {}
    for g in grammars:
        W = LANGS[g][1]
        checked = with_premise = fails_with = fails_without = 0
        examples = []
        for key in family(max_len):
            spec = family_item(key[0], key[1:])
            dele = [i for i, m in enumerate(spec) if "dele" in m["flags"]]
            if not dele:
                continue
            k = max(dele)
            ref = build(spec); acts = activation(SG, ref, DECLS)
            for c in candidates(ref):
                for a, b in list(c.assoc):
                    if a.kind != "lex" or c.real.get(a) != "A" or c.dom[a]["morph"] >= k:
                        continue
                    checked += 1
                    s1 = score(coefficients(SG, ref, c, DECLS, acts), W, LAM)
                    best = min(score(coefficients(SG, ref, c2, DECLS, acts), W, LAM) for c2 in routes(c, a))
                    p = premise(ref, W, a, c)
                    with_premise += p
                    if not best < s1:
                        if p:
                            fails_with += 1
                        else:
                            fails_without += 1
                        if len(examples) < 6:
                            examples.append(("+".join(key), surface(c), str(s1), str(best), p))
        out[g] = {"exchanges": checked, "with_premise": with_premise, "failures_under_premise": fails_with,
                  "failures_without_premise": fails_without, "examples": examples}
    W = LANGS["jp"][1]
    probe = {}
    for name, spec in (("ta1+prea+dom0", [R("t a".split(), 1), M(list(SUFFIX), rank=1, flags=("prea",)), M(list(SUFFIX), rank=2, flags=("dele",))]),
                       ("ta1+dom0", [R("t a".split(), 1), M(list(SUFFIX), rank=1, flags=("dele",))]),
                       ("r1+prea+dom0", family_item("r1", ("prea", "dom0")))):
        e = evaluate(build(spec), W)
        probe[name] = {"winners": e["winners"], "best": str(e["best"])}
    out["premise_boundary_jp"] = probe
    return out


def run_family(max_len, grammars=("jp", "ru"), keep=None):
    out = {}
    for g in grammars:
        W = LANGS[g][1]
        rows, fail1, fail3 = {}, [], []
        for key in family(max_len):
            if keep is not None and not keep(key):
                continue
            r = outermost_dominance(family_item(key[0], key[1:]), W)
            rows["+".join(key)] = r
            if r.get("L1") is False:
                fail1.append("+".join(key))
            if r.get("L3") is False:
                fail3.append("+".join(key))
        with_k = sum(1 for r in rows.values() if r["k"] is not None)
        out[g] = {"items": len(rows), "with_dominant": with_k, "L1_failures": fail1,
                  "L3_failures": fail3, "rows": rows}
    return out


def relabel_made(s, start):
    from .core import NodeId, Struct
    ren = {}
    for a in s.order.get("acc", ()):
        if a.kind == "made" and s.real.get(a) == "A":
            ren[a] = NodeId("Acc", "lex", start + len(ren))
    if not ren:
        return s, {}
    order = dict(s.order)
    order["acc"] = tuple(ren.get(a, a) for a in s.order["acc"] if not (a.kind == "made" and a not in ren))
    real = {ren.get(k, k): v for k, v in s.real.items() if not (k.kind == "made" and k not in ren)}
    dom = {ren.get(k, k): v for k, v in s.dom.items() if not (k.kind == "made" and k not in ren)}
    assoc = frozenset((ren.get(a, a), b) for a, b in s.assoc)
    return Struct(order=order, real=real, dom=dom, assoc=assoc, corr=s.corr), ren


def winner_struct(ref, W, decls=DECLS):
    acts = activation(SG, ref, decls)
    best, first, surfs = None, None, set()
    for c in candidates(ref):
        sc = score(coefficients(SG, ref, c, decls, acts), W, LAM)
        if best is None or sc < best:
            best, first, surfs = sc, c, {surface(c)}
        elif sc == best:
            surfs.add(surface(c))
    if len(surfs) != 1:
        raise ValueError(f"Reset reference requires one observable base winner: {sorted(surfs)}")
    return first, sorted(surfs), best


def base_spec(spec, policy):
    if len(spec) == 1:
        return None
    if policy == "recursive":
        return spec[:-1]
    flagged = [i for i, m in enumerate(spec) if m.get("flags")]
    cut = flagged[-1] if flagged else 1
    return spec[:cut] if cut >= 1 else None


def reset_reference(spec, W, decls=DECLS, policy="recursive"):
    base = base_spec(spec, policy)
    if base is None:
        return build(spec), []
    base_ref, _ = reset_reference(base, W, decls, policy)
    base_win, _, _ = winner_struct(base_ref, W, decls)
    new_spec = [dict(m) for m in spec]
    morph_acc = {}
    for a, b in base_win.assoc:
        if base_win.real.get(a) == "A":
            morph = base_win.dom[b]["morph"]
            if morph in morph_acc and morph_acc[morph] != b:
                raise ValueError("Reset reference cannot represent multiple accents in one morpheme")
            morph_acc[morph] = b
    nb = len(base)
    for i in range(nb):
        host = morph_acc.get(i)
        if host is None:
            new_spec[i]["acc"] = None
        else:
            segs_before = sum(len(spec[j]["segs"]) for j in range(i))
            new_spec[i]["acc"] = host.index - segs_before
    return build(new_spec), [i for i in range(nb) if new_spec[i]["acc"] != spec[i]["acc"]]


ANTI = [n for n in NAMES if n.startswith("ANTI_")]
NOT_ANTI = [n for n in NAMES if not n.startswith("ANTI_")]


def oo_faithfulness():
    from .core import Decl, Linked, Made, Not, Or_, Present, TRUE
    from .frag_morphaccent import HREF, TA
    return {"OO_MAX": Decl("OO_MAX", "Acc", (TA,), Not(Made("t")), Present("t"),
                           kind="faithfulness", locus_side="reference"),
            "OO_DEP": Decl("OO_DEP", "Acc", (TA,), Made("t"), Or_((Not(Made("t")), Not(Present("t")))),
                           kind="faithfulness"),
            "OO_MAXLINK": Decl("OO_MAXLINK", "Acc", (TA, HREF), Not(Made("t")),
                               Or_((Not(Present("t")), Linked("t", "hr", where="current"))),
                               kind="faithfulness", locus_side="reference")}


OO = oo_faithfulness()


def oo_weights(W):
    return {"OO_MAX": W["MAX_R"], "OO_DEP": W["DEP"], "OO_MAXLINK": W["MAXLINK_R"]}


def evaluate_two(spec, W, decls=DECLS, W_OO=None, rows_only=False, policy="recursive", base_W=None):
    from .core import NodeId, Struct
    ref_io = build(spec)
    ref_oo, changed = reset_reference(spec, base_W if base_W is not None else W, decls, policy)
    io_acc = list(ref_io.order["acc"])
    oo_acc = list(ref_oo.order["acc"])
    def keyed(ref):
        return {(ref.dom[a]["morph"], b.index): a for a, b in ref.assoc if ref.real.get(a) == "A"}
    kio, koo = keyed(ref_io), keyed(ref_oo)
    extra = [k for k in koo if k not in kio]
    nuc = nuclei(ref_io)
    res = {"surfaces": None}
    dio = {n: decls[n] for n in NOT_ANTI}
    doo = {n: decls[n] for n in ANTI}
    doo.update(OO)
    W = dict(W, **(W_OO if W_OO is not None else oo_weights(W)))
    acts_io = activation(SG, ref_io, dio)
    rows = []
    best, surfs = None, set()
    seg_nodes = list(ref_io.order["seg"])
    for c in candidates(ref_io):
        hosts_taken = {b for a, b in c.assoc if c.real.get(a) == "A"}
        options = [[None] + [n for n in nuc if n not in hosts_taken] for _ in extra]
        for combo in itertools.product(*options):
            hs = [h for h in combo if h is not None]
            if len(hs) != len(set(hs)):
                continue
            cc = c
            for j, h in enumerate(combo):
                if h is not None:
                    cc = with_made(cc, h, index=200 + j)
            if not well_formed(cc):
                continue
            ren = {}
            for j, (m, hi) in enumerate(extra):
                node = NodeId("Acc", "made", 200 + j)
                if node in cc.real:
                    ren[node] = koo[(m, hi)]
            for k, a in kio.items():
                if k not in koo:
                    ren[a] = NodeId("Acc", "made", 300 + a.index)
            order = dict(cc.order); order["acc"] = tuple(ren.get(a, a) for a in cc.order["acc"])
            real = {ren.get(k, k): v for k, v in cc.real.items()}
            dom = {ren.get(k, k): v for k, v in cc.dom.items()}
            assoc = frozenset((ren.get(a, a), b) for a, b in cc.assoc)
            c_oo = Struct(order=order, real=real, dom=dom, assoc=assoc, corr=cc.corr)
            oo_order = dict(ref_oo.order)
            oo_order["acc"] = tuple(dict.fromkeys(list(ref_oo.order["acc"]) + [a for a in order["acc"] if a not in ref_oo.order["acc"]]))
            oo_real = dict(ref_oo.real); oo_dom = dict(ref_oo.dom)
            for a in order["acc"]:
                if a not in oo_real:
                    oo_real[a] = ABSENT; oo_dom[a] = dom[a]
            ref_oo2 = Struct(order=oo_order, real=oo_real, dom=oo_dom, assoc=ref_oo.assoc, corr=ref_oo.corr)
            co = coefficients(SG, ref_io, cc, dio, acts_io)
            co.update(coefficients(SG, ref_oo2, c_oo, doo, activation(SG, ref_oo2, doo)))
            if rows_only:
                rows.append((surface(cc), co))
                continue
            sc = score(co, W, LAM)
            if best is None or sc < best:
                best, surfs = sc, {surface(cc)}
            elif sc == best:
                surfs.add(surface(cc))
    if rows_only:
        return rows
    return {"winners": sorted(surfs), "best": best, "base_changed": changed, "extra": len(extra)}


def _lp_blocks(blocks, names, bounds_fn, choice):
    import numpy as np
    from scipy.optimize import linprog
    rows_all = []
    for (tg, ls), j in zip(blocks, choice):
        t = tg[j]
        for l in ls:
            d = [float(x - y) for x, y in zip(l, t)]
            if all(abs(x) < 1e-12 for x in d):
                return None, None
            rows_all.append(d)
    A = np.array(rows_all); n = len(names)
    c = np.zeros(n + 1); c[-1] = -1.0
    res = linprog(c, A_ub=np.hstack([-A, np.ones((len(rows_all), 1))]), b_ub=np.zeros(len(rows_all)),
                  bounds=bounds_fn() + [(None, 1.0)], method="highs")
    if res.status == 0 and res.x[-1] > 1e-9:
        witness = [F(str(float(v))) for v in res.x[:-1]]
        bounds_ok = all((lo is None or v >= F(str(lo))) and (hi is None or v <= F(str(hi)))
                        for v, (lo, hi) in zip(witness, bounds_fn()))
        margins = [sum(w * (l - t) for w, l, t in zip(witness, loser, tg[j]))
                   for (tg, ls), j in zip(blocks, choice) for loser in ls]
        if bounds_ok and min(margins) > 0:
            return witness, float(min(margins))
        return None, None
    return None, float(res.x[-1]) if res.status == 0 else None


def region_search(blocks, names, bounds_fn, w0, rounds=6):
    w = w0
    seen = set()
    for _ in range(rounds):
        choice = tuple(min(range(len(tg)), key=lambda j: sum(a * b for a, b in zip(w, tg[j]))) for tg, _ in blocks)
        if choice in seen:
            break
        seen.add(choice)
        x, slack = _lp_blocks(blocks, names, bounds_fn, choice)
        if x is not None:
            return {"feasible": True, "status": "EXACT_BRANCH_WITNESS", "slack": slack, "choice": list(choice),
                    "witness": {k: str(v) for k, v in zip(names, x) if v > 0}}
        if slack is None:
            return {"feasible": None, "status": "UNRESOLVED_BRANCH_SEARCH", "conclusive": False}
        w = [F(str(round(float(v), 6))) for v in _best_point(blocks, names, bounds_fn, choice)]
    return {"feasible": None, "status": "UNRESOLVED_ALTERNATING_SEARCH", "conclusive": False,
            "note": "no polyhedron found by the alternating search"}


def _best_point(blocks, names, bounds_fn, choice):
    import numpy as np
    from scipy.optimize import linprog
    rows_all = []
    for (tg, ls), j in zip(blocks, choice):
        t = tg[j]
        for l in ls:
            rows_all.append([float(x - y) for x, y in zip(l, t)])
    A = np.array(rows_all); n = len(names)
    c = np.zeros(n + 1); c[-1] = -1.0
    res = linprog(c, A_ub=np.hstack([-A, np.ones((len(rows_all), 1))]), b_ub=np.zeros(len(rows_all)),
                  bounds=bounds_fn() + [(None, 1.0)], method="highs")
    return res.x[:-1] if res.status == 0 else np.zeros(n)


def pair_exact(blocks_pair, names, bounds_fn):
    for j0 in range(len(blocks_pair[0][0])):
        for j1 in range(len(blocks_pair[1][0])):
            x, _ = _lp_blocks(blocks_pair, names, bounds_fn, (j0, j1))
            if x is not None:
                return True
    return None


def _blocks(lang, kind, policy="recursive", names=None):
    from .observations import ALDERETE_CU, ALDERETE_JP, ALDERETE_RU
    obs = {"jp": ALDERETE_JP, "ru": ALDERETE_RU, "cu": ALDERETE_CU}[lang]
    items, W = LANGS[lang]
    out, keys = [], []
    for key, spec in items.items():
        exp = obs[key][0]
        if kind == "two":
            rows = evaluate_two(spec, W, rows_only=True, policy=policy)
        else:
            ref = build(spec) if kind == "fixed" else reset_reference(spec, W, policy=policy)[0]
            acts = activation(SG, ref, DECLS)
            rows = [(surface(c), coefficients(SG, ref, c, DECLS, acts)) for c in candidates(ref)]
        vec = lambda co: [F(co[k][0]) + LAM * F(co[k][1]) for k in names]
        tg = [vec(co) for sf, co in rows if sf == exp]
        ls = [vec(co) for sf, co in rows if sf != exp]
        if not tg:
            out.append(None); keys.append(key); continue
        out.append((tg, ls)); keys.append(key)
    return keys, out


def region_reading(lang, kind, policy="recursive", min_copy=0.0, fixed_language_vector=False):
    names = sorted(DECLS) + (sorted(OO) if kind == "two" else [])
    keys, blocks = _blocks(lang, kind, policy, names)
    missing = [k for k, b in zip(keys, blocks) if b is None]
    blocks_ok = [b for b in blocks if b is not None]
    if missing:
        return {"feasible": False, "status": "TARGET_ABSENT_FROM_DECLARED_GEN",
                "targets_absent_from_gen": missing, "items": len(keys)}
    W = LANGS[lang][1]
    w0 = [F(W.get(k, 0)) if k in DECLS else F(oo_weights(W)[k]) for k in names]
    def bounds_fn():
        b = []
        for k in names:
            if fixed_language_vector and k in DECLS:
                b.append((float(W.get(k, 0)), float(W.get(k, 0))))
            elif k in OO:
                b.append((min_copy, 1000))
            else:
                b.append((0, 1000))
        return b
    r = region_search(blocks_ok, names, bounds_fn, w0)
    r["targets_absent_from_gen"] = missing
    r["items"] = len(blocks_ok)
    return r


def pair_conflicts(lang, kind, policy="recursive", min_copy=0.0, only=None):
    names = sorted(DECLS) + (sorted(OO) if kind == "two" else [])
    keys, blocks = _blocks(lang, kind, policy, names)
    B = {k: b for k, b in zip(keys, blocks) if b is not None}
    bounds_fn = lambda: [(min_copy if k in OO else 0, 1000) for k in names]
    ks = list(B) if only is None else [k for k in B if k in only]
    return [{"pair": [a, b], "status": "UNRESOLVED_NUMERICAL_BRANCH_SEARCH"}
            for a, b in itertools.combinations(ks, 2) if pair_exact([B[a], B[b]], names, bounds_fn) is None]


def run_references(max_len, grammars=("jp", "ru")):
    out = {"regions": {}}
    for lang in LANGS:
        out["regions"][lang] = {
            "fixed": region_reading(lang, "fixed"),
            "reset": region_reading(lang, "reset"),
            "two_recursive_copies_ge_1": region_reading(lang, "two", "recursive", min_copy=1.0),
            "two_to_last_class_copies_ge_1": region_reading(lang, "two", "to_last_class", min_copy=1.0),
            "two_recursive_copies_only_language_vector_fixed": region_reading(lang, "two", "recursive", fixed_language_vector=True),
        }
    out["regions"]["ru"]["reset_pair_rak_u_stol_u"] = pair_conflicts("ru", "reset", only=("rak_u", "stol_u"))
    woo = {}
    for g in grammars:
        r = out["regions"][g]["two_recursive_copies_ge_1"]
        woo[g] = {k: F(v) for k, v in r["witness"].items()} if r.get("feasible") else None
    for g in grammars:
        W = LANGS[g][1]
        W2 = {k: woo[g].get(k, F(0)) for k in list(DECLS) + list(OO)} if woo[g] else None
        rows, sep_reset, sep_two = {}, [], []
        for key in family(max_len):
            spec = family_item(key[0], key[1:])
            fixed = evaluate(build(spec), W)["winners"]
            rr, changed = reset_reference(spec, W)
            reset = evaluate(rr, W)["winners"]
            two = evaluate_two(spec, W2, W_OO={k: W2[k] for k in OO}, base_W=W)["winners"] if W2 else None
            rows["+".join(key)] = {"fixed": fixed, "reset": reset, "two": two, "base_changed": changed}
            if reset != fixed:
                sep_reset.append("+".join(key))
            if two is not None and two != fixed:
                sep_two.append("+".join(key))
        out[g] = {"items": len(rows), "reset_differs": sep_reset, "two_differ": sep_two, "rows": rows,
                  "two_reference_witness": {k: str(v) for k, v in woo[g].items()} if woo[g] else None}
    printed = {}
    for lang, (items, W) in LANGS.items():
        d = {}
        r = out["regions"][lang]["two_recursive_copies_ge_1"]
        W2 = {k: F(r["witness"].get(k, "0")) for k in list(DECLS) + list(OO)} if r.get("feasible") else None
        for key, spec in items.items():
            fixed = evaluate(build(spec), W)["winners"]
            rr, changed = reset_reference(spec, W)
            reset = evaluate(rr, W)["winners"]
            two = evaluate_two(spec, W2, W_OO={k: W2[k] for k in OO}, base_W=W)["winners"] if W2 else None
            if not (fixed == reset == two):
                d[key] = {"fixed": fixed, "reset": reset, "two": two, "base_changed": changed}
        printed[lang] = d
    out["printed_separations"] = printed
    return out


def reo_candidates(word):
    acc = [i for i, (_, a) in enumerate(word) if a]
    for i in range(len(word)):
        if i in acc:
            lost = [j for j in acc if j != i]
            nR = sum(1 for j in lost if word[j][0]); nA = len(lost) - nR
            yield (f"keep{i}", nR, nA, i, 0)
        nR = sum(1 for j in acc if word[j][0]); nA = len(acc) - nR
        yield (f"ins{i}", nR, nA, i, 1)


def reo_regions():
    words = {"af+root": [(False, False), (True, False)],
             "af+ROOT": [(False, False), (True, True)],
             "AF+ROOT": [(False, True), (True, True)],
             "AF+AF+root": [(False, True), (False, True), (True, False)],
             "af+AF+root": [(False, False), (False, True), (True, False)],
             "ROOT+AF": [(True, True), (False, True)]}
    def cost(c):
        _, nR, nA, e, d = c
        return f"{nR}*wR + {nA}*wA + {e}*wE + {d}*wD"
    out = {}
    for name, w in words.items():
        cs = list(reo_candidates(w))
        out[name] = {c[0]: {"cost": cost(c),
                            "wins_iff": [f"({cost(c)}) < ({cost(o)})" for o in cs if o is not c]}
                     for c in cs}
    patterns = {
        "root_contrast": ("af+ROOT", "keep1"),
        "affix_contrast": ("af+AF+root", "keep1"),
        "prefix_overrides_root": ("AF+ROOT", "keep0"),
        "leftmost_among_affixes": ("AF+AF+root", "keep0"),
        "root_over_prefix": ("AF+ROOT", "keep1"),
    }
    return {"words": out, "patterns": {k: {"word": w, "winner": c, "iff": out[w][c]["wins_iff"]}
                                        for k, (w, c) in patterns.items()}}


def reo_check_point(w):
    wR, wA, wE, wD = (F(x) for x in w)
    words = {"af+ROOT": [(False, False), (True, True)],
             "AF+ROOT": [(False, True), (True, True)],
             "af+AF+root": [(False, False), (False, True), (True, False)],
             "AF+AF+root": [(False, True), (False, True), (True, False)]}
    res = {}
    for name, word in words.items():
        cs = list(reo_candidates(word))
        sc = {c[0]: c[1] * wR + c[2] * wA + c[3] * wE + c[4] * wD for c in cs}
        b = min(sc.values())
        res[name] = sorted(k for k, v in sc.items() if v == b)
    excluded = (res["af+ROOT"] == ["keep1"] and res["af+AF+root"] == ["keep1"]
                and res["AF+ROOT"] == ["keep0"])
    return {"weights": [str(x) for x in (wR, wA, wE, wD)], "winners": res,
            "contrastive_with_prefix_override": excluded}


def reo_ot_typology():
    out = {}
    for perm in itertools.permutations(["wR", "wA", "wE"]):
        if perm.index("wA") < perm.index("wR"):
            continue
        w = {"wD": 1}
        for rank, name in zip((1000, 100, 10), perm):
            w[name] = rank
        pt = reo_check_point((w["wR"], w["wA"], w["wE"], w["wD"]))
        out[" >> ".join(perm)] = pt
    return out


def emit_reo_wolfram(reg):
    nm = lambda n: n.replace("_", "")
    L = ["vars = {wR, wA, wE, wD};",
         "nonneg = And @@ (# >= 0 & /@ vars);",
         "intrinsic = wR > wA;"]
    for name, p in reg["patterns"].items():
        L.append(f"{nm(name)} = And[" + ", ".join(p["iff"]) + "];")
    L.append("excluded = And[rootcontrast, affixcontrast, prefixoverridesroot];")
    L.append('root = NestWhile[ParentDirectory, DirectoryName[$InputFileName], !(DirectoryQ[FileNameJoin[{#, "python"}]] && DirectoryQ[FileNameJoin[{#, "wolfram"}]]) &, 1, 8];\noutdir = FileNameJoin[{root, "results", "requirements", "wolfram"}];\nIf[!DirectoryQ[outdir], CreateDirectory[outdir, CreateIntermediateDirectories -> True]];')
    L.append('res = <|"excluded_region" -> ToString[Reduce[nonneg && intrinsic && excluded, {wE, wR, wA, wD}, Reals], InputForm], "exists_wE" -> ToString[Reduce[Exists[wE, nonneg && intrinsic && excluded], {wR, wA, wD}, Reals], InputForm], "witness" -> ToString[FindInstance[nonneg && intrinsic && excluded, vars, Reals], InputForm], "no_strict_ranking_with_wR_gt_wA" -> ToString[Reduce[Exists[{wR, wA, wE, wD}, nonneg && intrinsic && excluded && wR >= 10 wA && (wE >= 10 wR || wA >= 10 wE) && wD <= wE/10], Reals], InputForm], "root_contrast_at_distance" -> ToString[Reduce[d*wE < wR + wD && d > 0 && wE > 0, d, Reals], InputForm], "rca_root_wins_for_every_n" -> ToString[Reduce[ForAll[n, n >= 1, n*wA + d*wE < wR + (n - 1)*wA], {wR, wA, wE, d}, Reals], InputForm]|>;')
    L.append('Export[FileNameJoin[{outdir, "morphological_accent_orientation.json"}], res, "JSON"];')
    L.append('Print[res];')
    d = paths.GENERATED_WOLFRAM; d.mkdir(parents=True, exist_ok=True)
    (d / "morphological_accent_orientation.wl").write_text("\n".join(L))


def single_affix_rows():
    out = {}
    for flags in ((), ("dele",), ("prea",), ("dele", "prea")):
        for root in ("r1", "r0"):
            spec = [R("t a t a".split(), ROOTS[root]), M(list(SUFFIX), side=2, rank=1, flags=flags)]
            ref = build(spec)
            acts = activation(SG, ref, DECLS)
            rows = []
            for c in candidates(ref):
                co = coefficients(SG, ref, c, DECLS, acts)
                rows.append({"surface": surface(c), "kept": analysis(ref, c)[0], "made": analysis(ref, c)[1],
                             "cost": " + ".join(f"({o} + lam*{n})*{k}" for k, (o, n) in co.items() if (o, n) != (0, 0)) or "0"})
            out["+".join(flags) or "none", root] = rows
    return {f"{k[0]}|{k[1]}": v for k, v in out.items()}


def cumulative_point():
    W = dict(ZERO, CULM=200, DEP=2, MAX_R=10, MAXLINK_R=20, LOCAL=5, ANTI_DEL=8, ANTI_PRE_A=6)
    res = {}
    for flags in (("dele",), ("prea",), ("dele", "prea")):
        for root in ("r1", "r0"):
            spec = [R("t a t a".split(), ROOTS[root]), M(list(SUFFIX), side=2, rank=1, flags=flags)]
            e = evaluate(build(spec), W)
            res[f"{'+'.join(flags)}|{root}"] = e["winners"]
    return {"weights": {k: v for k, v in W.items() if v}, "winners": res,
            "cumulative": res["dele|r1"] == ["táta-ka"] and res["prea|r1"] == ["táta-ka"]
                          and res["dele+prea|r1"] == ["tatá-ka"]}


def emit_typology_wolfram(rows):
    import re
    names = sorted(DECLS)
    ren = {n: "w" + "".join(p.capitalize() for p in n.lower().split("_")) for n in names}
    def wl(e):
        for n in sorted(ren, key=len, reverse=True):
            e = re.sub(r"\b" + n + r"\b", ren[n], e)
        return e
    L = ["vars = {" + ", ".join(sorted(set(ren.values()))) + ", lam};",
         "nonneg = And @@ (# >= 0 & /@ vars);", "att = 0 < lam < 1;"]
    def region(key, winner_pred):
        cs = rows[key]
        w = [c for c in cs if winner_pred(c)]
        assert len(w) == 1, (key, [c["surface"] for c in w])
        w = w[0]
        return "And[" + ", ".join(f"({wl(w['cost'])}) < ({wl(o['cost'])})" for o in cs if o is not w) + "]"
    keep = lambda c: c["surface"] == "táta-ka" and c["made"] is None and c["kept"] == (0,)
    ins = lambda c: c["surface"] == "tatá-ka" and c["made"] == 0 and c["kept"] == ()
    delonly = lambda c: c["surface"] == "tata-ka" and c["kept"] == () and c["made"] is None
    L.append("deleRec = " + region("dele|r1", keep) + ";")
    L.append("deleDom = " + region("dele|r1", delonly) + ";")
    L.append("preaRec = " + region("prea|r1", keep) + ";")
    L.append("preaDom = " + region("prea|r1", ins) + ";")
    L.append("bothDom = " + region("dele+prea|r1", ins) + ";")
    L.append("preaIns0 = " + region("prea|r0", lambda c: c["surface"] == "tatá-ka" and c["made"] == 0) + ";")
    L.append("cumulative = And[deleRec, preaRec, bothDom];")
    L.append('root = NestWhile[ParentDirectory, DirectoryName[$InputFileName], !(DirectoryQ[FileNameJoin[{#, "python"}]] && DirectoryQ[FileNameJoin[{#, "wolfram"}]]) &, 1, 8];\noutdir = FileNameJoin[{root, "results", "requirements", "wolfram"}];\nIf[!DirectoryQ[outdir], CreateDirectory[outdir, CreateIntermediateDirectories -> True]];')
    L.append('res = <|"cumulative_region_nonempty" -> ToString[Resolve[Exists[Evaluate[vars], nonneg && att && cumulative], Reals], InputForm]|>;')
    L.append("keep = {wMaxR, wDep, wAntiDel, wAntiPreA, wMaxlinkR, wCulm, lam};")
    L.append("zero = Thread[Complement[vars, keep] -> 0];")
    L.append("red[e_] := Reduce[(nonneg && att && e) /. zero, keep, Reals];")
    L.append('res = Join[res, <|"dele_recessive" -> ToString[red[deleRec], InputForm], "dele_dominant" -> ToString[red[deleDom], InputForm], "prea_recessive" -> ToString[red[preaRec], InputForm], "prea_dominant" -> ToString[red[preaDom], InputForm], "prea_insertion_unaccented_root" -> ToString[red[preaIns0], InputForm], "both_flags" -> ToString[red[bothDom], InputForm], "cumulative" -> ToString[red[cumulative], InputForm], "cumulative_witness" -> ToString[FindInstance[(nonneg && att && cumulative) /. zero, keep, Reals], InputForm]|>];')
    L.append('Export[FileNameJoin[{outdir, "morphological_accent_typology.json"}], res, "JSON"];')
    L.append('Print[res];')
    d = paths.GENERATED_WOLFRAM; d.mkdir(parents=True, exist_ok=True)
    (d / "morphological_accent_typology.wl").write_text("\n".join(L))


def main():
    import sys, time
    OUT.mkdir(parents=True, exist_ok=True)
    full = "--full" in sys.argv
    if full:
        rec = {"lambda": str(LAM),
               "what": "the productive family at suffix length 3, every sequence whose outermost suffix is dominant "
                       "(dom0 or dom1), at both grammars: the law's substance; sequences to length 2, the exchange "
                       "lemma and everything else are in the morphological-accent certificate"}
        outer_dom = lambda key: len(key) == 4 and key[-1] in ("dom0", "dom1")
        fam = rec["family"] = run_family(3, keep=outer_dom)
        for g, r in fam.items():
            print(f"2. {g}: {r['items']} length-3 sequences with a dominant outermost suffix; "
                  f"L1 failures {r['L1_failures']}; L3 failures {len(r['L3_failures'])} {r['L3_failures'][:8]}")
        certificate.write("morphological_accent_length3.json", rec)
        print("wrote X35b")
        return
    rec = {"lambda": str(LAM), "weights": {k: {n: v for n, v in W.items() if v} for k, (_, W) in LANGS.items()}}
    t0 = time.time()
    lg = rec["languages"] = run_languages()
    for lang, r in lg.items():
        bad = [k for k, v in r.items() if not v["agrees"]]
        print(f"1. {lang}: {len(r) - len(bad)}/{len(r)} printed forms"
              + (f"  DISAGREE {[(k, r[k]['winners'], r[k]['expected']) for k in bad]}" if bad else ""))
    rec["regions"] = {lang: necessary(lang) for lang in LANGS}
    for lang, r in rec["regions"].items():
        print(f"1. {lang}: region of the used declarations feasible={r['region_of_used']['feasible']}; "
              f"unresolved necessity: {[n for n, v in r['by_declaration'].items() if v == 'unresolved']}")
    L = 2
    fam = rec["family"] = run_family(L)
    for g, r in fam.items():
        print(f"2. {g}: {r['items']} items (suffix sequences to length {L}), {r['with_dominant']} with a dominant suffix; "
              f"L1 failures {r['L1_failures']}; L3 failures {len(r['L3_failures'])} {r['L3_failures'][:6]}")
    ex = rec["exchange"] = exchange_lemma(2)
    for g in ("jp", "ru"):
        print(f"2. {g}: exchange lemma on {ex[g]['exchanges']} candidates; premise holds for {ex[g]['with_premise']}; "
              f"failures under the premise {ex[g]['failures_under_premise']}, without it {ex[g]['failures_without_premise']}")
    print(f"2. premise boundary at W_JP: {ex['premise_boundary_jp']}")
    refs = rec["references"] = run_references(2)
    for lang, R in refs["regions"].items():
        print(f"3. {lang}: " + "; ".join(f"{k}: {'feasible' if v.get('feasible') else ('inconclusive' if v.get('conclusive') is False else 'infeasible')}"
                                        for k, v in R.items() if isinstance(v, dict)))
    print(f"3. ru reset, pair (rák-u, stol-ú) search: {refs['regions']['ru']['reset_pair_rak_u_stol_u']}")
    for g in ("jp", "ru"):
        print(f"3. {g}: reset differs on {refs[g]['reset_differs']}; two references differ on {refs[g]['two_differ']}")
    print(f"3. printed separations: {refs['printed_separations']}")
    reo = rec["reo"] = reo_regions()
    reo["ot_rankings"] = reo_ot_typology()
    reo["hg_witness"] = reo_check_point((3, 2, 2, 10))
    reo["hg_witness_2"] = reo_check_point((5, 1, 3, 1))
    emit_reo_wolfram(reo)
    print(f"4. OT rankings showing contrastive accent with prefix override: "
          f"{[k for k, v in reo['ot_rankings'].items() if v['contrastive_with_prefix_override']]}; "
          f"HG point (3,2,2,10): {reo['hg_witness']['contrastive_with_prefix_override']} {reo['hg_witness']['winners']}")
    rows = rec["single_affix"] = single_affix_rows()
    rec["cumulative"] = cumulative_point()
    emit_typology_wolfram(rows)
    print(f"5. cumulative point: {rec['cumulative']}")
    rec["seconds"] = round(time.time() - t0, 1)
    certificate.write("morphological_accent.json", rec)
    print(f"certificate written in {rec['seconds']} s")


if __name__ == "__main__":
    main()
