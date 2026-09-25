from __future__ import annotations
from phonological_requirements import certificate, paths

import itertools
import json
from fractions import Fraction as F
from pathlib import Path

from .core import read
from .evaluate import activation, coefficients, loci, score
from .frag_harmony import (ATR_PAIR, HEIGHT_PAIR, NEXT, NEXT_SPEC, NEXT_SPEC_OR_HIGH,
                           PREV, PREV_ROOT, PREV_SPEC, agree_pair, spread_with_two_sided_block, block_after_high_initial,
                           ident, sigma, spread, struct, two_sided_height)
from .core import Decl, Feat, Not, TRUE, Slot

OUT = paths.CERTIFICATES
LAM = F(1, 8)
T = Slot("t", "Or", "subject", kind="anchor")


def no_atr() -> Decl:
    return Decl("NO_ATR", "Or", (T,), TRUE, Not(Feat("atr", "t", True)))


def evaluate(vowels, sides, D, W, pairs, lam=LAM):
    sg = sigma()
    ref = struct(list(vowels), list(sides))
    nodes = ref.order["seg"]
    alt = [(i, pairs[v]) for i, v in enumerate(vowels) if v in pairs]
    acts = activation(sg, ref, D)
    rows = []
    for combo in itertools.product([0, 1], repeat=len(alt)):
        s = ref
        for (i, pr), k in zip(alt, combo):
            s = s.with_real(nodes[i], pr[k])
        cf = coefficients(sg, ref, s, D, acts)
        rows.append((" ".join(str(s.real[n]) for n in nodes), cf, score(cf, W, lam)))
    lo = min(r[2] for r in rows)
    return {"winners": sorted({r[0] for r in rows if r[2] == lo}), "score": str(lo),
            "n_candidates": len(rows), "rows": rows}


D_SUFFIX = {d.name: d for d in (spread("LR", PREV_SPEC), spread("RL", NEXT_SPEC_OR_HIGH, nonhigh_only=True),
                                 no_atr(), ident("ID_ATR", "atr"))}
W_SUFFIX = dict(LR=10, RL=20, NO_ATR=1, ID_ATR=100)


def liko():
    from .observations import LIKO
    out = {}
    for k, (inp, exp) in LIKO.items():
        toks = inp.split()
        e = evaluate(toks, [1] * len(toks), D_SUFFIX, W_SUFFIX, ATR_PAIR)
        out[k] = {"input": inp, "winners": e["winners"], "expected": exp,
                  "agrees": e["winners"] == [exp], "n_candidates": e["n_candidates"]}
    return out


D_HEIGHT = {d.name: d for d in (two_sided_height(), ident("ID_MID_ROOT", "mid", side=0), ident("ID_MID", "mid"))}
W_HEIGHT = dict(HEIGHT_2SIDED=20, ID_MID_ROOT=100, ID_MID=1)


def yaka():
    from .observations import YAKA
    out = {}
    for k, ((root, suf), exp) in YAKA.items():
        r, s = root.split(), suf.split()
        e = evaluate(r + s, [0] * len(r) + [1] * len(s), D_HEIGHT, W_HEIGHT, HEIGHT_PAIR)
        got = [w.split()[len(r):] for w in e["winners"]]
        got = sorted({" ".join(g) for g in got})
        out[k] = {"root": root, "suffixes": suf, "winners": got, "expected": exp,
                  "agrees": got == [exp], "n_candidates": e["n_candidates"]}
    return out


D_PREFIX = {d.name: d for d in (spread("T1", NEXT, value=True), block_after_high_initial(),
                                 ident("ID_ATR_ROOT", "atr", side=0), ident("ID_ATR", "atr"))}
W_PREFIX = dict(T1=80, BLOCK_INIT=1000, ID_ATR_ROOT=1000, ID_ATR=1)


def tutrugbu():
    from .observations import TUTRUGBU_TAFI
    out = {}
    for k, ((pre, root), exp) in TUTRUGBU_TAFI.items():
        p = pre.split()
        e = evaluate(p + [root], [-1] * len(p) + [0], D_PREFIX, W_PREFIX, ATR_PAIR)
        got = sorted({" ".join(w.split()[:len(p)]) for w in e["winners"]})
        out[k] = {"prefixes": pre, "root": root, "winners": got, "expected": exp,
                  "agrees": got == [exp], "n_candidates": e["n_candidates"]}
    return out


D_PREFIX_TARGET = {d.name: d for d in (spread_with_two_sided_block(), ident("ID_ATR_ROOT", "atr", side=0),
                                        ident("ID_ATR", "atr"))}
W_PREFIX_TARGET = dict(T1_TARGET=80, ID_ATR_ROOT=1000, ID_ATR=1)


def tutrugbu_target():
    from .observations import TUTRUGBU_TAFI
    out = {}
    for k, ((pre, root), exp) in TUTRUGBU_TAFI.items():
        p = pre.split()
        e = evaluate(p + [root], [-1] * len(p) + [0], D_PREFIX_TARGET, W_PREFIX_TARGET, ATR_PAIR)
        got = sorted({" ".join(w.split()[:len(p)]) for w in e["winners"]})
        out[k] = {"winners": got, "expected": exp, "agrees": got == [exp]}
    rows = {}
    for n in range(1, 13):
        e = evaluate(["a"] * n + ["u"], [-1] * n + [0], D_PREFIX_TARGET, W_PREFIX_TARGET, ATR_PAIR)
        rows[n] = e["winners"]
    full = [n for n, w in rows.items() if w == [" ".join(["e"] * n + ["u"])]]
    return {"forms": out, "all_agree": all(v["agrees"] for v in out.values()),
            "spreading_by_n": rows, "full_spreading_at_n": full}


def prefix_threshold(nmax=12):
    rows = {}
    for n in range(1, nmax + 1):
        e = evaluate(["a"] * n + ["u"], [-1] * n + [0], D_PREFIX, W_PREFIX, ATR_PAIR)
        rows[n] = e["winners"]
    pred = 1 + LAM * W_PREFIX["T1"] / W_PREFIX["ID_ATR"]
    return {"winners_by_n": rows, "predicted_bound_n_lt": str(pred),
            "full_spreading_up_to": max((n for n, w in rows.items() if w == [" ".join(["e"] * n + ["u"])]), default=0)}


def shapes(nmax=12):
    W = dict(LR=10, AGREE_PAIR=10, NO_ATR=1, ID_ATR=1, ID_FIXED=1000)
    decls = {"chain, affix subjects": spread("LR", PREV, value=True, side=1),
             "chain, all subjects": spread("LR", PREV, value=True),
             "target = nearest specified, affix subjects": spread("LR", PREV_SPEC, value=True, side=1),
             "target = nearest root, affix subjects": spread("LR", PREV_ROOT, value=True, side=1),
             "pairwise agreement": agree_pair()}
    out, worst = {}, F(0)
    for shape, d in decls.items():
        for spec, V in (("specified", "a"), ("unspecified", "a?")):
            D = {d.name: d, "NO_ATR": no_atr(), "ID_ATR": ident("ID_ATR", "atr"),
                 "ID_FIXED": ident("ID_FIXED", "atr", side=(0, 2))}
            for blocker in (False, True):
                row = {}
                for n in range(1, nmax + 1):
                    vs = ["i"] + [V] * n + (["U"] if blocker else [])
                    pairs = {V: ATR_PAIR[V]}
                    e = evaluate(vs, [0] + [1] * n + ([2] if blocker else []), D, W, pairs)
                    worst = max(worst, max(r[2] for r in e["rows"]))
                    row[n] = e["winners"]
                out[f"{shape} | {spec} | {'T V^n Z' if blocker else 'T V^n'}"] = row
    assert worst < W["ID_FIXED"], worst
    return {"weights": W, "lambda": str(LAM), "rows": out, "largest_score_without_touching_fixed": str(worst)}


def full_spread(winners, n, blocker, V):
    plus = ATR_PAIR[V][0]
    return winners == [" ".join(["i"] + [plus] * n + (["U"] if blocker else []))]


def theorem_summary(sh):
    summ = {}
    for key, row in sh["rows"].items():
        blocker = key.endswith("Z")
        V = "a" if "| specified" in key else "a?"
        full = [n for n, w in row.items() if full_spread(w, n, blocker, V)]
        ff = min((n for n in row if n not in full), default=None)
        summ[key] = {"full_spreading_at_n": full, "first_failure": ff,
                     "winners_at_first_failure": row[ff] if ff else None}
    return summ


def predicted_thresholds(W=dict(LR=10, AGREE_PAIR=10, NO_ATR=1, ID_ATR=1), lam=LAM):
    return {"chain, specified": f"n < 1 + lam*w_LR/w_ID = {1 + lam * W['LR'] / W['ID_ATR']}",
            "chain, unspecified": f"n < w_LR/w_def = {F(W['LR'], W['NO_ATR'])}",
            "pairwise, specified": f"n < 1 + lam*w_AG/w_ID = {1 + lam * W['AGREE_PAIR'] / W['ID_ATR']}",
            "pairwise, unspecified": f"n < w_AG/w_def = {F(W['AGREE_PAIR'], W['NO_ATR'])}",
            "target, specified (nearest root)": "all n, iff w_ID < w_LR",
            "target, unspecified": "all n, iff w_def < w_LR"}


def main():
    rec = {"liko": (lk := liko()), "yaka": (yk := yaka()), "tutrugbu_tafi": (tt := tutrugbu()),
           "prefix_threshold": prefix_threshold(),
           "tutrugbu_tafi_target_counting": (tt2 := tutrugbu_target()),
           "shapes": (sh := shapes()),
           "weights": {"suffix": W_SUFFIX, "height": W_HEIGHT, "prefix": W_PREFIX},
           "lambda": str(LAM)}
    rec["shapes_summary"] = theorem_summary(sh)
    rec["predicted_thresholds"] = predicted_thresholds()
    OUT.mkdir(parents=True, exist_ok=True)
    certificate.write("nonmyopic_harmony.json", rec)
    ok = True
    for name, tab in (("Liko", lk), ("Yaka", yk), ("Tutrugbu/Tafi", tt)):
        bad = [k for k, v in tab.items() if not v["agrees"]]
        ok &= not bad
        print(f"1. {name}: {len(tab) - len(bad)}/{len(tab)} agree" + (f"; DISAGREE {bad}" if bad else ""))
        for k in bad:
            print("     ", k, tab[k])
    print("   prefix chain threshold:", rec["prefix_threshold"]["full_spreading_up_to"],
          "predicted n <", rec["prefix_threshold"]["predicted_bound_n_lt"])
    print("   one target-counting declaration:", f"{sum(v['agrees'] for v in tt2['forms'].values())}/{len(tt2['forms'])} agree;",
          "full spreading at n =", tt2["full_spreading_at_n"])
    ok &= tt2["all_agree"]
    print("2. shapes (largest score without touching a fixed vowel:", sh["largest_score_without_touching_fixed"], ")")
    for k, v in rec["shapes_summary"].items():
        print(f"   {k:60s} full at n={v['full_spreading_at_n']}; first failure n={v['first_failure']} -> {v['winners_at_first_failure']}")
    print("   predicted:", rec["predicted_thresholds"])
    if not ok:
        raise SystemExit("F02-2: a reproduction failed")


if __name__ == "__main__":
    main()
