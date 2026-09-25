from __future__ import annotations
from phonological_requirements import certificate, paths

import itertools
import json
import time
from dataclasses import replace
from fractions import Fraction as F
from pathlib import Path

from .core import ABSENT, Decl, NodeId, Not, Or_, Present, SameSeg, Scope, Struct, TRUE, read
from .evaluate import _keys, activation, coefficients, loci, score, tier_of
from .footprint import footprint
from .frag_seq import T, WORD, make_sigma, rule_decl, surface
from .generate import canonical, closure, productive_ext
from . import regimes as R

OUT = paths.CERTIFICATES

ALPHABET = {"a": {"V"}, "i": {"V"}, "t": {"C"}, "n": {"C"}}
SET_ALPHA = ("a", "i", "t", ABSENT)
INS_ALPHA = ("t", "n")
OPS = ("set", "insert")
PHRASE = Scope(same=("phrase",), label="phrase")

IDENT = Decl("IDENT", "Or", (T,), TRUE,
             Or_((Not(Present("t")), SameSeg(("t", "current"), ("t", "reference")))),
             kind="faithfulness", locus_side="reference")
HIATUS = rule_decl("HIATUS", "V", ("V",), (), None, "discharge")
HIATUS_PHR = rule_decl("HIATUS", "V", ("V",), (), None, "discharge", scope=PHRASE)
DECLS = {"HIATUS": HIATUS, "MAX": R.MAXD, "IDENT": IDENT, "DEP": R.DEP}
DECLS_PHR = {**DECLS, "HIATUS": HIATUS_PHR}
W = {"HIATUS": 3, "MAX": 1, "IDENT": 1, "DEP": 1}
LAMS = (F(0), F(1, 8), F(1, 2), F(1))

PAIRS = {"P1": ("ai", "ia"), "P2": ("aia", "i"), "P3": ("ai", "ai"), "P4": ("ai", "ti")}
CONTROL = ("a", "i")


def build2(words):
    nodes, real, dom = [], {}, {}
    i = 0
    for w, syms in enumerate(words):
        for s in syms:
            n = NodeId("Or", "lex", i); i += 1
            nodes.append(n); real[n] = s; dom[n] = {"word": w, "phrase": 0}
    return Struct(order={"seg": tuple(nodes)}, real=real, dom=dom)


def word_of(s, n):
    return s.dom[n]["word"]


def project(s, w):
    ns = tuple(n for n in s.nodes("seg") if word_of(s, n) == w)
    return Struct(order={"seg": ns}, real={n: s.real[n] for n in ns}, dom={n: s.dom[n] for n in ns})


def mask(s, w):
    real = {n: (s.real[n] if word_of(s, n) == w else ABSENT) for n in s.nodes("seg")}
    return Struct(order=s.order, real=real, dom=s.dom)


def key(s):
    return canonical(s, "seg")


def made_of_key(k):
    return sum(1 for e in k if e[0] == "made")


def coeffs_word(sigma, ref, state, decls, acts, w):
    out = {}
    for name, d in decls.items():
        old = new = 0
        dt = tier_of(sigma, d, "seg")
        for n in loci(state, d, dt, ref):
            src = ref if (d.locus_side == "reference") else state
            if word_of(src, n) != w:
                continue
            r = read(sigma, ref, state, d, n, dt)
            p, c = r.pressure, r.context
            a = any(acts[name].get(k, False) for k in _keys(state, n, "unique"))
            if d.kind == "faithfulness":
                old += int(p and c)
            else:
                old += int(p and a)
                new += int(p and (not a) and c)
        out[name] = (old, new)
    return out


def certify_pair(sigma, words, decls, lam, label):
    rec = {"words": list(words), "lambda": str(lam)}
    ref = build2(words)
    refs = [project(ref, w) for w in range(2)]
    acts = activation(sigma, ref, decls)
    acts_w = [activation(sigma, refs[w], decls) for w in range(2)]
    best, mins, cert = productive_ext(sigma, ref, decls, W, lam, OPS, SET_ALPHA, INS_ALPHA, incumbent="creation_free")
    M = cert["max_created_nodes"]
    parts = [productive_ext(sigma, refs[w], decls, W, lam, OPS, SET_ALPHA, INS_ALPHA, incumbent="creation_free") for w in range(2)]
    rec["reduction"] = {"product": cert, "word0": parts[0][2], "word1": parts[1][2]}
    Cl = closure(ref, OPS, SET_ALPHA, INS_ALPHA, M)
    ClW = [closure(refs[w], OPS, SET_ALPHA, INS_ALPHA, M) for w in range(2)]
    rec["sizes"] = {"product_closure": len(Cl), "word_closures": [len(c) for c in ClW], "bound": M}
    contiguous = all([word_of(s, n) for n in s.nodes("seg")] == sorted(word_of(s, n) for n in s.nodes("seg")) for s in Cl)
    one_word = all(word_of(s, n) in (0, 1) for s in Cl for n in s.nodes("seg"))
    pairs = [(key(project(s, 0)), key(project(s, 1))) for s in Cl]
    injective = len(set(pairs)) == len(Cl)
    kw = [set(map(key, c)) for c in ClW]
    expected = {(a, b) for a in kw[0] for b in kw[1] if made_of_key(a) + made_of_key(b) <= M}
    product_identity = (set(pairs) == expected)
    slices = {}
    for a, b in pairs:
        slices[f"{made_of_key(a)},{made_of_key(b)}"] = slices.get(f"{made_of_key(a)},{made_of_key(b)}", 0) + 1
    rec["a_region_local"] = {"contiguous": contiguous, "every_node_in_one_word": one_word, "projection_injective": injective,
                             "global_bound_closure_equals_count_filtered_product": product_identity,
                             "slices_by_created_nodes": slices}
    straddle = []
    for s in Cl:
        for name, d in decls.items():
            dt = tier_of(sigma, d, "seg")
            for n in loci(s, d, dt, ref):
                src = ref if d.locus_side == "reference" else s
                w = word_of(src, n)
                fp = footprint(sigma, s, d, n, dt)
                if any(word_of(s, m) != w for m in fp):
                    straddle.append({"structure": surface_pair(s), "declaration": name, "locus": repr(n)})
    rec["b_footprint_contained"] = {"violations": len(straddle), "witnesses": straddle[:5]}
    fails = {"mask": 0, "projection": 0, "activation": 0, "additivity": 0}
    wit = {}
    for s in Cl:
        total = score(coefficients(sigma, ref, s, decls, acts), W, lam)
        parts_score = F(0)
        for w in range(2):
            cw = coeffs_word(sigma, ref, s, decls, acts, w)
            cm = coeffs_word(sigma, ref, mask(s, w), decls, acts, w)
            pj = project(s, w)
            cp = coefficients(sigma, refs[w], pj, decls, acts_w[w])
            if cw != cm:
                fails["mask"] += 1; wit.setdefault("mask", surface_pair(s))
            if cm != cp:
                fails["projection"] += 1; wit.setdefault("projection", surface_pair(s))
            parts_score += score(cp, W, lam)
        if total != parts_score:
            fails["additivity"] += 1; wit.setdefault("additivity", {"structure": surface_pair(s), "score": str(total), "sum_of_parts": str(parts_score)})
    for w in range(2):
        for name in decls:
            for n, v in acts_w[w][name].items():
                if acts[name].get(n) != v:
                    fails["activation"] += 1
    rec["c_bridge"] = {"failures": fails, "witnesses": wit}
    min_pairs = {(key(project(s, 0)), key(project(s, 1))) for s in mins}
    min_w = [set(map(key, parts[w][1])) for w in range(2)]
    factorises = (min_pairs == {(a, b) for a in min_w[0] for b in min_w[1]}) and len(mins) == len(min_w[0]) * len(min_w[1])
    surf = sorted({surface_pair(s) for s in mins})
    surf_w = [sorted({surface(x) for x in parts[w][1]}) for w in range(2)]
    surf_fact = (set(surf) == {a + "|" + b for a in surf_w[0] for b in surf_w[1]})
    rec["d_minimisers"] = {"product_min_score": str(best), "word_min_scores": [str(parts[w][0]) for w in range(2)],
                           "n_minimisers": [len(mins), len(min_w[0]), len(min_w[1])],
                           "argmin_factorises_with_ties": factorises, "surfaces_factorise": surf_fact,
                           "surfaces": surf, "word_surfaces": surf_w}
    rec["min_keys_word0"] = sorted(map(str, min_w[0]))
    rec["min_keys_word0_from_product"] = sorted({str(a) for a, _ in min_pairs})
    kw_max = [max(made_of_key(k) for k in kw[w]) for w in range(2)]
    rank = None
    if M >= 1 and kw_max[0] >= 1:
        a = next(k for k in kw[0] if made_of_key(k) == kw_max[0]); a2 = next(k for k in kw[0] if made_of_key(k) == 0)
        b = next(k for k in kw[1] if made_of_key(k) == 0); b2 = next((k for k in kw[1] if made_of_key(k) == 1), None)
        if b2 is not None and made_of_key(a) + made_of_key(b2) > M:
            rank = {"in_family": [(a, b) in set(pairs), (a2, b2) in set(pairs), (a2, b) in set(pairs)],
                    "out_of_family": (a, b2) not in set(pairs),
                    "statement": "Pr(a,b)Pr(a',b') > 0 = Pr(a,b')Pr(a',b) on the globally-bounded family: not a product law; on the componentwise-bounded family (a product set, by (a)) the law is the product of the word laws, an algebraic identity given (c)"}
    rec["g_probabilistic_boundary"] = {"global_family_is_product_set": (set(pairs) == {(a, b) for a in kw[0] for b in kw[1]}),
                                       "rank_witness": rank}
    rec["all_pass"] = all([contiguous, one_word, injective, product_identity, not straddle,
                           not any(fails.values()), factorises, surf_fact])
    return rec, min_w[0]


def surface_pair(s):
    return "|".join("".join(s.real[n] for n in s.nodes("seg") if word_of(s, n) == w and s.real[n] != ABSENT) for w in range(2))


def main():
    t0 = time.time()
    sigma = replace(make_sigma(ALPHABET), domains=("word", "phrase"))
    rec = {"weights": W, "operations": list(OPS), "set_alphabet": list(SET_ALPHA),
           "insert_alphabet": list(INS_ALPHA), "declarations": list(DECLS)}
    main_rec = {}
    for name, words in PAIRS.items():
        for lam in LAMS:
            r, m0 = certify_pair(sigma, words, DECLS, lam, name)
            main_rec[f"{name}@{lam}"] = r
            print(name, lam, r["sizes"], r["d_minimisers"]["n_minimisers"], "pass" if r["all_pass"] else "FAIL", f"{time.time() - t0:.0f}s", flush=True)
    rec["word_scope"] = main_rec
    f_ok = True
    for lam in LAMS:
        sets = [tuple(main_rec[f"{n}@{lam}"]["min_keys_word0_from_product"]) for n in ("P1", "P3", "P4")]
        alone = tuple(main_rec[f"P1@{lam}"]["min_keys_word0"])
        f_ok = f_ok and all(s == alone for s in sets)
    rec["f_outside_material"] = {"word0_minimisers_identical_across_P1_P3_P4_and_alone": f_ok}
    ctrl = {}
    for lam in (F(1, 8),):
        r, _ = certify_pair(sigma, CONTROL, DECLS_PHR, lam, "control")
        ctrl[f"control@{lam}"] = r
        r2, _ = certify_pair(sigma, CONTROL, DECLS, lam, "control_word")
        ctrl[f"control_word_scope@{lam}"] = r2
        print("control", r["b_footprint_contained"]["violations"], r["c_bridge"]["failures"], r["d_minimisers"]["n_minimisers"],
              "factorises" if r["d_minimisers"]["argmin_factorises_with_ties"] else "does not factorise", flush=True)
    rec["e_control"] = ctrl
    rc = ctrl[f"control@{F(1, 8)}"]
    rec["e_control_summary"] = {"phrase_scope_footprint_violations": rc["b_footprint_contained"]["violations"],
                                "phrase_scope_additivity_failures": rc["c_bridge"]["failures"]["additivity"],
                                "phrase_scope_argmin_factorises": rc["d_minimisers"]["argmin_factorises_with_ties"],
                                "phrase_scope_n_minimisers": rc["d_minimisers"]["n_minimisers"],
                                "word_scope_same_words_all_pass": ctrl[f"control_word_scope@{F(1, 8)}"]["all_pass"]}
    rec["lean"] = {"theorems": ["ProductComposition.reachable_product", "ProductComposition.argmin_product", "ProductComposition.noninterference", "FootprintSupport.external_region_irrelevant"],
                   "bridge": "The universal theorem uses arbitrary local relations and real additive scores. This executable separately checks the native generator, masking, projection, activation and additivity at the registered references and parameters. A global creation bound gives a count-filtered product, not a product domain; the independent positive-cost cutoff preserves all productive minimizers."}
    rec["all_pass"] = all(r["all_pass"] for r in main_rec.values()) and f_ok and ctrl[f"control_word_scope@{F(1, 8)}"]["all_pass"] \
        and (not rc["d_minimisers"]["argmin_factorises_with_ties"]) and rc["b_footprint_contained"]["violations"] > 0 \
        and rc["c_bridge"]["failures"]["additivity"] > 0
    rec["status"] = "FINITE_EXHAUSTIVE_CERTIFIED" if rec["all_pass"] else "FAILED"
    rec["elapsed_s"] = round(time.time() - t0, 1)
    certificate.write("noninterference.json", rec)
    print("status", rec["status"], rec["elapsed_s"], "s")

    return 0 if rec["all_pass"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
