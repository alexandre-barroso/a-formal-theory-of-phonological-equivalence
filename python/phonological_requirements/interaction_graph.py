from __future__ import annotations
from phonological_requirements import certificate, paths

import itertools
import json
import time
from fractions import Fraction as F
from pathlib import Path

from .core import ABSENT
from .evaluate import activation, coefficients, score
from .frag_seq import build as seq_build, candidates as seq_candidates, faith_decls, make_sigma, rule_decl, surface
from .interaction import CLASSES, classify, locus_graph, read_set, sccs as locus_sccs
from .core import read as read_readers
from .footprint import footprint
from . import frag_gua as FG, frag_lith as FL
from .products import gua_products

OUT = paths.CERTIFICATES
CAP = 400
MODES = ("discharge", "retain", "ltr", "rtl")


def subsample(states, cap=CAP):
    states = list(states)
    if len(states) <= cap:
        return states, False
    k = -(-len(states) // cap)
    return states[::k], True


def census_items():
    items = []
    sg = FG.make_sigma(); Dg = FG.declarations("typed")
    for focal, prod in gua_products():
        ref = FG.struct_from_segments(prod.reference, prod.words, prod.phrase_of_word)
        cands = []
        for combo in itertools.product(FG.ALPHABET, repeat=len(focal)):
            st = list(prod.reference)
            for q, v in zip(focal, combo):
                st[q] = v
            cands.append(FG.struct_from_segments(tuple(st), prod.words, prod.phrase_of_word))
        items.append((f"gua:{prod.id}", sg, ref, cands, Dg))
    sgl = FL.make_sigma(); Dl = FL.declarations()
    for pid in FL.PRODUCTS:
        ref, marks, _ = FL.build(pid)
        items.append((f"lith:{pid}", sgl, ref, [c[1] for c in FL.candidates(ref, marks)], Dl))
    from . import interaction_typology
    for name, pat in interaction_typology.PATTERNS.items():
        for mode in ("retain", "discharge"):
            sgq, D = interaction_typology.build_pattern(pat, (mode,) * len(pat["rules"]))
            for inp in pat["mappings"]:
                ref = seq_build(interaction_typology.split(inp, pat["alphabet"]))
                items.append((f"seq:{name}:{inp}:{mode}", sgq, ref, list(seq_candidates(ref, pat["options"])), D))
    from . import frag_redup, reduplication_template
    sgr = frag_redup.make_sigma(); Dr = frag_redup.declarations()
    for it in reduplication_template.ITEMS[:12] + reduplication_template.ITEMS[13:16]:
        ref = frag_redup.build(it[1])
        items.append((f"redup:{it[0]}", sgr, ref, list(frag_redup.candidates(ref, it[1], **it[4])), Dr))
    from . import frag_schwa, schwa_attenuation
    sgs = frag_schwa.make_sigma(); Ds = frag_schwa.declarations()
    for k, (label, syms, site, kind) in schwa_attenuation.CONTEXTS.items():
        ref = frag_schwa.build(syms, site, kind)
        items.append((f"schwa:{k}", sgs, ref, list(frag_schwa.candidates(ref, site, kind)), Ds))
    from . import frag_nuer, frag_sandhi, frag_stratal, observations as O
    sgn = frag_nuer.sigma(); Dn = frag_nuer.declarations()
    for key, (spec, _e, _l) in O.NUER.items():
        ref = frag_nuer.build(spec)
        items.append((f"nuer:{key}", sgn, ref, list(frag_nuer.candidates(ref)), Dn))
    sgt = frag_sandhi.sigma(); Dt = frag_sandhi.declarations()
    from .tone_sandhi import toks
    urs = sorted({ur for exp in O.SANDHI.values() for ur in exp["table"]})
    for ur in urs:
        ref = frag_sandhi.build(toks(ur))
        items.append((f"sandhi:{ur}", sgt, ref, list(frag_sandhi.candidates(ref)), Dt))
    sgx = frag_stratal.sigma(); Dx = frag_stratal.declarations()
    for key, (spec, _e, _l) in list(O.NEZ.items()) + list(O.NEZ_RESIDUE.items()):
        ref = frag_stratal.build(spec)
        items.append((f"stratal:{key}", sgx, ref, list(frag_stratal.candidates(ref)), Dx))
    return items


def perturb_check(sigma, ref, states, decls, rng_seed=0, per_state=3):
    import random
    rnd = random.Random(rng_seed)
    checks = viol = notcontained = 0
    syms = sorted({v for st in states for v in st.real.values() if v != ABSENT})
    for st in states:
        for name, d in decls.items():
            from .evaluate import tier_of, loci
            dt = tier_of(sigma, d, "seg")
            for l in loci(st, d, dt, ref):
                R, exact = read_set(sigma, ref, st, d, l, dt)
                if not (R <= footprint(sigma, st, d, l, dt)):
                    notcontained += 1
                if not exact:
                    continue
                outside = [n for n in st.nodes(dt) if n not in R]
                if not outside:
                    continue
                base = read_readers(sigma, ref, st, d, l, dt).triple()
                for _ in range(per_state):
                    n = rnd.choice(outside)
                    v = rnd.choice([x for x in syms + [ABSENT] if x != st.real.get(n)] or [ABSENT])
                    st2 = st.with_real(n, v)
                    checks += 1
                    if read_readers(sigma, ref, st2, d, l, dt).triple() != base:
                        viol += 1
    return {"perturbations": checks, "reader_changes": viol, "read_sets_outside_T06_region": notcontained}


def census():
    out, totals = {}, {c: 0 for c in CLASSES}
    t0 = time.time()
    by_fragment = {}
    sound = {"perturbations": 0, "reader_changes": 0, "read_sets_outside_T06_region": 0}
    for key, sigma, ref, states, decls in census_items():
        used, sub = subsample(states)
        keys, E, SH, inexact = locus_graph(sigma, ref, [ref] + used, decls)
        pairs, comps, refs, des = classify(decls, keys, E, SH)
        cnt = {c: sum(p["counts"][c] for p in pairs.values()) for c in CLASSES}
        for c in CLASSES:
            totals[c] += cnt[c]
        pc = perturb_check(sigma, ref, ([ref] + used)[:60], decls)
        for k in sound:
            sound[k] += pc[k]
        frag = key.split(":")[0]
        fb = by_fragment.setdefault(frag, {"items": 0, "counts": {c: 0 for c in CLASSES}, "strongest": {}, "declarations": sorted(decls), "inexact": set(), "max_scc": 0})
        fb["items"] += 1
        for c in CLASSES:
            fb["counts"][c] += cnt[c]
        for pr, v in pairs.items():
            if RANK_[v["strongest"]] > RANK_[fb["strongest"].get(pr, "independent")]:
                fb["strongest"][pr] = v["strongest"]
        fb["inexact"] |= inexact
        fb["max_scc"] = max(fb["max_scc"], max((len(c) for c in comps), default=0))
        out[key] = {"states_total": len(states), "states_used": len(used) + 1, "subsampled": sub,
                    "n_declarations": len(decls), "n_loci": len(keys), "locus_edges": len(E), "locus_sccs": [len(c) for c in comps],
                    "class_counts": cnt, "pairs": pairs, "destructive": {a: d for a, d in des.items() if d},
                    "reads_reference": sorted(a for a, v in refs.items() if v), "inexact_read_sets": sorted(inexact), "soundness": pc}
        print(f"  {key}: {len(decls)} decls, {len(keys)} loci, {len(used) + 1}/{len(states) + 1} states, edges {len(E)}, sccs {[len(c) for c in comps]}, {cnt}, sound {pc}  {time.time() - t0:.0f}s", flush=True)
    summary = {}
    for frag, fb in by_fragment.items():
        summary[frag] = {"items": fb["items"], "declarations": fb["declarations"], "locus_pair_class_counts": fb["counts"],
                         "strongest_class_per_declaration_pair": fb["strongest"], "inexact_read_sets": sorted(fb["inexact"]), "largest_locus_scc": fb["max_scc"]}
    return out, totals, summary, sound


RANK_ = {c: i for i, c in enumerate(CLASSES)}


ALPHA = {"x": {"X", "any"}, "y": {"Y", "any"}, "z": {"Z", "any"}}
INSTANCES = {
    "cycle2": ("xy", [("A", "X", (), ("Y",)), ("B", "Y", ("X",), ())], [("B", "A", "right"), ("A", "B", "left")]),
    "cycle3_chorded": ("xyz", [("A", "X", (), ("Y",)), ("B", "Y", (), ("Z",)), ("C", "Z", ("Y", "X"), ())],
                       [("B", "A", "right"), ("C", "B", "right"), ("A", "C", "left"), ("B", "C", "left")]),
    "chain": ("xyz", [("A", "X", (), ("Y",)), ("B", "Y", (), ("Z",))], [("B", "A", "right")]),
}
CARRIES = {"discharge": {"left", "right"}, "retain": set(), "ltr": {"left"}, "rtl": {"right"}}


def compiled_cost(S, rules, attacks, modes, r, w):
    tot = F(0)
    for i, (name, *_r) in enumerate(rules):
        if name in S:
            tot += r[name]
        else:
            discharged = any(att in S and side in CARRIES[modes[vic]] for att, vic, side in attacks if vic == name)
            if not discharged:
                tot += w[name]
    return tot


def instance(name, grid=(1, 2, 3)):
    inp, rules, attacks = INSTANCES[name]
    sigma = make_sigma(ALPHA)
    ref = seq_build(list(inp))
    sym_of = {rn: t for rn, t, *_ in rules}
    targets = {t: None for _, t, *_ in rules}
    options = {s: [s, ABSENT] for s in inp if any(s in {"X": "x", "Y": "y", "Z": "z"}[t] for t in targets)}
    cands = list(seq_candidates(ref, options))
    node_of = {rn: next(n for n in ref.order["seg"] if ref.real[n] == {"X": "x", "Y": "y", "Z": "z"}[t]) for rn, t, *_ in rules}
    def S_of(c):
        return frozenset(rn for rn, n in node_of.items() if c.real[n] == ABSENT)
    rec = {"input": inp, "rules": [r_[0] + ": " + r_[1] + " -> 0 / " + "".join(r_[2][::-1]) + " _ " + "".join(r_[3]) for r_ in rules],
           "attacks": attacks, "candidates": len(cands), "checks": 0, "mismatches": [], "new_cells": 0}
    mode_sets = list(itertools.product(MODES, repeat=len(rules)))
    names = [r_[0] for r_ in rules]
    faith = faith_decls({s: ALPHA[s] for s in inp}, [(t, None) for t in targets])
    thm = {"pointwise_when_uncarried": True, "all_apply_never_when_all_carried": True, "cases_uncarried": 0, "cases_all_carried": 0,
           "cycle2_symmetric_tie": None}
    for ms in mode_sets:
        modes = dict(zip(names, ms))
        D = {rn: rule_decl(rn, t, left, right, None, modes[rn]) for rn, t, left, right in rules}
        D.update(faith)
        acts = activation(sigma, ref, D)
        rows = [(S_of(c), coefficients(sigma, ref, c, D, acts)) for c in cands]
        rec["new_cells"] += sum(v[1] for _, co in rows for v in co.values())
        for wv in itertools.product(grid, repeat=len(rules)):
            for rv in itertools.product(grid, repeat=len(rules)):
                w = dict(zip(names, wv)); r = dict(zip(names, rv))
                W = {**w, **{f"MAX_{t}": r[rn] for rn, t, *_ in rules}}
                sc = {S: score(co, W, F(1, 8)) for S, co in rows}
                best = min(sc.values()); mins = {S for S, v in sc.items() if v == best}
                cc = {S: compiled_cost(S, rules, attacks, modes, r, w) for S in sc}
                cbest = min(cc.values()); cmins = {S for S, v in cc.items() if v == cbest}
                rec["checks"] += 1
                if sc != cc or mins != cmins:
                    if len(rec["mismatches"]) < 5:
                        rec["mismatches"].append({"modes": modes, "w": w, "r": r, "evaluator": {"".join(sorted(S)): str(v) for S, v in sc.items()},
                                                  "compiled": {"".join(sorted(S)): str(v) for S, v in cc.items()}})
                    continue
                attacked = {vic: side for att, vic, side in attacks}
                carried = {rn: (attacked.get(rn) in CARRIES[modes[rn]]) if rn in attacked else None for rn in names}
                if all(not c for c in carried.values()):
                    thm["cases_uncarried"] += 1
                    pw = {frozenset(rn for rn in names if (r[rn] < w[rn]) or (r[rn] == w[rn] and choose)) for choose in (False, True)}
                    ok = all(all((r[rn] <= w[rn]) if rn in S else (w[rn] <= r[rn]) for rn in names) for S in mins) \
                        and all(S in mins for S in pw)
                    thm["pointwise_when_uncarried"] &= ok
                if name != "chain" and all(carried[rn] for rn in names if rn in attacked):
                    thm["cases_all_carried"] += 1
                    thm["all_apply_never_when_all_carried"] &= (frozenset(names) not in mins)
                if name == "cycle2" and ms == ("rtl", "ltr") and w == {"A": 3, "B": 3} and r == {"A": 1, "B": 1}:
                    thm["cycle2_symmetric_tie"] = sorted("".join(sorted(S)) for S in mins)
    rec["theorems"] = thm
    rec["compiled_model_matches_evaluator"] = not rec["mismatches"]
    return rec


def pure_cycles(kmax=9):
    out = {}
    for k in range(2, kmax + 1):
        names = list(range(k))
        pred = {j: (j - 1) % k for j in names}
        res = {}
        for label, r, w in (("symmetric r<w", {j: 1 for j in names}, {j: 3 for j in names}),
                            ("asymmetric", {j: 1 + (j * 7) % 3 for j in names}, {j: 2 + (j * 5) % 4 for j in names})):
            best, mins = None, []
            for bits in itertools.product((0, 1), repeat=k):
                S = {j for j in names if bits[j]}
                c = sum(r[j] if j in S else (0 if pred[j] in S else w[j]) for j in names)
                if best is None or c < best:
                    best, mins = c, [S]
                elif c == best:
                    mins.append(S)
            comp_indep = all(all(not ((j not in S) and (pred[j] not in S)) for j in names) for S in mins)
            res[label] = {"min_cost": best, "n_minimisers": len(mins), "sizes": sorted({len(S) for S in mins}),
                          "all_apply_is_minimiser": set(names) in mins, "complements_independent": comp_indep,
                          "expected_ties_if_symmetric": (k if k % 2 else 2)}
        out[str(k)] = res
    return out


def main():
    t0 = time.time()
    rec = {}
    print("(a) census", flush=True)
    items, totals, summary, sound = census()
    rec["census"] = {"items": items, "locus_pair_class_totals": totals, "by_fragment": summary, "cap": CAP, "read_set_soundness": sound,
                     "subsampled_items": sorted(k for k, v in items.items() if v["subsampled"])}
    print("(a) totals", totals, f"{time.time() - t0:.0f}s", flush=True)
    for frag, v in summary.items():
        from collections import Counter
        print(f"  {frag}: {v['locus_pair_class_counts']} strongest {dict(Counter(v['strongest_class_per_declaration_pair'].values()))} largest SCC {v['largest_locus_scc']}", flush=True)
    print("(b) constructed destruction graphs", flush=True)
    rec["constructed"] = {name: instance(name) for name in INSTANCES}
    for name, r in rec["constructed"].items():
        print(f"  {name}: {r['checks']} checks, match={r['compiled_model_matches_evaluator']}, new cells={r['new_cells']}, {r['theorems']}", flush=True)
    print("(c) pure cycles (compiled model)", flush=True)
    rec["pure_cycles"] = pure_cycles()
    for k, v in rec["pure_cycles"].items():
        print(f"  k={k}: symmetric minimisers {v['symmetric r<w']['n_minimisers']} (expected {v['symmetric r<w']['expected_ties_if_symmetric']}), sizes {v['symmetric r<w']['sizes']}, all-apply {v['symmetric r<w']['all_apply_is_minimiser']}/{v['asymmetric']['all_apply_is_minimiser']}", flush=True)
    pc_ok = all(v["symmetric r<w"]["n_minimisers"] == v["symmetric r<w"]["expected_ties_if_symmetric"]
                and not v["symmetric r<w"]["all_apply_is_minimiser"] and not v["asymmetric"]["all_apply_is_minimiser"]
                and v["symmetric r<w"]["complements_independent"] for v in rec["pure_cycles"].values())
    rec["semantics"] = {"activation": "read once off the reference (evaluate.activation takes no candidate); a locus created by a repair is a new cell charged lambda*w, never a reactivation",
                        "domain": "Registered finite candidate families; at most 400 sampled states per item, plus the reference. Evaluation is one-shot. Constructed destruction graphs have separately checked score identities.",
                        "graph": "Conservative possible dependencies from overlap between subject sets and sufficient read supports. Overlap does not prove a licensed repair changes a reader; strongly connected components need not be realized destruction cycles. The inexact_read_sets field identifies declarations using full fixed-frame support, not minimal access sets.",
                        "perturbation_scope": "Fixed structural frame; sampled realization changes outside the computed supports. Insertions, changes of association or correspondence, and changes of domains are separate obligations.",
                        "boundary": "The checked simultaneous fragments generate mutual counterfeeding under the parameter regions recorded by interaction_regions; this is not a classification of all possible ordered or parallel theories"}
    rec["lean"] = ["Interaction.separable_argmin", "Interaction.all_apply_not_min"]
    ok_b = all(r["compiled_model_matches_evaluator"] and r["new_cells"] == 0 and r["theorems"]["pointwise_when_uncarried"]
               and r["theorems"]["all_apply_never_when_all_carried"] for r in rec["constructed"].values())
    rec["all_pass"] = ok_b and pc_ok and rec["constructed"]["cycle2"]["theorems"]["cycle2_symmetric_tie"] == ["A", "B"] \
        and sound["reader_changes"] == 0 and sound["read_sets_outside_T06_region"] == 0
    rec["status"] = "SAMPLED_CENSUS_AND_EXHAUSTIVE_CONTROLS_PASSED" if rec["all_pass"] else "FAILED"
    rec["elapsed_s"] = round(time.time() - t0, 1)
    certificate.write("interaction_graph.json", rec)
    print("status", rec["status"], rec["elapsed_s"], "s")

    return 0 if rec["all_pass"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
