from __future__ import annotations
from phonological_requirements import certificate, paths

import itertools
import json
import random
import time
from fractions import Fraction as F
from pathlib import Path

from .automaton import Compiled
from .core import ABSENT, read
from .evaluate import activation, coefficients, score, tier_of, loci
from .frag_seq import build, candidates, faith_decls, make_sigma, rule_decl
from . import interaction_typology as R10

OUT = paths.CERTIFICATES
LAMS = (F(0), F(1, 8), F(1))
MODES = ("retain", "discharge", "ltr", "rtl")


def evaluator_best(sigma, D, W, lam, ref, options):
    acts = activation(sigma, ref, D)
    best, mins = None, []
    nodes = ref.order["seg"]
    for c in candidates(ref, options):
        v = score(coefficients(sigma, ref, c, D, acts), W, lam)
        seq = tuple(c.real[n] for n in nodes)
        if best is None or v < best:
            best, mins = v, [seq]
        elif v == best:
            mins.append(seq)
    return best, sorted(set(mins))


def part_a_b():
    rnd = random.Random(15)
    rec = {"patterns": {}, "checks": 0, "mismatches": [], "max_residual_over_bound": F(0), "residual_checks": 0}
    for name, pat in R10.PATTERNS.items():
        alpha = list(pat["alphabet"])
        res = {"inputs": set(), "checks": 0, "max_states": 0}
        for mode in MODES:
            sigma, D = R10.build_pattern(pat, (mode,) * len(pat["rules"]))
            inputs = list(pat["mappings"]) + ["".join(rnd.choice(alpha) for _ in range(rnd.randint(5, 9))) for _ in range(3)]
            for inp in inputs:
                syms = R10.split(inp, pat["alphabet"])
                ref = build(syms)
                res["inputs"].add(inp)
                for trial in range(2):
                    W = {k: rnd.randint(1, 5) for k in D}
                    for lam in LAMS:
                        eb, em = evaluator_best(sigma, D, W, lam, ref, pat["options"])
                        C = Compiled(sigma, D, W, lam, pat["options"])
                        ab, am, nst, mins_by_layer = C.best(syms, layer_mins=True)
                        rec["checks"] += 1; res["checks"] += 1; res["max_states"] = max(res["max_states"], nst)
                        if eb != ab or em != am:
                            rec["mismatches"].append({"pattern": name, "mode": mode, "input": inp, "W": W, "lam": str(lam),
                                                      "evaluator": (str(eb), ["".join(x) for x in em][:5]), "automaton": (str(ab), ["".join(x) for x in am][:5])})
                            continue
                        cmax = sum(F(W[k]) for k in D)
                        for seq in am:
                            pc = C.replay(syms, seq)
                            for i, (c_i, m_i) in enumerate(zip(pc, mins_by_layer)):
                                rec["residual_checks"] += 1
                                r = (c_i - m_i) / (4 * cmax) if cmax else F(0)
                                if r > rec["max_residual_over_bound"]:
                                    rec["max_residual_over_bound"] = r
        res["inputs"] = len(res["inputs"])
        rec["patterns"][name] = res
    rec["max_residual_over_bound"] = str(rec["max_residual_over_bound"])
    return rec


def part_c():
    pat = R10.PATTERNS["noniterative_left_to_right"]
    sigma, D = R10.build_pattern(pat, ("ltr",) * len(pat["rules"]))
    W = {k: 3 if not k.startswith(("MAX", "IDENT")) else 1 for k in D}
    C = Compiled(sigma, D, W, F(1, 8), pat["options"])
    rnd = random.Random(3)
    alpha = list(pat["alphabet"])
    out = []
    for n in (8, 16, 32, 64, 128):
        syms = [rnd.choice(alpha) for _ in range(n)]
        t0 = time.time(); b, _, nst, _ = C.best(syms, layer_mins=True, paths=False); dt = time.time() - t0
        out.append({"length": n, "seconds": round(dt, 4), "states_last_layer": nst, "best": str(b)})
    return {"timings": out, "state_bound_per_layer": C.n_states_bound(), "note": "timings are measurements on this machine; the bound on states per layer is the theorem's constant; tie enumeration is output-sensitive and excluded here"}


def part_d():
    alpha = {"a": {"VA", "V"}, "b": {"VB", "V"}}
    sigma = make_sigma(alpha)
    D = {"R1": rule_decl("R1", "VB", ("VA",), (), "a", "discharge"), "R2": rule_decl("R2", "VA", ("VB",), (), "b", "discharge")}
    D.update(faith_decls(alpha, [("VB", "a"), ("VA", "b")]))
    options = {"a": ["a", "b"], "b": ["b", "a"]}
    lam = F(1, 8)
    rec = {"declarations": list(D), "ot": {}, "hg": {}, "summary": {}}
    ot_majority = hg_bounded = hg_faithful = True
    max_edits = 0
    for p in range(1, 7):
        for q in range(1, 7):
            syms = ["a"] * p + ["b"] * q
            ref = build(syms); nodes = ref.order["seg"]
            faithful = "".join(syms)
            rows = []
            for c in candidates(ref, options):
                seq = "".join(c.real[n] for n in nodes)
                v = {}
                for name, d in D.items():
                    v[name] = sum(int(r.pressure and r.context) for l in loci(c, d, "seg", ref) for r in [read(sigma, ref, c, d, l, "seg")])
                rows.append((seq, (v["R1"] + v["R2"], v["IDENT_VB_a"] + v["IDENT_VA_b"])))
            best = min(r[1] for r in rows)
            ot = sorted(s for s, r in rows if r == best)
            rec["ot"][f"a^{p}b^{q}"] = ot
            expect = ["a" * (p + q)] if p > q else ["b" * (p + q)] if q > p else ["a" * (p + q), "b" * (p + q)]
            ot_majority &= (ot == expect)
            hg = {}
            acts = activation(sigma, ref, D)
            for wR in (1, 2, 3, 5, 8):
                W = {"R1": wR, "R2": wR, "IDENT_VB_a": 1, "IDENT_VA_b": 1}
                sc = {}
                for c in candidates(ref, options):
                    sc["".join(c.real[n] for n in nodes)] = score(coefficients(sigma, ref, c, D, acts), W, lam)
                b = min(sc.values()); win = sorted(s for s, v in sc.items() if v == b)
                hg[str(wR)] = win
                edits = max(sum(1 for x, y in zip(w, faithful) if x != y) for w in win)
                max_edits = max(max_edits, edits)
                bound = min(F(wR), F(1) + lam * wR)
                hg_bounded &= all(F(sum(1 for x, y in zip(w, faithful) if x != y)) <= bound for w in win)
                if F(wR) * (1 - lam) <= 1 and min(p, q) >= 2:
                    hg_faithful &= (faithful in win)
            rec["hg"][f"a^{p}b^{q}"] = hg
    rec["summary"] = {"ranked_map_is_majority_rules_on_all_36_inputs": ot_majority,
                      "weighted_winners_edit_at_most_incumbent_over_w_I": hg_bounded, "max_edits_of_a_weighted_winner": max_edits,
                      "weighted_map_faithful_when_w_R(1-lambda)<=w_I_and_min_pq>=2": hg_faithful,
                      "argument": "the faithful candidate costs w_R (one activated locus) whatever p and q, and changing the segment next to the boundary costs w_I + lambda w_R (a created locus) or w_I at an edge; every harmonic candidate changes min(p, q) segments.  Under strict ranking (markedness over faithfulness) the faithful candidate loses to any harmonic one and the winner is the majority value, a map whose range distinguishes p < q from p > q --- not a regular relation (Heinz and Lai 2013 as reported by Chandlee, Heinz and Jardine 2018 p. 26; Lamont 2021 pp. 729-731).  Under fixed weights every winner costs at most the incumbent min(w_R, w_I + lambda w_R), so it changes at most that many segments divided by w_I: a bounded edit, so the weighted map on a^p b^q is a regular relation and no weight vector reproduces the ranked map on unbounded inputs."}
    return rec


def part_e():
    rec = {}
    alpha = {"N": {"nas", "C"}, "C": {"C"}, "V": {"V", "oral"}, "W": {"V", "nas"}}
    sigma = make_sigma(alpha)
    D = {"NAS": rule_decl("NAS", "oral", ("nas",), (), "W", "discharge")}
    D.update(faith_decls(alpha, [("oral", "W")]))
    W = {"NAS": 8, "IDENT_oral_W": 1}
    lam = F(1, 2)
    options = {"V": ["V", "W"]}
    C = Compiled(sigma, D, W, lam, options)
    T = 1 + lam * W["NAS"] / W["IDENT_oral_W"]
    e1 = {"rule": "V -> W (nasal) / N _ ; discharge mode; w = 8, w_I = 1, lambda = 1/2: threshold n <= 1 + lambda w / w_I = 5", "inputs": {}, "length_bounded_as_predicted": True, "automaton_equals_evaluator": True}
    for n in range(1, 11):
        syms = ["N"] + ["V"] * n + ["C", "V"]
        ref = build(syms)
        eb, em = evaluator_best(sigma, D, W, lam, ref, options)
        ab, am, _, _ = C.best(syms, layer_mins=True)
        e1["automaton_equals_evaluator"] &= (eb == ab and em == am)
        e1["inputs"][n] = {"minimisers": ["".join(x) for x in am], "cost": str(eb)}
        full = tuple(["N"] + ["W"] * n + ["C", "V"]); first = tuple(["N", "W"] + ["V"] * (n - 1) + ["C", "V"])
        expect = [full] if n < T else [first] if n > T else sorted([first, full])
        e1["length_bounded_as_predicted"] &= (am == expect)
    e1["statement"] = "along a feeding chain of k repairs the only violated created locus is the frontier, so the cost of nasalising the first k of n vowels is k w_I + [k < n] lambda w; the chain runs to the end iff n w_I <= w_I + lambda w and otherwise stops after the first vowel: iterative feeding is length-bounded at fixed weights (here as an exact threshold), and unbounded spreading needs a trigger reached by a search over a class (outside the rule-shaped fragment)"
    rec["e1_feeding_chain"] = e1
    alpha = {"C": {"C"}, "e": {"E", "V"}, "V": {"V"}}
    sigma = make_sigma(alpha)
    D = {"SYNC": rule_decl("SYNC", "E", ("C", "V"), ("C", "V"), None, "ltr")}
    D.update(faith_decls(alpha, [("E", None)]))
    W = {"SYNC": 3, "MAX_E": 1}
    options = {"e": ["e", ABSENT]}
    C = Compiled(sigma, D, W, F(1, 8), options)
    e2 = {"rule": "e -> 0 / VC _ CV, left-to-right mode", "inputs": {}, "minimisers_are_minimum_left_covering_sets": True, "automaton_equals_evaluator": True}
    for n in range(1, 11):
        syms = ["V"] + ["C", "e"] * n + ["C", "V"]
        ref = build(syms)
        eb, em = evaluator_best(sigma, D, W, F(1, 8), ref, options)
        ab, am, _, _ = C.best(syms, layer_mins=True)
        e2["automaton_equals_evaluator"] &= (eb == ab and em == am)
        got = sorted(tuple(k + 1 for k in range(n) if s[2 + 2 * k] == ABSENT) for s in am)
        cands = []
        for bits in itertools.product((0, 1), repeat=n):
            S = {k + 1 for k in range(n) if bits[k]}
            if 1 in S and all((k in S) or (k - 1 in S) for k in range(2, n + 1)):
                cands.append(S)
        m = min(len(S) for S in cands)
        expect = sorted(tuple(sorted(S)) for S in cands if len(S) == m)
        e2["inputs"][n] = {"deleted_sets": [list(g) for g in got], "n_minimisers": len(got), "cost": str(eb)}
        e2["minimisers_are_minimum_left_covering_sets"] &= (got == expect)
    e2["statement"] = "the first schwa is activated with its left context intact and must delete; a later schwa keeps its charge unless the schwa to its left is deleted (the left side is carried); so the minimisers are the minimum sets containing 1 in which no two consecutive schwas are both kept --- ceil(n/2) deletions, unique for even n and tied for odd n (the path analogue of T08's cycle covering)"
    rec["e2_directional_deletion"] = e2
    alpha3 = {"C": {"C"}, "e": {"E", "V"}, "V": {"V"}, "X": {"C"}}
    sigma3 = make_sigma(alpha3)
    D3 = {"SYNC": rule_decl("SYNC", "E", ("C", "V"), ("C", "V"), None, "ltr"), "CCC": rule_decl("CCC", "C", ("C", "C"), (), "X", "discharge")}
    D3.update(faith_decls(alpha3, [("E", None)]))
    W3 = {"SYNC": 3, "CCC": 1, "MAX_E": 1}
    C3 = Compiled(sigma3, D3, W3, F(1, 8), options)
    e3 = {"rules": ["e -> 0 / VC _ CV (left-to-right)", "C -> X / CC _ with X not among C's realisations: an unrepairable requirement, a created locus charged lambda*w"], "inputs": {}, "odd_schwas_deleted_uniquely": True, "automaton_equals_evaluator": True}
    for n in range(1, 11):
        syms = ["V"] + ["C", "e"] * n + ["C", "V"]
        ref = build(syms)
        eb, em = evaluator_best(sigma3, D3, W3, F(1, 8), ref, options)
        ab, am, _, _ = C3.best(syms, layer_mins=True)
        e3["automaton_equals_evaluator"] &= (eb == ab and em == am)
        got = [tuple(k + 1 for k in range(n) if s[2 + 2 * k] == ABSENT) for s in am]
        e3["inputs"][n] = {"deleted": [list(g) for g in got], "cost": str(eb)}
        e3["odd_schwas_deleted_uniquely"] &= (got == [tuple(k for k in range(1, n + 1) if k % 2 == 1)])
    e3["argument"] = "the k-th schwa is deleted iff k is odd, for every n; inputs V(Ce)^{2m} C and V(Ce)^{2m+1} C share every suffix of bounded length once m is large, yet the next schwa is deleted after the one and kept after the other: their tails differ, so this function is not k-ISL for any k (Chandlee and Heinz 2018, Definition 1 and their argument for iterative rules); by (a) it is realised by the alignment automaton, hence a regular function"
    rec["e3_parity_function"] = e3
    return rec


def main():
    t0 = time.time()
    rec = {}
    print("(a)/(b) automaton against the evaluator", flush=True)
    rec["a_b"] = part_a_b()
    print("  checks", rec["a_b"]["checks"], "mismatches", len(rec["a_b"]["mismatches"]), "max residual / bound", rec["a_b"]["max_residual_over_bound"], f"{time.time() - t0:.0f}s", flush=True)
    print("(c) timing", flush=True)
    rec["c"] = part_c(); print("  ", rec["c"]["timings"], flush=True)
    print("(d) ranking against weighting", flush=True)
    rec["d"] = part_d(); print("  ", {k: v for k, v in rec["d"]["summary"].items() if k != "argument"}, flush=True)
    print("(e) not ISL", flush=True)
    rec["e"] = part_e(); print("  e1 bounded", rec["e"]["e1_feeding_chain"]["length_bounded_as_predicted"], "e2 covering", rec["e"]["e2_directional_deletion"]["minimisers_are_minimum_left_covering_sets"], "e3 parity", rec["e"]["e3_parity_function"]["odd_schwas_deleted_uniquely"], "automaton=evaluator", all(v["automaton_equals_evaluator"] for v in rec["e"].values()), flush=True)
    rec["all_pass"] = (not rec["a_b"]["mismatches"]) and F(rec["a_b"]["max_residual_over_bound"]) <= 1 \
        and rec["d"]["summary"]["ranked_map_is_majority_rules_on_all_36_inputs"] and rec["d"]["summary"]["weighted_winners_edit_at_most_incumbent_over_w_I"] \
        and rec["d"]["summary"]["weighted_map_faithful_when_w_R(1-lambda)<=w_I_and_min_pq>=2"] \
        and rec["e"]["e1_feeding_chain"]["length_bounded_as_predicted"] and rec["e"]["e2_directional_deletion"]["minimisers_are_minimum_left_covering_sets"] \
        and rec["e"]["e3_parity_function"]["odd_schwas_deleted_uniquely"] and all(v["automaton_equals_evaluator"] for v in rec["e"].values())
    rec["status"] = "FINITE_EXHAUSTIVE_CERTIFIED" if rec["all_pass"] else "FAILED"
    rec["elapsed_s"] = round(time.time() - t0, 1)
    certificate.write("alignment_automaton.json", rec)
    print("status", rec["status"], rec["elapsed_s"], "s")


if __name__ == "__main__":
    main()
