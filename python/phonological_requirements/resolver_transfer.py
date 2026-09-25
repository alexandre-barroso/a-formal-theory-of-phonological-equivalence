from __future__ import annotations
from phonological_requirements import certificate, paths
import itertools, json
from fractions import Fraction
from pathlib import Path

from . import frag_gua as FG
from . import frag_lith as FL
from .core import read, NodeId, Struct, ABSENT
from .evaluate import (loci, activation, marked_subjects, coefficients, score,
                       subject_tuple)
from .indep_gua import ALPHABET
from .products import gua_products, gua_observations

OUT = paths.CERTIFICATES

POLICIES = {"dynamic_stop": ("dynamic", "stop"),
            "dynamic_skip": ("dynamic", "skip"),
            "origin_bound": ("origin_bound", "skip"),
            "witness": ("witness", "skip")}


def theories():
    T = {}
    for pn, (pol, fm) in POLICIES.items():
        for idx in ("locus", "subject"):
            T[f"{pn}+{idx}"] = (FG.declarations("typed", pol, FG.NEXT_WORD, None, fm), idx)
    T["appendix+locus"] = (FG.declarations("baseline"), "locus")
    return T


def gua_scores():
    sg = FG.make_sigma(); T = theories()
    vals = {k: [] for k in T}; outs = []; ids = []
    for focal, prod in gua_products():
        ref = FG.struct_from_segments(prod.reference, prod.words, prod.phrase_of_word)
        A = {k: (activation(sg, ref, D), marked_subjects(sg, ref, D)) for k, (D, _) in T.items()}
        base = list(prod.reference)
        for combo in itertools.product(ALPHABET, repeat=len(focal)):
            st = list(base)
            for q, v in zip(focal, combo):
                st[q] = v
            cur = FG.struct_from_segments(tuple(st), prod.words, prod.phrase_of_word)
            outs.append(prod.observe(tuple(st))); ids.append(prod.id)
            for k, (D, idx) in T.items():
                acts, subs = A[k]
                cf = coefficients(sg, ref, cur, D, acts, subjects=(subs if idx == "subject" else None))
                vals[k].append(score(cf, FG.WEIGHTS, FG.LAMBDA))
    return vals, outs, ids


def transfer_witnesses():
    sg = FG.make_sigma()
    D = FG.declarations("typed", "dynamic", FG.NEXT_WORD, None, "stop")
    A = D["A"]; found = []
    for focal, prod in gua_products():
        ref = FG.struct_from_segments(prod.reference, prod.words, prod.phrase_of_word)
        acts = activation(sg, ref, D); subs = marked_subjects(sg, ref, D)
        base = list(prod.reference)
        for combo in itertools.product(ALPHABET, repeat=len(focal)):
            st = list(base)
            for q, v in zip(focal, combo):
                st[q] = v
            cur = FG.struct_from_segments(tuple(st), prod.words, prod.phrase_of_word)
            for nd in loci(cur, A):
                r = read(sg, ref, cur, A, nd)
                if not r.pressure:
                    continue
                sub = subject_tuple(sg, ref, cur, A, nd)
                if acts["A"].get(nd, False) and sub not in subs["A"]:
                    found.append({"product": prod.id, "state": "".join(st),
                                  "locus": repr(nd),
                                  "reference_subjects": sorted(repr(x) for x in subs["A"]),
                                  "current_subject": repr(sub),
                                  "readers": list(r.triple())})
    return found


def discriminator():
    sigma = FL.make_sigma()
    nodes = [NodeId("Or", "lex", 0), NodeId("Or", "lex", 1), NodeId("Or", "made", 1000),
             NodeId("Or", "lex", 2), NodeId("Or", "lex", 3)]
    dom = {nodes[0]: {"word": 0, "morph": 0}, nodes[1]: {"word": 0, "morph": 0},
           nodes[2]: {"word": 0, "morph": 1}, nodes[3]: {"word": 0, "morph": 1},
           nodes[4]: {"word": 0, "morph": 1}}

    def mk(gap):
        return Struct(order={"seg": tuple(nodes)},
                      real={nodes[0]: "a", nodes[1]: "p", nodes[2]: gap,
                            nodes[3]: "b", nodes[4]: "a"}, dom=dom)
    ref = mk(ABSENT); rows = []
    for pn, (pol, fm) in POLICIES.items():
        D = FL.declarations(policy=pol, filt=("obstruent" if pol == "dynamic" else None),
                            filter_mode=fm)
        ag = D["AGREE"]
        a_ref = {nd: int(read(sigma, ref, ref, ag, nd).marked) for nd in loci(ref, ag)}
        subs = {subject_tuple(sigma, ref, ref, ag, nd) for nd in loci(ref, ag)
                if read(sigma, ref, ref, ag, nd).marked}
        for idx in ("locus", "subject"):
            for gap, lab in ((ABSENT, "reference"), ("t", "agreeing obstruent"),
                             ("d", "disagreeing obstruent"), ("i", "vowel")):
                s = mk(gap); rd = read(sigma, ref, s, ag, nodes[1])
                st = subject_tuple(sigma, ref, s, ag, nodes[1])
                aq = a_ref.get(nodes[1], 0) if idx == "locus" else int(st in subs)
                contrib = ("w" if (aq and rd.pressure) else
                           ("lambda*w" if ((not aq) and rd.context and rd.pressure) else "0"))
                rows.append({"policy": pn, "indexing": idx, "gap": lab,
                             "readers": list(rd.triple()), "subject": repr(st),
                             "a": aq, "contribution": contrib})
    return rows


def winner_locality():
    sg = FG.make_sigma()
    W = dict(zip(FG.SCHEMA_ORDER, (9, 2, 3, 4, 8, 12, 12, 20, 5)))
    words = [0, 1, 2, 3]; ph = [0, 0, 1, 1]
    ref = FG.struct_from_segments(["e", "ɔ", "e", "e"], words, ph)
    out = {}
    for k, (D, idx) in theories().items():
        acts = activation(sg, ref, D); subs = marked_subjects(sg, ref, D)
        res = {}
        for second in (("a", "a"), ("e", "a")):
            best = None; mins = []
            for v0 in FG.ALPHABET:
                for v1 in FG.ALPHABET:
                    cur = FG.struct_from_segments([v0, v1, second[0], second[1]], words, ph)
                    cf = coefficients(sg, ref, cur, D, acts,
                                      subjects=(subs if idx == "subject" else None))
                    s = score(cf, W, FG.LAMBDA)
                    if best is None or s < best:
                        best, mins = s, [(v0, v1)]
                    elif s == best:
                        mins.append((v0, v1))
            res["".join(second)] = sorted({tuple(x for x in m if x != ABSENT) for m in mins})
        out[k] = {"second_aa": [list(x) for x in res["aa"]],
                  "second_ea": [list(x) for x in res["ea"]],
                  "local": res["aa"] == res["ea"]}
    return out


def main():
    vals, outs, ids = gua_scores()
    obs = gua_observations()
    keys = list(vals)
    pair = {k: {j: sum(1 for x, y in zip(vals[k], vals[j]) if x != y) for j in keys} for k in keys}
    sel = {}
    for k in keys:
        ok = True
        byprod = {}
        for pid in {i for i in ids}:
            idxs = [i for i, x in enumerate(ids) if x == pid]
            m = min(vals[k][i] for i in idxs)
            w = [i for i in idxs if vals[k][i] == m]
            good = all(outs[i] in set(obs[pid]["allowed"]) for i in w)
            byprod[pid] = good; ok &= good
        sel[k] = {"all_eight": ok, "per_product": byprod}
    tw = transfer_witnesses()
    rec = {"pairwise_score_differences": pair, "eight_selections": sel,
           "transfer_witness_count": len(tw),
           "transfer_by_product": {p: sum(1 for t in tw if t["product"] == p)
                                   for p in sorted({t["product"] for t in tw})},
           "transfer_examples": tw[:6],
           "discriminator": discriminator(),
           "winner_locality": winner_locality()}
    OUT.mkdir(parents=True, exist_ok=True)
    certificate.write("resolver_transfer.json", rec)
    print(json.dumps({"transfer_witness_count": rec["transfer_witness_count"],
                      "transfer_by_product": rec["transfer_by_product"],
                      "all_eight": {k: v["all_eight"] for k, v in sel.items()},
                      "winner_local": {k: v["local"] for k, v in rec["winner_locality"].items()}},
                     indent=1))


if __name__ == "__main__":
    main()
