from __future__ import annotations
from phonological_requirements import certificate, paths
import itertools, json
from fractions import Fraction
from pathlib import Path

from . import frag_lith as FL
from .core import ABSENT, Decl, Feat, NodeId, Present, Slot, Struct, TRUE
from .learn import minimal_characteristic_sample, outputs, separating_inputs

OUT = paths.CERTIFICATES
ANCHOR = Slot("t", "Or", "subject", kind="anchor")
CFG = {"R": dict(policy="dynamic", filt="obstruent", filter_mode="stop"),
       "S": dict(policy="origin_bound", filt=None, filter_mode="skip")}
PLACE = {"p": "lab", "b": "lab", "t": "cor", "d": "cor", "k": "vel", "g": "vel"}
VOI = {"lab": {0: "p", 1: "b"}, "cor": {0: "t", 1: "d"}, "vel": {0: "k", 1: "g"}}


def factorisation(a, n):
    D = dict(FL.declarations(**CFG["R"]))
    D["AGREE"] = FL.agree(**CFG[a]); D["NOGEM"] = FL.nogem(**CFG[n])
    D["MAX"] = Decl("MAX", "Or", (ANCHOR,), Feat("present", "t", True, where="reference"), Present("t"),
                    kind="faithfulness", locus_side="reference")
    return D


def build(c1, c2, tail="a"):
    segs = ["a", c1, ABSENT, c2] + list(tail)
    nodes = [NodeId("Or", "lex", 0), NodeId("Or", "lex", 1), NodeId("Or", "made", 1000)] + \
            [NodeId("Or", "lex", i) for i in range(2, 3 + len(tail))]
    dom = {nodes[0]: {"word": 0, "morph": 0}, nodes[1]: {"word": 0, "morph": 0}}
    for n in nodes[2:]:
        dom[n] = {"word": 0, "morph": 1}
    ref = Struct(order={"seg": tuple(nodes)}, real=dict(zip(nodes, segs)), dom=dom)
    cands = []
    for x in (0, 1):
        for y in (0, 1):
            for z in (0, 1):
                real = dict(ref.real)
                real[nodes[1]] = VOI[PLACE[c1]][x]
                real[nodes[3]] = VOI[PLACE[c2]][y]
                real[nodes[2]] = "i" if z else ABSENT
                cands.append(((x, y, z), Struct(order=ref.order, real=real, dom=ref.dom)))
    return ref, cands


def main():
    sigma = FL.make_sigma()
    HYP = {f"{a}{n}": factorisation(a, n) for a in "RS" for n in "RS"}
    obs = lambda s: FL.observe(sigma, s)
    INPUTS = []
    for c1 in "pbtdkg":
        for c2 in "pbtdkg":
            ref, cands = build(c1, c2)
            INPUTS.append((f"{c1}-{c2}", ref, cands, obs))
    W1 = {"IDENT_PREFIX": 1, "IDENT_STEM": 4, "DEP": 2, "AGREE": 16, "NOGEM": 16, "MAX": 40}
    W2 = {"IDENT_PREFIX": 2, "IDENT_STEM": 9, "DEP": 5, "AGREE": 40, "NOGEM": 40, "MAX": 90}
    lam = Fraction(1, 8)
    table, sep = separating_inputs(sigma, HYP, INPUTS, W1, lam)
    cs, unsep = minimal_characteristic_sample(sep, INPUTS)
    weight_differences = {h: sum(1 for iid, ref, cands, o in INPUTS
                                if outputs(sigma, ref, cands, D, W1, lam, o)
                                != outputs(sigma, ref, cands, D, W2, lam, o))
                          for h, D in HYP.items()}
    lengths = {}
    for n in range(5):
        seps = set()
        for c1, c2 in (("p", "p"), ("p", "b")):
            ref, cands = build(c1, c2, "a" * n)
            outs = {h: outputs(sigma, ref, cands, D, W1, lam, obs) for h, D in HYP.items()}
            names = list(HYP)
            for i, a in enumerate(names):
                for b in names[i + 1:]:
                    if outs[a] != outs[b]:
                        seps.add((a, b))
        lengths[n] = len(seps)
    rec = {"hypotheses": list(HYP), "schema_size": len(INPUTS),
           "pairwise_separating_counts": {f"{a}|{b}": len(v) for (a, b), v in sep.items()},
           "minimal_characteristic_sample": cs,
           "unseparated_pairs": [list(p) for p in unsep],
           "outputs_at_characteristic_inputs":
               {iid: {h: sorted(table[(iid, h)]) for h in HYP} for iid in (cs or [])},
           "weight_region_indistinguishable_inputs":
               {h: len(INPUTS) - n for h, n in weight_differences.items()},
           "observation_model": "complete surface minimizer sets",
           "length_test_tails": "a^n",
           "MAX_scope": "positions present in the reference",
           "pairs_separated_by_tail_length": lengths}
    OUT.mkdir(parents=True, exist_ok=True)
    certificate.write("identification_sample.json", rec)
    print(json.dumps({k: rec[k] for k in
                      ("minimal_characteristic_sample", "unseparated_pairs",
                       "weight_region_indistinguishable_inputs",
                       "pairs_separated_by_tail_length")}, indent=1))


if __name__ == "__main__":
    main()
