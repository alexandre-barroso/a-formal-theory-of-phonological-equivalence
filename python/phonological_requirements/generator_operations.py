from __future__ import annotations
from phonological_requirements import certificate, paths

import itertools
import json
import time
from fractions import Fraction as F
from pathlib import Path

from .core import ABSENT, And, Decl, Feat, NodeId, Not, Or_, Present, Resolves, SameFeat, Scope, Slot, Struct, TRUE
from .evaluate import activation, coefficients, score
from .generate import canonical_corr, closure, copy, fuse, productive_ext, rename_created, split, swap
from . import regimes as R

OUT = paths.CERTIFICATES


def corr_ref(segs):
    ref = R.ref_struct(segs)
    return Struct(order=ref.order, real=ref.real, dom=ref.dom, assoc=ref.assoc, corr={n: (n,) for n in ref.order["seg"]})


class _RefBefore:
    def __init__(self, first, second): self.first, self.second = first, second
    def slots(self): return frozenset({self.first, self.second})
    def eval(self, ctx):
        a, b = ctx.resolve(self.first), ctx.resolve(self.second)
        if a is None or b is None: return None
        ca, cb = ctx.state.correspondents(a), ctx.state.correspondents(b)
        if len(ca) != 1 or len(cb) != 1: return None
        order = list(ctx.reference.nodes("seg"))
        return order.index(ca[0]) < order.index(cb[0])
    def depth(self): return 1


def main():
    t0 = time.time()
    rec = {}
    sg = R.sigma()
    ref = corr_ref(["a", "t", "i"])
    alpha, ins = ("a", "i", "t", ABSENT), ("a", "i", "t")
    res = {}
    for ops in (("set",), ("set", "swap"), ("set", "insert"), ("set", "fuse"), ("set", "split"), ("set", "copy"), ("set", "swap", "fuse", "split", "copy", "insert")):
        S = closure(ref, ops, alpha, ins, 2 if ops == ("set", "split") else 1)
        wf = sum(1 for s in S if s.well_formed(ref)[0])
        D = {"MAX": R.MAXD, "IDENT": R.IDENT, "DEP": R.DEP}
        acts = activation(sg, ref, D)
        mism = 0; nren = 0
        for s in S:
            made = [n.index for n in s.order["seg"] if n.kind == "made"]
            if not made: continue
            r = rename_created(s, {i: 500 + i for i in made}); nren += 1
            if coefficients(sg, ref, r, D, acts) != coefficients(sg, ref, s, D, acts) or canonical_corr(r) != canonical_corr(s):
                mism += 1
        res["+".join(ops)] = {"structures": len(S), "well_formed": wf, "renamed": nren, "mismatches": mism}
        print(f"(a) closure {'+'.join(ops):32s} {len(S):6d} structures, {wf} well-formed, {nren} renamed, {mism} mismatches")
    rec["closures"] = res
    WORD = R.WORD
    T = Slot("t", "Or", "subject", kind="anchor")
    N1 = Slot("n1", "Or", "subject", kind="step", relation="succ", scope=WORD, direction=+1, filter="present")
    voc = lambda s: Feat("vocalic", s, True)
    NOCC = Decl("NOCC", "Or", (T, N1), And((Present("t"), Not(voc("t")), Resolves("n1"), Not(voc("n1")))), Not(And((Resolves("n1"), Not(voc("n1"))))), scope=WORD)
    LIN = Decl("LINEARITY", "Or", (T, N1), And((Present("t"), Resolves("n1"))), _RefBefore("t", "n1"), kind="faithfulness")
    IDENT_VOC = Decl("IDENT_VOC", "Or", (T,), TRUE, SameFeat("vocalic", ("t", "current"), ("t", "reference")), kind="faithfulness", locus_side="reference")
    D = {"NOCC": NOCC, "LINEARITY": LIN, "MAX": R.MAXD, "IDENT": R.IDENT, "IDENT_VOC": IDENT_VOC, "DEP": R.DEP}
    ref2 = corr_ref(["a", "t", "t", "i"])
    W = {"NOCC": 10, "LINEARITY": 3, "MAX": 8, "IDENT": 8, "IDENT_VOC": 8, "DEP": 8}
    best, minima, cert = productive_ext(sg, ref2, D, W, F(1, 8), ("set", "swap", "insert"), alpha, ins)
    outs = sorted({"".join(s.real[n] for n in s.order["seg"] if s.real[n] != ABSENT) for s in minima})
    rec["metathesis"] = {"reference": "atti", "weights": W, "winners": outs, "score": str(best), "certificate": cert}
    print("(b) metathesis: winners", outs, "score", best, "| enumerated", cert["structures_enumerated_up_to_renaming"], "max created", cert["max_created_nodes"])
    from . import frag_redup, reduplication_template
    ok_c = 0; tot = 0
    for it in reduplication_template.ITEMS[13:20]:
        r = frag_redup.build(it[1]); order = list(r.order["seg"])
        stem = [n for n in order if r.dom[n]["kind"] == "stem"]
        for c in frag_redup.candidates(r, it[1]):
            made = [n for n in c.order["seg"] if n.kind == "made"]
            if not made: continue
            tot += 1
            cs = [c.correspondents(n) for n in made]
            if all(len(x) == 1 and x[0] in stem for x in cs) and [x[0] for x in cs] == stem[:len(cs)]:
                ok_c += 1
    rec["bridge_copies"] = {"candidates_with_copies": tot, "left_anchored_copies_of_stem_nodes": ok_c}
    print(f"(c) reduplication bridge: {ok_c}/{tot} candidates' created nodes are left-anchored copies of stem nodes")
    from . import frag_nuer
    from .observations import NUER
    fus = tot2 = 0
    for key in list(NUER)[:8]:
        spec = NUER[key][0]
        r = frag_nuer.build(spec)
        tones_ref = [n for ns in r.order.values() for n in ns if n.sort == "Tone" and n.kind == "lex"]
        for c in frag_nuer.candidates(r):
            for n in (m for ns in c.order.values() for m in ns if m.sort == "Tone"):
                cs = c.correspondents(n)
                if len(cs) == 2:
                    tot2 += 1
                    i, j = tones_ref.index(cs[0]), tones_ref.index(cs[1])
                    if j == i + 1: fus += 1
    rec["bridge_fusion"] = {"fused_tones": tot2, "of_adjacent_reference_tones": fus}
    print(f"(c) fusion bridge: {fus}/{tot2} fused tones correspond to two adjacent reference tones")
    rec["seconds"] = round(time.time() - t0, 1)
    certificate.write("generator_operations.json", rec)
    print(f"certificate written in {rec['seconds']} s")


if __name__ == "__main__":
    main()
