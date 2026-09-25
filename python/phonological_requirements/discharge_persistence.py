from __future__ import annotations
from phonological_requirements import certificate, paths
import json
from fractions import Fraction
from pathlib import Path

from . import frag_auto as A
from .core import (ABSENT, And, Decl, Feat, Linked, NodeId, Not, Or_, Present, read,
                   Resolves, SameFeat, Scope, Slot, Struct, TRUE)
from .evaluate import activation, coefficients, score
from .strictness import subject_strict

OUT = paths.CERTIFICATES

HIATUS_N = Slot("n", "Rel", "trigger", kind="step", relation="succ",
                scope=Scope(same=("word",), label="w"), direction=+1,
                policy="dynamic", filter_mode="stop")
HIATUS = Decl("HIATUS", "Or", (Slot("t", "Or", "subject", kind="anchor"), HIATUS_N),
              And((Feat("vocalic", "t", True), Resolves("n"),
                   Feat("vocalic", "n", True))), Not(Present("t")))
IDENT = Decl("IDENT", "Or", (Slot("t", "Or", "subject", kind="anchor"),), TRUE,
             SameFeat("hi", ("t", "current"), ("t", "reference")),
             kind="faithfulness", locus_side="reference")
LINKHI = Decl("LINKHI", "Tone", (A.T, A.HOST_CUR), TRUE, Feat("hi", "h", True))


def tone_stability():
    sg = A.make_sigma()
    ref = A.build(["t", "a", "i"], tones=("H",), links=(("tone", 0, 1),))
    out = {}
    for lab, decl, w in (("existence_form_FLOAT", A.FLOAT_T, 24),
                         ("property_form_LINKHI", LINKHI, 24)):
        D = {"IDENT": IDENT, "MAXLINK-T": A.MAXLINK_T, "DEPLINK-T": A.DEPLINK_T,
             decl.name: decl}
        W = {"IDENT": 4, "MAXLINK-T": 1, "DEPLINK-T": 1, decl.name: w}
        acts = activation(sg, ref, D)
        rows = []
        for r1 in ("a", "i"):
            for link in (None, 1, 2):
                real = dict(ref.real); real[NodeId("Or", "lex", 1)] = r1
                assoc = (frozenset() if link is None else
                         frozenset({(NodeId("Tone", "lex", 0), NodeId("Or", "lex", link))}))
                c = Struct(order=ref.order, real=real, dom=ref.dom, assoc=assoc)
                cf = coefficients(sg, ref, c, D, acts)
                rows.append({"seg1": r1, "tone_host": link,
                             "score8": str(score(cf, W, A.LAM) * 8),
                             "coefficients": {k: list(v) for k, v in cf.items()}})
        m = min(Fraction(r["score8"]) for r in rows)
        out[lab] = {"subject_strict_in_h": subject_strict(decl, "h")[0],
                    "minimisers": [r for r in rows if Fraction(r["score8"]) == m],
                    "all": rows}
    return out


SEG = ["s", "e", "o", "l", "u"]
VOW = {1: 0, 2: 1, 4: 2}


def _cl_build(regime, realisations, links):
    segn = tuple(NodeId("Or", "lex", i) for i in range(len(SEG)))
    if regime == "total":
        morn = tuple(NodeId("Mora", "lex", i) for i in range(3))
    else:
        morn = tuple(NodeId("Mora", "lex", m) for s, m in sorted(VOW.items())
                     if realisations.get(s, SEG[s]) != ABSENT)
    real = {n: realisations.get(i, SEG[i]) for i, n in enumerate(segn)}
    real.update({n: "μ" for n in morn})
    dom = {n: {"word": 0} for n in segn + morn}
    assoc = frozenset((NodeId("Mora", "lex", m), NodeId("Or", "lex", s))
                      for m, s in links.items()
                      if NodeId("Mora", "lex", m) in morn)
    return Struct(order={"seg": segn, "mora": morn}, real=real, dom=dom, assoc=assoc)


def compensatory_lengthening():
    MAXLINKM = Decl("MAXLINK-M", "Mora",
                    (A.M, Slot("h", "Or", "subject", kind="assoc",
                               relation="assoc", where="reference")),
                    TRUE, Linked("t", "h", where="current"), kind="faithfulness")
    D = {"MAX": A.MAXSEG, "HIATUS": HIATUS, "FLOAT-M": A.FLOAT_M,
         "MAXLINK-M": MAXLINKM}
    W = {"MAX": 6, "HIATUS": 30, "FLOAT-M": 24, "MAXLINK-M": 1}
    out = {}
    for regime in ("total", "derived"):
        sg = A.make_sigma(mora_totality=regime)
        ref = _cl_build("total", {}, {0: 1, 1: 2, 2: 4})
        acts = activation(sg, ref, D)
        rows = []
        for del1 in (False, True):
            for m0 in (1, 2, None):
                realis = {1: ABSENT} if del1 else {}
                links = {1: 2, 2: 4}
                if m0 is not None:
                    links[0] = m0
                c = _cl_build(regime, realis, links)
                cf = coefficients(sg, ref, c, D, acts)
                wt = sum(1 for (_m, h) in c.assoc if h == NodeId("Or", "lex", 2))
                rows.append({"V1_deleted": del1, "mu0_host": m0,
                             "moras_on_V2": wt,
                             "score8": str(score(cf, W, A.LAM) * 8),
                             "coefficients": {k: list(v) for k, v in cf.items()}})
        m = min(Fraction(r["score8"]) for r in rows)
        out[regime] = {"minimisers": [r for r in rows if Fraction(r["score8"]) == m],
                       "compensatory_lengthening":
                           all(r["moras_on_V2"] == 2 for r in rows
                               if Fraction(r["score8"]) == m),
                       "all": rows}
    return out


def third_party_discharge():
    import itertools
    from . import frag_gua as FG
    from . import frag_lith as FL
    from .core import Ctx
    from .evaluate import subject_tuple
    from .products import gua_products

    def classify(sigma, ref, cands, decl, locus, relata):
        sat = dis = third = 0; wit = []
        for key, c in cands:
            r = read(sigma, ref, c, decl, locus)
            if r.pressure:
                continue
            if r.defined:
                sat += 1; continue
            dis += 1
            if all(c.real.get(i) == ref.real.get(i) for i in relata):
                third += 1
                if len(wit) < 3:
                    wit.append(str(key))
        return {"candidates": len(cands), "satisfied": sat, "discharged": dis,
                "third_party_discharged": third, "witnesses": wit}

    out = {}
    sl = FL.make_sigma(); ref, marks, _ = FL.build("ap-berti")
    D = FL.declarations(policy="dynamic", filt="obstruent", filter_mode="stop")
    n1, site, n2 = marks
    out["lithuanian_AGREE_relational"] = classify(
        sl, ref, list(FL.candidates(ref, marks)), D["AGREE"], n1, [n1, n2])
    sg = FG.make_sigma()
    focal, prod = [p for p in gua_products() if p[1].id == "G34a"][0]
    refG = FG.struct_from_segments(prod.reference, prod.words, prod.phrase_of_word)
    DG = FG.declarations("typed")
    cg = []
    for combo in itertools.product(FG.ALPHABET, repeat=len(focal)):
        st = list(prod.reference)
        for q, v in zip(focal, combo):
            st[q] = v
        cg.append((tuple(st), FG.struct_from_segments(tuple(st), prod.words,
                                                      prod.phrase_of_word)))
    tgt = refG.nodes("seg")[2]
    out["gua_H_total_anchor"] = classify(sg, refG, cg, DG["H"], tgt, [tgt])
    anchor = refG.nodes("seg")[4]
    ctx = Ctx(sg, refG, refG, DG["A"], anchor)
    partner = ctx.resolve("n")
    out["gua_A_relational"] = classify(sg, refG, cg, DG["A"], anchor,
                                       [x for x in (anchor, partner) if x])
    return out


def main():
    rec = {"tone_stability": tone_stability(),
           "compensatory_lengthening": compensatory_lengthening(),
           "third_party_discharge": third_party_discharge()}
    OUT.mkdir(parents=True, exist_ok=True)
    certificate.write("discharge_persistence.json", rec)
    print("tone stability:")
    for k, v in rec["tone_stability"].items():
        print(f"  {k:22s} subject-strict={v['subject_strict_in_h']}  "
              f"minimisers={[(r['seg1'], r['tone_host']) for r in v['minimisers']]}")
    print("third-party discharge:")
    for k, v in rec["third_party_discharge"].items():
        print(f"  {k:32s} satisfied={v['satisfied']:4d} discharged={v['discharged']:4d} "
              f"third-party={v['third_party_discharged']}")
    print("compensatory lengthening:")
    for k, v in rec["compensatory_lengthening"].items():
        print(f"  mora {k:8s} CL={v['compensatory_lengthening']}  "
              f"minimisers={[(r['V1_deleted'], r['mu0_host'], r['moras_on_V2']) for r in v['minimisers']]}")


if __name__ == "__main__":
    main()
