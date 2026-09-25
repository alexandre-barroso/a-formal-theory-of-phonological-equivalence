from __future__ import annotations
from phonological_requirements import paths

import itertools
import json
import time
from fractions import Fraction as F
from pathlib import Path

import sympy as sp

from .core import ABSENT
from .evaluate import activation, coefficients, score
from .frag_arapaho import (ALPHABET, CONFIGS, LEX_TRIGGER, config,
                           declarations, sigma, struct)
from .observations import ARAPAHO
from .search import bb_search, complete_search

OUT = paths.CERTIFICATES

W = dict(ID_SEG=5, ID_NUCLEAR=3, ID_CONT=2, ID_GLOTTAL=2, ID_DOR=1, ID_ANT=1,
         ID_LAB=1, ID_NAS=1, ID_OBS=1, ID_FRONT=1, ID_HIGH=1, ID_ROUND=1,
         ID_HTONE=1, MUT_DOR=8, MUT_ANT=8, NOCODA=2, DEP=10, MAX=10, SYNC=0)
LAM = F(1, 8)
EPEN = ("TRIG1", "TRIG2", "TRIG3", "CLUS1", "CLUS2", "CLUS3", "RND1", "RND2")
LEX = ("SUPP1", "SUPP2", "SUPP3", "SUPP4", "SUPP5")
DOY = ("CLUS1", "CLUS2", "CLUS3")
TRANSPARENT = ("TRIG1", "TRIG2", "TRIG3")
BLOCKED = ("RND1", "RND2")


def cell_table():
    w, lam, p = sp.symbols("w lam p", nonnegative=True)
    rows = {}
    for a in (0, 1):
        for c in (0, 1):
            e = sp.expand(w * (a * p + lam * (1 - a) * c * p))
            rows[f"a={a},C={c}"] = str(e)
    return rows


def bounding(sg, ref, D, acts, att):
    ca = coefficients(sg, ref, att, D, acts)
    cf = coefficients(sg, ref, ref, D, acts)
    diff = {k: (ca[k][0] - cf[k][0], ca[k][1] - cf[k][1]) for k in ca}
    diff = {k: v for k, v in diff.items() if v != (0, 0)}
    nonneg = all(o >= 0 and n >= 0 for o, n in diff.values())
    strict = any(o > 0 or n > 0 for o, n in diff.values())
    return nonneg and strict, diff


def region(sg, ref, D, acts, att, names):
    sym = {n: sp.Symbol(n, nonnegative=True) for n in names}
    lam = sp.Symbol("lam", nonnegative=True)

    def sc(s):
        c = coefficients(sg, ref, s, D, acts)
        return sp.expand(sum(sym[k] * (sp.Integer(o) + lam * sp.Integer(n))
                             for k, (o, n) in c.items()))
    sa = sc(att)
    ineqs = []
    for p in ref.nodes("seg"):
        for v in ALPHABET:
            if ref.real.get(p) == v:
                continue
            t = ref.with_real(p, v)
            if all(t.real[n] == att.real.get(n) for n in t.order["seg"]):
                continue
            d = sp.simplify(sc(t) - sa)
            if d != 0:
                ineqs.append(d)
    ineqs.append(sp.simplify(sc(ref) - sa) if ref.real != att.real else None)
    ineqs = [i for i in ineqs if i is not None and i != 0]
    tails = [sp.expand(2 * sym["ID_SEG"] - sa), sp.expand(sym["DEP"] - sa)]
    return sa, sorted({str(i) for i in ineqs}), [str(t) for t in tails]


def _emit_wolfram(rec, names):
    ren = {n: "w" + n.replace("_", "").capitalize() for n in names}

    def wl(e):
        e = e.replace("**", "^")
        for n in sorted(names, key=len, reverse=True):
            e = __import__("re").sub(r"\b" + n + r"\b", ren[n], e)
        return e
    L = ["vars = {" + ", ".join(ren[n] for n in names) + ", lam};",
         "nonneg = And @@ (# >= 0 & /@ vars);"]
    cons = []
    for cid, g in sorted(rec["region"].items()):
        cons += [wl(s) + " > 0" for s in g["strictly_positive_required"]]
        cons += [wl(s) + " > 0" for s in g["tail_bounds_required"]]
    L += ["cons = And[", ",\n".join("  " + c for c in cons), "];"]
    L.append("wsub = {" + ", ".join(f"{ren[k]} -> {v}" for k, v in sorted(W.items()))
             + ", lam -> 1/8};")
    L.append("control = wMutdor*lam < wIddor + wIdseg;")
    L.append("wv = DeleteCases[vars, lam];")
    L.append('root = NestWhile[ParentDirectory, DirectoryName[$InputFileName], !(DirectoryQ[FileNameJoin[{#, "python"}]] && DirectoryQ[FileNameJoin[{#, "wolfram"}]]) &, 1, 8];\noutdir = FileNameJoin[{root, "results", "requirements", "wolfram"}];\nIf[!DirectoryQ[outdir], CreateDirectory[outdir, CreateIntermediateDirectories -> True]];')
    L.append('res = <|"witness_satisfies_all" -> ToString[And @@ (List @@ cons /. wsub), InputForm], "feasible_lambda_with_control" -> ToString[Reduce[Exists[Evaluate[wv], nonneg && cons && control] && lam >= 0, lam, Reals], InputForm], "feasible_lambda_without_control" -> ToString[Reduce[Exists[Evaluate[wv], nonneg && cons] && lam >= 0, lam, Reals], InputForm]|>;')
    L.append('Export[FileNameJoin[{outdir, "transient_environments_region.json"}], res, "JSON"];')
    L.append('Print[res];')
    d = paths.GENERATED_WOLFRAM
    d.mkdir(parents=True, exist_ok=True)
    d.mkdir(parents=True, exist_ok=True)
    (d / "transient_environments_region.wl").write_text("\n".join(L))


def main():
    sg = sigma()
    names = sorted(declarations("plain"))
    rec = {"cell_table": cell_table(), "weights": W, "lambda": str(LAM),
           "configurations": {}, "bounding": {}, "selection": {},
           "recoding": {}, "region": {}, "control_created_cluster": {}}

    for variant in ("plain", "lookahead", "duplicated"):
        D = declarations(variant)
        rec["bounding"][variant] = {}
        rec["selection"][variant] = {}
        for cid in EPEN:
            ref = config(cid)
            att = struct(ARAPAHO[cid][0], CONFIGS[cid][1])
            acts = activation(sg, ref, D)
            ok, diff = bounding(sg, ref, D, acts, att)
            rec["bounding"][variant][cid] = {
                "attested_bounded_by_faithful": ok,
                "coefficient_difference": {k: list(v) for k, v in diff.items()}}
            t0 = time.time()
            mi, ce = bb_search(sg, ref, D, W, LAM, ALPHABET, incumbent=att)
            forms = ["".join(str(m.real[n]) for n in m.order["seg"]) for m in mi]
            tgt = "".join(ARAPAHO[cid][0])
            rec["selection"][variant][cid] = {
                "faithful": str(score(coefficients(sg, ref, ref, D, acts), W, LAM)),
                "attested": str(score(coefficients(sg, ref, att, D, acts), W, LAM)),
                "best": ce["best"], "minima": forms,
                "attested_is_unique_minimum": len(mi) == 1 and forms[0] == tgt,
                "search": {k: ce[k] for k in ("status", "delta_sub", "delta_ins",
                                              "incumbent_bound", "kmax",
                                              "leaves_scored")},
                "seconds": round(time.time() - t0, 1)}

    D = declarations("duplicated")
    for cid in EPEN:
        ref = config(cid)
        att = struct(ARAPAHO[cid][0], CONFIGS[cid][1])
        acts = activation(sg, ref, D)
        sa, ineqs, tails = region(sg, ref, D, acts, att, names)
        rec["region"][cid] = {"attested_score": str(sa),
                              "strictly_positive_required": ineqs,
                              "tail_bounds_required": tails}

    for mode in ("skip", "stop"):
        D = declarations("duplicated", pv_mode=mode)
        out = {}
        for cid in EPEN:
            ref = config(cid); att = struct(ARAPAHO[cid][0], CONFIGS[cid][1])
            mi, _ = bb_search(sg, ref, D, W, LAM, ALPHABET, incumbent=att)
            forms = ["".join(str(m.real[n]) for n in m.order["seg"]) for m in mi]
            out[cid] = len(mi) == 1 and forms[0] == "".join(ARAPAHO[cid][0])
        rec["recoding"][mode] = out

    ref = config("MADE1"); n = ref.order["seg"]
    dele = ref.with_real(n[3], ABSENT)
    both = dele.with_real(n[2], "tʃ")
    for variant in ("plain", "duplicated"):
        D = declarations(variant); acts = activation(sg, ref, D)
        s0 = score(coefficients(sg, ref, ref, D, acts), W, LAM)
        s1 = score(coefficients(sg, ref, dele, D, acts), W, LAM)
        s2 = score(coefficients(sg, ref, both, D, acts), W, LAM)
        w, lam = sp.symbols("MUT_DOR lam", nonnegative=True)
        idd, ids = sp.symbols("ID_DOR ID_SEG", nonnegative=True)
        rec["control_created_cluster"][variant] = {
            "faithful": str(s0), "deletion_only": str(s1),
            "deletion_and_mutation": str(s2),
            "mutation_blocked": s1 < s2,
            "condition": str(sp.Lt(lam * w, idd + ids)) if variant == "duplicated" else "vacuous"}

    sym = {n: sp.Symbol(n, nonnegative=True) for n in names}
    lam = sp.Symbol("lam", nonnegative=True)
    D = declarations("plain")
    rec["supplied_trigger"] = {}
    for cid in LEX:
        ref = config(cid); n = ref.order["seg"]
        tr, loc = LEX_TRIGGER[cid]
        att = struct(ARAPAHO[cid][0], CONFIGS[cid][1])
        base = ref.with_real(n[tr], ABSENT)
        mut = base.with_real(n[loc], att.real[n[loc]])
        acts = activation(sg, ref, D)
        cb = coefficients(sg, ref, base, D, acts)
        cm = coefficients(sg, ref, mut, D, acts)

        def e(c):
            return sp.expand(sum(sym[q] * (sp.Integer(o) + lam * sp.Integer(nn))
                                 for q, (o, nn) in c.items()))
        d = sp.simplify(e(cm) - e(cb))
        rec["supplied_trigger"][cid] = {
            "unmutated": {q: list(v) for q, v in cb.items() if v != (0, 0)},
            "mutated": {q: list(v) for q, v in cm.items() if v != (0, 0)},
            "mutated_minus_unmutated": str(d),
            "mutation_forced_iff": str(d) + " < 0",
            "at_the_witness": str(score(cm, W, LAM) - score(cb, W, LAM)),
            "mutation_wins_at_the_witness":
                score(cm, W, LAM) < score(cb, W, LAM),
            "matches_surface": "".join(str(mut.real[x]) for x in mut.order["seg"])
                               == "".join(ARAPAHO[cid][0])}

    rec["refuted_extensions"] = {}
    Dn = declarations("no_trigger")
    out = []
    for cid, idx, new in (("RND1", 2, "s"), ("RND1", 0, "b"), ("RND2", 3, "b")):
        ref = config(cid); n = ref.order["seg"]
        acts = activation(sg, ref, Dn)
        mut = ref.with_real(n[idx], new)
        sf = score(coefficients(sg, ref, ref, Dn, acts), W, LAM)
        sm = score(coefficients(sg, ref, mut, Dn, acts), W, LAM)
        out.append({"configuration": cid, "position": idx,
                    "change": f"{ref.real[n[idx]]}->{new}",
                    "retained_bit": bool(acts["MUT_DOR"].get(n[idx], False)),
                    "faithful": str(sf), "mutated": str(sm),
                    "mutation_wins": sm < sf,
                    "attested_is_the_faithful_one": True})
    rec["refuted_extensions"]["no_trigger"] = {
        "description": "the activation drops the trigger conjunct altogether",
        "verdict": "refuted by attested controls",
        "rows": out}
    Dl = declarations("lookahead")
    rows = {}
    for cid in EPEN:
        ref = config(cid); att = struct(ARAPAHO[cid][0], CONFIGS[cid][1])
        mi, _ = bb_search(sg, ref, Dl, W, LAM, ALPHABET, incumbent=att)
        f0 = "".join(str(mi[0].real[x]) for x in mi[0].order["seg"])
        rows[cid] = {"selected": f0,
                     "matches_surface": len(mi) == 1 and f0 == "".join(ARAPAHO[cid][0])}
    rec["refuted_extensions"]["lookahead"] = {
        "description": "a search slot for a front vowel anywhere later in the word",
        "verdict": "refuted: repairs one configuration, leaves two bounded, and "
                   "selects the form the source stars at the attested control",
        "rows": rows}

    Dp = declarations("plain")
    rec["syncope"] = {}
    for cid in LEX:
        ref = config(cid); n = ref.order["seg"]; tr, loc = LEX_TRIGGER[cid]
        att = struct(ARAPAHO[cid][0], CONFIGS[cid][1])
        keep = ref.with_real(n[loc], att.real[n[loc]])
        drop = keep.with_real(n[tr], ABSENT)
        acts = activation(sg, ref, Dp)

        def ee(c):
            return sp.expand(sum(sym[q] * (sp.Integer(o) + lam * sp.Integer(nn))
                                 for q, (o, nn) in c.items()))
        d = sp.simplify(ee(coefficients(sg, ref, drop, Dp, acts))
                        - ee(coefficients(sg, ref, keep, Dp, acts)))
        rec["syncope"][cid] = {"drop_minus_keep": str(d),
                               "trigger_deleted_iff": str(d) + " < 0"}

    for cid in CONFIGS:
        rec["configurations"][cid] = {
            "input": "".join(CONFIGS[cid][0]), "morphs": CONFIGS[cid][1],
            "surface": "".join(ARAPAHO[cid][0]), "status": ARAPAHO[cid][1]}

    OUT.mkdir(parents=True, exist_ok=True)
    (OUT / "transient_environments.json").write_text(
        json.dumps(rec, ensure_ascii=False, indent=1))
    _emit_wolfram(rec, names)

    print("cells:", rec["cell_table"])
    for variant in ("plain", "lookahead", "duplicated"):
        print(f"\n--- {variant}")
        for cid in sorted(rec["selection"][variant]):
            s = rec["selection"][variant][cid]
            b = rec["bounding"][variant][cid]
            print(f"  {cid}: faithful={s['faithful']:>3} attested={s['attested']:>3} "
                  f"best={s['best']:>3} unique_attested={str(s['attested_is_unique_minimum']):5} "
                  f"bounded={b['attested_bounded_by_faithful']}")
    print("\n--- the supplied-trigger completion, plain declaration")
    for cid in LEX:
        s = rec["supplied_trigger"][cid]
        print(f"  {cid}: mutated - unmutated = {s['mutated_minus_unmutated']:<40} "
              f"wins={s['mutation_wins_at_the_witness']} surface={s['matches_surface']}")
    print("\nrefuted extensions:")
    print("   no_trigger:", [(r["configuration"], r["change"], r["mutation_wins"])
                             for r in rec["refuted_extensions"]["no_trigger"]["rows"]])
    print("   lookahead :", {k: v["matches_surface"]
                             for k, v in rec["refuted_extensions"]["lookahead"]["rows"].items()})
    print("\nsyncope needed by the supplied-trigger completion:")
    for cid in LEX:
        print(f"   {cid}: {rec['syncope'][cid]['trigger_deleted_iff']}")
    print("\nrecoding:", rec["recoding"])
    print("control, created cluster:",
          {k: v["mutation_blocked"] for k, v in rec["control_created_cluster"].items()})


if __name__ == "__main__":
    main()
