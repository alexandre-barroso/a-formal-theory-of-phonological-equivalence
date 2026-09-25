from __future__ import annotations
from phonological_requirements import certificate, paths

import itertools
import json
from fractions import Fraction as F
from pathlib import Path

import sympy as sp

from .core import ABSENT, NodeId, Struct, read
from .evaluate import activation, coefficients, loci, score
from .frag_accent import (build, feature_declarations, insert_after,
                          node_declarations, nuclei, relink, sigma, stressed,
                          surface, unstressed, with_default)

OUT = paths.CERTIFICATES

WN = dict(OSD=30, NONFINAL=4, RIGHTMOST=2, CLASH=20, FLOAT=30, DOCK_PREV=30,
          LOCAL=30, MAX_ACC=12, MAXLINK=5, DEPLINK=1, DEP_ACC=8)
WF = dict(OSD=30, NONFINAL=4, RIGHTMOST=2, CLASH=20, ID_STRESS=8)
WN_CURRENT = {k: F(v, 100) for k, v in dict(
    OSD=201, NONFINAL=101, RIGHTMOST=101, CLASH=201, FLOAT=1,
    DOCK_PREV=301, LOCAL=1, MAX_ACC=301, MAXLINK=201, DEPLINK=101,
    DEP_ACC=1).items()}
LAM = F(1, 8)

CONF = {
 "OWL_SG":  (["b","ee","θ","ei"], [0,0,1,1], [0,0,0,0], [(0, 1)]),
 "OWL_2":   (["h","e","b","ee","θ","ei","b","i","n"],
             [0,0,1,1,2,2,3,3,3], [0,0,1,1,1,1,2,3,3], [(1, 3)]),
 "OWL_3":   (["h","e","b","ee","θ","ei","b","i","n","oo"],
             [0,0,1,1,2,2,3,3,4,4], [0,0,1,1,1,1,2,3,4,4], [(1, 3)]),
 "CHIEF_SG": (["n","ee","c","ee"], [0,0,1,1], [0,0,0,0], []),
 "CHIEF_PL": (["n","ee","c","ee","n","o","ʔ"], [0,0,1,1,2,2,2], [0,0,0,0,0,1,1], []),
 "BULL_SG":  (["h","e","n","ee","c","ee"], [0,0,1,1,2,2], [0,0,0,0,0,0], [(0, 3)]),
 "BULL_PL":  (["h","e","n","ee","c","ee","n","o","ʔ"],
              [0,0,1,1,2,2,3,3,3], [0,0,0,0,0,0,0,1,1], [(0, 3)]),
 "SPRING_LOC": (["h","oo","x","e","b","i","n","e","ʔ"],
                [0,0,1,1,2,2,3,3,3], [0,0,0,0,0,0,0,1,1], [(0, 3), (1, None)]),
 "PUTDOWN_3PL": (["c","ii","n","e","n","ou","ʔ","u"],
                 [0,0,1,1,2,2,3,3], [0,0,0,0,0,1,1,1], [(0, 3), (1, 5)]),
 "BIGFISH": (["ee","b","e","θ","n","o","w","o","ʔ"],
             [0,1,1,1,2,2,3,3,3], [0,0,0,0,1,1,1,1,1], [(0, 2), (1, 5)]),
 "FUT_WALK": (["h","ee","t","n","ii","s","i","s","ee","t"],
              [0,0,0,1,1,2,2,3,3,3], [0,0,0,1,1,1,1,1,1,2], [(0, 1), (1, 4)]),
}


def candidates_node(ref: Struct, D, default_morph: int):
    nuc = nuclei(ref)
    opts = [("absent", None)] + [("float", None)] + [("link", n) for n in nuc]
    for combo in itertools.product(opts, repeat=len(ref.order["acc"])):
        hosts = [h for (k, h) in combo if h is not None]
        if len(hosts) != len(set(hosts)):
            continue
        s = ref
        for a, (kind, host) in zip(ref.order["acc"], combo):
            s = relink(s, a, host, present=(kind != "absent"))
        yield s
        for n in nuc:
            if n not in hosts:
                yield with_default(s, n, default_morph)


def select_node(cid, select="R", W=WN, current=False):
    sg = sigma("node"); D = node_declarations(select)
    segs, syl, mor, acc = CONF[cid]
    ref = build(segs, syl, mor, acc)
    acts = {k: {} for k in D} if current else activation(sg, ref, D)
    best, arg, n = None, [], 0
    for c in candidates_node(ref, D, default_morph=max(mor)):
        n += 1
        v = score(coefficients(sg, ref, c, D, acts), W, F(1) if current else LAM)
        if best is None or v < best:
            best, arg = v, [c]
        elif v == best:
            arg.append(c)
    return sorted({surface(a) for a in arg}), str(best), n


def candidates_feature(ref: Struct):
    nuc = nuclei(ref, sigma("feature"))
    for combo in itertools.product([False, True], repeat=len(nuc)):
        s = ref
        for n, st in zip(nuc, combo):
            base = unstressed(ref.real[n])
            s = s.with_real(n, stressed(base) if st else base)
        yield s


def select_feature(cid, select="R", guarded=True, W=WF):
    sg = sigma("feature"); D = feature_declarations(select, guarded)
    segs, syl, mor, acc = CONF[cid]
    hosts = {h for (_m, h) in acc if h is not None}
    segs = [stressed(v) if i in hosts else v for i, v in enumerate(segs)]
    ref = build(segs, syl, mor, [])
    acts = activation(sg, ref, D)
    best, arg = None, []
    for c in candidates_feature(ref):
        v = score(coefficients(sg, ref, c, D, acts), W, LAM)
        if best is None or v < best:
            best, arg = v, [c]
        elif v == best:
            arg.append(c)
    def surf(s):
        out, prev = [], None
        for n in s.order["seg"]:
            if prev is not None and s.dom[n]["syll"] != s.dom[prev]["syll"]:
                out.append(".")
            out.append(s.real[n]); prev = n
        return __import__("unicodedata").normalize("NFC", "".join(out))
    return sorted({surf(a) for a in arg}), str(best)


def window_strictness():
    out = {}
    segs, syl, mor = ["t","a","k","a"], [0,0,1,1], [0,0,0,0]
    sgn = sigma("node"); Dn = node_declarations()
    refn = build(segs, syl, mor, [])
    r = read(sgn, refn, refn, Dn["OSD"], refn.order["seg"][3])
    out["node, two syllables, no accent"] = dict(C=int(r.context), Def=int(r.defined),
                                                G=int(r.good), p=r.pressure)
    sgf = sigma("feature")
    reff = build(segs, syl, mor, [])
    for g in (True, False):
        Df = feature_declarations(guarded=g)
        r = read(sgf, reff, reff, Df["OSD"], reff.order["seg"][3])
        out[f"feature, two syllables, no stress, guarded={g}"] = dict(
            C=int(r.context), Def=int(r.defined), G=int(r.good), p=r.pressure)
    return out


def epenthesis_region():
    from .core import And, Decl, Feat, Not, Or_, Present, Resolves, Slot, Scope
    from .frag_accent import T, TA, H, WORD
    sg = sigma("node")
    D = node_declarations()
    A0T = Slot("a", "Acc", "trigger", kind="assoc", relation="assoc", tier="acc")
    sync = Decl("SYNC", "Or", (T, A0T),
                And((Feat("nuclear", "t", True), Feat("high", "t", True),
                     Feat("long", "t", False), Not(Resolves("a")))),
                Not(Present("t")), scope=WORD)
    NXT = Slot("n", "Or", "trigger", kind="step", relation="succ", scope=WORD,
               direction=+1, policy="dynamic")
    NXS = Slot("n", "Or", "subject", kind="step", relation="succ", scope=WORD,
               direction=+1, policy="dynamic")
    nocoda = Decl("NOCODA", "Or", (T, NXS),
                  Feat("nuclear", "t", False),
                  Or_((Not(Present("t")), Not(Resolves("n")),
                       Feat("nuclear", "n", True))), scope=WORD)
    from .core import Made
    dep = Decl("DEP", "Or", (T,), Made("t"),
               Or_((Not(Made("t")), Not(Present("t")))), kind="faithfulness")
    D = dict(D); D.update({"SYNC": sync, "NOCODA": nocoda, "DEP": dep})
    names = sorted(D)
    sym = {k: sp.Symbol(k, nonnegative=True) for k in names}
    lam = sp.Symbol("lam", nonnegative=True)

    def sc(ref, s, acts):
        c = coefficients(sg, ref, s, D, acts)
        return sp.expand(sum(sym[k] * (sp.Integer(o) + lam * sp.Integer(nn))
                             for k, (o, nn) in c.items())), c

    rows = {}
    ref = build(["c","e","w","s","ee"], [0,0,0,1,1], [0,0,0,1,1], [(1, None)])
    acts = activation(sg, ref, D)
    n = ref.order["seg"]; a = ref.order["acc"][0]
    ins = insert_after(ref, 2, "i", syll=1, morph=0)
    mi = ins.order["seg"][3]
    cands = {
        "no epenthesis, accent on e (previous morph)": relink(ref, a, n[1]),
        "no epenthesis, accent floats": ref,
        "no epenthesis, accent on ee (own morph)": relink(ref, a, n[4]),
        "epenthesis, accent on the epenthetic i": relink(ins, a, mi),
        "epenthesis, accent on e": relink(ins, a, n[1]),
    }
    rows["WALK_ALONG"] = {k: {"surface": surface(v), "score": str(sc(ref, v, acts)[0]),
                              "coefficients": {q: list(x) for q, x in sc(ref, v, acts)[1].items() if x != (0, 0)}}
                          for k, v in cands.items()}
    ref = build(["w","oo","x","h","oo","x"], [0,0,0,1,1,1], [0]*6, [(0, 1)])
    acts = activation(sg, ref, D)
    n = ref.order["seg"]; a = ref.order["acc"][0]
    ins = insert_after(ref, 2, "u", syll=1, morph=0)
    mi = ins.order["seg"][3]
    cands = {"faithful": ref,
             "epenthesis, vowel unaccented": ins,
             "epenthesis, accent moved onto it": relink(ins, a, mi)}
    rows["HORSE"] = {k: {"surface": surface(v), "score": str(sc(ref, v, acts)[0]),
                         "coefficients": {q: list(x) for q, x in sc(ref, v, acts)[1].items() if x != (0, 0)}}
                     for k, v in cands.items()}
    ref = build(["n","e","w","o","ʔ","ei","n"], [0,0,1,1,2,2,2], [0,0,1,1,1,1,1],
                [(1, None), (1, 5)])
    acts = activation(sg, ref, D)
    n = ref.order["seg"]; a0, a1 = ref.order["acc"]
    ins = insert_after(ref, 1, "i", syll=1, morph=0)
    mi = ins.order["seg"][2]
    cands = {"no epenthesis, accent on e (previous morph)": relink(ref, a0, n[1]),
             "epenthesis, accent on the epenthetic i": relink(ins, a0, mi)}
    rows["NECKLACE"] = {k: {"surface": surface(v), "score": str(sc(ref, v, acts)[0]),
                            "coefficients": {q: list(x) for q, x in sc(ref, v, acts)[1].items() if x != (0, 0)}}
                        for k, v in cands.items()}
    return rows


def regions(select="R"):
    from .observations import ARAPAHO_ACCENT as OBS
    sg = sigma("node"); D = node_declarations(select)
    names = sorted(D)
    sym = {k: sp.Symbol(k, nonnegative=True) for k in names}
    lam = sp.Symbol("lam", nonnegative=True)
    out = {}
    for cid, (segs, syl, mor, acc) in CONF.items():
        ref = build(segs, syl, mor, acc)
        acts = activation(sg, ref, D)
        by_surface = {}
        for c in candidates_node(ref, D, default_morph=max(mor)):
            cf = coefficients(sg, ref, c, D, acts)
            e = sp.expand(sum(sym[k] * (sp.Integer(o) + lam * sp.Integer(nn))
                              for k, (o, nn) in cf.items()))
            by_surface.setdefault(surface(c), set()).add(e)
        att = OBS[cid][0]
        if att not in by_surface:
            out[cid] = {"attested_generated": False}
            continue
        rivals = {s: es for s, es in by_surface.items() if s != att}
        alts = []
        for e_att in by_surface[att]:
            ineqs = sorted({str(sp.simplify(e_r - e_att)) for es in rivals.values() for e_r in es})
            alts.append(ineqs)
        alts.sort()
        out[cid] = {"attested_generated": True, "attested": att,
                    "n_surfaces": len(by_surface), "n_attested_candidates": len(by_surface[att]),
                    "alternatives": alts}
    return out


def emit_wolfram(reg, epen):
    import re
    names = sorted(node_declarations())
    ren = {n: "w" + n.replace("_", "").capitalize() for n in names}
    ren.update({"SYNC": "wSync", "NOCODA": "wNocoda", "DEP": "wDep"})

    def wl(e):
        e = e.replace("**", "^")
        for n in sorted(ren, key=len, reverse=True):
            e = re.sub(r"\b" + n + r"\b", ren[n], e)
        return e
    L = ["vars = {" + ", ".join(sorted(set(ren.values()))) + ", lam};",
         "nonneg = And @@ (# >= 0 & /@ vars);"]
    wname = {cid: "c" + cid.lower().replace("_", "") for cid in reg}
    for cid, r in reg.items():
        if not r.get("attested_generated"):
            L.append(f"{wname[cid]} = False;")
            continue
        alts = ["And[" + ", ".join(wl(i) + " > 0" for i in a) + "]" for a in r["alternatives"]]
        L.append(f"{wname[cid]} = Or[" + ", ".join(alts) + "];")
    ids = [wname[c] for c in reg]
    L.append("all = And[" + ", ".join(ids) + "];")
    L.append("nobig = And[" + ", ".join(i for i in ids if i != wname["BIGFISH"]) + "];")
    L.append("noshift = And[" + ", ".join(i for i in ids if i not in (wname["BIGFISH"], wname["SPRING_LOC"])) + "];")
    L.append("nodel = And[" + ", ".join(i for i in ids if i != wname["PUTDOWN_3PL"]) + "];")
    L.append("pairSP = And[" + wname["SPRING_LOC"] + ", " + wname["PUTDOWN_3PL"] + "];")
    L.append("pairBP = And[" + wname["BIGFISH"] + ", " + wname["PUTDOWN_3PL"] + "];")
    tgt = {"WALK_ALONG": "epenthesis, accent on the epenthetic i",
           "HORSE": "faithful", "NECKLACE": "no epenthesis, accent on e (previous morph)"}
    ep = []
    for inp, cs in epen.items():
        a = cs[tgt[inp]]["score"]
        for k, v in cs.items():
            if k != tgt[inp]:
                ep.append(f"({wl(v['score'])}) - ({wl(a)}) > 0")
    L.append("epen = And[" + ", ".join(ep) + "];")
    L.append("wv = DeleteCases[vars, lam];")
    L.append('region[e_, t_] := TimeConstrained[Reduce[Exists[Evaluate[wv], nonneg && e] && lam >= 0, lam, Reals], t, "TIMEOUT"];')
    L.append('pointwise[e_, t_] := Table[{ToString[l0, InputForm], ToString[TimeConstrained[Resolve[Exists[Evaluate[wv], (nonneg && e) /. lam -> l0], Reals], t, "TIMEOUT"], InputForm]}, {l0, {0, 1/16, 1/8, 1/4, 1/2, 1}}];')
    L.append("deletionWitness = {wClash -> 4 + 2/lam, wDep -> 1, wDeplink -> 1, wDepacc -> 0, wDockprev -> 3, wFloat -> 0, wLocal -> 0, wMaxlink -> 1, wMaxacc -> 0, wNocoda -> 2, wNonfinal -> 1/lam, wOsd -> 2 + 2/lam, wRightmost -> 2/lam, wSync -> 0};")
    L.append('deletionChecks = Table[TimeConstrained[Resolve[ForAll[lam, Implies[lam > 0, c /. deletionWitness]], Reals], 60, "TIMEOUT"], {c, {nonneg, nodel, epen}}];')
    L.append('deletionZero = TimeConstrained[Resolve[Exists[Evaluate[wv], (nonneg && cowl3) /. lam -> 0], Reals], 60, "TIMEOUT"];')
    L.append('deletionRegion = If[deletionChecks === {True, True, True} && deletionZero === False, lam > 0, "UNVERIFIED"];')
    L.append("show[x_] := ToString[x, InputForm];")
    L.append("pairSPRegion = region[pairSP, 300]; pairBPRegion = region[pairBP, 300];")
    L.append('implied[x_] := If[pairSPRegion === False, "False", show[x]];')
    L.append('root = NestWhile[ParentDirectory, DirectoryName[$InputFileName], !(DirectoryQ[FileNameJoin[{#, "python"}]] && DirectoryQ[FileNameJoin[{#, "wolfram"}]]) &, 1, 8];')
    L.append('outdir = FileNameJoin[{root, "results", "requirements", "wolfram"}];')
    L.append('If[!DirectoryQ[outdir], CreateDirectory[outdir, CreateIntermediateDirectories -> True]];')
    per = ", ".join(f'"{cid}" -> show[region[{wname[cid]}, 120]]' for cid in reg)
    L.append('res = <|"per_configuration" -> <|' + per + '|>, '
             '"spring_loc_with_putdown_3pl" -> show[pairSPRegion], "bigfish_with_putdown_3pl" -> show[pairBPRegion], '
             '"epenthesis" -> show[region[epen, 300]], '
             '"all_eleven" -> implied[all], "without_bigfish" -> implied[nobig], "all_but_bigfish_with_epenthesis" -> implied[nobig && epen], '
             '"shift_regime" -> show[region[noshift && epen, 600]], "shift_regime_points" -> pointwise[noshift && epen, 120], '
             '"deletion_regime" -> show[deletionRegion], "deletion_witness_checks" -> deletionChecks, "deletion_zero_feasible" -> deletionZero, "deletion_regime_points" -> pointwise[nodel && epen, 120]|>;')
    L.append('Export[FileNameJoin[{outdir, "accent_encoding_regions.json"}], res, "JSON"];')
    L.append("Print[res];")
    d = paths.GENERATED_WOLFRAM; d.mkdir(parents=True, exist_ok=True)
    (d / "accent_encoding_regions.wl").write_text("\n".join(L))


def main():
    rec = {"weights_node": WN, "weights_feature": WF, "lambda": str(LAM),
           "weights_current": {k: str(v) for k, v in WN_CURRENT.items()},
           "node": {}, "node_current": {}, "node_select_L": {},
           "feature": {}, "feature_unguarded": {}}
    for cid in CONF:
        forms, best, n = select_node(cid, "R")
        rec["node"][cid] = {"minima": forms, "score": best, "candidates": n}
        forms, best, n = select_node(cid, W=WN_CURRENT, current=True)
        rec["node_current"][cid] = {"minima": forms, "score": best, "candidates": n}
        forms, best, n = select_node(cid, "L")
        rec["node_select_L"][cid] = {"minima": forms, "score": best}
        forms, best = select_feature(cid, "R", True)
        rec["feature"][cid] = {"minima": forms, "score": best}
        forms, best = select_feature(cid, "R", False)
        rec["feature_unguarded"][cid] = {"minima": forms, "score": best}
    rec["window_strictness"] = window_strictness()
    rec["epenthesis"] = epenthesis_region()
    rec["regions"] = regions("R")
    emit_wolfram(rec["regions"], rec["epenthesis"])
    OUT.mkdir(parents=True, exist_ok=True)
    certificate.write("accent_encoding.json", rec)
    for k in ("node", "node_select_L", "feature", "feature_unguarded"):
        print(f"--- {k}")
        for cid, v in rec[k].items():
            print(f"  {cid:12s} {v['minima']}  ({v['score']})")
    print("--- regions (node, select R):")
    for cid, r in rec["regions"].items():
        if r.get("attested_generated"):
            print(f"  {cid:12s} attested {r['attested']:22s} surfaces={r['n_surfaces']} "
                  f"attested-candidates={r['n_attested_candidates']} "
                  f"inequalities={[len(a) for a in r['alternatives']]}")
        else:
            print(f"  {cid:12s} attested surface NOT generated by any candidate")
    print("--- window strictness:", rec["window_strictness"])
    print("--- epenthesis:")
    for inp, cs in rec["epenthesis"].items():
        print("  ", inp)
        for k, v in cs.items():
            print(f"     {k:46s} {v['surface']:12s} {v['score']}")


if __name__ == "__main__":
    main()
