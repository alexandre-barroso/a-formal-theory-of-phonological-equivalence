from __future__ import annotations
from phonological_requirements import certificate, paths

import itertools
import json
from fractions import Fraction as F
from pathlib import Path

from .evaluate import activation, coefficients, score
from .frag_voice import GAPPED, EXTRA_PAIRS, VOICED_OBS, VOICELESS_OBS, gap_declarations, sigma, struct

OUT = paths.CERTIFICATES
LAM = F(1, 8)
W_RU = dict(ID_VOICE=1, ID_PRESON_VOICE=80, NO_VOICE=4, AGREE_BOTH=80,
            NO_VOICED_AFF=80, NO_VOICED_DORFRIC=80, NO_VOICED_PALFRIC=80)
W_HU = dict(ID_VOICE=10, ID_PRESON_VOICE=80, NO_VOICE=1, AGREE_BOTH=80,
            NO_VOICED_AFF=80, NO_VOICED_DORFRIC=80, NO_VOICED_PALFRIC=80)

PAIR = {}
for vd, vl in zip(VOICED_OBS, VOICELESS_OBS):
    PAIR[vd] = PAIR[vl] = (vd, vl)
for triples in GAPPED.values():
    for vl, vd, un in triples:
        PAIR[vl] = PAIR[vd] = PAIR[un] = (vd, vl)
for vl, vd in EXTRA_PAIRS:
    PAIR[vl] = PAIR[vd] = (vd, vl)
UNSPEC = {un: (vl, vd) for triples in GAPPED.values() for vl, vd, un in triples}
TO_UNSPEC = {vl: un for triples in GAPPED.values() for vl, vd, un in triples}
DECL_L = gap_declarations(())
DECL_R = gap_declarations(tuple(GAPPED))


def parse(inp: str):
    segs, words, w = [], [], 0
    for ch in inp:
        if ch == " ":
            w += 1
        elif ch != "-":
            segs.append(ch); words.append(w)
    return segs, words


def render(s, words):
    out = []
    for i, n in enumerate(s.order["seg"]):
        if i and words[i] != words[i - 1]:
            out.append(" ")
        out.append(str(s.real[n]))
    return "".join(out)


def evaluate(inp, D, W, lam=LAM, surface_unspecified=False):
    sg = sigma("binary")
    segs, words = parse(inp)
    ref = struct(segs, None, words)
    nodes = ref.order["seg"]
    obs = [i for i, c in enumerate(segs) if c in PAIR]
    acts = activation(sg, ref, D)
    rows = []
    for combo in itertools.product([0, 1, 2], repeat=len(obs)):
        s = ref
        skip = False
        for i, v in zip(obs, combo):
            if v == 2:
                if not (surface_unspecified and segs[i] in UNSPEC):
                    skip = True; break
                val = segs[i]
            else:
                val = PAIR[segs[i]][v]
            s = s.with_real(nodes[i], val)
        if skip:
            continue
        cf = coefficients(sg, ref, s, D, acts)
        rows.append((render(s, words), cf, score(cf, W, lam)))
    lo = min(r[2] for r in rows)
    return {"winners": sorted({r[0] for r in rows if r[2] == lo}), "score": str(lo),
            "n_candidates": len(rows), "rows": rows}


def specified(inp: str) -> str:
    return "".join(UNSPEC[c][0] if c in UNSPEC else c for c in inp)


def lexical_form(inp: str, hypothesis: str) -> str:
    if hypothesis == "L":
        return "".join(TO_UNSPEC.get(c, c) for c in inp)
    return inp


def expected_of(inp: str, out: str) -> str:
    return out.replace("-", "")


def paradigm():
    from .observations import GOUSKOVA_21, GOUSKOVA_OTHER
    cases = {}
    for stem, (r, n, d, t) in GOUSKOVA_21.items():
        cases[f"{stem}-am"] = r; cases[stem] = n
        cases[f"{stem} ʐe"] = d; cases[f"{stem} to"] = t
    cases.update(GOUSKOVA_OTHER)
    rec = {}
    for hyp, D in (("L", DECL_L), ("R", DECL_R)):
        rows = {}
        for inp, out in cases.items():
            lex = lexical_form(inp, hyp)
            e = evaluate(lex, D, W_RU)
            rows[inp] = {"lexical": lex, "winners": e["winners"], "expected": expected_of(inp, out),
                         "agrees": e["winners"] == [expected_of(inp, out)], "score": e["score"],
                         "n_candidates": e["n_candidates"]}
        rec[hyp] = rows
    return rec


def hypotheticals():
    rec = {}
    for inp in ("ǰop", "ɣoda", "ǰop bi"):
        rec[inp] = {"R": evaluate(inp, DECL_R, W_RU)["winners"],
                    "L_if_fed": evaluate(inp, DECL_L, W_RU)["winners"]}
    return rec


def separation():
    rec = {}
    for inp in ("obČa", "adŢi"):
        for wname, W in (("markedness_over_identity", W_RU), ("identity_over_markedness", W_HU)):
            rec[f"{inp} | {wname}"] = {
                "L": evaluate(inp, DECL_L, W)["winners"],
                "R": evaluate(specified(inp), DECL_R, W)["winners"]}
    return rec


def surface_totality():
    rec = {}
    for inp in ("noČ ʐe", "noČ", "noČ-am"):
        e = evaluate(inp, DECL_L, W_RU, surface_unspecified=True)
        rec[inp] = {"winners_with_surface_unspecified": e["winners"],
                    "winners_total_surface": evaluate(inp, DECL_L, W_RU)["winners"],
                    "n_candidates": e["n_candidates"]}
    return rec


def controls():
    rec = {}
    for inp, note in (("noČ Xe", "two gapped segments in one cluster"),
                      ("noČ li", "gapped segment word-final before a sonorant-initial enclitic"),
                      ("aČ ta", "gapped before voiceless"),
                      ("moX ŢaX bi", "gapped segments at three loci, one in an assimilating cluster"),
                      ("boɣ", "a specified voiced dorsal fricative, word-final"),
                      ("boɣ-a", "a specified voiced dorsal fricative, presonorant"),
                      ("roga", "the ordinary velar stop"),
                      ("moX bi", "the unspecified dorsal fricative in an assimilating cluster")):
        rec[inp] = {"note": note, "L": evaluate(inp, DECL_L, W_RU)["winners"],
                    "R": evaluate(specified(inp), DECL_R, W_RU)["winners"]}
    return rec


def inequalities(inp, expected, D, lam=LAM):
    e = evaluate(inp, D, W_RU, lam)
    names = sorted(D)
    ex = [r for r in e["rows"] if r[0] == expected]
    if not ex:
        raise SystemExit(f"{expected!r} is not a candidate for {inp!r}")
    ce = ex[0][1]
    out = []
    for c, cf, _ in e["rows"]:
        if c == expected:
            continue
        diff = tuple(F(cf[k][0] - ce[k][0]) + lam * F(cf[k][1] - ce[k][1]) for k in names)
        if all(d == 0 for d in diff):
            raise SystemExit(f"{c!r} has the same coefficients as {expected!r} for {inp!r}")
        out.append((inp, c, diff))
    return names, out


def region(ineqs, names, bound=100.0):
    import numpy as np
    from scipy.optimize import linprog
    A = np.array([[float(d) for d in diff] for _, _, diff in ineqs])
    n = len(names)
    c = np.zeros(n + 1); c[-1] = -1.0
    A_ub = np.hstack([-A, np.ones((len(ineqs), 1))])
    b_ub = np.zeros(len(ineqs))
    res = linprog(c, A_ub=A_ub, b_ub=b_ub, bounds=[(0, bound)] * n + [(None, 1.0)], method="highs")
    if res.status != 0:
        return {"feasible": False, "status": res.message}
    t = float(res.x[-1])
    w = {k: round(float(v), 4) for k, v in zip(names, res.x[:-1])}
    return {"feasible": t > 1e-9, "slack": round(t, 6), "witness": w}


def exact_check(ineqs, names, w):
    wf = {k: F(str(v)) for k, v in w.items()}
    return all(sum(wf[k] * d for k, d in zip(names, diff)) > 0 for _, _, diff in ineqs)


def pretty(ineq, names):
    inp, c, diff = ineq
    terms = [f"{'+' if d > 0 else '-'} {abs(d)}·{k}" for k, d in zip(names, diff) if d != 0]
    return f"{inp} ≠ {c}:  " + " ".join(terms).lstrip("+ ") + " > 0"


def regions():
    from .observations import GOUSKOVA_21, GOUSKOVA_OTHER
    cases = {}
    for stem, (r, n, d, t) in GOUSKOVA_21.items():
        cases[f"{stem}-am"] = r; cases[stem] = n
        cases[f"{stem} ʐe"] = d; cases[f"{stem} to"] = t
    cases.update(GOUSKOVA_OTHER)
    rec = {}
    for hyp, D in (("L", DECL_L), ("R", DECL_R)):
        allin, names = [], None
        for inp, out in cases.items():
            names, ins = inequalities(lexical_form(inp, hyp), expected_of(inp, out), D)
            allin += ins
        distinct = sorted({tuple(d) for _, _, d in allin})
        reg = region(allin, names)
        rec[hyp] = {"n_inequalities": len(allin), "n_distinct": len(distinct),
                    "region": reg,
                    "witness_exact": exact_check(allin, names, reg["witness"]) if reg.get("witness") else None,
                    "point_weights_exact": exact_check(allin, names, {k: W_RU[k] for k in names}),
                    "distinct_inequalities": [pretty((("", ""), "", d), names)[len(("", "")) + 6:] for d in distinct]}
    sep = {}
    for hyp, D, inp in (("L", DECL_L, "obČa"), ("R", DECL_R, "obča")):
        names, ins = inequalities(inp, "obǰa", D)
        reg = region(ins, names)
        sep[hyp] = {"target": "obǰa", "region": reg,
                    "witness_exact": exact_check(ins, names, reg["witness"]) if reg.get("witness") else None,
                    "inequalities": [pretty(i, names) for i in ins]}
    from .observations import GOUSKOVA_18, GOUSKOVA_18_INPUTS
    names, ins = inequalities("obČa", "obǰa", DECL_L)
    for row in ("a", "b"):
        allin = []
        for u, out in zip(GOUSKOVA_18_INPUTS, GOUSKOVA_18[row][1]):
            allin += inequalities(u, out, DECL_L)[1]
        joint = region(allin + ins, names)
        sep[f"L_joint_with_row_18{row}"] = {
            "region": joint,
            "witness_exact": exact_check(allin + ins, names, joint["witness"]) if joint.get("witness") else None}
    for row, W in (("a", W_RU), ("b", W_HU)):
        sep[f"point_check_row_18{row}"] = {
            u: {"winners": evaluate(u, DECL_L, W)["winners"], "row": out}
            for u, out in zip(GOUSKOVA_18_INPUTS, GOUSKOVA_18[row][1])}
        sep[f"point_check_row_18{row}"]["all_agree"] = all(
            v["winners"] == [v["row"]] for k, v in sep[f"point_check_row_18{row}"].items() if k != "all_agree")
    rec["separation"] = sep
    return rec


def source_typology():
    from . import recon_gouskova as G
    from .observations import GOUSKOVA_18, GOUSKOVA_18_INPUTS, GOUSKOVA_18_SYSTEMS_STATED
    pats = G.factorial_typology(GOUSKOVA_18_INPUTS)
    rows = {}
    for key, (strata, printed) in GOUSKOVA_18.items():
        outs = set()
        for order in G.stratified_orders(strata):
            outs.add(tuple(tuple(G.ot_winners(u, order)) for u in GOUSKOVA_18_INPUTS))
        got = sorted(outs)
        rows[key] = {"printed": list(printed), "reconstructed": [[list(w) for w in o] for o in got],
                     "agrees": got == [tuple((p,) for p in printed)]}
    printed_set = {tuple((p,) for p in printed) for _, printed in GOUSKOVA_18.values()}
    return {"n_patterns_over_24_rankings": len(pats),
            "patterns": {" | ".join("/".join(w) for w in pat): rk for pat, rk in pats.items()},
            "printed_rows": rows,
            "printed_rows_all_reproduced": all(r["agrees"] for r in rows.values()),
            "patterns_not_printed": [" | ".join("/".join(w) for w in pat) for pat in pats if pat not in printed_set],
            "systems_stated_in_text": GOUSKOVA_18_SYSTEMS_STATED}


def source_tableaux():
    from . import recon_gouskova as G
    T = {}
    r13 = ("Id-pson", "*ObsVoice", "Ident")
    T["(13) bok, kod"] = {u: G.ot_winners(u, r13) for u in ("bok", "kod")}
    r15 = ("Id-pson", "Agree", "*ObsVoice", "Ident")
    T["(15) kot bi"] = G.ot_winners("kot bi", r15)
    r19 = ("Id-pson", "Agree", "*VcdAff", "*ObsVoice", "Ident")
    T["(19) noč bi"] = G.ot_winners("noč bi", r19)
    T["(20) ǰop  [the rich-base problem]"] = G.ot_winners("ǰop", r19)
    r46 = ("Agree", "NoVcdPWdCoda", "Id-pson", "*VcdAff", "Ident")
    T["(46) nočbi, bokbi, ǰop  [clitic domain-internal, as printed]"] = {u: G.ot_winners(u, r46) for u in ("nočbi", "bokbi", "ǰop")}
    T["(46) noč bi, bok bi  [clitic outside the PWd, as in (23c)]"] = {u: G.ot_winners(u, r46) for u in ("noč bi", "bok bi")}
    return T


def inertness():
    from .core import read
    from .evaluate import loci
    from .observations import GOUSKOVA_21, GOUSKOVA_OTHER
    sg = sigma("binary")
    cases = [f"{s}{x}" for s in GOUSKOVA_21 for x in ("-am", "", " ʐe", " to")] + list(GOUSKOVA_OTHER)
    checks = defined = 0
    for inp in cases:
        lex = lexical_form(inp, "L")
        segs, words = parse(lex)
        ref = struct(segs, None, words)
        nodes = ref.order["seg"]
        gapped = [n for n, c in zip(nodes, segs) if c in UNSPEC]
        if not gapped:
            continue
        obs = [i for i, c in enumerate(segs) if c in PAIR]
        for combo in itertools.product([0, 1], repeat=len(obs)):
            s = ref
            for i, v in zip(obs, combo):
                s = s.with_real(nodes[i], PAIR[segs[i]][v])
            for name, d in DECL_L.items():
                if d.kind != "faithfulness":
                    continue
                for l in loci(s, d, "seg", ref):
                    if l in gapped:
                        r = read(sg, ref, s, d, l)
                        checks += 1
                        defined += int(bool(r.defined) or r.pressure != 0)
    return {"faithfulness_readings_at_gapped_loci": checks,
            "defined_or_charging": defined}


def main():
    rec = {"paradigm": (par := paradigm()),
           "inertness": (inert := inertness()),
           "hypotheticals": hypotheticals(),
           "separation": separation(),
           "surface_totality": surface_totality(),
           "controls": controls(),
           "regions": regions(),
           "source_typology_18": (ty := source_typology()),
           "source_tableaux": (tb := source_tableaux()),
           "weights": {"markedness_over_identity": W_RU, "identity_over_markedness": W_HU},
           "lambda": str(LAM)}
    OUT.mkdir(parents=True, exist_ok=True)
    certificate.write("gapped_inventory.json", rec)

    for hyp in ("L", "R"):
        bad = [k for k, v in par[hyp].items() if not v["agrees"]]
        print(f"1. paradigm under {hyp}: {len(par[hyp]) - len(bad)}/{len(par[hyp])} agree"
              + (f"; DISAGREE {bad}" if bad else ""))
        for k in bad:
            print("     ", k, par[hyp][k])
    print("2. hypothetical inputs:", rec["hypotheticals"])
    print("3. separation:")
    for k, v in rec["separation"].items():
        print(f"     {k:45s} L={v['L']}  R={v['R']}")
    print("4. surface totality:")
    for k, v in rec["surface_totality"].items():
        print(f"     {k:10s} with unspecified surface -> {v['winners_with_surface_unspecified']}; total surface -> {v['winners_total_surface']}")
    print("5. controls:")
    for k, v in rec["controls"].items():
        print(f"     {k:12s} L={v['L']}  R={v['R']}   ({v['note']})")
    print("6. regions:")
    for hyp in ("L", "R"):
        r = rec["regions"][hyp]
        print(f"     {hyp}: {r['n_inequalities']} inequalities, {r['n_distinct']} distinct; region {r['region']}; witness exact {r['witness_exact']}; point exact {r['point_weights_exact']}")
    for k, v in rec["regions"]["separation"].items():
        if "region" in v:
            print(f"     separation {k}: {v['region']}")
        else:
            print(f"     {k}: all agree = {v['all_agree']}")
    print(f"7. source typology (18): {ty['n_patterns_over_24_rankings']} patterns over 24 rankings; "
          f"printed rows reproduced: {ty['printed_rows_all_reproduced']}; not printed: {ty['patterns_not_printed']}; "
          f"stated in text: {ty['systems_stated_in_text']}")
    print("8. source tableaux:", tb)
    print("9. inertness at gapped loci:", inert)
    if any(not v["agrees"] for h in ("L", "R") for v in par[h].values()) or not ty["printed_rows_all_reproduced"] \
            or inert["defined_or_charging"] != 0:
        raise SystemExit("F01-2: a reproduction failed")


if __name__ == "__main__":
    main()
