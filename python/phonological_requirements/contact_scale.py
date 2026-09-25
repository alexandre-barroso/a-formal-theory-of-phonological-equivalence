from __future__ import annotations
from phonological_requirements import certificate, paths

import itertools
import json
from fractions import Fraction as F
from pathlib import Path

from .core import ABSENT
from .evaluate import activation, coefficients, score
from .frag_contact import (CONS, agree_voice, contact_threshold, ident_feats, ident_length, ident_place,
                           ident_seg, ident_son, linearity, max_c, nasal_place, no_geminate, no_long_v,
                           no_tl, sigma, stress_to_weight, struct)

OUT = paths.CERTIFICATES
LAM = F(1, 8)
KS = list(range(-7, 7))
ALT = ["t", "d", "s", "z", "n", "l", "r", "p", "b", "f", "m", "k", "g", "ŋ", "j", "w", "ʃ", "ʒ"]


def family():
    return {f"CONTACT_LE_{k:+d}": contact_threshold(k) for k in KS}


def cost_profile(W):
    return {d: sum(W.get(f"CONTACT_LE_{k:+d}", 0) for k in KS if d > k) for d in range(-7, 8)}


def tokens(s):
    out = []
    for ch in s:
        if ch == "ː":
            out[-1] = out[-1] + "ː"
        elif ch == "ʰ":
            out.append("ʰ")
        elif out and out[-1] == "ʰ":
            out[-1] = "ʰ" + ch
        elif ch in ".-'":
            continue
        elif ch in "aeiouyɯœ" and out and out[-1][0] in "aeiouyɯœ" and not out[-1].endswith("ː"):
            out[-1] = out[-1] + ch
        else:
            out.append(ch)
    return out


def syllabify(segs):
    syl, k = [], 0
    for i, s in enumerate(segs):
        v = s[0] in "aeiouyɯœ"
        if not v and i + 1 < len(segs) and segs[i + 1][0] in "aeiouyɯœ" and i > 0:
            k += 1
        syl.append(k)
    return syl


def render(s, boundary_after=None):
    nodes = [n for n in s.order["seg"] if s.real[n] != ABSENT]
    out = []
    for i, n in enumerate(nodes):
        out.append(str(s.real[n]).lstrip("'"))
        if boundary_after is not None and i == boundary_after:
            out.append(".")
    return "".join(out)


def cands_desonorise(form):
    stem, suf = form.split("-")
    segs = tokens(stem) + tokens(suf)
    syl = syllabify(tokens(stem))
    syl = syl + [syl[-1] + 1] * len(tokens(suf))
    sides = [0] * len(tokens(stem)) + [1] * len(tokens(suf))
    ref = struct(segs, syl, sides); nodes = ref.order["seg"]
    ci, oi = len(tokens(stem)) - 1, len(tokens(stem))
    coda_alts = sorted(set(ALT) | {segs[ci]}) if segs[ci] in CONS else [segs[ci]]
    onset_alts = sorted(set(ALT) | {segs[oi]}) if segs[oi] in CONS else [segs[oi]]
    out = []
    for c in coda_alts:
        for o in onset_alts:
            s = ref.with_real(nodes[ci], c).with_real(nodes[oi], o)
            out.append((render(s, ci), s))
    return ref, out


def cands_reorder(form):
    stem, suf = form.split("-")
    segs = tokens(stem) + tokens(suf)
    syl = syllabify(tokens(stem)); syl = syl + [syl[-1] + 1] * len(tokens(suf))
    sides = [0] * len(tokens(stem)) + [1] * len(tokens(suf))
    ref = struct(segs, syl, sides); n = len(segs)
    ci, oi = len(tokens(stem)) - 1, len(tokens(stem))
    out = []
    calts = sorted(set(ALT) | {segs[ci]}); oalts = sorted(set(ALT) | {segs[oi]})
    for swap in (False, True):
        order = list(range(n))
        if swap:
            order[ci], order[oi] = oi, ci
        for c in calts:
            for o in oalts:
                real = list(segs); real[ci] = c; real[oi] = o
                s = struct(real, syl, sides, order=order)
                out.append((render(s, ci), s))
    for c in calts:
        real = list(segs); real[ci] = c + "ː"; real[oi] = ABSENT
        s = struct(real, syl, sides)
        out.append((render_gem(s, ci), s))
    return ref, out


def render_gem(s, ci):
    nodes = [n for n in s.order["seg"] if s.real[n] != ABSENT]
    out = []
    for i, n in enumerate(nodes):
        r = str(s.real[n])
        if r.endswith("ː") and r[:-1] in CONS:
            out.append(r[:-1] + "." + r[:-1])
        else:
            out.append(r.lstrip("'"))
    return "".join(out)


def cands_parse(form_short):
    segs = tokens(form_short)
    vi = next(i for i, s in enumerate(segs) if s[0] in "aeiouyɯœ")
    ci = vi + 1
    base = list(segs); base[vi] = "'" + base[vi].rstrip("ː")
    syl0 = [0] * (ci + 1) + [1] * (len(segs) - ci - 1)
    syl1 = [0] * ci + [1] * (len(segs) - ci)
    sides = [0] * len(segs)
    out = []
    for parse, syl in (("coda", syl0), ("onset", syl1)):
        for long in (False, True):
            real = list(base); real[vi] = base[vi] + ("ː" if long else "")
            s = struct(real, syl, sides)
            out.append((render(s, ci if parse == "coda" else vi), s))
    return out


def unharmonise(form):
    if "." not in form:
        return form
    stem, suf = form.rsplit(".", 1)
    return stem + "." + suf.replace("e", "a").replace("ɯ", "u")


def evaluate(ref, cands, D, W, lam=LAM):
    sg = sigma(); acts = activation(sg, ref, D)
    rows = []
    for name, s in cands:
        cf = coefficients(sg, ref, s, D, acts)
        rows.append((name, cf, score(cf, {k: W.get(k, 0) for k in D}, lam)))
    lo = min(r[2] for r in rows)
    return {"winners": sorted({r[0] for r in rows if r[2] == lo}), "rows": rows}


def geometric(k0, base=3, unit=F(1, 10)):
    W = {}
    for k in KS:
        W[f"CONTACT_LE_{k:+d}"] = unit * F(base) ** (k - k0) if k >= k0 else unit / F(base) ** (k0 - k)
    return W


def lang_desonorise(name, data, k0, extra_w):
    D = family(); D.update({"IDENT": ident_seg("IDENT"), "IDENT_RT": ident_seg("IDENT_RT", side=0),
                            "IDENT_PLACE": ident_place(), "AGREE_VOICE": agree_voice(), "NO_GEMINATE": no_geminate()})
    W = geometric(k0, base=4, unit=F(2)); W.update(extra_w)
    rows = {}
    for stem, outs in data.items():
        for suf, exp in zip(("lar", "ma", "ga") if name == "kazakh" else ("lar", "nu"), outs):
            form = f"{stem}-{suf}"
            ref, cands = cands_desonorise(form)
            e = evaluate(ref, cands, D, W)
            rows[form] = {"winners": e["winners"], "expected": exp, "agrees": e["winners"] == [unharmonise(exp)]}
    return D, W, rows


def sidamo_decls():
    D = family(); D.update({"IDENT": ident_seg("IDENT"), "IDENT_RT": ident_feats("IDENT_RT", ("son", "voice"), side=0),
                            "IDENT_PLACE": ident_place(), "IDENT_PLACE_OBS": ident_place(True),
                            "IDENT_SON": ident_son(), "MAX_C": max_c(),
                            "AGREE_VOICE_OBS": agree_voice(True),
                            "NO_GEMINATE": no_geminate(), "LINEARITY": linearity(), "NASAL_PLACE": nasal_place()})
    from .core import And, Decl, Feat, Not, Resolves, Slot, Scope
    from .frag_contact import T, NEXT_ANY_C, WORD
    D["NO_RN"] = Decl("NO_RN", "Or", (T, NEXT_ANY_C), And((Feat("son", "t", 7), Resolves("a"))),
                      Not(Feat("son", "a", 5)), scope=WORD)
    return D


def parse_decls(tl=False):
    D = family(); D.update({"STRESS_TO_WEIGHT": stress_to_weight(), "NO_LONG_V": no_long_v(),
                            "IDENT_LENGTH": ident_length()})
    if tl:
        D["NO_TL"] = no_tl()
    return D


def run_languages():
    from .observations import FAROESE, ICELANDIC, KAZAKH, KIRGHIZ, KIRGHIZ_59, SIDAMO
    rec = {}
    D, W, rows = lang_desonorise("kazakh", KAZAKH, -1, dict(IDENT=1, IDENT_RT=1000, IDENT_PLACE=100, AGREE_VOICE=1000, NO_GEMINATE=1000))
    rec["kazakh"] = {"threshold": -1, "profile": {k: str(v) for k, v in cost_profile(W).items()}, "forms": rows}
    D, W, rows = lang_desonorise("kirghiz", KIRGHIZ, -4, dict(IDENT=1, IDENT_RT=1000, IDENT_PLACE=100, AGREE_VOICE=1000, NO_GEMINATE=1000))
    for form, exp in KIRGHIZ_59.items():
        ref, cands = cands_desonorise(form)
        e = evaluate(ref, cands, D, W)
        rows[form] = {"winners": e["winners"], "expected": exp, "agrees": e["winners"] == [unharmonise(exp)]}
    rec["kirghiz"] = {"threshold": -4, "profile": {k: str(v) for k, v in cost_profile(W).items()}, "forms": rows}
    D = sidamo_decls()
    W = geometric(-2, base=4, unit=F(60)); W.update(dict(IDENT=3, IDENT_RT=100, IDENT_PLACE=1, IDENT_PLACE_OBS=5, IDENT_SON=40, MAX_C=10,
                                                      AGREE_VOICE_OBS=1000, NO_GEMINATE=3, LINEARITY=2, NASAL_PLACE=50, NO_RN=1000))
    rows = {}
    for form, exp in SIDAMO.items():
        ref, cands = cands_reorder(form)
        e = evaluate(ref, cands, D, W)
        rows[form] = {"winners": e["winners"], "expected": exp, "agrees": e["winners"] == [exp]}
    rec["sidamo"] = {"threshold": -2, "profile": {k: str(v) for k, v in cost_profile(W).items()},
                     "weights": {k: str(v) for k, v in W.items() if not k.startswith("CONTACT")}, "forms": rows}
    for name, data, k0, tl in (("faroese", FAROESE, 4, True), ("icelandic", ICELANDIC, 5, False)):
        D = parse_decls(tl)
        W = geometric(k0, base=16, unit=F(8)); W.update(dict(STRESS_TO_WEIGHT=1000, NO_LONG_V=8, IDENT_LENGTH=F(1, 100), NO_TL=200))
        rows = {}
        for out, dist, parse in data:
            short = out.replace(":", "").replace("ː", "")
            exp = out.replace(":", "ː").replace("'", "")
            for long_in in (False, True):
                cands = cands_parse(short)
                ref = cands[1][1] if long_in else cands[0][1]
                e = evaluate(ref, cands, D, W)
                rows[f"{out} <{'long' if long_in else 'short'} input>"] = {"winners": e["winners"], "expected": exp,
                                                                          "agrees": e["winners"] == [exp], "distance": dist}
        rec[name] = {"threshold": k0, "profile": {k: str(v) for k, v in cost_profile(W).items()}, "forms": rows}
    return rec


def limiting_profiles():
    from .observations import KAZAKH
    D = family(); D.update({"IDENT": ident_seg("IDENT"), "IDENT_RT": ident_seg("IDENT_RT", side=0),
                            "IDENT_PLACE": ident_place(), "AGREE_VOICE": agree_voice(), "NO_GEMINATE": no_geminate()})
    base = dict(IDENT=1, IDENT_RT=1000, IDENT_PLACE=100, AGREE_VOICE=1000, NO_GEMINATE=1000)
    tests = [("kol-lar", "kol.dar"), ("kijar-lar", "kijar.lar"), ("syjek-lar", "syjek.ter"), ("murin-ma", "murin.ba")]
    out = {}
    profiles = {
        "single threshold LE_-1 (step)": {**base, "CONTACT_LE_-1": 10},
        "linear profile (constant increments)": {**base, **{f"CONTACT_LE_{k:+d}": 2 for k in KS}},
        "concave: one step at -4": {**base, "CONTACT_LE_-4": 10},
        "convex geometric at -1 (used above)": {**base, **geometric(-1, base=4, unit=F(2))},
    }
    for pname, W in profiles.items():
        row = {}
        for form, exp in tests:
            ref, cands = cands_desonorise(form)
            e = evaluate(ref, cands, D, W)
            row[form] = {"winners": e["winners"], "expected": exp, "agrees": e["winners"] == [unharmonise(exp)]}
        out[pname] = {"profile": {d: str(v) for d, v in cost_profile(W).items()}, "forms": row,
                      "all_agree": all(r["agrees"] for r in row.values())}
    return out


def regions():
    import numpy as np
    from scipy.optimize import linprog
    from .observations import KAZAKH, KIRGHIZ, KIRGHIZ_59
    out = {}
    D = family(); D.update({"IDENT": ident_seg("IDENT"), "IDENT_RT": ident_seg("IDENT_RT", side=0),
                            "IDENT_PLACE": ident_place(), "AGREE_VOICE": agree_voice(), "NO_GEMINATE": no_geminate()})
    names = sorted(D)
    for lang, data, sufs, extra in (("kazakh", KAZAKH, ("lar", "ma", "ga"), {}), ("kirghiz", KIRGHIZ, ("lar", "nu"), KIRGHIZ_59)):
        ineqs = []
        forms = [(f"{s}-{suf}", exp) for s, outs in data.items() for suf, exp in zip(sufs, outs)] + list(extra.items())
        for form, exp in forms:
            ref, cands = cands_desonorise(form)
            e = evaluate(ref, cands, D, {n: 1 for n in names})
            exp = unharmonise(exp)
            tgt = [r for r in e["rows"] if r[0] == exp]
            assert tgt, (form, exp)
            ct = [F(tgt[0][1][k][0]) + LAM * F(tgt[0][1][k][1]) for k in names]
            for c, cf, _ in e["rows"]:
                if c == exp:
                    continue
                d = [F(cf[k][0]) + LAM * F(cf[k][1]) - x for k, x in zip(names, ct)]
                if all(x == 0 for x in d):
                    continue
                ineqs.append(d)
        A = np.array([[float(x) for x in d] for d in ineqs]); n = len(names)
        def solve(convex):
            c = np.zeros(n + 1); c[-1] = -1.0
            A_ub = np.hstack([-A, np.ones((len(ineqs), 1))]); b_ub = np.zeros(len(ineqs))
            if convex:
                rows_c = []
                for k in KS[:-1]:
                    r = np.zeros(n + 1); r[names.index(f"CONTACT_LE_{k:+d}")] = 1; r[names.index(f"CONTACT_LE_{k+1:+d}")] = -1
                    rows_c.append(r)
                A_ub = np.vstack([A_ub, np.array(rows_c)]); b_ub = np.concatenate([b_ub, np.zeros(len(rows_c))])
            res = linprog(c, A_ub=A_ub, b_ub=b_ub, bounds=[(0, 1000)] * n + [(None, 1.0)], method="highs")
            if res.status != 0 or res.x[-1] <= 1e-9:
                return {"feasible": False}
            w = {k: round(float(v), 4) for k, v in zip(names, res.x[:-1])}
            return {"feasible": True, "slack": round(float(res.x[-1]), 4), "witness": w}
        out[lang] = {"n_inequalities": len(ineqs), "free": solve(False), "convex_increments": solve(True)}
    return out


def main():
    rec = {"languages": (lg := run_languages()), "limiting_profiles": (lp := limiting_profiles()),
           "regions": (rg := regions()), "lambda": str(LAM)}
    OUT.mkdir(parents=True, exist_ok=True)
    certificate.write("contact_scale.json", rec)
    ok = True
    for lang, r in lg.items():
        bad = [k for k, v in r["forms"].items() if not v["agrees"]]
        ok &= not bad
        print(f"1. {lang:10s} threshold {r['threshold']:+d}: {len(r['forms']) - len(bad)}/{len(r['forms'])}"
              + (f"  DISAGREE {[(k, r['forms'][k]['winners']) for k in bad][:6]}" if bad else ""))
    print("2. limiting profiles:")
    for k, v in lp.items():
        print(f"   {k:42s} all agree={v['all_agree']}  " + "; ".join(f"{f}: {r['winners']}" for f, r in v["forms"].items()))
    print("3. regions:")
    for k, v in rg.items():
        print(f"   {k}: free {v['free'].get('feasible')} convex {v['convex_increments'].get('feasible')} ({v['n_inequalities']} inequalities)")
    if not ok:
        raise SystemExit("F05-1: a reproduction failed")


if __name__ == "__main__":
    main()
