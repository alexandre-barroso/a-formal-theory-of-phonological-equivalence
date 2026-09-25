from __future__ import annotations
from phonological_requirements import certificate, paths

import itertools
import json
from fractions import Fraction as F
from pathlib import Path

from .evaluate import activation, coefficients, score
from .frag_antigem import max_v, ocp, sigma, struct, syncope

OUT = paths.CERTIFICATES
LAM = F(1, 8)
W_BLOCK = dict(OCP=100, SYNCOPE=10, MAX_V=1)
SETTINGS = {
    "afar": ("morph", "segment", "single", W_BLOCK),
    "tonkawa": ("morph", "segment", "single", W_BLOCK),
    "tiberian": ("morph", "segment", "single", W_BLOCK),
    "modern_hebrew": ("morph", "segment", "single", W_BLOCK),
    "iraqi": ("morph", "segment", "cluster", W_BLOCK),
    "damascene": ("word", ("place", "manner"), "none", W_BLOCK),
    "yupik": ("word", "segment", "single", W_BLOCK),
    "chevak": ("lexdom", "segment", "single", W_BLOCK),
    "akkadian": ("morph", "segment", "single", dict(OCP=10, SYNCOPE=10, MAX_V=1)),
}


def parse(form: str):
    segs, morphs, lex = [], [], []
    m = d = 0
    for ch in form:
        if ch == "-":
            m += 1
        elif ch == "=":
            m += 1; d += 1
        elif ch in "ˈ`´ʹ'":
            continue
        else:
            segs.append(ch); morphs.append(m); lex.append(d)
    return segs, morphs, lex


def render(s, morphs, lex, form):
    out, i = [], 0
    nodes = s.order["seg"]
    k = 0
    for ch in form:
        if ch in "-=":
            out.append(ch)
        elif ch in "ˈ`´ʹ'":
            continue
        else:
            v = s.real[nodes[k]]
            if v != "∅" and str(v) != "ABSENT" and s.real[nodes[k]] is not None:
                from .core import ABSENT
                if v != ABSENT:
                    out.append(str(v))
            k += 1
    return "".join(out)


def evaluate(form, scope, identity, W, lam=LAM, adjacency="step", with_ocp=True, left="single"):
    from .core import ABSENT
    segs, morphs, lex = parse(form)
    sg = sigma()
    ref = struct(segs, morphs, lex)
    nodes = ref.order["seg"]
    D = {"SYNCOPE": syncope(left), "MAX_V": max_v()}
    if with_ocp:
        o = ocp(scope, identity, adjacency); D["OCP"] = o
    Wn = {"SYNCOPE": W["SYNCOPE"], "MAX_V": W["MAX_V"], "OCP": W.get("OCP", 0)}
    acts = activation(sg, ref, D)
    weak = [i for i, s in enumerate(segs) if s == "ə"]
    rows = []
    for combo in itertools.product([0, 1], repeat=len(weak)):
        s = ref
        for i, k in zip(weak, combo):
            if k:
                s = s.with_real(nodes[i], ABSENT)
        cf = coefficients(sg, ref, s, D, acts)
        rows.append((render(s, morphs, lex, form), cf, score(cf, Wn, lam)))
    lo = min(r[2] for r in rows)
    return {"winners": sorted({r[0] for r in rows if r[2] == lo}), "score": str(lo), "rows": rows}


def survey():
    from .observations import ANTIGEM
    rec = {}
    for lang, forms in ANTIGEM.items():
        scope, ident, left, W = SETTINGS[lang]
        rows = {}
        for inp, exp in forms:
            e = evaluate(inp, scope, ident, W, left=left)
            rows[inp] = {"winners": e["winners"], "expected": exp, "agrees": e["winners"] == [exp]}
        rec[lang] = {"scope": scope, "identity": ident if isinstance(ident, str) else list(ident),
                     "syncope_left_context": left, "weights": W, "forms": rows, "all_agree": all(r["agrees"] for r in rows.values())}
    return rec


def alternatives():
    from .observations import ANTIGEM
    out = {}
    scope, ident, _left, W = SETTINGS["afar"]
    out["afar_without_surface_OCP"] = {inp: evaluate(inp, scope, ident, W, with_ocp=False)["winners"]
                                      for inp, _ in ANTIGEM["afar"][6:13]}
    out["afar_with_tier_adjacency"] = {inp: evaluate(inp, scope, ident, W, adjacency="search")["winners"]
                                      for inp, _ in ANTIGEM["afar"][:13]}
    out["afar_hetero_under_word_scope"] = {inp: evaluate(inp, "word", ident, W)["winners"]
                                          for inp, _ in ANTIGEM["afar"][13:]}
    out["yupik_under_morph_scope"] = {inp: evaluate(inp, "morph", "segment", W)["winners"]
                                     for inp, _ in ANTIGEM["yupik"][3:]}
    out["damascene_partial_under_full_identity"] = {inp: evaluate(inp, "word", "segment", W, left="none")["winners"]
                                                   for inp, _ in ANTIGEM["damascene"][5:]}
    return out


def blocking_region():
    rows = {}
    for w_ocp in (60, 70, 71, 72, 73, 80, 100):
        W = dict(OCP=w_ocp, SYNCOPE=10, MAX_V=1)
        rows[w_ocp] = evaluate("xarər-e", "morph", "segment", W)["winners"]
    return {"by_w_OCP": rows, "bound": "w_OCP > (w_SYNCOPE - w_MAX)/lambda = 72",
            "coefficients_at_100": {r[0]: {k: list(v) for k, v in r[1].items()}
                                    for r in evaluate("xarər-e", "morph", "segment", dict(OCP=100, SYNCOPE=10, MAX_V=1))["rows"]}}


def main():
    rec = {"survey": (sv := survey()), "alternatives": alternatives(), "blocking_region": blocking_region(),
           "lambda": str(LAM)}
    OUT.mkdir(parents=True, exist_ok=True)
    certificate.write("antigemination.json", rec)
    ok = True
    for lang, r in sv.items():
        bad = [k for k, v in r["forms"].items() if not v["agrees"]]
        ok &= not bad
        print(f"1. {lang:14s} scope={r['scope']:6s} identity={r['identity']}: {len(r['forms']) - len(bad)}/{len(r['forms'])}"
              + (f"  DISAGREE {[(k, r['forms'][k]['winners']) for k in bad]}" if bad else ""))
    print("2. alternatives:")
    for k, v in rec["alternatives"].items():
        print(f"   {k}: {v}")
    print("3. blocking region:", rec["blocking_region"]["by_w_OCP"], rec["blocking_region"]["bound"])
    if not ok:
        raise SystemExit("F03-1: a reproduction failed")


if __name__ == "__main__":
    main()
