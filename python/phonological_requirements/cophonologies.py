from __future__ import annotations
from phonological_requirements import certificate, paths

import itertools
import json
import math
from fractions import Fraction as F
from pathlib import Path

from .core import NodeId, Struct
from .evaluate import activation, coefficients, score
from .frag_phase import (build, melody_declarations, nuclei, set_tone, sigma,
                         surface, tone_declarations)

OUT = paths.CERTIFICATES
LAM = F(1, 8)


def replay():
    from .observations import CBP_TABLEAUX as T
    out = {}
    for name, tb in T.items():
        w = tb["weights"]
        hs = [sum(wi * vi for wi, vi in zip(w, r[1])) for r in tb["rows"]]
        z = sum(math.exp(-h) for h in hs)
        preds = [math.exp(-h) / z for h in hs]
        rows = []
        for r, h, p in zip(tb["rows"], hs, preds):
            rows.append({"candidate": r[0], "H_recomputed": h, "H_printed": r[2],
                         "H_agrees": abs(h - r[2]) < 1e-9,
                         "pred_recomputed": round(p, 3), "pred_printed": r[4],
                         "pred_agrees_to_0.01": abs(p - r[4]) < 0.011})
        out[name] = {"rows": rows,
                     "all_H_agree": all(x["H_agrees"] for x in rows),
                     "all_pred_agree": all(x["pred_agrees_to_0.01"] for x in rows)}
    return out


W_TONE = dict(ALIGN_H_L=10, NEED_H=10, STAR_H=1, ID_TONE=9)


def tone_candidates(ref):
    nuc = nuclei(ref)
    choices = [tuple(dict.fromkeys((ref.real[n].split("_")[1], "H", "M")))
               for n in nuc]
    for combo in itertools.product(*choices):
        s = ref
        for n, c in zip(nuc, combo):
            s = set_tone(s, n, c)
        yield s


def select_tone(ref, D, W=W_TONE):
    sg = sigma(); acts = activation(sg, ref, D)
    best, arg = None, set()
    for c in tone_candidates(ref):
        v = score(coefficients(sg, ref, c, D, acts), W, LAM)
        if best is None or v < best:
            best, arg = v, {surface(c)}
        elif v == best:
            arg.add(surface(c))
    return sorted(arg), str(best)


def tone_cases():
    D = tone_declarations()
    stem = ["tʃ", "o_M", "m", "b", "ə_M", "D"]
    ipfv_vp = build(stem + ["a_M"], [0]*7, [0]*7, phrase=0, aspect=1)
    pfv_vp = build(stem + ["o_H"], [0]*7, [0]*7, phrase=0, aspect=0)
    pre = ["g", "a_M"]
    ipfv_cp = build(pre + stem + ["a_M"], [0, 0] + [1]*7, [0, 0] + [1]*7,
                    phrase=0, aspect=1, vdom=[0, 0] + [1]*7)
    ipfv_cp = Struct(order=ipfv_cp.order, real=ipfv_cp.real,
                     dom={n: (dict(d, aspect=0) if d["word"] == 0 else d)
                          for n, d in ipfv_cp.dom.items()}, assoc=ipfv_cp.assoc)
    from .observations import CBP_WINNERS as WIN
    norm = lambda x: x.replace("(", "").replace(")", "").replace(" ", "")
    out = {}
    for cid, ref in (("MORO_IPFV_VP", ipfv_vp), ("MORO_PFV_VP", pfv_vp), ("MORO_IPFV_CP", ipfv_cp)):
        forms, best = select_tone(ref, D)
        out[cid] = {"minima": forms, "score": best,
                    "matches_source": [norm(f) for f in forms] == [norm(WIN[cid])]}
    return out


def dp(noun_tones, poss_tone="H", adj_tones=("L", "H")):
    segs, words, morphs, mel = [], [], [], []
    if poss_tone is not None:
        segs += ["u_" + poss_tone]; words += [0]; morphs += [0]; mel.append(("HL", 0))
    for i, t in enumerate(noun_tones):
        segs += ["b", "a_" + t]; words += [1, 1]; morphs += [1, 1]
    if adj_tones:
        for i, t in enumerate(adj_tones):
            segs += ["m", "O_" + t]; words += [2, 2]; morphs += [2, 2]
        mel.append(("L", 2))
    return build(segs, words, morphs, phrase=0, aspect=0, melodies=mel)


def overlay_candidates(ref, hl_realisation="H.HL"):
    mels = {ref.real[m]: m for m in ref.order["mel"]}
    hl, l = mels.get("HL"), mels.get("L")
    nuc = nuclei(ref)
    byw = {}
    for n in nuc:
        byw.setdefault(ref.dom[n]["word"], []).append(n)
    hl_opts = [None, "noun"] if hl is not None else [None]
    l_opts = [None, "noun", "phrase"] if l is not None else [None]
    if 0 not in byw:
        l_opts = [o for o in l_opts if o != "phrase"]
    for hl_on, l_on in itertools.product(hl_opts, l_opts):
        s = ref; links = set()
        if hl_on:
            last = len(byw[1]) - 1
            for i, n in enumerate(byw[1]):
                s = set_tone(s, n, "HL" if (hl_realisation == "H.HL" and i == last) else "H")
            links.add((hl, byw[1][0]))
        if l_on:
            targets = [1] if l_on == "noun" else [0, 1]
            for w in targets:
                for n in byw[w]:
                    s = set_tone(s, n, "L")
                links.add((l, byw[w][0]))
        if hl_on and l_on:
            continue
        yield Struct(order=s.order, real=s.real, dom=s.dom, assoc=frozenset(links)), (hl_on, l_on)


def melody_cases():
    sg = sigma()
    out = {}
    HLR = {"TOMMO_SO": "H.H", "JAMSAY": "H.H", "NANGA": "H.HL"}
    LANG = {
        "TOMMO_SO": ("word", dict(DOCK_HL_R=16, DOCK_L_L=17, ID_TONE=8)),
        "JAMSAY": ("phrase", dict(DOCK_HL_R=8, DOCK_L_L=16, ID_TONE=1)),
        "NANGA": ("phrase", dict(DOCK_HL_R=10, DOCK_L_L=F(19, 2), ID_TONE=1)),
        "JAMSAY_fixedID": ("phrase", dict(DOCK_HL_R=8, DOCK_L_L=16, ID_TONE=8)),
        "NANGA_fixedID": ("phrase", dict(DOCK_HL_R=10, DOCK_L_L=F(19, 2), ID_TONE=8)),
    }
    LANG.update({
        "JAMSAY_fixedID_refit": ("phrase", dict(DOCK_HL_R=8, DOCK_L_L=24, ID_TONE=8)),
        "NANGA_fixedID_refit": ("phrase", dict(DOCK_HL_R=F(61, 2), DOCK_L_L=30, ID_TONE=8)),
    })
    refs = {"both": dp(("L", "H")), "poss_only": dp(("L", "H"), adj_tones=()),
            "mod_only": dp(("L", "H"), poss_tone=None)}
    for lang, (target, W) in LANG.items():
        D = melody_declarations(target)
        rows = []
        constructions = ("both",) if not lang.startswith("TOMMO") else ("both", "poss_only", "mod_only")
        for cons in constructions:
          ref = refs[cons]
          acts = activation(sg, ref, D)
          for c, (hl_on, l_on) in overlay_candidates(ref, HLR.get(lang.split("_fixed")[0], "H.HL")):
            if cons == "poss_only" and l_on: continue
            if cons == "mod_only" and hl_on: continue
            cf = coefficients(sg, ref, c, D, acts)
            h = score(cf, W, LAM)
            rows.append({"construction": cons, "overlay": f"HL:{hl_on} L:{l_on}",
                         "surface": surface(c), "harmony": h,
                         "coefficients": {k: list(v) for k, v in cf.items() if v != (0, 0)}})
        out[lang] = {"weights": {k: str(v) for k, v in W.items()}, "left_target": target}
        for cons in constructions:
            sub = [r for r in rows if r["construction"] == cons]
            z = sum(math.exp(-float(r["harmony"])) for r in sub)
            for r in sub:
                r["p"] = round(math.exp(-float(r["harmony"])) / z, 4)
            m = min(r["harmony"] for r in sub)
            out[lang][cons] = {"rows": [dict(r, harmony=str(r["harmony"])) for r in sub],
                               "minima": sorted(r["surface"] for r in sub if r["harmony"] == m),
                               "distribution": {r["surface"]: r["p"] for r in sub}}
    return out


def reset_comparison():
    D = tone_declarations(); sg = sigma()
    stem = ["tʃ", "o_M", "m", "b", "ə_M", "D"]; pre = ["g", "a_M"]
    cp = build(pre + stem + ["a_M"], [0, 0] + [1]*7, [0, 0] + [1]*7,
               phrase=0, aspect=1, vdom=[0, 0] + [1]*7)
    cp = Struct(order=cp.order, real=cp.real,
                dom={n: (dict(d, aspect=0) if d["word"] == 0 else d) for n, d in cp.dom.items()},
                assoc=cp.assoc)
    o = [n for n in nuclei(cp) if cp.dom[n]["vdom"] == 1][0]
    lower_out = set_tone(cp, o, "H")
    out = {}
    for label, ref in (("fixed reference (underlying form)", cp),
                       ("reference reset to the lower domain's output", lower_out)):
        acts = activation(sg, ref, D)
        rows = []
        for c in tone_candidates(cp):
            h = score(coefficients(sg, ref, c, D, acts), W_TONE, LAM)
            rows.append((surface(c), h))
        z = sum(math.exp(-float(h)) for _, h in rows)
        m = min(h for _, h in rows)
        out[label] = {"minima": sorted({sf for sf, h in rows if h == m}),
                      "harmony_of_winner": str(m),
                      "p_winner_at_T1": round(math.exp(-float(m)) / z, 4),
                      "p_faithful_no_H_at_T1": round(math.exp(-float(dict(rows)["ga tʃombəDa"])) / z, 6)}
    return out


def main():
    rec = {"replay": replay(), "tone": tone_cases(), "melodies": melody_cases(),
           "reset": reset_comparison()}
    n1 = rec["melodies"]["NANGA"]["both"]["distribution"]
    n2 = rec["melodies"]["NANGA_fixedID_refit"]["both"]["distribution"]
    rec["nanga_split_identity"] = {"printed": [.62, .38],
                                   "reweighted": [n1["ú bábâ mÒmÓ"], n1["ù bàbà mÒmÓ"]],
                                   "fixed_ID_refit": [n2["ú bábâ mÒmÓ"], n2["ù bàbà mÒmÓ"]]}
    OUT.mkdir(parents=True, exist_ok=True)
    certificate.write("cophonologies.json", rec)
    print("1. replay of the printed tableaux")
    for k, v in rec["replay"].items():
        print(f"   {k:40s} H agrees: {v['all_H_agree']}  predictions agree: {v['all_pred_agree']}")
    print("2. aspect-conditioned tone placement, one fixed weight vector")
    for k, v in rec["tone"].items():
        print(f"   {k:14s} -> {v['minima']}  matches source: {v['matches_source']}")
    print("reset comparison:", json.dumps(rec["reset"], ensure_ascii=False, indent=1))
    print("Nanga split:", rec["nanga_split_identity"])
    print("3. floating melodies")
    for k, v in rec["melodies"].items():
        for cons in ("both", "poss_only", "mod_only"):
            if cons not in v: continue
            print(f"   {k:20s} {cons:9s} minima={v[cons]['minima']}  p={v[cons]['distribution']}")


if __name__ == "__main__":
    main()
