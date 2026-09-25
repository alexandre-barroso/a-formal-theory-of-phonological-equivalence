from __future__ import annotations
from phonological_requirements import paths

import itertools
import json
from fractions import Fraction as F
from pathlib import Path

from .core import (And, Ctx, Decl, Feat, Positional, Slot, read)
from .evaluate import activation, coefficients, loci, score
from .frag_voice import declarations, sigma, struct

OUT = paths.CERTIFICATES

W = dict(ID_VOICE=1, ID_ONSET_VOICE=3, DEVOICE_SYLL=10, DEVOICE_WORD=10,
         CLUSTER_DEVOICE=10, AGREE_BOTH=20, AGREE_PLUS=20, AGREE_MINUS=20)
LAM = F(1, 8)
PAIR = {"z": ("z", "s"), "s": ("z", "s"), "b": ("b", "p"), "p": ("b", "p"),
        "d": ("d", "t"), "t": ("d", "t"), "g": ("g", "k"), "k": ("g", "k"),
        "v": ("v", "f"), "f": ("v", "f")}


def best(segs, syll, word, D, mode="binary"):
    sg = sigma(mode)
    ref = struct(list(segs), syll, word)
    nodes = ref.order["seg"]
    obs = [i for i, c in enumerate(segs) if c in PAIR]
    acts = activation(sg, ref, D)
    lo, arg = None, []
    for combo in itertools.product([0, 1], repeat=len(obs)):
        s = ref
        for i, v in zip(obs, combo):
            s = s.with_real(nodes[i], PAIR[segs[i]][v])
        val = score(coefficients(sg, ref, s, D, acts), W, LAM)
        if lo is None or val < lo:
            lo, arg = val, [s]
        elif val == lo:
            arg.append(s)
    return sorted({"".join(str(a.real[n]) for n in nodes) for a in arg}), str(lo)


def readers_under_both():
    segs = ["a", "z", "z", "t", "a", "s", "d", "a"]
    syll = [0, 0, 1, 1, 1, 2, 2, 2]
    D = dict(declarations(("syll", "word"), "plus_minus"))
    D.update(declarations(("syll", "word"), "both"))
    out = {}
    for mode in ("binary", "privative"):
        sg = sigma(mode)
        s = struct(segs, syll, syll)
        rows = {}
        for nm, d in sorted(D.items()):
            cells = []
            for l in loci(s, d, "seg", s):
                r = read(sg, s, s, d, l)
                if r.context or r.pressure:
                    cells.append({"segment": str(s.real[l]), "index": l.index,
                                  "C": int(r.context), "Def": int(r.defined),
                                  "G": int(r.good), "p": r.pressure})
            rows[nm] = cells
        out[mode] = rows
    return out


def markedness_witnesses():
    segs = ["a", "z", "z", "t", "a", "s", "d", "a"]
    syll = [0, 0, 1, 1, 1, 2, 2, 2]
    D = dict(declarations(("syll", "word"), "plus_minus"))
    D.update(declarations(("syll", "word"), "both"))
    out = {}
    for mode in ("binary", "privative"):
        sg = sigma(mode)
        ref = struct(segs, syll, syll)
        nodes = ref.order["seg"]
        states = [ref]
        for i, c in enumerate(segs):
            if c in PAIR:
                for v in PAIR[c]:
                    if v != c:
                        states.append(ref.with_real(nodes[i], v))
        row = {}
        for nm, d in sorted(D.items()):
            hit = False
            for s in states:
                for l in loci(s, d, "seg", ref):
                    r = read(sg, ref, s, d, l)
                    if r.marked:
                        hit = True
            row[nm] = hit
        out[mode] = row
    return out


def refinement(nmax: int = 5):
    sg = sigma("binary")
    T = Slot("t", "Or", "subject", kind="anchor")

    def probe(domain):
        return Decl(f"P_{domain}", "Or", (T,), Feat("obs", "t", True),
                    Positional("last_live_of", "t", domain))
    ps, pw = probe("syll"), probe("word")
    SEGS = ("a", "b", "s", "m")
    bad = structures = checks = 0
    for n in range(2, nmax + 1):
        for segs in itertools.product(SEGS, repeat=n):
            for scuts in itertools.product([0, 1], repeat=n - 1):
                syll = [0]
                for c in scuts:
                    syll.append(syll[-1] + c)
                for wcuts in itertools.product([0, 1], repeat=syll[-1]):
                    wof = [0]
                    for c in wcuts:
                        wof.append(wof[-1] + c)
                    st = struct(list(segs), syll, [wof[s] for s in syll])
                    structures += 1
                    for nd in st.order["seg"]:
                        a = ps.consequence.eval(Ctx(sg, st, st, ps, nd, "seg"))
                        b = pw.consequence.eval(Ctx(sg, st, st, pw, nd, "seg"))
                        checks += 1
                        if b is True and a is not True:
                            bad += 1
    return {"max_length": nmax, "structures": structures, "node_checks": checks,
            "violations_of_word_final_implies_syllable_final": bad}


def typology():
    segs = list("azlaztasdad")
    syll = [0, 0, 1, 1, 1, 2, 2, 2, 3, 3, 3]
    word = [0] * 11
    names = {(): "no devoicing", ("word",): "word-final",
             ("syll",): "syllable-final"}
    rows = {}
    for dev in ((), ("word",), ("syll",)):
        for assim in ("none", "plus", "minus", "both"):
            forms, sc = best(segs, syll, word, declarations(dev, assim))
            pretty = []
            for f in forms:
                out = []
                for i, ch in enumerate(f):
                    if i and syll[i] != syll[i - 1]:
                        out.append(" ")
                    out.append(ch)
                pretty.append("".join(out))
            rows[f"{names[dev]} | {assim}"] = {"output": pretty, "score": sc}
    return rows


def cluster_test():
    cases = {"/azb/ one syllable": (list("azb"), [0, 0, 0], [0, 0, 0]),
             "/az.bo/ two syllables": (list("azbo"), [0, 0, 1, 1], [0, 0, 0, 0])}
    grammars = {
        "cluster devoicing only": declarations((), "none", cluster=True),
        "word-final devoicing only": declarations(("word",), "none"),
        "syllable-final devoicing only": declarations(("syll",), "none"),
        "assimilation only": declarations((), "both"),
        "word-final devoicing + assimilation": declarations(("word",), "both")}
    return {k: {g: best(*v, D)[0] for g, D in grammars.items()}
            for k, v in cases.items()}


def compare_to_source(rows):
    from .observations import WETZELS_MASCARO_TABLE_10 as T10
    names = {(): "no devoicing", ("word",): "word-final",
             ("syll",): "syllable-final"}
    out = {}
    for key, printed in T10.items():
        dev, assim = key
        got = rows[f"{names[dev]} | {assim}"]["output"]
        out[f"{names[dev]} | {assim}"] = {
            "source": printed, "core": got,
            "agrees": got == [printed]}
    return out


def collapses(rows):
    g = lambda k: rows[k]["output"]
    return {
        "minus-spreading is invisible under syllable-final devoicing":
            g("syllable-final | minus") == g("syllable-final | none"),
        "plus-spreading is indistinguishable from both under syllable-final devoicing":
            g("syllable-final | plus") == g("syllable-final | both"),
    }


def main():
    rd = readers_under_both()
    rec = {"readers": rd,
           "markedness_witnesses": markedness_witnesses(),
           "witness_domain": {"reference": "azztasda", "candidate_scope": "reference and single obstruent-voicing changes", "false_means": "no markedness witness in this finite domain"},
           "refinement": refinement(5),
           "typology": (ty := typology()),
           "against_the_source": compare_to_source(ty),
           "source_collapses_reproduced": collapses(ty),
           "cluster": cluster_test(),
           "weights": W, "lambda": str(LAM)}
    OUT.mkdir(parents=True, exist_ok=True)
    (OUT / "laryngeal_neutralization.json").write_text(
        json.dumps(rec, ensure_ascii=False, indent=1))

    print("1. markedness witnesses in the reference and single-change candidates")
    for mode, row in rec["markedness_witnesses"].items():
        print(f"   {mode:10s}", {k: v for k, v in sorted(row.items())})
    print()
    print("2. refinement:", rec["refinement"])
    print()
    print("3. the generated typology, input /az.laz.tas.dad/")
    for k, v in rec["typology"].items():
        cmp = rec["against_the_source"].get(k)
        mark = "" if cmp is None else ("  == source" if cmp["agrees"] else "  != SOURCE")
        print(f"   {k:30s} -> {v['output']}{mark}")
    agree = all(v["agrees"] for v in rec["against_the_source"].values())
    print(f"   all eight statable rows agree with the source: {agree}")
    print(f"   the source's own collapses: {rec['source_collapses_reproduced']}")
    if not agree or not all(rec["source_collapses_reproduced"].values()):
        raise SystemExit("the generated typology does not match the source")
    print()
    print("4. the dismissed process")
    for k, v in rec["cluster"].items():
        print(f"   {k}")
        for g, f in v.items():
            print(f"      {g:38s} -> {f}")


if __name__ == "__main__":
    main()
