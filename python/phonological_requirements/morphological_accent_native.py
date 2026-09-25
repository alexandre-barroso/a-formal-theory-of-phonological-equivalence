from __future__ import annotations
from phonological_requirements import certificate, paths

import itertools
import json
from pathlib import Path

OUT = paths.CERTIFICATES


class Word:
    def __init__(self, sylls, morphs, base, pwd=None, mwd_final_mora=None):
        self.sylls, self.morphs, self.base = sylls, morphs, base
        self.pwd = pwd or [0] * len(sylls)
        self.mwd_final_mora = mwd_final_mora
        self.n = len(sylls)

    def input_accents(self):
        return [(m, d["acc"]) for m, d in self.morphs.items() if d["acc"] is not None]

    def in_base(self, i):
        return self.morphs[self.sylls[i]]["in_base"]

    def cls(self, i):
        return self.morphs[self.sylls[i]]["class"]

    def taf(self):
        outer = [d["taf"] for d in self.morphs.values() if not d["in_base"] and d["taf"] is not None]
        return outer[-1] if outer else None


def gen(word: Word, policy: str):
    n = word.n
    inputs = word.input_accents()
    for k in range(0, 3):
        for out in itertools.combinations(range(n), k):
            for io in itertools.product([None] + list(out), repeat=len(inputs)):
                tgt = [t for t in io if t is not None]
                if len(tgt) != len(set(tgt)):
                    continue
                io_map = {inputs[j][0]: io[j] for j in range(len(inputs))}
                base_out = [o for o in out if word.in_base(o)]
                if policy == "induced":
                    oo_map = {}
                    for b in word.base:
                        m = word.sylls[b]
                        d = word.morphs[m]
                        if d["acc"] == b and io_map.get(m) is not None and word.in_base(io_map[m]):
                            oo_map[b] = io_map[m]
                        else:
                            oo_map[b] = None
                    for relink in itertools.product([False, True], repeat=len(word.base)):
                        rl = {b: r for b, r in zip(word.base, relink)}
                        if any(rl[b] and oo_map[b] is None for b in word.base):
                            continue
                        yield {"out": out, "io": io_map, "oo": oo_map, "relink": rl}
                else:
                    for oo in itertools.product([None] + base_out, repeat=len(word.base)):
                        t2 = [t for t in oo if t is not None]
                        if len(t2) != len(set(t2)):
                            continue
                        oo_map = {word.base[j]: oo[j] for j in range(len(word.base))}
                        for relink in itertools.product([False, True], repeat=len(word.base)):
                            rl = {b: r for b, r in zip(word.base, relink)}
                            if any(rl[b] and oo_map[b] is None for b in word.base):
                                continue
                            yield {"out": out, "io": io_map, "oo": oo_map, "relink": rl}


def label(word: Word, c):
    parts = []
    for o in c["out"]:
        src = [m for m, t in c["io"].items() if t == o]
        oo = [b for b, t in c["oo"].items() if t == o]
        tag = f"{o}"
        if src:
            tag += f"<io{src[0]}"
        else:
            tag += "<ins"
        if oo:
            tag += f"<oo{oo[0]}" + ("'" if c["relink"].get(oo[0]) else "")
        parts.append(tag)
    return "acc[" + ",".join(parts) + "]" if parts else "acc[]"


def constraints(word: Word, c, edge_syll=None, psp_syll=None):
    out, io, oo, rl = c["out"], c["io"], c["oo"], c["relink"]
    v = {}
    v["Culmin"] = max(0, len(out) - 1)
    v["Head"] = int(len(out) == 0)
    for cl in ("root", "stem", "affix"):
        v[f"IO-Max-{cl}"] = sum(1 for m, t in io.items() if word.morphs[m]["class"] == cl and t is None)
    v["IO-Max"] = sum(1 for t in io.values() if t is None)
    v["IO-Dep"] = sum(1 for o in out if o not in io.values())
    v["IO-Dep-root"] = sum(1 for o in out if o not in io.values() and word.cls(o) == "root")
    v["IO-NoFlop"] = sum(1 for m, t in io.items() if t is not None
                         and (t != word.morphs[m]["acc"] or rl.get(word.morphs[m]["acc"], False)))
    v["s1-Max"] = sum(1 for m, t in io.items() if t is None and word.morphs[m]["class"] == "root"
                      and word.morphs[m]["acc"] == min(i for i in range(word.n) if word.sylls[i] == m))
    v["OO-Max"] = sum(1 for b in word.base if oo[b] is None)
    v["OO-Dep"] = sum(1 for o in out if word.in_base(o) and o not in oo.values())
    v["OO-NoFlop"] = sum(1 for b in word.base if oo[b] is not None and (oo[b] != b or rl[b]))
    taf = word.taf()
    not_max = int(all(oo[b] is not None for b in word.base))
    not_noflop = int(not any(oo[b] is not None and (oo[b] != b or rl[b]) for b in word.base))
    edge = edge_syll
    not_dep_edge = int(not any(o == edge and o not in oo.values() for o in out)) if edge is not None else 0
    fin = word.mwd_final_mora
    not_max_fin = int(all(oo[b] is not None for b in word.base if b == fin)) if fin is not None else 0
    for idx in ("dom", "dom2", "dom3", "dom4", "rec"):
        on = int(taf == idx)
        v[f"nOO{idx}-Max"] = not_max * on
        v[f"nOO{idx}-NoFlop"] = not_noflop * on
        v[f"nOO{idx}-DepEdge"] = not_dep_edge * on
        v[f"nOO{idx}-MaxFin"] = not_max_fin * on
    last = word.n - 1
    v["Nonfin"] = sum(1 for o in out if o == last)
    v["Align-R"] = sum(1 for o in out if any(word.pwd[j] == word.pwd[o] for j in range(o + 1, word.n)))
    v["Align-L"] = sum(1 for o in out if any(word.pwd[j] == word.pwd[o] for j in range(0, o)))
    v["Align-R-gradient"] = sum(sum(1 for j in range(o + 1, word.n) if word.pwd[j] == word.pwd[o]) for o in out)
    v["PSP"] = sum(abs(o - psp_syll) for o in out) if psp_syll is not None else 0
    return v


def select(word: Word, ranking, cands, edge_syll=None, psp_syll=None):
    rows = [(tuple(constraints(word, c, edge_syll, psp_syll)[k] for k in ranking), c) for c in cands]
    best = min(r[0] for r in rows)
    return [c for r, c in rows if r == best], best


def winners_by_out(word, ranking, policy, edge_syll=None, psp_syll=None, extra_filter=None):
    cands = list(gen(word, policy))
    if extra_filter:
        cands = [c for c in cands if extra_filter(c)]
    ws, _ = select(word, ranking, cands, edge_syll, psp_syll)
    return sorted({label(word, w) for w in ws}), sorted({w["out"] for w in ws}), len(cands)


def M(cls, acc=None, in_base=True, taf=None):
    return {"class": cls, "acc": acc, "in_base": in_base, "taf": taf}


TABLEAUX = {}


def T(name, word, ranking, printed, expected_out, **kw):
    TABLEAUX[name] = dict(word=word, ranking=ranking, printed=printed, expected=expected_out, **kw)


T("5.6 koobe-kko", Word([0, 0, 1], {0: M("root", 0), 1: M("affix", None, False, "dom")}, base=[0]),
  ["nOOdom-Max", "OO-Max", "IO-Dep"], printed={"kóobe-kko": (0,), "koobé-kko": (1,), "koobe-kko": ()},
  expected_out=())
T("5.17 koobe-kko", Word([0, 0, 1], {0: M("root", 0), 1: M("affix", None, False, "dom")}, base=[0]),
  ["nOOdom-Max", "IO-Dep", "Head"], printed={"kóobe-kko": (0,), "koobé-kko": (1,), "koobe-kko": ()},
  expected_out=())
T("5.15 ada-ppo-i", Word([0, 0, 1, 2], {0: M("root", 1), 1: M("affix", 2, False, "dom"), 2: M("affix", None, False, None)},
                          base=[1]),
  ["nOOdom-Max", "OO-Max", "IO-Max"], printed={"adá-ppo-i": (1,), "ada-ppo-i": (), "ada-ppó-i": (2,)},
  expected_out=(2,))
T("5.16 yom-tara", Word([0, 1, 1], {0: M("root", 0), 1: M("affix", 1, False, "rec")}, base=[0]),
  ["OO-Max", "nOOrec-Max"], printed={"yon-dára": (1,), "yón-dara": (0,)}, expected_out=(0,))
T("5.30 luz-ic-a", Word([0, 1, 2], {0: M("root", 0), 1: M("stem", 1, False, "rec"), 2: M("affix", None, False, None)},
                         base=[0]),
  ["IO-Max-root", "IO-Max-stem", "PSP"], printed={"luž-ic-á": (2,), "luž-íc-a": (1,), "lúž-ic-a": (0,)},
  expected_out=(0,), psp_syll=2)
T("5.31 cast-ic-a", Word([0, 1, 2], {0: M("root", None), 1: M("stem", 1, False, "rec"), 2: M("affix", None, False, None)},
                          base=[]),
  ["IO-Max-root", "IO-Max-stem", "PSP"], printed={"čast'-ic-á": (2,), "čast'-íc-a": (1,)},
  expected_out=(1,), psp_syll=2)
T("5.33 siv-ux-a", Word([0, 1, 2], {0: M("root", 0), 1: M("stem", 1, False, "dom"), 2: M("affix", None, False, None)},
                         base=[0]),
  ["nOOdom-Max", "OO-Max", "IO-Max-stem", "PSP"], printed={"s'ív-ux-a": (0,), "s'iv-ux-á": (2,), "s'iv-úx-a": (1,)},
  expected_out=(1,), psp_syll=2)
T("5.34 puz-ac-u", Word([0, 1, 2], {0: M("root", 0), 1: M("stem", None, False, "dom"), 2: M("affix", None, False, None)},
                         base=[0]),
  ["nOOdom-Max", "OO-Max", "IO-Max-stem", "PSP"], printed={"púz-ač-u": (0,), "puz-áč-u": (1,), "puz-ač-ú": (2,)},
  expected_out=(2,), psp_syll=2)
T("5.78 nisimura-ke", Word([0, 0, 0, 0, 1], {0: M("root", 1), 1: M("affix", None, False, "dom")}, base=[1]),
  ["Culmin", "nOOdom-DepEdge", "IO-Max-root"], printed={"nisímura-ke": (1,), "nisimurá-ke": (3,)},
  expected_out=(3,), edge_syll=3)
T("5.82a yosida-si", Word([0, 0, 0, 1], {0: M("root", None), 1: M("affix", None, False, "rec")}, base=[]),
  ["IO-Max-root", "nOOrec-DepEdge"], printed={"yosidá-si": (2,), "yosida-si": ()}, expected_out=(2,), edge_syll=2)
T("5.82b nisimura-si", Word([0, 0, 0, 0, 1], {0: M("root", 1), 1: M("affix", None, False, "rec")}, base=[1]),
  ["IO-Max-root", "nOOrec-DepEdge"], printed={"nisímura-si": (1,), "nisimurá-si": (3,)}, expected_out=(1,), edge_syll=3)
T("5.122 kaki-mono", Word([0, 0, 1, 1], {0: M("root", 0), 1: M("affix", None, False, "dom3")}, base=[0], pwd=[0, 0, 1, 1]),
  ["nOOdom3-NoFlop", "OO-NoFlop"], printed={"káki-mono": (0,), "kaki-móno": (2,), "kakí-mono": (1,)},
  expected_out=(1,))
T("5.123 nori-mono", Word([0, 0, 1, 1], {0: M("root", None), 1: M("affix", None, False, "dom3")}, base=[], pwd=[0, 0, 1, 1]),
  ["nOOdom3-NoFlop", "IO-Dep"], printed={"norí-mono": (1,), "nori-mono": ()}, expected_out=())
T("5.124 tititi-mono", Word([0, 0, 0, 1, 1], {0: M("root", 0), 1: M("affix", None, False, "dom3")}, base=[0], pwd=[0, 0, 0, 1, 1]),
  ["nOOdom3-NoFlop", "OO-NoFlop", "Align-R"], printed={"títiti-mono": (0,), "tititi-móno": (3,), "titíti-mono": (1,), "titití-mono": (2,)},
  expected_out=(2,))
T("5.125 kaki-te", Word([0, 0, 1], {0: M("root", 0), 1: M("affix", None, False, "dom2")}, base=[0], pwd=[0, 0, 1]),
  ["nOOdom2-Max", "IO-Max-root", "Nonfin"], printed={"káki-te": (0,), "kakí-te": (1,), "kaki-te": (), "kaki-té": (2,)},
  expected_out=(2,))
T("5.126 inoti-nagara", Word([0, 0, 0, 1, 1, 1], {0: M("root", 0), 1: M("affix", None, False, "dom2")}, base=[0], pwd=[0, 0, 0, 1, 1, 1]),
  ["nOOdom2-Max", "Nonfin", "Align-R", "Align-L"], printed={"ínoti-nagara": (0,), "inoti-nagará": (5,), "inoti-nágara": (3,)},
  expected_out=(3,))
T("5.43a kawa-no", Word([0, 0, 1], {0: M("root", 1), 1: M("affix", None, False, "dom4")}, base=[1], mwd_final_mora=1),
  ["nOOdom4-MaxFin", "OO-Max"], printed={"kawá no": (1,), "kawa no": ()}, expected_out=())
T("5.43b utiwa-no", Word([0, 0, 0, 1], {0: M("root", 1), 1: M("affix", None, False, "dom4")}, base=[1], mwd_final_mora=2),
  ["nOOdom4-MaxFin", "OO-Max"], printed={"utíwa no": (1,), "utiwa no": ()}, expected_out=(1,))
T("5.44 ha-no", Word([0, 1], {0: M("root", 0), 1: M("affix", None, False, "dom4")}, base=[0], mwd_final_mora=0),
  ["s1-Max", "nOOdom4-MaxFin", "OO-Max"], printed={"há no": (0,), "ha no": ()}, expected_out=(0,))


def printed_candidate(word: Word, out, flop: bool):
    io = {}
    for m, a in word.input_accents():
        if a in out:
            io[m] = a
        elif flop and len(out) == 1:
            io[m] = out[0]
        else:
            io[m] = None
    oo = {}
    for b in word.base:
        m = word.sylls[b]
        d = word.morphs[m]
        oo[b] = io[m] if (d["acc"] == b and io.get(m) is not None and word.in_base(io[m])) else None
    return {"out": out, "io": io, "oo": oo, "relink": {b: False for b in word.base}}


COMPLETION = {
    "jp": (["Culmin"], ["IO-Max-root", "IO-NoFlop", "OO-Dep", "IO-Max-affix", "IO-Dep", "Nonfin", "Align-R", "Align-L", "Head"]),
    "ru": (["Culmin", "Head", "IO-NoFlop"], ["OO-Dep", "IO-Max-root", "IO-Max-stem", "IO-Max-affix", "IO-Dep", "PSP", "Align-R"]),
}
LANG = {n: ("ru" if n.split()[0] in ("5.30", "5.31", "5.33", "5.34") else "jp") for n in TABLEAUX}


def completed(name, repair=False):
    top, rest = COMPLETION[LANG[name]]
    rk = list(top) + [c for c in TABLEAUX[name]["ranking"] if c not in top]
    rk += [c for c in rest if c not in rk]
    if repair:
        rk = [c for c in rk if c != "OO-Dep"]
        rk.insert(1, "OO-Dep")
    return rk


def total_repaired(lang, where):
    rk = [c for c in TOTAL[lang] if c != "OO-Dep"]
    if where == "top":
        rk.insert(1, "OO-Dep")
    else:
        i = max([k for k, c in enumerate(rk) if c.endswith("DepEdge")] or [0])
        rk.insert(i + 1, "OO-Dep")
    return rk


TOTAL = {
    "jp": ["Culmin", "nOOdom-DepEdge", "nOOdom-Max", "s1-Max", "nOOdom4-MaxFin", "nOOdom3-NoFlop", "OO-NoFlop",
           "IO-Max-root", "nOOrec-DepEdge", "nOOdom2-Max", "IO-NoFlop", "OO-Max", "OO-Dep", "IO-Max-affix",
           "IO-Dep", "IO-Dep-root", "Nonfin", "Align-R", "Align-L", "Head", "nOOrec-Max", "nOOrec-NoFlop"],
    "ru": ["Culmin", "Head", "IO-NoFlop", "nOOdom-Max", "OO-Max", "IO-Max-root", "IO-Max-stem", "nOOrec-Max",
           "PSP", "IO-Max-affix", "OO-Dep", "IO-Dep", "Align-R"],
}


def replay_total():
    rec = {}
    for name, t in TABLEAUX.items():
        w = t["word"]
        kw = {k: t[k] for k in ("edge_syll", "psp_syll") if k in t}
        rk = TOTAL[LANG[name]]
        li, oi, ni = winners_by_out(w, rk, "induced", **kw)
        lf, of, nf = winners_by_out(w, rk, "free", **kw)
        r1 = winners_by_out(w, total_repaired(LANG[name], "top"), "free", **kw)[1]
        r2 = winners_by_out(w, total_repaired(LANG[name], "below_dep_edge"), "free", **kw)[1]
        rec[name] = {"expected": t["expected"], "induced": oi, "induced_labels": li, "free": of, "free_labels": lf,
                     "free_oo_dep_top": r1, "free_oo_dep_below_dep_edge": r2,
                     "agree_induced": oi == [t["expected"]], "agree_free": of == [t["expected"]],
                     "agree_free_oo_dep_top": r1 == [t["expected"]], "agree_free_oo_dep_below_dep_edge": r2 == [t["expected"]]}
    return rec


def distinguishing():
    pairs = {
        "koobe-kko over koobe-kkó": ("5.17 koobe-kko", (), (2,), False),
        "kaki-té over kaki-te": ("5.125 kaki-te", (2,), (), True),
        "kaki-té over káki-te": ("5.125 kaki-te", (2,), (0,), True),
        "kokóro over kókoro": ("kokoro", (1,), (0,), False),
        "atamá over atáma": ("atama", (2,), (1,), False),
        "atamá over atama": ("atama", (2,), (), False),
        "kawa-no over kawa-nó": ("5.43a kawa-no", (), (2,), False),
        "há-no over ha-nó": ("5.44 ha-no", (0,), (1,), False),
        "kakí-mono over kaki-móno": ("5.122 kaki-mono", (1,), (2,), False),
    }
    out = {}
    for key, (src, win, lose, second) in pairs.items():
        w = TABLEAUX[src]["word"] if src in TABLEAUX else UNDERIVED[src][0]
        kw = {k: TABLEAUX[src][k] for k in ("edge_syll", "psp_syll") if src in TABLEAUX and k in TABLEAUX[src]}
        def best(o):
            cs = [c for c in gen(w, "induced") if c["out"] == o]
            vs = []
            for c in cs:
                vs.append(constraints(w, c, **kw))
            return min(vs, key=lambda v: sum(v.values()))
        a, b = best(win), best(lose)
        diff = {k: (a[k], b[k]) for k in a if a[k] != b[k]}
        out[key] = {"winner_prefers": sorted(k for k, (x, y) in diff.items() if x < y),
                    "loser_prefers": sorted(k for k, (x, y) in diff.items() if x > y)}
    return out


def replay():
    rec = {}
    for name, t in TABLEAUX.items():
        w, rk = t["word"], t["ranking"]
        kw = {k: t[k] for k in ("edge_syll", "psp_syll") if k in t}
        flop = name.split()[0] in ("5.122", "5.124", "5.125", "5.126")
        pr = [printed_candidate(w, o, flop) for o in t["printed"].values()]
        ws, _ = select(w, rk, pr, **kw)
        printed_win = sorted({c["out"] for c in ws})
        crk = completed(name)
        li, oi, ni = winners_by_out(w, crk, "induced", **kw)
        lf, of, nf = winners_by_out(w, crk, "free", **kw)
        lr, orp, _ = winners_by_out(w, completed(name, repair=True), "free", **kw)
        rec[name] = {"ranking": rk, "completed_ranking": crk, "expected": t["expected"],
                     "printed_rows_winner": printed_win, "agree_printed": printed_win == [t["expected"]],
                     "induced": {"winners": oi, "labels": li, "candidates": ni}, "agree_induced": oi == [t["expected"]],
                     "free": {"winners": of, "labels": lf, "candidates": nf}, "agree_free": of == [t["expected"]],
                     "free_repaired": {"winners": orp, "labels": lr}, "agree_free_repaired": orp == [t["expected"]]}
    return rec


UNDERIVED = {
    "kokoro": (Word([0, 0, 0], {0: M("root", 1)}, base=[]), (1,)),
    "atama": (Word([0, 0, 0], {0: M("root", 2)}, base=[]), (2,)),
    "hasi_0": (Word([0, 0], {0: M("root", None)}, base=[]), ()),
}


def kko_te_conflict():
    cons = ["nOOdom-Max", "nOOdom2-Max", "IO-Max-root", "IO-Dep", "Head", "Nonfin", "IO-NoFlop", "Align-L", "Align-R"]
    words = {"koobe-kko": (TABLEAUX["5.17 koobe-kko"]["word"], (), False),
             "kaki-te": (TABLEAUX["5.125 kaki-te"]["word"], (2,), True)}
    for k, (w, e) in UNDERIVED.items():
        words[k] = (w, e, False)
    table = {}
    for k, (w, e, second) in words.items():
        rows = []
        for c in gen(w, "induced"):
            v = constraints(w, c)
            if v["Culmin"]:
                continue
            rows.append((v, c["out"]))
        table[k] = (rows, e)
    good, tested = [], 0
    for rk in itertools.permutations(cons):
        tested += 1
        ok = True
        for k, (rows, e) in table.items():
            b = min(tuple(v[c] for c in rk) for v, _ in rows)
            if {o for v, o in rows if tuple(v[c] for c in rk) == b} != {e}:
                ok = False
                break
        if ok:
            good.append(rk)
    common = []
    if good:
        for a, b in itertools.permutations(cons, 2):
            if all(r.index(a) < r.index(b) for r in good):
                common.append(f"{a} >> {b}")
    printed_dep_head = [r for r in good if r.index("IO-Dep") < r.index("Head")]
    te_labels = set()
    if good:
        w = TABLEAUX["5.125 kaki-te"]["word"]
        cands = [c for c in gen(w, "induced") if not constraints(w, c)["Culmin"]]
        for rk in good:
            def key(c):
                v = constraints(w, c)
                return tuple(v[x] for x in rk)
            b = min(key(c) for c in cands)
            te_labels |= {label(w, c) for c in cands if key(c) == b}
    return {"constraints": cons, "words": {k: str(e) for k, (_, e, _) in words.items()},
            "rankings_tested": tested, "rankings_giving_all": len(good),
            "survivors_with_printed_IO-Dep_over_Head": len(printed_dep_head),
            "kaki_te_realisation_in_survivors": sorted(te_labels),
            "examples": [" >> ".join(r) for r in good[:5]], "shared_orders": common,
            "note": "koobe-kkó (the root accent relinked to the suffix) satisfies -kko's ¬OO-Max under "
                    "Stem-to-Stem correspondence exactly as kaki-té satisfies -te's; what separates the "
                    "two printed outcomes is the fate of the relinked candidate, decided by the "
                    "non-affix-specific constraints and by the prosodic structure the source assigns "
                    "([koobe-kko] one prosodic word; [[kaki][te]] two)."}


def loopholes():
    rec = replay()
    out = {}
    for name, r in rec.items():
        if not r["agree_free"]:
            out[name] = {"induced": r["induced"]["winners"], "free": r["free"]["winners"],
                         "free_labels": r["free"]["labels"], "repaired": r["free_repaired"]["winners"]}
    return out


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    rec = {"replay": replay()}
    for key in ("agree_printed", "agree_induced", "agree_free", "agree_free_repaired"):
        bad = [n for n, r in rec["replay"].items() if not r[key]]
        print(f"replay {key}: {len(rec['replay']) - len(bad)}/{len(rec['replay'])}" + (f"  disagree {bad}" if bad else ""))
    for key in ("agree_induced",):
        for n, r in rec["replay"].items():
            if not r[key]:
                print(f"  induced disagreement {n}: winners {r['induced']['winners']} {r['induced']['labels'][:4]}")
    rec["loopholes"] = loopholes()
    for n, r in rec["loopholes"].items():
        print(f"  free correspondence in {n}: induced {r['induced']} free {r['free']} {r['free_labels'][:3]} repaired {r['repaired']}")
    rec["total"] = replay_total()
    for pol in ("induced", "free", "free_oo_dep_top", "free_oo_dep_below_dep_edge"):
        bad = [n for n, r in rec["total"].items() if not r[f"agree_{pol}"]]
        print(f"total ranking, {pol}: {len(rec['total']) - len(bad)}/{len(rec['total'])}"
              + (f"  disagree {[(n, rec['total'][n][pol]) for n in bad]}" if bad else ""))
    rec["distinguishing"] = distinguishing()
    for k, v in rec["distinguishing"].items():
        print(f"  {k}: needs one of {v['winner_prefers']} above all of {v['loser_prefers']}")
    rec["kko_te"] = kko_te_conflict()
    k = rec["kko_te"]
    print(f"kko/te + underived: {k['rankings_tested']} rankings, {k['rankings_giving_all']} give all five; "
          f"{k['survivors_with_printed_IO-Dep_over_Head']} of them with the printed IO-Dep >> Head; "
          f"kaki-té realised as {k['kaki_te_realisation_in_survivors']}; shared orders {k['shared_orders']}")
    certificate.write("morphological_accent_native.json", rec)


if __name__ == "__main__":
    main()
