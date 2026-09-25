from __future__ import annotations
from phonological_requirements import certificate, paths

import itertools
import json
import time
from fractions import Fraction as F
from pathlib import Path

import numpy as np

from .core import ABSENT
from .evaluate import activation, coefficients
from .frag_seq import MODES, build, candidates, faith_decls, make_sigma, rule_decl, surface

OUT = paths.CERTIFICATES
LAMS = ("0", "1/8", "1/4", "2/5", "5/12", "499/1000", "1/2", "501/1000", "33/50", "2/3", "3/4", "1")

PATTERNS = {
 "counterfeeding": dict(kind='schematic counterfeeding control',
    alphabet={"k": {"C"}, "V": {"V"}, "N": {"C", "N"}, "T": {"C", "T"}},
    rules=[("NDEL", "N", (), ("#",), None), ("TDEL", "T", ("N",), ("#",), None)],
    mappings={"kVN": "kV", "kVNT": "kVN", "kVNV": "kVNV"},
    options={"N": ["N", ABSENT], "T": ["T", ABSENT]}),
 "feeding": dict(kind='schematic reversal of the Catalan counterfeeding control',
    alphabet={"k": {"C"}, "V": {"V"}, "N": {"C", "N"}, "T": {"C", "T"}},
    rules=[("NDEL", "N", (), ("#",), None), ("TDEL", "T", ("N",), ("#",), None)],
    mappings={"kVN": "kV", "kVNT": "kV", "kVNV": "kVNV"},
    options={"N": ["N", ABSENT], "T": ["T", ABSENT]}),
 "counterbleeding": dict(kind='schematic counterbleeding control',
    alphabet={"k": {"C", "k"}, "kj": {"C"}, "i": {"V", "i"}, "I": {"V"}, "m": {"C"}, "t": {"C"}, "n": {"C"}, "a": {"V"}},
    rules=[("PAL", "k", (), ("i",), "kj"), ("SYNC", "i", (), ("C", "V"), None)],
    mappings={"kim": "kjim", "timIn": "tmIn", "kimIn": "kjmIn"},
    options={"k": ["k", "kj"], "i": ["i", ABSENT]}),
 "bleeding": dict(kind='schematic reversal of the Bedouin counterbleeding control',
    alphabet={"k": {"C", "k"}, "kj": {"C"}, "i": {"V", "i"}, "I": {"V"}, "m": {"C"}, "t": {"C"}, "n": {"C"}, "a": {"V"}},
    rules=[("PAL", "k", (), ("i",), "kj"), ("SYNC", "i", (), ("C", "V"), None)],
    mappings={"kim": "kjim", "timIn": "tmIn", "kimIn": "kmIn"},
    options={"k": ["k", "kj"], "i": ["i", ABSENT]}),
 "mutual_counterbleeding": dict(kind='schematic mutual counterbleeding control',
    alphabet={"g": {"C"}, "a": {"V"}, "h": {"C", "h"}, "w": {"C", "w"}, "u": {"V"}, "t": {"C"}, "d": {"C"}, "r": {"C"}, "e": {"V"}, "m": {"C"}},
    rules=[("HDEL", "h", (), ("C",), None), ("VOC", "w", ("C",), ("#",), "u")],
    mappings={"gaht": "gat", "darw": "daru", "maw": "maw", "gahe": "gahe", "gahw": "gau"},
    options={"h": ["h", ABSENT], "w": ["w", "u"]}),
 "mutual_bleeding_h_first": dict(kind='schematic mutual bleeding h first control',
    alphabet={"g": {"C"}, "a": {"V"}, "h": {"C", "h"}, "w": {"C", "w"}, "u": {"V"}, "t": {"C"}, "d": {"C"}, "r": {"C"}, "e": {"V"}, "m": {"C"}},
    rules=[("HDEL", "h", (), ("C",), None), ("VOC", "w", ("C",), ("#",), "u")],
    mappings={"gaht": "gat", "darw": "daru", "maw": "maw", "gahe": "gahe", "gahw": "gaw"},
    options={"h": ["h", ABSENT], "w": ["w", "u"]}),
 "mutual_bleeding_voc_first": dict(kind='schematic mutual bleeding voc first control',
    alphabet={"g": {"C"}, "a": {"V"}, "h": {"C", "h"}, "w": {"C", "w"}, "u": {"V"}, "t": {"C"}, "d": {"C"}, "r": {"C"}, "e": {"V"}, "m": {"C"}},
    rules=[("HDEL", "h", (), ("C",), None), ("VOC", "w", ("C",), ("#",), "u")],
    mappings={"gaht": "gat", "darw": "daru", "maw": "maw", "gahe": "gahe", "gahw": "gahu"},
    options={"h": ["h", ABSENT], "w": ["w", "u"]}),
 "mutual_counterfeeding": dict(kind='hypothetical categorical paradigm; variable cases disputed',
    alphabet={"g": {"C"}, "a": {"V"}, "h": {"C", "h"}, "r": {"C"}, "@": {"V", "@"}, "m": {"C"}, "u": {"V"}, "p": {"C"}, "e": {"V"}, "t": {"C"}},
    rules=[("HDEL", "h", (), ("C",), None), ("SYNC", "@", ("C", "V"), ("C", "V"), None)],
    mappings={"gahe": "gahe", "gaht": "gat", "mae": "mae", "mat": "mat", "mar@mu": "marmu", "ah@pt": "ah@pt",
              "ah@pr@mu": "ah@pr@mu", "gahr@mu": "gar@mu", "ah@pe": "ahpe"},
    options={"h": ["h", ABSENT], "@": ["@", ABSENT]}),
 "fed_counterfeeding": dict(kind='schematic local context; Lardil reconstructed separately',
    alphabet={"C": {"C", "L"}, "V": {"V"}, "K": {"C", "K"}},
    rules=[("APO", "V", ("C", "V"), ("#",), None), ("KDEL", "K", (), ("#",), None)],
    mappings={"CVCVCV": "CVCVC", "CVCVK": "CVCV", "CVCVKV": "CVCV"},
    options={"V": ["V", ABSENT], "K": ["K", ABSENT]}),
 "mutual_counterfeeding_deletions": dict(kind='hypothetical final deletion; block rival admits it',
    alphabet={"C": {"C"}, "V": {"V"}},
    rules=[("CDEL", "C", (), ("#",), None), ("VDEL", "V", (), ("#",), None)],
    mappings={"CVC": "CV", "CVCV": "CVC"},
    options={"C": ["C", ABSENT], "V": ["V", ABSENT]}),
 "noniterative_simultaneous": dict(kind='schematic noniterative simultaneous control',
    alphabet={"V": {"V"}, "C": {"C"}, "@": {"V", "@"}},
    rules=[("SYNC", "@", ("C", "V"), ("C", "V"), None)],
    mappings={"VC@C@CV": "VCCCV"},
    options={"@": ["@", ABSENT]}),
 "noniterative_left_to_right": dict(kind='schematic noniterative left to right control',
    alphabet={"V": {"V"}, "C": {"C"}, "@": {"V", "@"}},
    rules=[("SYNC", "@", ("C", "V"), ("C", "V"), None)],
    mappings={"VC@C@CV": "VCC@CV"},
    options={"@": ["@", ABSENT]}),
 "noniterative_right_to_left": dict(kind='schematic noniterative right to left control',
    alphabet={"V": {"V"}, "C": {"C"}, "@": {"V", "@"}},
    rules=[("SYNC", "@", ("C", "V"), ("C", "V"), None)],
    mappings={"VC@C@CV": "VC@CCV"},
    options={"@": ["@", ABSENT]}),
 "self_counterfeeding": dict(kind='schematic self counterfeeding control',
    alphabet={"u": {"V", "rd"}, "y": {"V", "y"}},
    rules=[("RND", "y", ("rd",), (), "u")],
    mappings={"uyy": "uuy"},
    options={"y": ["y", "u"]}),
 "self_feeding": dict(kind='schematic self feeding control',
    alphabet={"u": {"V", "rd"}, "y": {"V", "y"}},
    rules=[("RND", "y", ("rd",), (), "u")],
    mappings={"uyy": "uuu"},
    options={"y": ["y", "u"]}),
 "self_counterbleeding": dict(kind='schematic self counterbleeding control',
    alphabet={"p": {"C"}, "L": {"V", "L"}, "s": {"C"}, "v": {"C"}, "a": {"V"}},
    rules=[("SHORT", "L", ("C", "L"), (), "a")],
    mappings={"pLsLvL": "pLsava"},
    options={"L": ["L", "a"]}),
 "self_bleeding": dict(kind='schematic self bleeding control',
    alphabet={"p": {"C"}, "L": {"V", "L"}, "s": {"C"}, "v": {"C"}, "a": {"V"}},
    rules=[("SHORT", "L", ("C", "L"), (), "a")],
    mappings={"pLsLvL": "pLsavL"},
    options={"L": ["L", "a"]}),
 "circular_chain_shift": dict(kind='schematic circular chain shift control',
    alphabet={"X": {"C", "X"}, "Y": {"C", "Y"}, "A": {"V", "A"}, "B": {"V", "B"}, "Q": {"V", "Q"}},
    rules=[("AB", "A", ("X",), ("Y",), "B"), ("BQ", "B", ("X",), ("Y",), "Q"), ("QA", "Q", ("X",), ("Y",), "A")],
    mappings={"XAY": "XBY", "XBY": "XQY", "XQY": "XAY"},
    options={"A": ["A", "B", "Q"], "B": ["A", "B", "Q"], "Q": ["A", "B", "Q"]}),
 "vipratisedha_blocking": dict(kind='schematic vipratisedha blocking control',
    alphabet={"i": {"V", "i"}, "k": {"C", "k"}, "kj": {"C"}, "ts": {"C"}, "a": {"V"}},
    rules=[("PAL", "k", (), ("i",), "kj"), ("AFF", "k", ("i",), (), "ts")],
    mappings={"aki": "akji", "ika": "itsa", "iki": "iki"},
    options={"k": ["k", "kj", "ts"]}),
 "vipratisedha_first_wins": dict(kind='schematic vipratisedha first wins control',
    alphabet={"i": {"V", "i"}, "k": {"C", "k"}, "kj": {"C"}, "ts": {"C"}, "a": {"V"}},
    rules=[("PAL", "k", (), ("i",), "kj"), ("AFF", "k", ("i",), (), "ts")],
    mappings={"aki": "akji", "ika": "itsa", "iki": "ikji"},
    options={"k": ["k", "kj", "ts"]}),
 "changtin": dict(kind='schematic reconstruction of source-reported Changtin',
    alphabet={"M": {"V", "M"}, "R": {"V", "R"}, "H": {"V"}, "L": {"V"}},
    rules=[("MR", "M", (), ("R",), "L"), ("RM", "R", (), ("M",), "H")],
    mappings={"MR": "LR", "RM": "HM", "MRM": "LHM", "RMR": "HLR"},
    options={"M": ["M", "L"], "R": ["R", "H"]}),
}


KEY = {"discharge": "D", "retain": "R", "ltr": "L2R", "rtl": "R2L"}


def toks(s):
    return s


def build_pattern(pat, modes):
    if len(modes) != len(pat["rules"]) or any(m not in MODES for m in modes):
        raise ValueError("one valid mode is required for every rule")
    alpha = pat["alphabet"]
    classes = {c for cs in alpha.values() for c in cs}
    for r in pat["rules"]:
        for c in (r[1],) + tuple(r[2]) + tuple(r[3]):
            if c != "#" and c not in classes:
                raise ValueError(f"rule {r[0]} names the class {c!r}, which no symbol carries")
    sg = make_sigma(alpha)
    D = {r[0]: rule_decl(r[0], r[1], r[2], r[3], r[4], m) for r, m in zip(pat["rules"], modes)}
    changes = [(r[1], r[4]) for r in pat["rules"]]
    for sym, opts in pat["options"].items():
        cls = sym if sym in alpha[sym] else sorted(alpha[sym])[0]
        for o in opts:
            if o != sym:
                changes.append((cls, None if o is ABSENT else o))
    D.update(faith_decls(alpha, list(dict.fromkeys(changes))))
    return sg, D


def split(s, alpha):
    out, i = [], 0
    syms = sorted(alpha, key=len, reverse=True)
    while i < len(s):
        for a in syms:
            if s.startswith(a, i):
                out.append(a); i += len(a); break
        else:
            raise ValueError((s, i))
    return out


def rows_for(pat, modes, lam):
    sg, D = build_pattern(pat, modes)
    names = sorted(D)
    out = {}
    for inp, target in pat["mappings"].items():
        ref = build(split(inp, pat["alphabet"]))
        acts = activation(sg, ref, D)
        rows = []
        for c in candidates(ref, pat["options"]):
            co = coefficients(sg, ref, c, D, acts)
            rows.append((surface(c), [F(co[k][0]) + lam * F(co[k][1]) for k in names]))
        out[inp] = (target, rows)
    return names, out


def pareto(rows):
    rows = [list(r) for r in dict.fromkeys(tuple(r) for r in rows)]
    if len(rows) <= 1:
        return rows
    keep = []
    for i in sorted(range(len(rows)), key=lambda j: sum(rows[j])):
        if not any(all(a <= b for a, b in zip(rows[j], rows[i])) for j in keep):
            keep.append(i)
    return [rows[i] for i in keep]


def lp_strict(strict, n):
    from scipy.optimize import linprog
    if not strict:
        return True, [F(0)] * n
    A = np.array([[float(x) for x in r] for r in strict]); m = len(strict)
    c = np.zeros(n + 1); c[-1] = -1.0
    res = linprog(c, A_ub=np.hstack([-A, np.ones((m, 1))]), b_ub=np.zeros(m),
                  bounds=[(0, 1000)] * n + [(None, 1.0)], method="highs")
    if res.status == 0 and res.x[-1] > 1e-9:
        w = [F(x).limit_denominator(10**6) for x in res.x[:-1]]
        if all(x >= 0 for x in w) and all(sum(a * x for a, x in zip(r, w)) > 0 for r in strict):
            return True, w
    for r in strict:
        if all(a <= 0 for a in r):
            return False, {tuple(r): F(1)}
    res2 = linprog(np.zeros(m), A_ub=A.T, b_ub=np.zeros(n), A_eq=np.ones((1, m)), b_eq=[1.0],
                   bounds=[(0, None)] * m, method="highs")
    if res2.status == 0:
        candidates = [[F(float(v)).limit_denominator(10**6) for v in res2.x]]
        candidates.extend([F(round(v * den), den) for v in res2.x]
                          for den in (1, 2, 3, 4, 6, 8, 12, 24, 100, 1000))
        for y in candidates:
            if all(yi >= 0 for yi in y) and sum(y) > 0 and all(sum(yi * r[j] for yi, r in zip(y, strict)) <= 0 for j in range(n)):
                dual = {}
                for yi, row in zip(y, strict):
                    if yi > 0:
                        key = tuple(row)
                        dual[key] = dual.get(key, F(0)) + yi
                return False, dual
    return None, None


def generable(pat, modes, lam):
    names, R = rows_for(pat, modes, lam)
    per_input = []
    for inp, (target, rows) in R.items():
        tg = [r for sf, r in rows if sf == target]
        others = pareto([r for sf, r in rows if sf != target])
        if not tg:
            return {"feasible": False, "reason": f"the output {target} of {inp} is not a candidate"}, names
        per_input.append((inp, tg, others))
    refutations = []
    inconclusive = False
    for choice in itertools.product(*[range(len(tg)) for _, tg, _ in per_input]):
        strict, label = [], []
        for (inp, tg, others), j in zip(per_input, choice):
            x = tg[j]
            for o in others:
                strict.append([p - q for p, q in zip(o, x)]); label.append(inp)
        ok, cert = lp_strict(strict, len(names))
        if ok:
            return {"feasible": True, "witness": {k: str(v) for k, v in zip(names, cert) if v > 0}, "exact": True}, names
        if ok is None:
            inconclusive = True
            continue
        refutations.append([
            {"input": label[strict.index(list(r))],
             "inequality": [str(x) for x in r], "multiplier": str(y)}
            for r, y in cert.items()])
    if inconclusive:
        return {"feasible": None, "reason": "LP inconclusive for at least one output-fiber branch"}, names
    return {"feasible": False, "exact": True,
            "reason": "every realisation of the outputs is refuted by an exact nonnegative combination of rival inequalities",
            "farkas": refutations}, names


def main():
    t0 = time.time()
    rec = {"lambdas": list(LAMS), "patterns": {}}
    for name, pat in PATTERNS.items():
        k = len(pat["rules"])
        res = {}
        for modes in itertools.product(MODES, repeat=k):
            key = "+".join(KEY[m] for m in modes)
            res[key] = {}
            for lam in LAMS:
                g, names = generable(pat, modes, F(lam))
                res[key][lam] = g
        counts = {inp: len(list(candidates(build(split(inp, pat["alphabet"])), pat["options"]))) for inp in pat["mappings"]}
        rec["patterns"][name] = {"kind": pat["kind"], "rules": [r[0] for r in pat["rules"]], "mappings": pat["mappings"],
                                 "candidates_per_input": counts, "results": res}
        summary = {key: [lam for lam, g in v.items() if g["feasible"]] for key, v in res.items()}
        print(f"{name:34s} {pat['kind'][:40]:40s}", {k: (v[0] + ".." + v[-1] if v else "-") for k, v in summary.items()})
    rec["seconds"] = round(time.time() - t0, 1)
    certificate.write("interaction_typology.json", rec)
    d = paths.GENERATED_WOLFRAM
    d.mkdir(parents=True, exist_ok=True)
    wolfram_systems(d / "interaction_typology_systems.wl")
    print(f"certificate written in {rec['seconds']} s")


def rows_sym(pat, modes):
    sg, D = build_pattern(pat, modes)
    names = sorted(D)
    out = {}
    for inp, target in pat["mappings"].items():
        ref = build(split(inp, pat["alphabet"]))
        acts = activation(sg, ref, D)
        rows = []
        for c in candidates(ref, pat["options"]):
            co = coefficients(sg, ref, c, D, acts)
            rows.append((surface(c), [(F(co[k][0]), F(co[k][1])) for k in names]))
        out[inp] = (target, rows)
    return names, out


def wolfram_systems(path):
    lines = []
    for name, pat in PATTERNS.items():
        k = len(pat["rules"])
        for modes in itertools.product(MODES, repeat=k):
            key = "+".join(KEY[m] for m in modes)
            names, R = rows_sym(pat, modes)
            wsym = [f"w{i}" for i in range(len(names))]
            per_input = []
            for inp, (target, rows) in R.items():
                tg = [r for sf, r in rows if sf == target]
                others = [r for sf, r in rows if sf != target]
                keep = []
                for r in dict.fromkeys(tuple(x) for x in others):
                    if not any(all(a[0] <= b[0] and a[1] <= b[1] for a, b in zip(q, r)) and q != r for q in keep):
                        keep = [q for q in keep if not all(a[0] <= b[0] and a[1] <= b[1] for a, b in zip(r, q))] + [r]
                per_input.append((inp, tg, keep))
            disj = []
            for choice in itertools.product(*[range(len(tg)) for _, tg, _ in per_input]):
                ineqs = []
                for (inp, tg, keep), j in zip(per_input, choice):
                    x = tg[j]
                    for o in keep:
                        terms = []
                        for (o0, o1), (x0, x1), w in zip(o, x, wsym):
                            a0, a1 = o0 - x0, o1 - x1
                            if a0 or a1:
                                terms.append(f"({a0} + ({a1}) lam) {w}")
                        ineqs.append(" + ".join(terms) + " > 0" if terms else "False")
                disj.append("Exists[{" + ", ".join(wsym) + "}, " + " && ".join(f"{w} >= 0" for w in wsym) + " && " + " && ".join(ineqs) + "]")
            body = " || ".join(disj)
            lines.append((name, key, body))
    uniq = list(dict.fromkeys(b for _, _, b in lines))
    idx = {b: i + 1 for i, b in enumerate(uniq)}
    Path(path).write_text("systems = {\n" + ",\n".join(uniq) + "\n};\n" +
                          "labels = {\n" + ",\n".join('{"%s", "%s", %d}' % (n, k, idx[b]) for n, k, b in lines) + "\n};\n")
    return len(uniq), len(lines)


if __name__ == "__main__":
    main()
