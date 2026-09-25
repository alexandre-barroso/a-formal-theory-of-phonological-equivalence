from __future__ import annotations
import json, sys, itertools
from fractions import Fraction as F
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from phonological_requirements import certificate, paths
from phonological_requirements.core import ABSENT, read
from phonological_requirements.evaluate import activation, coefficients
from phonological_requirements.frag_seq import build, candidates, faith_decls, make_sigma, rule_decl, surface

PAT = {
 "palatalisation_syncope": dict(
    alphabet={"k": {"C", "k"}, "kj": {"C"}, "i": {"V", "i"}, "I": {"V"}, "m": {"C"}, "t": {"C"}, "n": {"C"}, "a": {"V"}},
    rules=[("PAL", "k", (), ("i",), "kj"), ("SYNC", "i", (), ("C", "V"), None)],
    inputs=["kimIn"], options={"k": ["k", "kj"], "i": ["i", ABSENT]}),
 "nasal_stop_deletion": dict(
    alphabet={"k": {"C"}, "V": {"V"}, "N": {"C", "N"}, "T": {"C", "T"}},
    rules=[("NDEL", "N", (), ("#",), None), ("TDEL", "T", ("N",), ("#",), None)],
    inputs=["kVNT"], options={"N": ["N", ABSENT], "T": ["T", ABSENT]}),
}
MODE_KEY = {"discharge": "D", "retain": "R", "ltr": "L2R", "rtl": "R2L"}

def split(s, alpha):
    out, i = [], 0
    for _ in range(len(s)):
        for a in sorted(alpha, key=len, reverse=True):
            if s.startswith(a, i):
                out.append(a); i += len(a); break
        if i >= len(s): break
    return out

def build_pattern(pat, modes):
    alpha = pat["alphabet"]; sg = make_sigma(alpha)
    D = {r[0]: rule_decl(r[0], r[1], r[2], r[3], r[4], m) for r, m in zip(pat["rules"], modes)}
    changes = [(r[1], r[4]) for r in pat["rules"]]
    for sym, opts in pat["options"].items():
        cls = sym if sym in alpha[sym] else sorted(alpha[sym])[0]
        for o in opts:
            if o != sym: changes.append((cls, None if o is ABSENT else o))
    D.update(faith_decls(alpha, list(dict.fromkeys(changes))))
    return sg, D

def pm_readers(alpha, rule, mode, ref_syms, cand_syms, i):
    name, target, left, right, out = rule
    present = [j for j, s in enumerate(cand_syms) if s is not ABSENT]
    def classes(s): return alpha[s] if s is not ABSENT else set()
    def ctx_holds(side_spec, direction):
        pos = i; ok = True; parts = []
        for c in side_spec:
            nxt = [j for j in present if (j > pos if direction > 0 else j < pos)]
            nxt = (min(nxt) if direction > 0 else max(nxt)) if nxt else None
            if c == "#":
                parts.append(nxt is None)
                pos = pos if nxt is None else nxt
            else:
                parts.append(nxt is not None and c in classes(cand_syms[nxt]))
                if nxt is None: pos = pos
                else: pos = nxt
        return all(parts)
    is_target = cand_syms[i] is not ABSENT and target in classes(cand_syms[i])
    C = bool(is_target and ctx_holds(left, -1) and ctx_holds(right, +1))
    repaired = (cand_syms[i] is ABSENT) if out is None else (cand_syms[i] == out)
    lt = ctx_holds(left, -1); rt = ctx_holds(right, +1)
    carried = {"discharge": [lt, rt], "retain": [], "ltr": [lt], "rtl": [rt]}[mode]
    escaped = bool(carried and not all(carried))
    if cand_syms[i] is ABSENT and out is not None:
        Def = escaped; G = escaped
        return C, Def, G
    Def = True
    G = bool(repaired or escaped)
    return C, Def, G

def run():
    report = {"patterns": {}, "bridge_checks": 0, "bridge_mismatches": []}
    for pname, pat in PAT.items():
        alpha = pat["alphabet"]
        for modes in itertools.product(("discharge", "retain", "ltr", "rtl"), repeat=len(pat["rules"])):
            sg, D = build_pattern(pat, modes)
            key = "+".join(MODE_KEY[m] for m in modes)
            for inp in pat["inputs"]:
                syms = split(inp, alpha); ref = build(syms)
                acts = activation(sg, ref, D)
                rows = []
                for cand in candidates(ref, pat["options"]):
                    csyms = [cand.real[n] for n in ref.order["seg"]]
                    cells = {}
                    for rname, rule in zip([r[0] for r in pat["rules"]], pat["rules"]):
                        d = D[rname]
                        for i, n in enumerate(ref.order["seg"]):
                            r = read(sg, ref, cand, d, n, "seg")
                            a = bool(acts[rname].get(n, False))
                            p = int(r.defined and not r.good)
                            pm = pm_readers(alpha, rule, modes[[x[0] for x in pat["rules"]].index(rname)], syms, csyms, i)
                            report["bridge_checks"] += 1
                            if (r.context, r.defined, r.good) != pm:
                                report["bridge_mismatches"].append(dict(pattern=pname, modes=key, cand=surface(cand), rule=rname, pos=i, core=(r.context, r.defined, r.good), pm=pm))
                            if a or r.context or p:
                                cells[f"{rname}@{i}"] = dict(a=int(a), C=int(r.context), Def=int(r.defined), G=int(r.good), p=p,
                                                             cell=("old" if (a and p) else "new" if (p and r.context and not a) else "inert"))
                    co = coefficients(sg, ref, cand, D, acts)
                    rows.append(dict(surface=surface(cand), realisation=["∅" if s is ABSENT else s for s in csyms], cells=cells,
                                     coefficients={k: list(v) for k, v in co.items()}))
                report["patterns"].setdefault(pname, {})[key] = dict(input=inp, rules=[list(r[:4]) + [r[4]] for r in pat["rules"]], rows=rows)
    return report

if __name__ == "__main__":
    rep = run()
    out = paths.EXAMPLES / "entry_bridge.json"
    paths.EXAMPLES.mkdir(parents=True, exist_ok=True)
    certificate.write(out.name, rep, paths.EXAMPLES)
    print("bridge checks:", rep["bridge_checks"], "mismatches:", len(rep["bridge_mismatches"]))
    for m in rep["bridge_mismatches"][:10]: print("  ", m)
    for pname, key in (("palatalisation_syncope", "R+D"), ("palatalisation_syncope", "D+D"), ("nasal_stop_deletion", "D+D"), ("nasal_stop_deletion", "R+R")):
        blk = rep["patterns"][pname][key]
        print(f"\n== {pname} modes {key} input {blk['input']} ==")
        for row in blk["rows"]:
            print(" ", row["surface"].ljust(8), row["coefficients"], {k: (v["a"], v["C"], v["p"], v["cell"]) for k, v in row["cells"].items()})
