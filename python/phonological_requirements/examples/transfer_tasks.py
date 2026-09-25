import json, sys, itertools
from fractions import Fraction as F
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from phonological_requirements import certificate, paths
from phonological_requirements.core import ABSENT, read
from phonological_requirements.evaluate import activation, coefficients
from phonological_requirements.frag_seq import build, candidates, faith_decls, make_sigma, rule_decl, surface

def task_a():
    alpha = {"k": {"C", "k"}, "kj": {"C", "kj"}, "i": {"V", "i"}, "I": {"V"}, "m": {"C", "m"}, "n": {"C"}}
    sg = make_sigma(alpha)
    out = {}
    for pal_mode in ("retain", "discharge"):
        D = {"PAL": rule_decl("PAL", "k", (), ("i",), "kj", pal_mode),
             "SYNC": rule_decl("SYNC", "i", (), ("C", "V"), None, "discharge"),
             "DEG": rule_decl("DEG", "kj", (), ("m",), "k", "discharge")}
        D.update(faith_decls(alpha, [("k", "kj"), ("i", None)]))
        ref = build(["k", "i", "m", "I", "n"]); acts = activation(sg, ref, D)
        rows = {}
        for c in candidates(ref, {"k": ["k", "kj"], "i": ["i", ABSENT]}):
            co = coefficients(sg, ref, c, D, acts)
            rows[surface(c)] = {k: list(v) for k, v in co.items()}
        out[pal_mode] = rows
    return out

def task_b():
    alpha = {"k": {"C"}, "V": {"V"}, "N": {"C", "N"}}
    sg = make_sigma(alpha)
    D = {"NDEL": rule_decl("NDEL", "N", (), ("#",), None, "discharge")}
    D.update(faith_decls(alpha, [("N", None)]))
    ref = build(["k", "V", "N", "V", "N"]); acts = activation(sg, ref, D)
    nodes = ref.order["seg"]
    a_schema = any(acts["NDEL"].get(n, False) for n in nodes)
    rows = {}
    for c in candidates(ref, {"N": ["N", ABSENT]}):
        per_locus = []
        for n in nodes:
            r = read(sg, ref, c, D["NDEL"], n, "seg")
            p = int(r.defined and not r.good); a = int(acts["NDEL"].get(n, False))
            per_locus.append((a, int(r.context), p))
        old_locus = sum(p for a, C, p in per_locus if a); new_locus = sum(p for a, C, p in per_locus if (not a) and C)
        old_schema = sum(p for a, C, p in per_locus) if a_schema else 0; new_schema = 0 if a_schema else sum(p for a, C, p in per_locus if C)
        co = coefficients(sg, ref, c, D, acts)
        rows[surface(c)] = {"per_locus_cells": per_locus, "locus_keyed": [old_locus, new_locus], "schema_keyed": [old_schema, new_schema], "MAX_N": list(co["MAX_N"])}
    return {"a_schema": a_schema, "rows": rows}

if __name__ == "__main__":
    res = {"task_A": task_a(), "task_B": task_b()}
    certificate.write("transfer_answers.json", res, paths.EXAMPLES)
    A = res["task_A"]
    print("Task A (PAL retain):"); [print("  ", s.ljust(7), r) for s, r in A["retain"].items()]
    print("Task A (PAL discharge):"); [print("  ", s.ljust(7), r) for s, r in A["discharge"].items()]
    B = res["task_B"]; print("Task B: a_schema =", B["a_schema"]); [print("  ", s.ljust(6), r) for s, r in B["rows"].items()]
