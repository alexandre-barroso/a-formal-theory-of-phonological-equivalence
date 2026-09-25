from __future__ import annotations
from phonological_requirements import paths
import itertools, json, sys
from fractions import Fraction
from pathlib import Path

from .indep_gua import (ALPHABET, MARKEDNESS, SCHEMATA, WEIGHTS, LAMBDA, Product)
from .multilocus import REGISTRY
from .products import gua_products, gua_observations

OUT = paths.CERTIFICATES
VOW = "aɜɛeɪiɔoʊu"


def score(prod, s, a, mode):
    C, D, G = prod.readers(s)
    tot = Fraction(0)
    for k in range(9):
        p = [D[k][q] and not G[k][q] for q in range(prod.n)]
        if k in MARKEDNESS:
            if mode == "B":
                ak = any(a[k])
                old = sum(1 for q in range(prod.n) if p[q] and ak)
                new = sum(1 for q in range(prod.n) if p[q] and (not ak) and C[k][q])
            else:
                old = sum(1 for q in range(prod.n) if p[q] and a[k][q])
                new = sum(1 for q in range(prod.n) if p[q] and not a[k][q] and C[k][q])
            if mode == "A":
                old, new = min(old, 1), min(new, 1)
        else:
            old = sum(1 for q in range(prod.n) if p[q] and C[k][q]); new = 0
        tot += Fraction(WEIGHTS[k]) * (Fraction(old) + LAMBDA * Fraction(new))
    return tot


def brute(prod, elig, mode):
    C0, D0, G0 = prod.readers(prod.reference)
    a = [[bool(C0[k][q] and D0[k][q] and not G0[k][q]) for q in range(prod.n)]
         for k in range(9)]
    base = list(prod.reference); best = None; mins = []
    for combo in itertools.product(ALPHABET, repeat=len(elig)):
        st = list(base)
        for q, v in zip(elig, combo):
            st[q] = v
        sc = score(prod, tuple(st), a, mode)
        if best is None or sc < best:
            best, mins = sc, [tuple(st)]
        elif sc == best:
            mins.append(tuple(st))
    return best, sorted({prod.observe(m) for m in mins})


def main():
    rec = {"declared_products": {}, "constructed_products": {}}
    obs = gua_observations()
    for focal, prod in gua_products():
        r = {m: brute(prod, focal, m) for m in ("none", "A", "B")}
        rec["declared_products"][prod.id] = {
            m: {"min8": str(r[m][0] * 8), "outputs": r[m][1]} for m in r}
        rec["declared_products"][prod.id]["A_inert"] = r["none"][1] == r["A"][1]
        rec["declared_products"][prod.id]["B_inert"] = r["none"][1] == r["B"][1]
    for name, f in REGISTRY.items():
        p = f(); elig = tuple(q for q in range(p.n) if p.reference[q] in VOW)
        if 13 ** len(elig) > 200000:
            rec["constructed_products"][name] = {"skipped": 13 ** len(elig)}
            continue
        r = {m: brute(p, elig, m) for m in ("none", "A", "B")}
        rec["constructed_products"][name] = {
            "reference": "".join(p.reference),
            **{m: {"min8": str(r[m][0] * 8), "outputs": r[m][1]} for m in r},
            "A_inert": r["none"][1] == r["A"][1],
            "B_inert": r["none"][1] == r["B"][1]}
    rec["summary"] = {
        "A_inert_in_all_declared": all(v["A_inert"] for v in rec["declared_products"].values()),
        "B_inert_in_all_declared": all(v["B_inert"] for v in rec["declared_products"].values()),
        "A_refuted_by": [k for k, v in rec["constructed_products"].items()
                         if "A_inert" in v and not v["A_inert"]],
        "B_refuted_by_declared": [k for k, v in rec["declared_products"].items()
                                  if not v["B_inert"]],
    }
    OUT.mkdir(parents=True, exist_ok=True)
    (OUT / "individuation_ablations.json").write_text(
        json.dumps(rec, ensure_ascii=False, indent=1))
    print(json.dumps(rec["summary"], ensure_ascii=False, indent=1))


if __name__ == "__main__":
    main()
