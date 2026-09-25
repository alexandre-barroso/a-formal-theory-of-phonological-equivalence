from __future__ import annotations
import json, sys, itertools
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))

from phonological_requirements.indep_gua import Product, ALPHABET, SCHEMATA, MARKEDNESS, WEIGHTS, LAMBDA
from phonological_requirements import frag_gua as FG
from phonological_requirements.core import read, NodeId


def products():
    out = []
    from phonological_opacity.gua.grammar import INPUTS_DELETION, INPUTS_SELECTION
    for inputs in (INPUTS_SELECTION, INPUTS_DELETION):
        for u in inputs:
            out.append((tuple(u["focal"]),
                        Product(u["id"], [x["phone"] for x in u["slots"]],
                                [x["word"] for x in u["slots"]], u["phrases"],
                                u["focal"])))
    return out


def core_readers(sigma, decls, prod, state):
    ref = FG.struct_from_segments(prod.reference, prod.words, prod.phrase_of_word)
    cur = FG.struct_from_segments(state, prod.words, prod.phrase_of_word)
    nodes = ref.nodes("seg")
    out = {}
    for name in FG.SCHEMA_ORDER:
        d = decls[name]
        out[name] = [read(sigma, ref, cur, d, n) for n in nodes]
    return out


def main(refined=True, limit=None):
    sigma = FG.make_sigma(refined=refined)
    decls = FG.declarations("baseline")
    bad = []
    n_checked = 0
    for focal, prod in products():
        base = list(prod.reference)
        a_ref = prod.activation_bits()
        for combo in itertools.product(ALPHABET, repeat=len(focal)):
            st = list(base)
            for q, v in zip(focal, combo):
                st[q] = v
            st = tuple(st)
            n_checked += 1
            C, D, G = prod.readers(st)
            R = core_readers(sigma, decls, prod, st)
            for k, name in enumerate(SCHEMATA):
                for q in range(prod.n):
                    got = R[name][q]
                    expC, expD, expG = bool(C[k][q]), bool(D[k][q]), bool(G[k][q])
                    if (got.context, got.defined) != (expC, expD):
                        bad.append((prod.id, st, name, q, "C/Def", (expC, expD),
                                    (got.context, got.defined)))
                    elif expD and got.good != expG:
                        bad.append((prod.id, st, name, q, "G|Def", expG, got.good))
                    exp_p = int(expD and not expG); exp_m = int(expC and exp_p)
                    if (got.pressure, got.marked) != (exp_p, exp_m):
                        bad.append((prod.id, st, name, q, "p/M", (exp_p, exp_m),
                                    (got.pressure, got.marked)))
            if limit and n_checked >= limit:
                break
    print(f"candidates compared: {n_checked}")
    if bad:
        print(f"DISAGREEMENTS: {len(bad)}")
        for b in bad[:10]:
            print("   ", b)
        return 1
    print("PASS: core derived readers == appendix-G readers at every origin of "
          f"every one of the {n_checked} candidates (refined={refined}).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(refined="--unrefined" not in sys.argv))
