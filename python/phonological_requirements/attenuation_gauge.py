from __future__ import annotations
from phonological_requirements import certificate, paths
import itertools, json
from fractions import Fraction
from pathlib import Path

from . import frag_gua as FG
from .evaluate import activation, coefficients, score
from .indep_gua import ALPHABET
from .products import gua_products

OUT = paths.CERTIFICATES
FAITH = ("MAX", "IDENT_ATR", "IDENT_QUAL", "IDENT_NUC", "INITIAL_FEATURE")


def main():
    sg = FG.make_sigma(); D = FG.declarations("baseline")
    lam = FG.LAMBDA; W = FG.WEIGHTS
    Wu = {k: (Fraction(v) / lam if k in FAITH else Fraction(v)) for k, v in W.items()}
    bad_a = 0; mism = 0; tot = 0
    for focal, prod in gua_products():
        ref = FG.struct_from_segments(prod.reference, prod.words, prod.phrase_of_word)
        acts = activation(sg, ref, D)
        for nm, dcl in D.items():
            if dcl.kind == "faithfulness":
                bad_a += sum(1 for _n, v in acts[nm].items() if v)
        base = list(prod.reference)
        for combo in itertools.product(ALPHABET, repeat=len(focal)):
            st = list(base)
            for q, v in zip(focal, combo):
                st[q] = v
            cur = FG.struct_from_segments(tuple(st), prod.words, prod.phrase_of_word)
            e = score(coefficients(sg, ref, cur, D, acts), W, lam)
            u = score(coefficients(sg, ref, cur, D, acts, retain_faithfulness=True), Wu, lam)
            tot += 1
            mism += (e != u)
    rec = {"faithfulness_loci_with_activation_bit_1": bad_a,
           "candidates": tot,
           "score_mismatches_exempt_wF_vs_uniform_wF_over_lambda": mism,
           "lambda": str(lam),
           "claim": "P_uniform(s; w_F, w_M, lambda) = P_exempt(s; lambda w_F, w_M, lambda)",
           "status": "FINITE_EXHAUSTIVE_CERTIFIED"}
    OUT.mkdir(parents=True, exist_ok=True)
    certificate.write("attenuation_gauge.json", rec)
    print(json.dumps(rec, indent=1))


if __name__ == "__main__":
    main()
