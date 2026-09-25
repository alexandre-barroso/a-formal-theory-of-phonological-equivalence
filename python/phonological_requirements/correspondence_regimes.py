from __future__ import annotations
from phonological_requirements import certificate, paths
import itertools, json
from pathlib import Path

from .core import ABSENT, Decl, FILTERS, NodeId
from . import core as CORE
from . import evaluate as EV
from . import regimes as R
from .evaluate import activation, coefficients, score

OUT = paths.CERTIFICATES
FILTERS.setdefault("vocalic", lambda g, x: g.ft(x, "vocalic") is True)
SEGS = ["a", "i", "t", ABSENT]


def _spec(ref, cont):
    out = []
    for i in range(3):
        v = cont.get(i, ref.real[NodeId("Or", "lex", i)])
        if v != ABSENT:
            out.append((v, (i,)))
    return out


def bijective_disagreements(ref, decls, keying="unique", inverse=True):
    saved = CORE.Ctx.realisation
    if not inverse:
        def naive(self, node, where):
            if where != "reference":
                return self.state.real.get(node)
            return self.reference.real.get(node)
        CORE.Ctx.realisation = naive
    bad = 0
    try:
        sg = R.sigma()
        for combo in itertools.product(SEGS, repeat=3):
            cont = {i: v for i, v in enumerate(combo)}
            c1 = R.containment(ref, cont)
            c2 = R.correspondence(ref, _spec(ref, cont))
            acts = activation(sg, ref, decls)
            f1 = coefficients(sg, ref, c1, decls, acts, keying=keying)
            f2 = coefficients(sg, ref, c2, decls, acts, keying=keying)
            bad += (f1 != f2)
    finally:
        CORE.Ctx.realisation = saved
    return bad


def main():
    ref = R.ref_struct(["a", "t", "i"]); sg = R.sigma(); D = R.DECLS
    nolocus = dict(D)
    for nm in ("MAX", "IDENT"):
        d = D[nm]
        nolocus[nm] = Decl(d.name, d.anchor_sort, d.slots, d.activation,
                           d.consequence, d.scope, d.kind,
                           d.definedness_override, "candidate")
    saved = EV._keys
    EV._keys = lambda state, node, mode: (node,) if state.corr is None else ()
    no_t = bijective_disagreements(ref, D)
    EV._keys = saved
    rec = {"bijective_universe": len(SEGS) ** 3,
           "disagreements": {
               "all_three_bridge_components": bijective_disagreements(ref, D),
               "locus_side_dropped": bijective_disagreements(ref, nolocus),
               "inverse_image_realisation_dropped":
                   bijective_disagreements(ref, D, inverse=False),
               "t_correspondence_keying_dropped": no_t}}
    acts = activation(sg, ref, D)
    tbl = {}
    for lab, spec in (("fusion_marked_with_unmarked", [("a", (0, 1)), ("i", (2,))]),
                      ("fusion_to_repaired", [("i", (0, 1)), ("i", (2,))]),
                      ("fission_of_marked", [("a", (0,)), ("a", (0,)),
                                             ("t", (1,)), ("i", (2,))]),
                      ("epenthesis", [("a", (0,)), ("t", (1,)), ("i", ()), ("i", (2,))])):
        c = R.correspondence(ref, spec)
        tbl[lab] = {k: {"coefficients": {n: list(v) for n, v in
                                         coefficients(sg, ref, c, D, acts, keying=k).items()},
                        "score8": str(score(coefficients(sg, ref, c, D, acts, keying=k),
                                            R.W, R.LAM) * 8)}
                    for k in ("unique", "existential", "universal")}
    rec["non_bijective"] = tbl
    OUT.mkdir(parents=True, exist_ok=True)
    certificate.write("correspondence_regimes.json", rec)
    print(json.dumps(rec["disagreements"], indent=1))
    for lab, v in tbl.items():
        print(lab, {k: v[k]["coefficients"]["HARM"] for k in v})


if __name__ == "__main__":
    main()
