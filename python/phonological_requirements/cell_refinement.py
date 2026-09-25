from __future__ import annotations
from phonological_requirements import certificate, paths
import itertools, json
from pathlib import Path

from . import frag_gua as FG
from .core import read
from .evaluate import activation, coefficients, loci, score
from .products import gua_products
from .interaction_cells import minimizers

OUT = paths.CERTIFICATES
MARK = ("H", "A", "GL", "D")
SOURCE_LABELS = {"G34a": "counterbleeding", "G34b": "countershifting",
                 "G37c": "self-counterfeeding", "OR38": "self-counterfeeding"}


def main():
    sg = FG.make_sigma(); D = FG.declarations("typed")
    rows = []
    for focal, prod in gua_products():
        ref = FG.struct_from_segments(prod.reference, prod.words, prod.phrase_of_word)
        acts = activation(sg, ref, D)
        _, winners, _ = minimizers(sg,D,ref,focal,prod,acts,FG.WEIGHTS,FG.LAMBDA)
        for win in winners:
            new = [(nm, n.index) for nm in MARK for n in loci(win, D[nm], "seg", ref)
                   if (lambda r: r.pressure and r.context
                       and not acts[nm].get(n, False))(read(sg, ref, win, D[nm], n))]
            rep = [(nm, n.index) for nm in MARK for n in loci(ref, D[nm], "seg", ref)
                   if acts[nm].get(n, False)
                   and not read(sg, ref, win, D[nm], n).pressure]
            same = any(a == b for a, _ in new for b, _ in rep)
            rows.append({"product": prod.id,
                         "repaired": [list(x) for x in rep],
                         "new_environment": [list(x) for x in new],
                         "same_schema": bool(new) and same,
                         "source_label": SOURCE_LABELS.get(prod.id)})
    rec = {"rows": rows,
           "all_underapplication_cases_are_same_schema":
               all(r["same_schema"] for r in rows if r["new_environment"]),
           "note": ("The local same-schema signature is computed for every minimizer. "
                    "Source labels are kept separate; no derivational classification "
                    "follows from this signature alone.")}
    OUT.mkdir(parents=True, exist_ok=True)
    certificate.write("cell_refinement.json", rec)
    for r in rows:
        print(f"  {r['product']:7s} new={r['new_environment']} same_schema={r['same_schema']}"
              f"  source label: {r['source_label']}")
    print("all underapplication cases are same-schema:",
          rec["all_underapplication_cases_are_same_schema"])


if __name__ == "__main__":
    main()
