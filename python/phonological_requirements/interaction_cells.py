from __future__ import annotations
from phonological_requirements import paths
import itertools, json
from pathlib import Path

from . import frag_gua as FG
from .core import read
from .evaluate import activation, coefficients, loci, score
from .products import gua_products

OUT = paths.CERTIFICATES
MARK = ("H", "A", "GL", "D")


def cells(sg, D, ref, s, acts):
    out = {k: [] for k in ("11", "10", "01", "00")}
    for nm in MARK:
        d = D[nm]
        for n in loci(s, d, "seg", ref):
            r = read(sg, ref, s, d, n)
            if not r.pressure:
                continue
            out[f"{int(bool(acts[nm].get(n, False)))}{int(r.context)}"].append((nm, n.index))
    return out


def minimizers(sg, D, ref, focal, prod, acts, weights, lam):
    best = None
    winners = []
    scored = 0
    for combo in itertools.product(FG.ALPHABET, repeat=len(focal)):
        st = list(prod.reference)
        for q, v in zip(focal, combo):
            st[q] = v
        state = FG.struct_from_segments(tuple(st), prod.words, prod.phrase_of_word)
        value = score(coefficients(sg, ref, state, D, acts), weights, lam)
        scored += 1
        if best is None or value < best:
            best, winners = value, [state]
        elif value == best:
            winners.append(state)
    assert scored == len(FG.ALPHABET) ** len(focal) and winners
    return best, winners, scored


def main():
    sg = FG.make_sigma(); D = FG.declarations("typed")
    rows = []
    for focal, prod in gua_products():
        ref = FG.struct_from_segments(prod.reference, prod.words, prod.phrase_of_word)
        acts = activation(sg, ref, D)
        best, winners, count = minimizers(sg,D,ref,focal,prod,acts,FG.WEIGHTS,FG.LAMBDA)
        records = []
        for win in winners:
            wc = cells(sg,D,ref,win,acts)
            rival = []
            for q in focal:
                node = ref.nodes("seg")[q]
                if win.real[node] != ref.real[node]:
                    rival += cells(sg,D,ref,win.with_real(node,ref.real[node]),acts)["10"]
            records.append({"winner": "".join(win.real[n] for n in win.nodes("seg") if win.real[n] != "∅"),
                "aligned": [win.real[n] for n in win.nodes("seg")],
                "winner_cell_01": [list(x) for x in wc["01"]],
                "rival_cell_10": [list(x) for x in sorted(set(rival))],
                "local_signature": [bool(rival),bool(wc["01"])]})
        rows.append({"product":prod.id,"minimum_score":str(best),"candidates":count,
            "minimizers":records,"all_local_signatures_equal":len({tuple(r["local_signature"]) for r in records})==1})
    OUT.mkdir(parents=True,exist_ok=True)
    (OUT/"interaction_cells.json").write_text(json.dumps({"rows":rows,
        "scope":"Local pressure diagnostics over complete minimizers, not a classical process classification theorem."},ensure_ascii=False,indent=1))
    print(json.dumps({"products":len(rows),"candidates":sum(r["candidates"] for r in rows),
        "minimizers":sum(len(r["minimizers"]) for r in rows),
        "signature_agreement":[r["all_local_signatures_equal"] for r in rows]}))


if __name__ == "__main__":
    main()
