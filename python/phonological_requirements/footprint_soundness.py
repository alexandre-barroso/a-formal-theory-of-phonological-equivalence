from __future__ import annotations
from phonological_requirements import certificate, paths
import itertools, json
from pathlib import Path

from . import frag_gua as FG
from .core import ABSENT, read
from .footprint import footprint, narrow_footprint
from .products import gua_products

OUT = paths.CERTIFICATES


def main():
    sg = FG.make_sigma()
    D = FG.declarations("typed", "dynamic", FG.NEXT_WORD, None, "stop")
    segs_a = ["ɛ", "t", "a"]; segs_b = ["ɛ", ABSENT, "a"]
    words = [0, 0, 1]; ph = [0, 0]
    ref = FG.struct_from_segments(segs_a, words, ph)
    loc = ref.nodes("seg")[0]
    wa = read(sg, ref, FG.struct_from_segments(segs_a, words, ph), D["A"], loc).triple()
    wb = read(sg, ref, FG.struct_from_segments(segs_b, words, ph), D["A"], loc).triple()
    rec = {"minimal_witness": {"state_a": "".join(segs_a), "state_b": "".join(segs_b),
                               "narrow_footprint": sorted(x.index for x in
                                                          narrow_footprint(sg, ref, D["A"], loc)),
                               "corrected_footprint": sorted(x.index for x in
                                                             footprint(sg, ref, D["A"], loc)),
                               "readers_a": list(wa), "readers_b": list(wb),
                               "equal": wa == wb}}
    viol_n, viol_w, inert = [], [], True
    candidates = reader_checks = product_count = 0
    for focal, prod in gua_products():
        r = FG.struct_from_segments(prod.reference, prod.words, prod.phrase_of_word)
        base = list(prod.reference)
        states = []
        for combo in itertools.product(FG.ALPHABET, repeat=len(focal)):
            st = list(base)
            for q, v in zip(focal, combo):
                st[q] = v
            states.append(tuple(st))
        product_count += 1
        candidates += len(states)
        for nm, d in D.items():
            for lc in r.nodes("seg"):
                gn, gw = {}, {}
                for st in states:
                    S = FG.struct_from_segments(st, prod.words, prod.phrase_of_word)
                    kn = tuple(st[x.index] for x in sorted(narrow_footprint(sg, S, d, lc),
                                                           key=lambda z: z.index))
                    kw = tuple(st[x.index] for x in sorted(footprint(sg, S, d, lc),
                                                           key=lambda z: z.index))
                    rr = read(sg, r, S, d, lc)
                    reader_checks += 1
                    gn.setdefault(kn, set()).add((rr.triple(), rr.context, rr.pressure))
                    gw.setdefault(kw, set()).add(rr.triple())
                for k, v in gn.items():
                    if len({x[0] for x in v}) > 1:
                        viol_n.append({"product": prod.id, "schema": nm, "locus": lc.index,
                                       "key": list(k), "readers": sorted(str(x[0]) for x in v),
                                       "context_false_in_all": all(not x[1] for x in v)})
                        inert &= all(not x[1] for x in v) and not read(sg, r, r, d, lc).marked
                        break
                for k, v in gw.items():
                    if len(v) > 1:
                        viol_w.append({"product": prod.id, "schema": nm, "locus": lc.index})
                        break
    rec["narrow_violations_in_the_eight_products"] = viol_n
    rec["corrected_violations_in_the_eight_products"] = viol_w
    rec["all_narrow_witnesses_have_false_context"] = inert
    rec["coverage"] = {"products": product_count, "candidates": candidates, "reader_checks": reader_checks}
    rec["all_pass"] = (product_count == 8 and candidates == 9464 and reader_checks > 0
                       and not rec["minimal_witness"]["equal"] and len(viol_n) == 12
                       and not viol_w and inert)
    OUT.mkdir(parents=True, exist_ok=True)
    certificate.write("footprint_soundness.json", rec)
    print(json.dumps({"minimal_witness_readers_equal": rec["minimal_witness"]["equal"],
                      "narrow_violations": len(viol_n),
                      "corrected_violations": len(viol_w),
                      "all_witnesses_score_inert": inert}, indent=1))

    return 0 if rec["all_pass"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
