from __future__ import annotations

import json
from typing import Mapping

from phonological_opacity.fragments.gua import MARKEDNESS, all_fragments, load_spec

from .adequacy import l_readers
from .gua_decls import SCHEMA_ORDER, signature_from_spec
from .lang import read
from .variants import build_declarations


def search(variant: str = "dynamic_next_word", spec: Mapping | None = None) -> dict:
    spec = spec or load_spec()
    decls = build_declarations(variant)
    out: dict[str, dict] = {}
    for frag in all_fragments(spec):
        sig = signature_from_spec(spec, frag.record)
        alphabet = list(spec["alphabet"])
        found = None
        checked = 0
        for name in SCHEMA_ORDER:
            d = decls[name]
            for q in range(frag.n):
                groups: dict[tuple, list[int]] = {}
                for i, cand in frag.all_candidates():
                    t = read(sig, frag.reference, cand, d, q).triple()
                    groups.setdefault(t, []).append(i)
                for triple, members in groups.items():
                    if len(members) < 2:
                        continue
                    for i in members[:80]:
                        ci = frag.candidate(i)
                        for j in members[:80]:
                            if j <= i:
                                continue
                            cj = frag.candidate(j)
                            for p in frag.focal:
                                for v in alphabet:
                                    ei = list(ci); ei[p] = v
                                    ej = list(cj); ej[p] = v
                                    checked += 1
                                    ti = read(sig, frag.reference, tuple(ei), d, q).triple()
                                    tj = read(sig, frag.reference, tuple(ej), d, q).triple()
                                    if ti != tj:
                                        found = {
                                            "schema": name, "locus": q,
                                            "shared_triple": list(triple),
                                            "state_a": list(ci), "state_b": list(cj),
                                            "edit": {"origin": p, "value": v},
                                            "triple_after_a": list(ti),
                                            "triple_after_b": list(tj),
                                        }
                                        break
                                if found:
                                    break
                            if found:
                                break
                        if found:
                            break
                    if found:
                        break
                if found:
                    break
            if found:
                break
        out[frag.id] = {"witness": found, "pairs_checked": checked}
        if found:
            break
    return {
        "variant": variant,
        "conjecture": ("the retained record's coordinates (Def, G) are contextual, "
                       "i.e. equality of the current typed triple survives every "
                       "licensed operation"),
        "verdict": ("REFUTED" if any(v["witness"] for v in out.values())
                    else "no witness found in the searched region"),
        "per_input": out,
    }


if __name__ == "__main__":
    print(json.dumps(search(), ensure_ascii=False, indent=1))
