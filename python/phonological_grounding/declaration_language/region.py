from __future__ import annotations

import json
from fractions import Fraction
from typing import Mapping, Sequence

from phonological_opacity.fragments.gua import MARKEDNESS, GuaFragment, all_fragments, load_spec

from .adequacy import l_locus_terms, l_readers
from .gua_decls import SCHEMA_ORDER, signature_from_spec
from .variants import VARIANTS, build_declarations


def coefficient_table(frag: GuaFragment, spec: Mapping, decls) -> list[tuple[int, ...]]:
    sig = signature_from_spec(spec, frag.record)
    ref = l_readers(sig, frag.reference, frag.reference, decls)
    rows = []
    for _i, cand in frag.all_candidates():
        t = l_locus_terms(sig, frag.reference, cand, decls, ref, MARKEDNESS)
        rows.append(tuple(x for k in SCHEMA_ORDER for x in t[k]))
    return rows


def coefficient_identity(spec: Mapping | None = None) -> dict:
    spec = spec or load_spec()
    frags = all_fragments(spec)
    base = {f.id: coefficient_table(f, spec, build_declarations("baseline"))
            for f in frags}
    out = {}
    for name in VARIANTS:
        decls = build_declarations(name)
        per = {}
        for f in frags:
            rows = coefficient_table(f, spec, decls)
            diff = [i for i, (a, b) in enumerate(zip(rows, base[f.id])) if a != b]
            per[f.id] = {"differing_candidates": len(diff), "first": diff[:5]}
        out[name] = {
            "identical_for_all_weights_and_lambda":
                all(v["differing_candidates"] == 0 for v in per.values()),
            "per_input": per,
        }
    return out


def difference_rows(frag: GuaFragment, spec: Mapping, decls, winner: int
                    ) -> list[tuple[tuple[int, ...], tuple[int, ...]]]:
    rows = coefficient_table(frag, spec, decls)
    obs = [frag.observe(c) for _i, c in frag.all_candidates()]
    target = frag.record["observation"]
    fiber = {i for i, y in enumerate(obs) if y == target}
    w = rows[winner]
    out = set()
    for i, r in enumerate(rows):
        if i in fiber:
            continue
        d_old = tuple(r[2 * k] - w[2 * k] for k in range(9))
        d_new = tuple(r[2 * k + 1] - w[2 * k + 1] for k in range(9))
        if any(d_old) or any(d_new):
            out.add((d_old, d_new))
        else:
            out.add((d_old, d_new))
    return sorted(out)


def _dominates(a, b) -> bool:
    return all(x <= y for x, y in zip(a, b)) and a != b


def reduce_rows(rows: Sequence[tuple[tuple[int, ...], tuple[int, ...]]],
                lam: Fraction) -> list[tuple[Fraction, ...]]:
    forms = sorted({tuple(Fraction(d_old[k]) + lam * d_new[k] for k in range(9))
                    for d_old, d_new in rows})
    keep = []
    for f in forms:
        if any(_dominates(g, f) for g in forms if g != f):
            continue
        keep.append(f)
    return keep


def region(name: str, spec: Mapping | None = None, lam: Fraction | None = None) -> dict:
    spec = spec or load_spec()
    decls = build_declarations(name)
    out = {"variant": name, "lambda": str(lam) if lam is not None else "1/8",
           "inputs": {}}
    for frag in all_fragments(spec):
        l = lam if lam is not None else frag.lam
        obs = [frag.observe(c) for _i, c in frag.all_candidates()]
        target = frag.record["observation"]
        fiber = [i for i, y in enumerate(obs) if y == target]
        branches = {}
        for j in fiber:
            rows = difference_rows(frag, spec, decls, j)
            forms = reduce_rows(rows, l)
            wvec = [frag.weights[k] for k in SCHEMA_ORDER]
            holds = all(sum(c * w for c, w in zip(f, wvec)) > 0 for f in forms)
            branches[j] = {
                "raw_rows": len(rows),
                "irredundant_forms": len(forms),
                "declared_point_satisfies": holds,
                "forms": [[str(c) for c in f] for f in forms],
            }
        out["inputs"][frag.id] = {
            "fiber": fiber,
            "schema_order": list(SCHEMA_ORDER),
            "branches": branches,
            "declared_point_feasible": any(b["declared_point_satisfies"]
                                           for b in branches.values()),
        }
    return out


if __name__ == "__main__":
    print(json.dumps(coefficient_identity(), indent=1))


def region_equality(spec: Mapping | None = None, variant: str = "witness") -> dict:
    spec = spec or load_spec()
    base = build_declarations("baseline")
    frozen = build_declarations(variant)
    out: dict[str, dict] = {}
    for frag in all_fragments(spec):
        rows_b = coefficient_table(frag, spec, base)
        rows_f = coefficient_table(frag, spec, frozen)
        delta = [i for i in range(len(rows_b)) if rows_b[i] != rows_f[i]]
        if not delta:
            out[frag.id] = {"cheapened_candidates": 0, "regions_equal": True,
                            "reason": "the two readings have identical coefficients"}
            continue
        obs = [frag.observe(c) for _i, c in frag.all_candidates()]
        fiber = [i for i, y in enumerate(obs) if y == frag.record["observation"]]
        j = fiber[0]
        lam = frag.lam

        def form(row, ref):
            return tuple(Fraction(row[2 * k] - ref[2 * k])
                         + lam * Fraction(row[2 * k + 1] - ref[2 * k + 1])
                         for k in range(9))

        appendix = sorted({form(rows_b[i], rows_b[j])
                           for i in range(len(rows_b)) if i not in fiber})
        extra = sorted({form(rows_f[i], rows_f[j]) for i in delta})
        certs, undominated = [], []
        for c in extra:
            witness = next((a for a in appendix
                            if all(x <= y for x, y in zip(a, c))), None)
            if witness is None:
                undominated.append([str(x) for x in c])
            else:
                certs.append({"extra_row": [str(x) for x in c],
                              "dominating_appendix_row": [str(x) for x in witness]})
        out[frag.id] = {
            "winner": j,
            "cheapened_candidates": len(delta),
            "distinct_extra_rows": len(extra),
            "appendix_rows": len(appendix),
            "dominated": len(certs),
            "undominated": undominated,
            "regions_equal": not undominated,
            "certificates": certs[:5],
        }
    return {
        "variant": variant,
        "schema_order": list(SCHEMA_ORDER),
        "regions_equal_everywhere": all(v["regions_equal"] for v in out.values()),
        "per_input": out,
    }
