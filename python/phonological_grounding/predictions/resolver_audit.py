from __future__ import annotations
from phonological_grounding.results import bare

import json
from fractions import Fraction
from pathlib import Path

from phonological_opacity.fragments.gua import SCHEMAS, GuaFragment, load_spec

from .design_length import battery
from .exact import verify
from .guaext import fragment, observation_of
from .lp import feasible
from .models import RETAINED_POINT, RETAINED_VARS
from .regions import (_dedupe_rows, item_system, minimal_infeasible_core,
                      reduce_under_nonnegativity)
from .resolvers import (VARIANTS, a_slot_spec, baseline_spec, load_asts,
                        locus_terms, score8, symbolic)

SPEC = load_spec()
DEV = ("G34a", "G34b", "N7", "G37c", "C24ei", "OR38", "C21b", "C23UE")
V = list(RETAINED_VARS)
LAM = Fraction(1, 8)


def _specs() -> dict[str, dict]:
    asts = load_asts()
    out = {"baseline": baseline_spec()}
    for name in VARIANTS:
        if name == "baseline":
            continue
        out[name] = a_slot_spec(asts, name)
    return out


def per_variant_effect(name: str, spec: dict) -> dict:
    rows = {}
    total_changed = 0
    delta_multiset: dict[str, int] = {}
    all_winners_same = True
    all_exclusive = True
    for iid in DEV:
        f = GuaFragment(SPEC, iid)
        base_ev = f.evaluate()
        changed = 0
        deltas: dict[str, int] = {}
        vals = []
        for i in range(f.size):
            segs = f.candidate(i)
            bt = f.locus_terms(segs)
            vt = locus_terms(f, segs, spec)
            if bt != vt:
                changed += 1
                for s in SCHEMAS:
                    if bt[s] != vt[s]:
                        key = f"{s}:old{vt[s][0]-bt[s][0]:+d},new{vt[s][1]-bt[s][1]:+d}"
                        deltas[key] = deltas.get(key, 0) + 1
                        delta_multiset[key] = delta_multiset.get(key, 0) + 1
            vals.append(score8(f, segs, spec, LAM))
        best = min(vals)
        minima = [i for i, v in enumerate(vals) if v == best]
        fibre = base_ev["fiber"]
        winners_same = minima == base_ev["minima"]
        exclusive = bool(minima) and set(minima) <= set(fibre)
        all_winners_same &= winners_same
        all_exclusive &= exclusive
        total_changed += changed
        rows[iid] = {"changed_candidates": changed, "coefficient_deltas": deltas,
                     "minima": minima, "baseline_minima": base_ev["minima"],
                     "winners_identical": winners_same,
                     "exclusively_correct": exclusive,
                     "minimum8": str(best), "baseline_minimum8": base_ev["minimum8"]}
    return {"variant": name, "declared": spec, "per_input": rows,
            "total_changed_candidates": total_changed,
            "coefficient_delta_multiset": delta_multiset,
            "score_identical_to_appendix": total_changed == 0,
            "all_winners_identical": all_winners_same,
            "all_eight_exclusively_correct": all_exclusive}


def region_for_variant(spec: dict) -> dict:
    systems = []
    for iid in DEV:
        f = GuaFragment(SPEC, iid)
        y = observation_of(iid)
        cands = [(i, symbolic(f, f.candidate(i), spec, LAM)) for i in range(f.size)]
        fib = [i for i in range(f.size) if f.observe(f.candidate(i)) == y]
        systems.append(item_system(iid, cands, fib, variables=V, nonneg=V))
    best = None
    for it in systems:
        pass
    import itertools
    for combo in itertools.product(*[s.representatives for s in systems]):
        rows = []
        for s, rep in zip(systems, combo):
            rows.extend(s.systems[rep])
        rows = _dedupe_rows(rows)
        small = reduce_under_nonnegativity(rows, V)
        res = feasible(small, V)
        if res.status == "FEASIBLE" and not verify(rows, res.witness):
            best = {"status": "NONEMPTY",
                    "witness": {k: str(v) for k, v in res.witness.items()},
                    "facets": len(small), "rows": small,
                    "dissertation_point_admissible": not verify(rows, RETAINED_POINT)}
            break
    if best is None:
        best = {"status": "EMPTY", "witness": None, "facets": 0, "rows": [],
                "dissertation_point_admissible": False}
    return best


def containment(a_rows, b_rows) -> str:
    from .exact import Ineq
    for r in b_rows:
        if not r.form.coeff:
            continue
        neg = Ineq(-r.form, False, "neg:" + r.tag)
        test = list(a_rows) + [neg]
        if feasible(reduce_under_nonnegativity(test, V), V).status != "INFEASIBLE":
            return "NOT_CONTAINED"
    return "CONTAINED"


def card_effect(spec: dict) -> dict:
    out = {}
    for c in battery():
        f = fragment(c.inp, c.opaque)
        vals = [score8(f, f.candidate(i), spec, LAM) for i in range(f.size)]
        best = min(vals)
        minima = [i for i, v in enumerate(vals) if v == best]
        base = f.evaluate()
        outs = sorted({f.observe(f.candidate(i)) for i in minima})
        changed = sum(1 for i in range(f.size)
                      if f.locus_terms(f.candidate(i)) != locus_terms(f, f.candidate(i), spec))
        out[c.inp.id] = {"changed_candidates": changed,
                         "minima": minima, "baseline_minima": base["minima"],
                         "winners_identical": minima == base["minima"],
                         "outputs": outs, "selects_opaque": outs == [c.opaque]}
    return out


def run(out_path: Path | None = None) -> dict:
    specs = _specs()
    report: dict = {
        "method": ("appendix I's ASTs are read from data/declaration_language/spec/ and "
                   "the slot resolution is reimplemented on appendix J's own copy of "
                   "the shared core. The reconstructed BASELINE reproduces the shared "
                   "core's locus terms on all 9,464 candidates, which is what licenses "
                   "the variant numbers below."),
        "variants": {}, "regions": {}, "containment": {}, "card_PC_L1": {},
    }
    base_region = region_for_variant(specs["baseline"])
    report["regions"]["baseline"] = {k: v for k, v in base_region.items() if k != "rows"}
    for name, spec in specs.items():
        eff = per_variant_effect(name, spec)
        report["variants"][name] = eff
        if not eff["all_eight_exclusively_correct"]:
            report["regions"][name] = {"status": "EMPTY on the eight products",
                                       "note": "a failed repair: it does not select the "
                                               "documented observations at the declared weights"}
            continue
        if name == "baseline":
            continue
        reg = region_for_variant(spec)
        report["regions"][name] = {k: v for k, v in reg.items() if k != "rows"}
        if reg["status"] == "NONEMPTY" and base_region["status"] == "NONEMPTY":
            report["containment"][name] = {
                "variant_in_appendix": containment(reg["rows"], base_region["rows"]),
                "appendix_in_variant": containment(base_region["rows"], reg["rows"]),
            }
    for name in ("dynamic_next_word", "dynamic_phrase", "witness", "witness_phrase",
                 "origin_bound", "dynamic_stop_nucleus"):
        report["card_PC_L1"][name] = card_effect(specs[name])
    if out_path:
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(json.dumps(bare(report), indent=2, ensure_ascii=False))
    return report


if __name__ == "__main__":
    import sys
    o = Path(sys.argv[1]) if len(sys.argv) > 1 else None
    r = run(o)
    print(f"{'variant':22s} {'changed':>8s}  {'winners':>8s} {'excl8':>6s}  deltas")
    for name, v in r["variants"].items():
        print(f"  {name:20s} {v['total_changed_candidates']:8d}  "
              f"{str(v['all_winners_identical']):>8s} {str(v['all_eight_exclusively_correct']):>6s}  "
              f"{v['coefficient_delta_multiset']}")
    print("\nregions:")
    for name, g in r["regions"].items():
        print(f"  {name:20s} {g.get('status'):26s} facets={g.get('facets')} "
              f"diss_point={g.get('dissertation_point_admissible')}")
    print("\ncontainment (variant region vs appendix region):")
    for name, c in r["containment"].items():
        print(f"  {name:20s} variant<=appendix: {c['variant_in_appendix']:14s} "
              f"appendix<=variant: {c['appendix_in_variant']}")
    print("\ncard PC-L1:")
    for name, cells in r["card_PC_L1"].items():
        ch = sum(c["changed_candidates"] for c in cells.values())
        same = all(c["winners_identical"] for c in cells.values())
        op = all(c["selects_opaque"] for c in cells.values())
        print(f"  {name:20s} changed={ch:5d} winners_identical={same} selects_opaque_everywhere={op}")
