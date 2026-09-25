from __future__ import annotations
from phonological_grounding.results import bare

import json
from fractions import Fraction
from pathlib import Path
from typing import Sequence

from phonological_opacity.fragments.gua import GuaFragment

from .design_length import TRANSPARENT_CONTROLS, LengthCell, battery
from .dev_regions import build as build_dev
from .guaext import fragment
from .models import SA_VARS, SharedActivity
from .regions import (ItemSystem, item_system, joint_region,
                      minimal_infeasible_core, reduce_under_nonnegativity)
from .ruleserial import RuleSerial

SA_DEV_ITEMS = ("OR12a", "OR25oE", "G34a")
SA_DEV_ITEMS_WIDE = ("OR12a", "OR25oE_wide", "G34a")


def sa_cell_system(cell: LengthCell, target: str, *, phrase_guard=True,
                   deleted_activity="zero") -> ItemSystem:
    frag = fragment(cell.inp, target)
    m = SharedActivity(frag, phrase_guard=phrase_guard,
                       deleted_activity=deleted_activity)
    cands, fib = [], []
    for idx, segs in m.candidates():
        cands.append((idx, m.symbolic(segs)))
        if frag.observe(segs) == target:
            fib.append(idx)
    return item_system(f"{cell.inp.id}->{target}", cands, fib,
                       variables=list(SA_VARS), nonneg=list(SA_VARS))


def sa_dev_systems(**kw) -> list[ItemSystem]:
    return [build_dev("SHARED-ACTIVITY", i, **kw)[0] for i in SA_DEV_ITEMS]


def analyse(out: Path | None = None, **kw) -> dict:
    dev = sa_dev_systems(**kw)
    dev_region = joint_region(dev, list(SA_VARS), label="SA:dev")
    report: dict = {
        "shared_activity_dev_region": {
            "items": SA_DEV_ITEMS, "status": dev_region.status,
            "witness": dev_region.witness, "detail": dev_region.detail,
        },
        "cells": [],
    }
    for cell in battery():
        frag = fragment(cell.inp, cell.opaque)
        row = {
            "cell": cell.inp.id, "v1": cell.v1, "v3": cell.v3,
            "opaque": cell.opaque, "transparent": cell.transparent,
            "RETAINED": _retained_row(frag, cell),
            "RULE-SERIAL": RuleSerial(frag).output(),
        }
        sa = {}
        for target, name in ((cell.opaque, "opaque"), (cell.transparent, "transparent")):
            try:
                sys_t = sa_cell_system(cell, target, **kw)
            except ValueError as exc:
                sa[name] = {"status": "UNREALISABLE", "detail": str(exc)}
                continue
            res = joint_region(dev + [sys_t], list(SA_VARS),
                               label=f"SA:dev+{cell.inp.id}:{name}")
            entry = {"status": res.status, "witness": res.witness,
                     "detail": res.detail}
            if res.status == "EMPTY":
                rows = []
                for it in dev + [sys_t]:
                    rows.extend(it.systems[it.representatives[0]])
                core = minimal_infeasible_core(
                    reduce_under_nonnegativity(rows, list(SA_VARS)), list(SA_VARS))
                entry["infeasible_core"] = [str(c) for c in (core or [])]
            sa[name] = entry
        row["SHARED-ACTIVITY"] = sa
        o, t = sa.get("opaque", {}).get("status"), sa.get("transparent", {}).get("status")
        row["sa_verdict"] = (
            "FORCED_OPAQUE" if o == "NONEMPTY" and t == "EMPTY" else
            "FORCED_TRANSPARENT" if t == "NONEMPTY" and o == "EMPTY" else
            "BOTH_AVAILABLE" if o == "NONEMPTY" and t == "NONEMPTY" else
            "UNKNOWN")
        report["cells"].append(row)

    controls = {}
    for name, ci in TRANSPARENT_CONTROLS.items():
        f = fragment(ci)
        r = f.evaluate()
        controls[name] = {
            "note": ci.note,
            "RETAINED_outputs": sorted({f.observe(f.candidate(i)) for i in r["minima"]}),
            "RETAINED_unique": len(r["minima"]) == 1,
            "RULE-SERIAL": RuleSerial(f).output(),
            "reference_projection": f.observe(f.reference),
        }
    report["transparent_controls"] = controls

    if out:
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(json.dumps(bare(report), indent=2, ensure_ascii=False))
    return report


def _retained_row(frag: GuaFragment, cell: LengthCell) -> dict:
    r = frag.evaluate()
    outs = sorted({frag.observe(frag.candidate(i)) for i in r["minima"]})
    return {"minimum8": r["minimum8"], "n_minima": len(r["minima"]),
            "outputs": outs,
            "selects_opaque": outs == [cell.opaque]}


if __name__ == "__main__":
    import sys
    out = Path(sys.argv[1]) if len(sys.argv) > 1 else None
    print(json.dumps(analyse(out), indent=2, ensure_ascii=False)[:9000])
