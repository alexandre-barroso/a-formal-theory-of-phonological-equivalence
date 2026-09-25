from __future__ import annotations

import json
from fractions import Fraction
from pathlib import Path
from typing import Sequence

from phonological_opacity.fragments.gua import GuaFragment, load_spec

from .exact import Ineq, verify
from .guaext import ConstructedInput, fragment, named_fragment, observation_of
from .models import CurrentMarkedness, Retained, SharedActivity
from .regions import (ItemSystem, RegionResult, item_system, joint_region,
                      minimal_infeasible_core, reduce_under_nonnegativity)
from .source_regression import TEBAY_12, TEBAY_13, TEBAY_13M
from phonological_grounding.results import bare

SPEC = load_spec()
DEV_ITEMS = ("G34a", "G34b", "N7", "G37c", "C24ei", "OR38", "C21b", "C23UE")

CONTROL_ITEMS = {
    "OR12a": (TEBAY_12, "tuhe"),
    "OR25oE": (TEBAY_13M, "kpɛɛsɛ"),
    "OR25oE_wide": (TEBAY_13, "kpɛɛsɛ"),
}


def _system(model, item: str, frag: GuaFragment, target: str) -> ItemSystem:
    cands, fibre = [], []
    for idx, segs in model.candidates():
        cands.append((idx, model.symbolic(segs)))
        if frag.observe(segs) == target:
            fibre.append(idx)
    return item_system(item, cands, fibre,
                       variables=list(model.variables()),
                       nonneg=list(model.variables()))


def build(model_name: str, item: str, **kw) -> tuple[ItemSystem, list[str]]:
    if item in CONTROL_ITEMS:
        ci, target = CONTROL_ITEMS[item]
        frag = fragment(ci, target)
    else:
        frag = named_fragment(item)
        target = observation_of(item)
    if model_name == "RETAINED":
        m = Retained(frag, **kw)
    elif model_name == "CURRENT-MARKEDNESS":
        m = CurrentMarkedness(frag)
    elif model_name == "SHARED-ACTIVITY":
        m = SharedActivity(frag, **kw)
    else:
        raise KeyError(model_name)
    return _system(m, item, frag, target), list(m.variables())


def region_for(model_name: str, items: Sequence[str], label: str = "", **kw) -> tuple[RegionResult, list[ItemSystem], list[str]]:
    systems = []
    variables: list[str] = []
    for it in items:
        s, variables = build(model_name, it, **kw)
        systems.append(s)
    res = joint_region(systems, variables, label=label or f"{model_name}:{'+'.join(items)}")
    return res, systems, variables


def _pack(r: RegionResult, systems: Sequence[ItemSystem]) -> dict:
    d = {"label": r.label, "status": r.status, "witness": r.witness,
         "representative_choice": r.choice, "detail": r.detail,
         "fibres": {s.item: s.fibre for s in systems},
         "candidates": {s.item: s.candidates for s in systems}}
    if r.status != "NONEMPTY" and r.empty_traces:
        d["traces"] = r.empty_traces[:4]
    return d


def run(out_dir: Path | None = None) -> dict:
    report: dict = {}

    per = {}
    systems_all = []
    for i in DEV_ITEMS:
        r, s, v = region_for("RETAINED", [i])
        per[i] = _pack(r, s)
        systems_all.extend(s)
    rj, sj, vj = region_for("RETAINED", list(DEV_ITEMS), label="RETAINED:joint(8)")
    per["JOINT"] = _pack(rj, sj)
    rows: list[Ineq] = []
    choice = rj.choice or {}
    for s in sj:
        rows.extend(s.systems[choice.get(s.item, s.representatives[0])])
    per["dissertation_point_ok"] = not verify(rows, Retained(named_fragment("N7")).point())
    report["RETAINED"] = per

    sa: dict = {}
    for guard in (True, False):
        for da in ("zero", "exempt"):
            key = f"guard={guard},deleted={da}"
            kw = dict(phrase_guard=guard, deleted_activity=da)
            block = {}
            for i in ("OR12a", "OR25oE", "G34a", "G34b"):
                r, s, v = region_for("SHARED-ACTIVITY", [i], **kw)
                block[i] = _pack(r, s)
            for combo, name in (
                (["OR12a", "OR25oE", "G34a"], "POSTER_DOMAIN"),
                (["OR12a", "OR25oE", "G34a", "G34b"], "POSTER_PLUS_G34b"),
                (["OR12a", "OR25oE_wide", "G34a"], "WIDE_GENERATOR"),
                (list(DEV_ITEMS), "FULL_DEV"),
            ):
                r, s, v = region_for("SHARED-ACTIVITY", combo,
                                     label=f"SA:{name}", **kw)
                block[name] = _pack(r, s)
                if r.status == "EMPTY":
                    allrows: list[Ineq] = []
                    for it in s:
                        allrows.extend(it.systems[it.representatives[-1]])
                    core = minimal_infeasible_core(
                        reduce_under_nonnegativity(allrows, v), v)
                    block[name]["infeasible_core"] = [str(c) for c in (core or [])]
                    block[name]["core_representatives"] = {
                        it.item: it.representatives[-1] for it in s}
            sa[key] = block
    report["SHARED-ACTIVITY"] = sa

    cm = {}
    for i in ("G34a", "G34b", "OR38"):
        r, s, v = region_for("CURRENT-MARKEDNESS", [i])
        cm[i] = _pack(r, s)
        if r.status == "EMPTY":
            allrows = list(s[0].systems[s[0].representatives[0]])
            core = minimal_infeasible_core(reduce_under_nonnegativity(allrows, v), v)
            cm[i]["infeasible_core"] = [str(c) for c in (core or [])]
    report["CURRENT-MARKEDNESS"] = cm

    if out_dir:
        out_dir.mkdir(parents=True, exist_ok=True)
        (out_dir / "dev_regions.json").write_text(
            json.dumps(bare(report), indent=2, ensure_ascii=False))
    return report


if __name__ == "__main__":
    import sys
    out = Path(sys.argv[1]) if len(sys.argv) > 1 else None
    print(json.dumps(run(out), indent=2, ensure_ascii=False)[:8000])
