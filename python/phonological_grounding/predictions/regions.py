from __future__ import annotations

import itertools
from dataclasses import dataclass
from fractions import Fraction
from typing import Callable, Sequence

from .exact import Infeasible, Ineq, LinForm, eliminate, feasible_witness, verify

GRID = tuple(Fraction(n) for n in (1, 2, 3, 4, 5, 6, 8, 10, 12, 16, 20, 24, 32, 48, 64)) + (
    Fraction(1, 2), Fraction(1, 4), Fraction(1, 8), Fraction(3, 2), Fraction(3, 4))


@dataclass
class ItemSystem:

    item: str
    representatives: list[int]
    systems: dict[int, list[Ineq]]
    fibre: list[int]
    candidates: int


def item_system(
    item: str,
    candidates: Sequence[tuple[int, LinForm]],
    fibre: Sequence[int],
    *,
    variables: Sequence[str],
    nonneg: Sequence[str] | None = None,
    positive: Sequence[str] = (),
) -> ItemSystem:
    score = dict(candidates)
    fib = sorted(set(fibre))
    if not fib:
        raise ValueError(f"{item}: empty correct fibre; the observation is unrealisable in GEN")
    base: list[Ineq] = []
    for v in (nonneg if nonneg is not None else variables):
        base.append(Ineq(LinForm.var(v), v in positive, f"dom:{v}"))
    systems: dict[int, list[Ineq]] = {}
    for rep in fib:
        rows = list(base)
        for idx, form in candidates:
            if idx in set(fib):
                continue
            rows.append(Ineq(form - score[rep], True, f"{item}:{rep}<{idx}"))
        systems[rep] = rows
    return ItemSystem(item=item, representatives=fib, systems=systems,
                      fibre=fib, candidates=len(score))


@dataclass
class RegionResult:
    label: str
    status: str
    witness: dict[str, str] | None
    choice: dict[str, int] | None
    rows: int
    detail: str = ""
    empty_traces: list[str] | None = None


def joint_region(
    items: Sequence[ItemSystem],
    variables: Sequence[str],
    *,
    label: str = "",
    grid: Sequence[Fraction] = GRID,
    max_choices: int = 4096,
) -> RegionResult:
    choices = [it.representatives for it in items]
    total = 1
    for c in choices:
        total *= len(c)
    if total > max_choices:
        return RegionResult(label, "UNKNOWN", None, None, 0,
                            f"{total} representative choices exceed max_choices={max_choices}")
    traces: list[str] = []
    pre: dict[tuple[str, int], list[Ineq]] = {}
    for it in items:
        for rep in it.representatives:
            pre[(it.item, rep)] = reduce_under_nonnegativity(it.systems[rep], list(variables))
    for combo in itertools.product(*choices):
        rows: list[Ineq] = []
        for it, rep in zip(items, combo):
            rows.extend(it.systems[rep])
        pre_rows: list[Ineq] = []
        for it, rep in zip(items, combo):
            pre_rows.extend(pre[(it.item, rep)])
        rows = _dedupe_rows(rows)
        small = reduce_under_nonnegativity(_dedupe_rows(pre_rows), list(variables))
        from .lp import feasible as _lp_feasible
        res = _lp_feasible(small, list(variables))
        if res.status == "INFEASIBLE":
            traces.append(f"choice {dict(zip([i.item for i in items], combo))}: "
                          f"exact LP infeasible over {len(small)} reduced rows")
            continue
        if res.status != "FEASIBLE":
            traces.append(f"choice {dict(zip([i.item for i in items], combo))}: LP {res.status}")
            continue
        w = res.witness
        bad = verify(rows, w)
        if bad:
            traces.append(f"choice {dict(zip([i.item for i in items], combo))}: "
                          f"witness failed {len(bad)} original rows")
            continue
        return RegionResult(
            label, "NONEMPTY", {k: str(v) for k, v in w.items()},
            {it.item: rep for it, rep in zip(items, combo)}, len(rows),
            "exact rational LP witness, verified against the original system")
    every_infeasible = all("LP infeasible" in t for t in traces)
    return RegionResult(label, "EMPTY" if every_infeasible else "UNKNOWN", None, None, 0,
                        "every representative choice is exactly LP-infeasible"
                        if every_infeasible else
                        "no witness found and emptiness not certified for every choice",
                        traces)


def _dedupe_rows(rows: Sequence[Ineq]) -> list[Ineq]:
    seen: dict[tuple, Ineq] = {}
    for r in rows:
        key = (tuple(sorted(r.form.coeff.items())), r.form.const, r.strict)
        if key not in seen:
            seen[key] = r
    return list(seen.values())


def reduce_under_nonnegativity(rows: Sequence[Ineq], variables: Sequence[str]) -> list[Ineq]:
    rows = _dedupe_rows(rows)
    vec = []
    for r in rows:
        vec.append(tuple(r.form.coeff.get(v, Fraction(0)) for v in variables) + (r.form.const,))
    keep = [True] * len(rows)
    order = sorted(range(len(rows)), key=lambda i: sum(vec[i]))
    for ai in range(len(order)):
        i = order[ai]
        if not keep[i]:
            continue
        for bj in range(len(order)):
            j = order[bj]
            if i == j or not keep[j]:
                continue
            if all(vec[j][k] >= vec[i][k] for k in range(len(vec[i]))):
                if rows[i].strict or not rows[j].strict:
                    keep[j] = False
    return [r for r, k in zip(rows, keep) if k]


def minimal_infeasible_core(rows: Sequence[Ineq], variables: Sequence[str]) -> list[Ineq] | None:
    from .lp import feasible as _lp_feasible
    if _lp_feasible(list(rows), list(variables)).status != "INFEASIBLE":
        return None
    core = list(rows)
    i = 0
    while i < len(core):
        trial = core[:i] + core[i + 1:]
        if _lp_feasible(trial, list(variables)).status == "INFEASIBLE":
            core = trial
        else:
            i += 1
    return core
