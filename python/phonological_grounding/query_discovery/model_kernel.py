from __future__ import annotations

import time
from fractions import Fraction
from typing import Optional, Sequence

from .discovery import selected_candidates
from .kernel import block_count, context_trace, join, minimum_cost_battery, partition_of
from .measure import query_space_report
from .models import LocusVector, ModelInstance, locus_vector, model_instances, observation_of
from .protocols import (
    BRIDGES,
    BRIDGE_COST,
    BRIDGE_LICENCE,
    LICENCE_ORDER,
    Context,
    Step,
    enumerate_steps,
)
from .structures import GuaContext, Skeleton, State

GUA_ORDER = ("G34a", "G34b", "N7", "G37c", "C24ei", "OR38", "C21b", "C23UE")


def _skeleton_budget(ctx: GuaContext, skeleton: Skeleton, budget: int) -> bool:
    return len(ctx.alphabet) ** len(ctx.focal(skeleton)) <= budget


def enumerate_model_protocols(ctx: GuaContext, licence_ceiling: str,
                              max_depth: int, budget: int
                              ) -> list[tuple[str, str, str, Skeleton]]:
    out: list[tuple[str, str, str, Skeleton]] = []
    for name in GUA_ORDER:
        base = ctx.skeletons[name]
        out.append((name, "[-]", "ATTESTED", base))
        if max_depth < 1:
            continue
        for step in enumerate_steps(ctx, base):
            if LICENCE_ORDER[step.licence()] > LICENCE_ORDER[licence_ceiling]:
                continue
            trace = context_trace(ctx, Context((step,)), base)
            if trace is None or not _skeleton_budget(ctx, trace.target, budget):
                continue
            out.append((name, step.describe(), step.licence(), trace.target))
    return out


def run_model_kernel(ctx: GuaContext, licence_ceiling: str = "PROPOSED_ELICITATION",
                     max_depth: int = 1, budget: int = 30_000,
                     verbose: bool = True) -> dict:
    started = time.time()
    instances = model_instances(ctx)
    elicitations = enumerate_model_protocols(ctx, licence_ceiling, max_depth, budget)
    bridges = [b for b in BRIDGES
               if LICENCE_ORDER[BRIDGE_LICENCE[b]] <= LICENCE_ORDER[licence_ceiling]
               and BRIDGE_COST[b] is not None]

    columns: list[list] = []
    protocol_meta: list[dict] = []
    costs: list[Optional[Fraction]] = []
    seen: dict[tuple, int] = {}
    for base_input, frame, licence, skeleton in elicitations:
        key = skeleton.key()
        candidates = ctx.candidates(skeleton)
        fragment = ctx.fragment(skeleton, f"mk_{base_input}_{frame}")
        vectors = [locus_vector(fragment, list(c.values)) for c in candidates]
        for bridge in bridges:
            fn = BRIDGES[bridge]
            column = [observation_of(ctx, m, skeleton, fn, vectors, candidates)
                      for m in instances]
            columns.append(column)
            protocol_meta.append({
                "base_input": base_input, "frame": frame, "licence": licence,
                "bridge": bridge, "bridge_licence": BRIDGE_LICENCE[bridge],
                "words": ["".join(w) for w in skeleton.words],
                "phrases": list(skeleton.phrases),
                "states": len(candidates),
            })
            costs.append(Fraction(1) + Fraction(max(0, len(skeleton.words) - 1))
                         + BRIDGE_COST[bridge])
        seen[key] = seen.get(key, 0) + 1
        if verbose:
            print(f"    {base_input} {frame}: {len(candidates)} candidates "
                  f"({time.time() - started:.0f}s)", flush=True)

    kernel = join(*[partition_of(c) for c in columns])
    m = block_count(kernel)
    classes: dict[int, list[str]] = {}
    for i, cls in enumerate(kernel):
        classes.setdefault(cls, []).append(instances[i].id)

    separating: dict[str, list[str]] = {}
    for k, column in enumerate(columns):
        pairs = []
        for i in range(len(instances)):
            for j in range(i + 1, len(instances)):
                if column[i] != column[j]:
                    pairs.append(f"{instances[i].id}|{instances[j].id}")
        if pairs:
            separating[str(k)] = pairs

    battery = minimum_cost_battery(columns, costs)
    n = len(instances)
    return {
        "artifact": "t5_model_level_kernel",
        "M_is_partial": True,
        "M_note": "appendix I's repaired resolvers and appendix J's rival "
                  "registry are not yet published; re-run when they are.",
        "licence_ceiling": licence_ceiling,
        "max_depth": max_depth,
        "compute_budget_states": budget,
        "instances": [{"id": i.id, "provenance": i.provenance,
                       "description": i.description,
                       "lambda": str(i.lam),
                       "modes": {k: v for k, v in i.modes.items() if v != "retained"}}
                      for i in instances],
        "protocols": len(columns),
        "protocol_meta": protocol_meta,
        "a_priori_query_space": query_space_report(n),
        "licensed_query_space": query_space_report(m),
        "classes": m,
        "class_members": list(classes.values()),
        "collapse_boolean_bits": max(0, n - 1) - max(0, m - 1),
        "separating_protocol_count": len(separating),
        "minimum_cost_battery": {
            "status": battery.status,
            "minimum_cost": None if battery.minimum_cost is None else str(battery.minimum_cost),
            "optima_count": len(battery.optima),
            "optima": [[protocol_meta[i] | {"index": i} for i in option]
                       for option in battery.optima[:20]],
            "explored": battery.explored,
            "note": battery.note,
        },
        "seconds": round(time.time() - started, 2),
    }


def verify_variant_scorer(ctx: GuaContext) -> dict:
    checked = 0
    for name in GUA_ORDER:
        skeleton = ctx.skeletons[name]
        fragment = ctx.fragment(skeleton, f"verify_{name}")
        baseline = model_instances(ctx)[0]
        for _i, candidate in fragment.all_candidates():
            vector = locus_vector(fragment, candidate)
            if baseline.score8(vector) != fragment.score8(candidate):
                raise AssertionError(f"variant scorer disagrees at {name} {candidate}")
            checked += 1
    return {"artifact": "variant_scorer_check", "candidates_checked": checked,
            "agreement": "exact"}
