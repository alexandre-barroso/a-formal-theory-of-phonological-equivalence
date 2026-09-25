from __future__ import annotations

import math
from fractions import Fraction
from typing import Optional, Sequence

from .kernel import (
    Family,
    block_count,
    graded_refinement,
    join,
    minimum_cost_battery,
    partition_of,
)
from .protocols import BRIDGES, BRIDGE_LICENCE, LICENCE_ORDER
from .structures import GuaContext, Skeleton, State

CEILINGS = ("ATTESTED", "PROPOSED_ELICITATION", "MODEL_INTERNAL")
BRIDGE_DEPTH_LIMIT = {"B_score8": 0}


def bell(n: int) -> int:
    row = [1]
    for _ in range(n):
        nxt = [row[-1]]
        for value in row:
            nxt.append(nxt[-1] + value)
        row = nxt
    return row[0]


def log2_bell_bits(n: int) -> int:
    return bell(n).bit_length()


def query_space_report(n: int) -> dict:
    return {
        "carrier": n,
        "boolean_kernels_log2": max(0, n - 1),
        "nominal_kernels_bits": log2_bell_bits(n),
    }


def measure_product(ctx: GuaContext, name: str, skeleton: Skeleton,
                    max_depth: int = 1) -> dict:
    states = ctx.candidates(skeleton)
    n = len(states)
    report: dict = {"input": name, "states": n, "words": len(skeleton.words),
                    "focal": list(ctx.focal(skeleton)), "max_depth": max_depth,
                    "a_priori": query_space_report(n), "by_licence": {}}
    for ceiling in CEILINGS:
        entry: dict = {}
        for depth in range(max_depth + 1):
            family = Family.build(ctx, skeleton, depth, ceiling, list(BRIDGES),
                                  BRIDGE_DEPTH_LIMIT)
            columns = family.observations(states)
            if not columns:
                continue
            vectors = [partition_of(c) for c in columns]
            kernel = join(*vectors)
            m = block_count(kernel)
            entry[f"depth<={depth}"] = {
                "protocols": len(columns),
                "classes_rep": m,
                "licensed_query_space": query_space_report(m),
                "collapse_boolean_bits": max(0, n - 1) - max(0, m - 1),
            }
        family0 = Family.build(ctx, skeleton, 0, ceiling, list(BRIDGES),
                               BRIDGE_DEPTH_LIMIT)
        columns0 = family0.observations(states)
        kernel0 = join(*[partition_of(c) for c in columns0])
        entry["experimental"] = {
            "protocols": len(columns0),
            "classes_exp": block_count(kernel0),
            "note": "depth-zero protocols only; see PhonologicalGrounding.QueryDiscovery.FrameFutility",
        }
        report["by_licence"][ceiling] = entry
    seg = [BRIDGES["B_seg"](ctx, s) for s in states]
    report["image_B_seg"] = len(set(seg))
    report["merged_pairs_B_seg"] = sum(
        c * (c - 1) // 2 for c in _fibre_sizes(seg))
    return report


def _fibre_sizes(column: Sequence) -> list[int]:
    counts: dict = {}
    for value in column:
        counts[repr(value)] = counts.get(repr(value), 0) + 1
    return list(counts.values())


def battery_report(ctx: GuaContext, skeleton: Skeleton, ceiling: str,
                   depth: int) -> dict:
    states = ctx.candidates(skeleton)
    family = Family.build(ctx, skeleton, depth, ceiling, list(BRIDGES),
                          BRIDGE_DEPTH_LIMIT)
    columns = family.observations(states)
    costs = family.costs()
    protocols = family.protocols()
    result = minimum_cost_battery(columns, costs)
    return {
        "ceiling": ceiling,
        "depth": depth,
        "status": result.status,
        "minimum_cost": None if result.minimum_cost is None else str(result.minimum_cost),
        "optima_count": len(result.optima),
        "optima": [[protocols[i].describe() for i in option] for option in result.optima],
        "explored": result.explored,
        "note": result.note,
    }
