from __future__ import annotations

import time
from dataclasses import dataclass
from typing import Optional, Sequence

from .kernel import (
    Trace,
    block_count,
    context_trace,
    join,
    partition_of,
)
from .protocols import (
    BRIDGES,
    BRIDGE_LICENCE,
    LICENCE_ORDER,
    Context,
    Step,
    bridge_seg,
    enumerate_steps,
)
from .structures import GuaContext, Skeleton, State


def selected_candidates(ctx: GuaContext, skeleton: Skeleton,
                        identifier: str) -> tuple[list[tuple[str, ...]], int]:
    fragment = ctx.fragment(skeleton, identifier)
    best: Optional[int] = None
    minima: list[tuple[str, ...]] = []
    for _i, candidate in fragment.all_candidates():
        value = fragment.score8(candidate)
        if best is None or value < best:
            best, minima = value, [tuple(candidate)]
        elif value == best:
            minima.append(tuple(candidate))
    return minima, int(best if best is not None else 0)


@dataclass
class FrameRecord:
    step: Step
    trace: Trace
    commutes: bool
    image_of_selected: list[str]
    selected_for_framed: list[str]
    framed_states: int
    framed_minimum8: int


def commuting_frames(ctx: GuaContext, name: str, skeleton: Skeleton,
                     licence_ceiling: str = "PROPOSED_ELICITATION",
                     budget_states: int = 60_000) -> tuple[list[FrameRecord], list[dict]]:
    base_minima, _base_best = selected_candidates(ctx, skeleton, f"base_{name}")
    base_images = sorted({bridge_seg(ctx, State(skeleton, m)) for m in base_minima})
    records: list[FrameRecord] = []
    skipped: list[dict] = []
    for step in enumerate_steps(ctx, skeleton):
        if LICENCE_ORDER[step.licence()] > LICENCE_ORDER[licence_ceiling]:
            continue
        trace = context_trace(ctx, Context((step,)), skeleton)
        if trace is None:
            continue
        size = len(ctx.alphabet) ** len(ctx.focal(trace.target))
        if size > budget_states:
            skipped.append({"frame": step.describe(), "framed_states": size,
                            "reason": "over the declared compute budget"})
            continue
        framed_minima, framed_best = selected_candidates(
            ctx, trace.target, f"framed_{name}_{step.describe()}")
        image = sorted({bridge_seg(ctx, State(trace.target, trace.apply(m)))
                        for m in base_minima})
        framed_obs = sorted({bridge_seg(ctx, State(trace.target, m))
                             for m in framed_minima})
        records.append(FrameRecord(step, trace, image == framed_obs, image,
                                   framed_obs, size, framed_best))
    _ = base_images
    return records, skipped


def experimental_kernel(ctx: GuaContext, skeleton: Skeleton,
                        records: Sequence[FrameRecord],
                        licence_ceiling: str) -> dict:
    states = ctx.candidates(skeleton)
    bridges = [b for b in BRIDGES
               if LICENCE_ORDER[BRIDGE_LICENCE[b]] <= LICENCE_ORDER[licence_ceiling]]
    depth0 = [partition_of([BRIDGES[b](ctx, s) for s in states]) for b in bridges]

    def columns_for(record: FrameRecord) -> list[tuple[int, ...]]:
        targets = [State(record.trace.target, record.trace.apply(s.values))
                   for s in states]
        return [partition_of([BRIDGES[b](ctx, t) for t in targets]) for b in bridges]

    all_columns = list(depth0)
    commuting_columns = list(depth0)
    for record in records:
        columns = columns_for(record)
        all_columns.extend(columns)
        if record.commutes:
            commuting_columns.extend(columns)
    kappa_rep = join(*all_columns)
    kappa_exp = join(*commuting_columns)
    kappa_direct = join(*depth0)
    return {
        "states": len(states),
        "classes_direct_depth0": block_count(kappa_direct),
        "classes_rep_depth1": block_count(kappa_rep),
        "classes_exp_depth1": block_count(kappa_exp),
        "commuting_frames": sum(1 for r in records if r.commutes),
        "non_commuting_frames": sum(1 for r in records if not r.commutes),
        "formal_minus_warranted_classes": block_count(kappa_rep) - block_count(kappa_exp),
    }


def registered_probes(ctx: GuaContext, name: str, skeleton: Skeleton,
                      frame_words: Sequence[str],
                      budget_states: int = 60_000) -> list[dict]:
    out: list[dict] = []
    for word in frame_words:
        for op in ("suffix_word", "prefix_word"):
            step = Step(op, (word,))
            trace = context_trace(ctx, Context((step,)), skeleton)
            if trace is None:
                continue
            size = len(ctx.alphabet) ** len(ctx.focal(trace.target))
            if size > budget_states:
                continue
            minima, best = selected_candidates(
                ctx, trace.target, f"probe_{name}_{op}_{word}")
            observations = sorted({bridge_seg(ctx, State(trace.target, m))
                                   for m in minima})
            faithful = bridge_seg(ctx, State(trace.target, trace.target.reference))
            out.append({
                "base_input": name,
                "frame": step.describe(),
                "licence": step.licence(),
                "framed_words": ["".join(w) for w in trace.target.words],
                "framed_phrases": list(trace.target.phrases),
                "framed_states": size,
                "predicted_outputs": observations,
                "unique_minimiser": len(minima) == 1,
                "minimum8": best,
                "faithful_output": faithful,
                "process_applies": observations != [faithful],
                "status": "COMPUTED_PREDICTION",
                "evidence_status": "PENDING_INDEPENDENT_EVIDENCE",
            })
    return out
