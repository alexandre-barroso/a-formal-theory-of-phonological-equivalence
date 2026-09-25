from __future__ import annotations
from phonological_grounding.results import bare

import json
import time
from fractions import Fraction
from pathlib import Path
from typing import Optional, Sequence

from phonological_opacity.fragments import lithuanian as lit

from .kernel import (
    Family,
    block_count,
    context_trace,
    graded_refinement,
    join,
    minimum_cost_battery,
    partition_of,
)
from .measure import BRIDGE_DEPTH_LIMIT, CEILINGS, battery_report, measure_product
from .protocols import BRIDGES, Context, Step, bridge_seg, bridge_segtone
from .structures import GuaContext, Skeleton, State, gua_context

from phonological_grounding.paths import results_dir
RESULTS = results_dir() / "query_discovery"
GUA_ORDER = ("G34a", "G34b", "N7", "G37c", "C24ei", "OR38", "C21b", "C23UE")


def _write(name: str, payload: dict) -> Path:
    RESULTS.mkdir(parents=True, exist_ok=True)
    path = RESULTS / name
    path.write_text(json.dumps(bare(payload), ensure_ascii=False, indent=2) + "\n",
                    encoding="utf-8")
    return path


def run_measurement(ctx: GuaContext, max_depth: int = 1) -> dict:
    started = time.time()
    per_input = {}
    for name in GUA_ORDER:
        per_input[name] = measure_product(ctx, name, ctx.skeletons[name], max_depth)
    return {
        "artifact": "t5_arbitrariness_measurement",
        "max_depth": max_depth,
        "bridge_depth_limit": BRIDGE_DEPTH_LIMIT,
        "seconds": round(time.time() - started, 2),
        "per_input": per_input,
    }


def run_batteries(ctx: GuaContext, depth: int = 1) -> dict:
    started = time.time()
    per_input = {}
    for name in GUA_ORDER:
        per_input[name] = {
            ceiling: battery_report(ctx, ctx.skeletons[name], ceiling, depth)
            for ceiling in CEILINGS
        }
    return {
        "artifact": "t5_minimum_cost_batteries",
        "depth": depth,
        "seconds": round(time.time() - started, 2),
        "per_input": per_input,
    }


def _merged_pairs(column: Sequence) -> dict[str, list[int]]:
    groups: dict[str, list[int]] = {}
    for i, value in enumerate(column):
        groups.setdefault(repr(value), []).append(i)
    return {k: v for k, v in groups.items() if len(v) > 1}


def run_tone_bridge(ctx: GuaContext) -> dict:
    started = time.time()
    per_input = {}
    for name in GUA_ORDER:
        skeleton = ctx.skeletons[name]
        states = ctx.candidates(skeleton)
        seg = [bridge_seg(ctx, s) for s in states]
        tone = [bridge_segtone(ctx, s) for s in states]
        groups = _merged_pairs(seg)
        merged = sum(len(v) * (len(v) - 1) // 2 for v in groups.values())
        resolved = 0
        residual = 0
        residual_examples: list[dict] = []
        fragment = ctx.fragment(skeleton, f"tone_{name}")
        focal = ctx.focal(skeleton)
        for members in groups.values():
            for a in range(len(members)):
                for b in range(a + 1, len(members)):
                    i, j = members[a], members[b]
                    if tone[i] != tone[j]:
                        resolved += 1
                    else:
                        residual += 1
                        if len(residual_examples) < 8:
                            residual_examples.append({
                                "observation": seg[i],
                                "left_focal": [states[i].values[q] for q in focal],
                                "right_focal": [states[j].values[q] for q in focal],
                                "left_score8": fragment.score8(list(states[i].values)),
                                "right_score8": fragment.score8(list(states[j].values)),
                            })
        focal_tones = [skeleton.tones[q] for q in focal]
        per_input[name] = {
            "states": len(states),
            "image_B_seg": len(set(seg)),
            "image_B_segtone": len(set(map(repr, tone))),
            "merged_pairs_B_seg": merged,
            "resolved_by_tone": resolved,
            "residual_after_tone": residual,
            "focal_origin_tones": focal_tones,
            "distinct_focal_tones": len(set(t for t in focal_tones if t is not None)),
            "residual_examples": residual_examples,
        }
    return {
        "artifact": "t7_tone_bridge",
        "seconds": round(time.time() - started, 2),
        "per_input": per_input,
    }


def run_two_correspondences(ctx: GuaContext) -> dict:
    cases = [
        ("OR38", [("ɔ", "∅", "i"), ("ɔ", "i", "∅")],
         "chapter 9, 'One observation, two correspondences': costs 89/2 and 43/2"),
        ("C21b", [("∅", "ʊ"), ("ʊ", "∅")],
         "chapter 9, 'One observation, two correspondences': costs 46 and 20"),
    ]
    out = {}
    for name, tuples, note in cases:
        skeleton = ctx.skeletons[name]
        focal = ctx.focal(skeleton)
        fragment = ctx.fragment(skeleton, f"pair_{name}")
        rows = []
        for values in tuples:
            full = list(skeleton.reference)
            for q, v in zip(focal, values):
                full[q] = v
            state = State(skeleton, tuple(full))
            rows.append({
                "focal": list(values),
                "B_seg": BRIDGES["B_seg"](ctx, state),
                "B_atr": list(BRIDGES["B_atr"](ctx, state)),
                "B_count": BRIDGES["B_count"](ctx, state),
                "B_segtone": [list(p) for p in BRIDGES["B_segtone"](ctx, state)],
                "score8": fragment.score8(full),
                "score": str(Fraction(fragment.score8(full), 8)),
            })
        separated = {b: rows[0][b] != rows[1][b]
                     for b in ("B_seg", "B_atr", "B_count", "B_segtone", "score8")}
        out[name] = {"note": note, "rows": rows, "separated_by": separated}
    return {"artifact": "t7_two_correspondences", "cases": out}


def _selected(ctx: GuaContext, skeleton: Skeleton, identifier: str) -> tuple[list[tuple[str, ...]], int]:
    fragment = ctx.fragment(skeleton, identifier)
    best: Optional[int] = None
    minima: list[tuple[str, ...]] = []
    for _i, candidate in fragment.all_candidates():
        value = fragment.score8(candidate)
        if best is None or value < best:
            best, minima = value, [tuple(candidate)]
        elif value == best:
            minima.append(tuple(candidate))
    return minima, int(best or 0)


def run_frame_commutation(ctx: GuaContext, frames: Sequence[tuple[str, tuple]] | None = None) -> dict:
    started = time.time()
    frames = frames or [("isolate_word", (0,)), ("isolate_word", (1,)),
                        ("drop_word", (0,)), ("drop_word", (1,))]
    per_input = {}
    for name in GUA_ORDER:
        skeleton = ctx.skeletons[name]
        base_minima, base_best = _selected(ctx, skeleton, f"base_{name}")
        rows = []
        for op, args in frames:
            step = Step(op, args)
            context = Context((step,))
            trace = context_trace(ctx, context, skeleton)
            if trace is None:
                rows.append({"frame": step.describe(), "status": "UNDEFINED"})
                continue
            framed_minima, framed_best = _selected(
                ctx, trace.target, f"framed_{name}_{op}_{args}")
            image = sorted({bridge_seg(ctx, State(trace.target, trace.apply(m)))
                            for m in base_minima})
            framed_obs = sorted({bridge_seg(ctx, State(trace.target, m))
                                 for m in framed_minima})
            rows.append({
                "frame": step.describe(),
                "licence": step.licence(),
                "image_of_selected": image,
                "selected_for_framed_input": framed_obs,
                "commutes": image == framed_obs,
                "framed_states": len(ctx.candidates(trace.target)),
                "framed_minimum8": framed_best,
            })
        per_input[name] = {
            "base_minimum8": base_best,
            "base_selected": sorted({bridge_seg(ctx, State(skeleton, m))
                                     for m in base_minima}),
            "frames": rows,
        }
    return {
        "artifact": "frame_commutation",
        "seconds": round(time.time() - started, 2),
        "note": "A frame that does not commute is a testable prediction of the "
                "grammar, not a readout of the unframed correspondence.",
        "per_input": per_input,
    }


def run_lithuanian(ceiling_note: str = "") -> dict:
    spec = lit.load_spec()
    weights, lam = lit.reference_weights(spec)
    configs = ("O", "RR", "SR", "RS", "SS", "RR0")
    rows = {}
    for config in configs:
        entry = {}
        for record in spec["inputs"]:
            evaluated = lit.evaluate(record, config, weights, lam)
            entry[record["id"]] = {
                "outputs": evaluated["outputs"],
                "minima": evaluated["minima"],
                "fiber": evaluated["fiber"],
                "exclusively_correct": evaluated["exclusively_correct"],
                "minimum8": evaluated["minimum8"],
            }
        rows[config] = entry
    signature = {c: tuple(tuple(rows[c][r["id"]]["outputs"]) for r in spec["inputs"])
                 for c in configs}
    classes: dict[str, list[str]] = {}
    for config, sig in signature.items():
        classes.setdefault(repr(sig), []).append(config)
    return {
        "artifact": "lithuanian_operational_kernel",
        "reference_point": {k: str(v) for k, v in weights.items()} | {"lambda": str(lam)},
        "per_config": rows,
        "operational_classes_at_reference_point": list(classes.values()),
        "note": "Two configurations fall in one class exactly when the segmental "
                "output bridge cannot tell them apart on the three attested inputs. "
                + ceiling_note,
    }
