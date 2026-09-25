from __future__ import annotations

import json
import sys
import time
from pathlib import Path


from phonological_grounding.query_discovery.discovery import commuting_frames, experimental_kernel, registered_probes
from phonological_grounding.query_discovery.experiments import (
    GUA_ORDER,
    _write,
    run_batteries,
    run_frame_commutation,
    run_lithuanian,
    run_measurement,
    run_tone_bridge,
    run_two_correspondences,
)
from phonological_grounding.query_discovery.structures import gua_context

FRAME_WORDS = ("W_bE", "W_akU", "W_njEE", "W_tei", "W_oni", "W_isE", "W_EbI", "W_ibie")


def main(stages: list[str]) -> int:
    ctx = gua_context()
    if "measure" in stages:
        _write("t5_measurement.json", run_measurement(ctx, 1))
        print("  t5_measurement.json")
    if "battery" in stages:
        _write("t5_batteries.json", run_batteries(ctx, 1))
        print("  t5_batteries.json")
    if "tone" in stages:
        _write("t7_tone_bridge.json", run_tone_bridge(ctx))
        _write("t7_two_correspondences.json", run_two_correspondences(ctx))
        print("  t7_tone_bridge.json, t7_two_correspondences.json")
    if "commute" in stages:
        _write("frame_commutation_small.json", run_frame_commutation(ctx))
        print("  frame_commutation_small.json")
    if "kernel" in stages:
        started = time.time()
        payload: dict = {"artifact": "experimental_vs_representational_kernel",
                         "per_input": {}}
        for name in GUA_ORDER:
            skeleton = ctx.skeletons[name]
            records, skipped = commuting_frames(ctx, name, skeleton)
            summary = experimental_kernel(ctx, skeleton, records, "PROPOSED_ELICITATION")
            summary["skipped_frames"] = skipped
            summary["frames"] = [{
                "frame": r.step.describe(),
                "licence": r.step.licence(),
                "commutes": r.commutes,
                "image_of_selected": r.image_of_selected,
                "selected_for_framed_input": r.selected_for_framed,
                "framed_states": r.framed_states,
                "framed_minimum8": r.framed_minimum8,
            } for r in records]
            payload["per_input"][name] = summary
            print(f"    {name}: rep={summary['classes_rep_depth1']} "
                  f"exp={summary['classes_exp_depth1']} "
                  f"direct={summary['classes_direct_depth0']} "
                  f"({time.time() - started:.0f}s)")
        payload["seconds"] = round(time.time() - started, 2)
        _write("t5_experimental_kernel.json", payload)
        print("  t5_experimental_kernel.json")
    if "probes" in stages:
        started = time.time()
        probes: list[dict] = []
        for name in GUA_ORDER:
            probes.extend(registered_probes(ctx, name, ctx.skeletons[name], FRAME_WORDS))
        _write("registered_probes.json", {
            "artifact": "registered_probes",
            "selection_policy": "spec/discovery_contract.v1.json, policy id "
                                "'length_driven_rephrasing_v1'",
            "seconds": round(time.time() - started, 2),
            "count": len(probes),
            "probes": probes,
        })
        print(f"  registered_probes.json ({len(probes)} probes)")
    if "lithuanian" in stages:
        _write("lithuanian_kernel.json", run_lithuanian())
        print("  lithuanian_kernel.json")
    return 0


if __name__ == "__main__":
    args = sys.argv[1:] or ["measure", "battery", "tone", "commute", "kernel",
                            "probes", "lithuanian"]
    raise SystemExit(main(args))
