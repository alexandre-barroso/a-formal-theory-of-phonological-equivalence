from __future__ import annotations

import sys
from pathlib import Path


from phonological_grounding.query_discovery.experiments import _write
from phonological_grounding.query_discovery.model_kernel import run_model_kernel, verify_variant_scorer
from phonological_grounding.query_discovery.structures import gua_context


def main(depths: list[int]) -> int:
    ctx = gua_context()
    _write("variant_scorer_check.json", verify_variant_scorer(ctx))
    print("  variant_scorer_check.json", flush=True)
    for depth in depths:
        for ceiling in ("ATTESTED", "PROPOSED_ELICITATION"):
            payload = run_model_kernel(ctx, ceiling, depth, 30_000, verbose=(depth > 0))
            name = f"t5_model_kernel_d{depth}_{ceiling.lower()}.json"
            _write(name, payload)
            print(f"  {name}: classes={payload['classes']} "
                  f"protocols={payload['protocols']} "
                  f"members={payload['class_members']}", flush=True)
    return 0


if __name__ == "__main__":
    args = [int(a) for a in sys.argv[1:]] or [0, 1]
    raise SystemExit(main(args))
