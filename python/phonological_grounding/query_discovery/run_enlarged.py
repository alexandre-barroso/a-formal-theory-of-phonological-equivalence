from __future__ import annotations

import json
import sys
import time
from fractions import Fraction
from pathlib import Path


from phonological_grounding.query_discovery.experiments import _write
from phonological_grounding.query_discovery.instances import EXCLUDED, enlarged_set, observation_of, predictions_of
from phonological_grounding.query_discovery.kernel import block_count, join, minimum_cost_battery, partition_of
from phonological_grounding.query_discovery.measure import query_space_report
from phonological_grounding.query_discovery.model_kernel import GUA_ORDER
from phonological_grounding.query_discovery.protocols import BRIDGE_COST, BRIDGE_LICENCE, BRIDGES
from phonological_grounding.query_discovery.structures import gua_context


def verify_p2_identities(ctx) -> dict:
    from phonological_grounding.declaration_language.adequacy import l_locus_terms, l_readers
    from phonological_grounding.declaration_language.gua_decls import SCHEMA_ORDER, signature_from_spec
    from phonological_grounding.declaration_language.variants import VARIANTS, build_declarations
    from phonological_opacity.fragments.gua import MARKEDNESS, SCHEMAS

    started = time.time()
    weights = {s: Fraction(ctx.shared["weights"][s]) for s in SCHEMAS}
    lam = Fraction(ctx.shared["lambda"]["num"], ctx.shared["lambda"]["den"])

    def terms_for(name: str, skeleton, fragment, sig, ref):
        decls = build_declarations(name)
        out = []
        for cand in ctx.candidates(skeleton):
            out.append(l_locus_terms(sig, fragment.reference, list(cand.values),
                                     decls, ref, MARKEDNESS))
        return out

    def score(terms) -> int:
        total = Fraction(0)
        for schema in SCHEMA_ORDER:
            old, new = terms[schema]
            total += weights[schema] * (Fraction(old) + lam * new)
        return int(total * 8)

    per_variant: dict[str, dict] = {}
    for name in VARIANTS:
        per_variant[name] = {"per_input": {}, "changed_total": 0,
                             "A_old_deltas": {}, "coefficient_identical": True}
    for uid in GUA_ORDER:
        skeleton = ctx.skeletons[uid]
        fragment = ctx.fragment(skeleton, f"id_{uid}")
        shim = dict(ctx.shared)
        shim["inputs"] = list(ctx.shared["inputs"]) + [fragment.record]
        sig = signature_from_spec(shim, fragment.record)
        ref = l_readers(sig, fragment.reference, fragment.reference,
                        build_declarations("baseline"))
        base_terms = terms_for("baseline", skeleton, fragment, sig, ref)
        base_scores = [score(t) for t in base_terms]
        for name in VARIANTS:
            terms = base_terms if name == "baseline" else terms_for(
                name, skeleton, fragment, sig, ref)
            scores = [score(t) for t in terms]
            changed = [i for i, (a, b) in enumerate(zip(scores, base_scores)) if a != b]
            coeff_same = all(t == b for t, b in zip(terms, base_terms))
            deltas = sorted({terms[i]["A"][0] - base_terms[i]["A"][0] for i in changed})
            per_variant[name]["per_input"][uid] = {
                "changed_candidates": len(changed),
                "coefficient_vectors_identical": coeff_same,
                "A_old_deltas_on_changed": [str(d) for d in deltas],
            }
            per_variant[name]["changed_total"] += len(changed)
            if not coeff_same:
                per_variant[name]["coefficient_identical"] = False
            for d in deltas:
                key = str(d)
                per_variant[name]["A_old_deltas"][key] = \
                    per_variant[name]["A_old_deltas"].get(key, 0) + 1
    identical = sorted(n for n, r in per_variant.items()
                       if r["coefficient_identical"] and n != "baseline")
    return {
        "artifact": "t5_p2_identity_check",
        "question": "are appendix I's score-identity claims true, checked candidate by candidate?",
        "method": "the per-candidate COEFFICIENT vectors are compared, not just the scores at the "
                  "declared weight point. Identical coefficients imply identical scores for every "
                  "weight and every lambda; equal scores at one point would not.",
        "coefficient_identical_to_baseline": identical,
        "per_variant": per_variant,
        "seconds": round(time.time() - started, 1),
    }


def run_enlarged(ctx, verbose: bool = True) -> dict:
    started = time.time()
    instances = enlarged_set(ctx)
    bridges = [b for b in BRIDGES if BRIDGE_COST[b] is not None]
    cache: dict = {}

    columns: list[list] = []
    costs: list[Fraction] = []
    meta: list[dict] = []
    for name in GUA_ORDER:
        skeleton = ctx.skeletons[name]
        for bridge in bridges:
            fn = BRIDGES[bridge]
            columns.append([observation_of(ctx, m, skeleton, fn, cache) for m in instances])
            costs.append(Fraction(1) + Fraction(max(0, len(skeleton.words) - 1))
                         + BRIDGE_COST[bridge])
            meta.append({"input": name, "bridge": bridge,
                         "bridge_licence": BRIDGE_LICENCE[bridge]})
        if verbose:
            print(f"    {name} done ({time.time() - started:.0f}s)", flush=True)

    kernel = join(*[partition_of(c) for c in columns])
    classes: dict[int, list[str]] = {}
    for i, cls in enumerate(kernel):
        classes.setdefault(cls, []).append(instances[i].id)
    members = list(classes.values())
    battery = minimum_cost_battery(columns, costs)

    undefined = {m.id: [meta[k]["input"] for k, col in enumerate(columns)
                        if col[i] is None and meta[k]["bridge"] == "B_seg"]
                 for i, m in enumerate(instances)}
    undefined = {k: v for k, v in undefined.items() if v}

    n, m = len(instances), block_count(kernel)
    return {
        "artifact": "t5_model_kernel_enlarged",
        "M_sources": ["p1 the first pass (dissertation baseline, declared comparator, attenuation "
                      "boundaries, per-schema ablations)",
                      "data/declaration_language/spec/resolver_semantics.v1.json",
                      "data/predictions/registry/rival_registry.v1.json"],
        "M_is_partial": True,
        "instances": [i.as_record() for i in instances],
        "excluded": EXCLUDED,
        "protocol_family": "the eight attested Gua products read through B_seg, B_atr, B_count and "
                           "B_segtone (32 depth-zero protocols, all ATTESTED at spec 1.2.0)",
        "protocols": len(columns),
        "classes": m,
        "class_members": members,
        "a_priori_query_space": query_space_report(n),
        "licensed_query_space": query_space_report(m),
        "collapse_boolean_bits": max(0, n - 1) - max(0, m - 1),
        "undefined_predictions": undefined,
        "minimum_cost_battery": {
            "status": battery.status,
            "minimum_cost": None if battery.minimum_cost is None else str(battery.minimum_cost),
            "optima_count": len(battery.optima),
            "optima": [[meta[i] | {"index": i} for i in option] for option in battery.optima],
            "explored": battery.explored,
        },
        "seconds": round(time.time() - started, 1),
    }


def main() -> int:
    ctx = gua_context()
    check = verify_p2_identities(ctx)
    _write("t5_p2_identity_check.json", check)
    print("  t5_p2_identity_check.json:",
          "coefficient-identical to baseline =", check["coefficient_identical_to_baseline"],
          flush=True)
    payload = run_enlarged(ctx)
    _write("t5_model_kernel_enlarged.json", payload)
    print(f"  t5_model_kernel_enlarged.json: |M|={len(payload['instances'])} "
          f"classes={payload['classes']} collapse={payload['collapse_boolean_bits']} bits "
          f"cost={payload['minimum_cost_battery']['minimum_cost']} "
          f"ties={payload['minimum_cost_battery']['optima_count']}", flush=True)
    for c in payload["class_members"]:
        print("     ", c, flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
