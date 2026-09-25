from __future__ import annotations
from phonological_grounding.results import bare

import hashlib
import json
from pathlib import Path

from phonological_grounding.paths import results_dir
RESULTS = results_dir() / "declaration_language"


def _write(name: str, payload) -> str:
    RESULTS.mkdir(parents=True, exist_ok=True)
    text = json.dumps(bare(payload), ensure_ascii=False, indent=1, sort_keys=True)
    (RESULTS / name).write_text(text, encoding="utf-8")
    return hashlib.sha256(text.encode()).hexdigest()[:16]


def main() -> None:
    from .adequacy import run as adequacy_run
    from .discriminate import (gua_winner_separation,
                               lithuanian_consonant_epenthesis)
    from .indexing import compare as indexing_compare
    from .lith_region import report as lith_report
    from .probe import guard_bite, probe_report
    from .carrier import search as carrier_search
    from .nucleus_audit import audit as nucleus_audit
    from .record import ablation, scope_witness
    from .winner_locality import run as winner_run, sweep as winner_sweep
    from .region import coefficient_identity, region_equality
    from .variants import compare_all
    from . import lith_decls as LD
    from phonological_opacity.fragments.lithuanian import coefficient_vector, load_spec as load_lt

    index = {}

    a = adequacy_run("baseline")
    index["adequacy_gua.json"] = _write("adequacy_gua.json", a)

    lt = load_lt()
    pairs = {
        "RR": (LD.agree("witness", "stop"), LD.nogem("witness", "stop")),
        "SR": (LD.agree_surviving_origins(), LD.nogem("witness", "stop")),
        "RS": (LD.agree("witness", "stop"), LD.nogem_surviving_origins()),
        "SS": (LD.agree_surviving_origins(), LD.nogem_surviving_origins()),
        "Sprime_dynamic_skip": (LD.agree("dynamic", "skip"), LD.nogem("dynamic", "skip")),
        "Sprime_origin_bound": (LD.agree("origin_bound", "skip"),
                                LD.nogem("origin_bound", "skip")),
    }
    lt_adeq = {}
    for cfg, (ad, nd) in pairs.items():
        rows = {rec["id"]: [list(LD.coefficients(rec, j, ad, nd)) for j in range(8)]
                for rec in lt["inputs"]}
        matches = [c for c in ("RR", "SR", "RS", "SS")
                   if all(LD.coefficients(rec, j, ad, nd) == coefficient_vector(rec, c, j)
                          for rec in lt["inputs"] for j in range(8))]
        wa, fa = ad.well_typed()
        wn, fn = nd.well_typed()
        lt_adeq[cfg] = {"coefficients": rows,
                        "reproduces_appendix_factorisation": matches,
                        "well_typed": wa and wn,
                        "faults": sorted(set(fa) | set(fn))}
    index["adequacy_lithuanian.json"] = _write("adequacy_lithuanian.json", lt_adeq)

    v = compare_all()
    for name in v:
        for uid in v[name]["per_input"]:
            v[name]["per_input"][uid].pop("values", None)
    index["resolver_variants.json"] = _write("resolver_variants.json", v)

    index["coefficient_identity.json"] = _write("coefficient_identity.json",
                                                coefficient_identity())
    index["probe_g6.json"] = _write("probe_g6.json",
                                    {"probe": probe_report(),
                                     "guard_bite": guard_bite()})
    index["lithuanian_region.json"] = _write("lithuanian_region.json", lith_report())
    index["record_ablation.json"] = _write("record_ablation.json",
                                           {"ablation": ablation(),
                                            "scope_witness": scope_witness()})
    index["obligation_indexing.json"] = _write("obligation_indexing.json",
                                               indexing_compare())
    index["carrier.json"] = _write("carrier.json", carrier_search())
    index["nucleus_audit.json"] = _write("nucleus_audit.json", nucleus_audit())
    index["region_equality.json"] = _write(
        "region_equality.json",
        {v: region_equality(variant=v)
         for v in ("witness", "origin_bound", "witness_phrase")})
    index["winner_locality.json"] = _write(
        "winner_locality.json", {"single": winner_run(), "sweep": winner_sweep()})
    index["discriminators.json"] = _write(
        "discriminators.json",
        {"gua_weight_axis": gua_winner_separation(),
         "lithuanian_consonant_epenthesis": lithuanian_consonant_epenthesis()})

    _write("INDEX.json", {"files": index})
    for k, h in sorted(index.items()):
        print(f"  {h}  {k}")


if __name__ == "__main__":
    main()
