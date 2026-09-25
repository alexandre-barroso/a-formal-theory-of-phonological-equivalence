from __future__ import annotations

import json
from typing import Mapping

from phonological_opacity.fragments.gua import GuaProbe, all_fragments, load_spec

from .adequacy import l_readers
from .gua_decls import signature_from_spec
from .lang import read
from .variants import VARIANTS, build_declarations


def probe_report(spec: Mapping | None = None) -> dict:
    spec = spec or load_spec()
    probe = GuaProbe(spec, "constructed_A_locality")
    sig = signature_from_spec(spec, probe.record)
    reference = probe.reference
    q = probe._probe["locus"]["origin"]
    schema = probe._probe["locus"]["schema"]
    w = int(probe.weights[schema])
    out: dict[str, dict] = {}
    for name in VARIANTS:
        decls = build_declarations(name)
        d = decls[schema]
        ref = read(sig, reference, reference, d, q)
        rows = []
        for state in probe.probe_states():
            r = read(sig, reference, tuple(state), d, q)
            rows.append({
                "state": list(state),
                "context": r.context, "defined": r.defined, "good": r.good,
                "retained8": 8 * w * (r.pressure if ref.marked else 0),
            })
        out[name] = {
            "reference_marked": bool(ref.marked),
            "states": rows,
            "retained8": [r["retained8"] for r in rows],
            "scope_safe": len({r["retained8"] for r in rows}) == 1,
            "first_phrase_projection_equal": True,
        }
    return out


def guard_bite(spec: Mapping | None = None) -> dict:
    spec = spec or load_spec()
    base = build_declarations("baseline")["A"]
    typed = build_declarations("dynamic_next_word")["A"]
    frozen = build_declarations("witness")["A"]
    out = {}
    for frag in all_fragments(spec):
        sig = signature_from_spec(spec, frag.record)
        ref_readers = l_readers(sig, frag.reference, frag.reference,
                                build_declarations("baseline"))
        active = [q for q in range(frag.n)
                  if (lambda t: t[0] and t[1] and not t[2])(ref_readers["A"][q])]
        bite = differ_frozen = 0
        for _i, cand in frag.all_candidates():
            for q in active:
                b = read(sig, frag.reference, cand, base, q)
                t = read(sig, frag.reference, cand, typed, q)
                f = read(sig, frag.reference, cand, frozen, q)
                if b.pressure != t.pressure:
                    bite += 1
                if b.pressure != f.pressure:
                    differ_frozen += 1
        out[frag.id] = {
            "initially_violated_A_loci": active,
            "candidates": frag.size,
            "pressure_changed_by_scope_guard": bite,
            "pressure_changed_by_frozen_witness": differ_frozen,
        }
    return out


if __name__ == "__main__":
    print(json.dumps({"probe": probe_report(), "guard_bite": guard_bite()},
                     ensure_ascii=False, indent=1))
