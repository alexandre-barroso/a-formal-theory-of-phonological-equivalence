from __future__ import annotations

import json
from fractions import Fraction
from typing import Mapping

from phonological_opacity.fragments.gua import MARKEDNESS, all_fragments, load_spec

from .adequacy import l_locus_terms, l_readers
from .gua_decls import (ANCHOR, NEXT_WORD, NONHIGH, NUC, SCHEMA_ORDER,
                        agree_typed, declarations, relatum, signature_from_spec)
from .lang import (And, Declaration, Feat, Not, Or, Present, Resolves, SameSeg,
                   SlotDecl)


def _typed(policy: str, filter_mode: str) -> Declaration:
    a = agree_typed(policy="dynamic", scope=NEXT_WORD, filter="nuclear_nonhigh")
    slots = tuple(
        s if s.kind != "relatum" else
        SlotDecl(s.name, s.kind, s.role, s.scope, s.direction, s.filter,
                 policy, filter_mode)
        for s in a.slots)
    return Declaration(name=a.name, slots=slots, activation=a.activation,
                       consequence=a.consequence, scope=a.scope)


def agree_split() -> Declaration:
    return Declaration(
        name="A",
        slots=(ANCHOR,
               relatum("n_guarded", NEXT_WORD, +1, None, "dynamic", role="trigger"),
               relatum("n", NEXT_WORD, +1, "nuclear_nonhigh", "dynamic",
                       role="subject")),
        scope=NEXT_WORD,
        activation=And((NUC, NONHIGH, Resolves("n_guarded"),
                        Feat("nuclear", "n_guarded", True),
                        Not(Feat("high", "n_guarded", True)))),
        consequence=Or((Not(Present("t")),
                        SameSeg(("t", "current"), ("n", "current")))),
    )


def variants() -> dict[str, dict]:
    out: dict[str, dict] = {}
    out["appendix"] = declarations("baseline")
    for label, (pol, mode) in (("stop", ("dynamic", "stop")),
                               ("skip", ("dynamic", "skip")),
                               ("skip_in_scope", ("dynamic_in_scope", "skip"))):
        d = declarations("typed", policy="dynamic")
        d["A"] = _typed(pol, mode)
        out[label] = d
    d = declarations("typed", policy="dynamic")
    d["A"] = agree_split()
    out["split"] = d
    out["no_filter"] = declarations("typed", policy="dynamic")
    return out


def audit(spec: Mapping | None = None) -> dict:
    spec = spec or load_spec()
    report: dict[str, dict] = {}
    for label, decls in variants().items():
        rows = {}
        for frag in all_fragments(spec):
            sig = signature_from_spec(spec, frag.record)
            ref = l_readers(sig, frag.reference, frag.reference, decls)
            obligations = {
                k: [q for q in range(frag.n)
                    if ref[k][q][0] and ref[k][q][1] and not ref[k][q][2]]
                for k in MARKEDNESS}
            vals, obs = [], []
            for _i, cand in frag.all_candidates():
                t = l_locus_terms(sig, frag.reference, cand, decls, ref, MARKEDNESS)
                total = Fraction(0)
                for n in SCHEMA_ORDER:
                    old, new = t[n]
                    total += frag.weights[n] * (Fraction(old) + frag.lam * new)
                vals.append(int(total * 8))
                obs.append(frag.observe(cand))
            target = frag.record["observation"]
            fiber = [i for i, y in enumerate(obs) if y == target]
            best = min(vals)
            minima = [i for i, v in enumerate(vals) if v == best]
            rows[frag.id] = {
                "retained_obligations": {k: v for k, v in obligations.items() if v},
                "A_obligations": obligations["A"],
                "minima": minima, "fiber": fiber, "minimum8": best,
                "output_of_minima": sorted({obs[i] for i in minima}),
                "exclusively_correct": bool(minima) and set(minima) <= set(fiber),
            }
        ok, faults = decls["A"].well_typed()
        report[label] = {
            "well_typed": ok, "faults": sorted(faults),
            "destroyed": [k for k, v in rows.items()
                          if not v["exclusively_correct"]],
            "per_input": rows,
        }
    base = report["appendix"]
    for label, rep in report.items():
        rep["A_obligations_differ_from_appendix"] = {
            uid: {"appendix": base["per_input"][uid]["A_obligations"],
                  label: rep["per_input"][uid]["A_obligations"]}
            for uid in rep["per_input"]
            if rep["per_input"][uid]["A_obligations"]
            != base["per_input"][uid]["A_obligations"]}
    return report


if __name__ == "__main__":
    print(json.dumps(audit(), ensure_ascii=False, indent=1))
