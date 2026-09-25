from __future__ import annotations

import json
from typing import Mapping

from .lang import (And, Const, Declaration, Feat, InScope, Not, Or, Positional,
                   Present, Resolves, SameFeat, SameSeg, Scope, SlotDecl, Term)


def term_json(t: Term) -> dict:
    if isinstance(t, Const):
        return {"op": "const", "value": t.value}
    if isinstance(t, Resolves):
        return {"op": "resolves", "slot": t.slot}
    if isinstance(t, Present):
        return {"op": "present", "slot": t.slot, "where": t.where}
    if isinstance(t, Feat):
        return {"op": "feat", "feature": t.feature, "slot": t.slot,
                "value": t.value, "where": t.where}
    if isinstance(t, SameFeat):
        return {"op": "sameFeat", "feature": t.feature,
                "left": list(t.left), "right": list(t.right)}
    if isinstance(t, SameSeg):
        return {"op": "sameSeg", "left": list(t.left), "right": list(t.right)}
    if isinstance(t, Positional):
        return {"op": "positional", "kind": t.kind, "slot": t.slot}
    if isinstance(t, InScope):
        return {"op": "inScope", "slot": t.slot, "anchor": t.anchor,
                "scope": scope_json(t.scope)}
    if isinstance(t, Not):
        return {"op": "not", "arg": term_json(t.a)}
    if isinstance(t, And):
        return {"op": "and", "args": [term_json(p) for p in t.parts]}
    if isinstance(t, Or):
        return {"op": "or", "args": [term_json(p) for p in t.parts]}
    raise TypeError(type(t))


def scope_json(s: Scope) -> dict:
    return {"same_phrase": s.same_phrase, "word_delta": s.word_delta,
            "min_word_delta": s.min_word_delta, "label": s.label or "unscoped"}


def slot_json(s: SlotDecl) -> dict:
    return {"name": s.name, "kind": s.kind, "role": s.role,
            "scope": scope_json(s.scope), "direction": s.direction,
            "filter": s.filter, "policy": s.policy, "filter_mode": s.filter_mode}


def decl_json(d: Declaration) -> dict:
    ok, faults = d.well_typed()
    return {
        "name": d.name,
        "scope": scope_json(d.scope),
        "slots": [slot_json(s) for s in d.slots],
        "activation": term_json(d.activation),
        "consequence": term_json(d.consequence),
        "definedness_override": (None if d.definedness_override is None
                                 else term_json(d.definedness_override)),
        "derived_definedness": d.definedness_override is None,
        "well_typed": ok,
        "faults": list(faults),
        "relational_subject": d.relational(),
        "consequence_depth": d.consequence.depth(),
        "activation_depth": d.activation.depth(),
        "consequence_slots": sorted(d.consequence.slots()),
        "subject_slots": list(d.subject_slots()),
    }


def bundle() -> dict:
    from .gua_decls import declarations
    from . import lith_decls as LD
    from .variants import VARIANTS, build_declarations

    gua = {name: {k: decl_json(v) for k, v in build_declarations(name).items()}
           for name in VARIANTS}
    lith = {
        "witness": {"A": decl_json(LD.agree("witness", "stop")),
                    "N": decl_json(LD.nogem("witness", "stop"))},
        "dynamic_stop": {"A": decl_json(LD.agree("dynamic", "stop")),
                         "N": decl_json(LD.nogem("dynamic", "stop"))},
        "dynamic_skip": {"A": decl_json(LD.agree("dynamic", "skip")),
                         "N": decl_json(LD.nogem("dynamic", "skip"))},
        "origin_bound": {"A": decl_json(LD.agree("origin_bound", "skip")),
                         "N": decl_json(LD.nogem("origin_bound", "skip"))},
        "appendix_S": {"A": decl_json(LD.agree_surviving_origins()),
                       "N": decl_json(LD.nogem_surviving_origins())},
        "IDENT": decl_json(LD.IDENT_VOI),
        "DEP": decl_json(LD.DEP),
    }
    return {
        "language": "L",
        "version": "1.0.0",
        "semantics": {
            "consequence": "strong Kleene three-valued; Def = the consequence "
                           "has a truth value; G = it is true",
            "activation": "strong Kleene, then undefined |-> false",
            "definedness": "derived, never declared, except where "
                           "definedness_override is non-null",
            "slot_roles": "a slot occurring in the consequence must have role "
                          "'subject'; trigger slots may occur only in the "
                          "activation",
            "feature_partiality": "a feature access is undefined exactly where "
                                  "the declared feature table says so; "
                                  "'present' is total and absence is a value",
        },
        "gua": gua,
        "lithuanian": lith,
    }


if __name__ == "__main__":
    print(json.dumps(bundle(), ensure_ascii=False, indent=1))
