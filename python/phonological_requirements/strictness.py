from __future__ import annotations

import itertools
from typing import Iterable

from .core import (And, Const, Decl, Feat, InScope, Linked, Made, Not, Or_,
                   Positional, Present, Resolves, SameFeat, SameSeg, Term)

ATOMS = (Resolves, Present, Feat, SameFeat, SameSeg, Positional, InScope,
         Linked, Made)


def atoms(t: Term) -> list[Term]:
    if isinstance(t, (Not,)):
        return atoms(t.a)
    if isinstance(t, (And, Or_)):
        out = []
        for p in t.parts:
            out.extend(atoms(p))
        return out
    if isinstance(t, Const):
        return []
    return [t]


def _eval(t: Term, env: dict):
    from .core import k_and, k_or, k_not
    if isinstance(t, Const):
        return t.value
    if isinstance(t, Not):
        return k_not(_eval(t.a, env))
    if isinstance(t, And):
        return k_and(*[_eval(p, env) for p in t.parts])
    if isinstance(t, Or_):
        return k_or(*[_eval(p, env) for p in t.parts])
    return env[id(t)]


def possible_values(t: Term, env: dict):
    from .core import k_and, k_or, k_not
    if type(t) is Const:
        return {t.value}
    if type(t) is Not:
        return {k_not(v) for v in possible_values(t.a, env)}
    if type(t) in (And, Or_):
        result = {True if type(t) is And else False}
        operation = k_and if type(t) is And else k_or
        for part in t.parts:
            values = possible_values(part, env)
            result = {operation(a, b) for a in result for b in values}
        return result
    return env[id(t)]


def subject_strict(decl: Decl, slot: str):
    from .syntax import faults, undefined_slots
    terms = [decl.consequence] + ([decl.definedness_override]
                                  if decl.definedness_override is not None else [])
    for term in terms:
        invalid = faults(term)
        if invalid:
            return False, "; ".join(invalid)
    at = []
    for t in terms:
        at.extend(atoms(t))
    seen, at2 = set(), []
    for a in at:
        if id(a) not in seen:
            seen.add(id(a)); at2.append(a)
    fixed = [a for a in at2 if slot in undefined_slots(a)]
    resolves_false = [a for a in at2 if slot in a.slots() and type(a) is Resolves]
    constrained = {id(a) for a in fixed + resolves_false}
    free = [a for a in at2 if id(a) not in constrained]
    abstract = {id(a): {None} for a in fixed}
    abstract.update({id(a): {False} for a in resolves_false})
    abstract.update({id(a): {True, False, None} for a in free})
    if decl.definedness_override is None and False not in possible_values(decl.consequence, abstract):
        return True, f"compositional Kleene values exclude false with {slot} unresolved"
    if len(free) > 14:
        return False, f"too many free atoms ({len(free)}) for the exhaustive test"
    for combo in itertools.product((True, False, None), repeat=len(free)):
        env = {id(a): None for a in fixed}
        env.update({id(a): False for a in resolves_false})
        env.update({id(a): v for a, v in zip(free, combo)})
        value = _eval(decl.consequence, env)
        if decl.definedness_override is None:
            defined = value is not None
        else:
            defined = _eval(decl.definedness_override, env) is True
        good = value is True
        if defined and not good:
            reason = ("a Kleene assignment gives pressure 1 with "
                      f"{slot} unresolved"
                      + (" (the declared definedness override supplies Def=1 "
                         "where the derived Def would be 0)"
                         if decl.definedness_override is not None else "")
                      + ": " + ", ".join(
                          f"{type(a).__name__}{tuple(sorted(a.slots()))}={v}"
                          for a, v in zip(free, combo)))
            return False, reason
    return True, f"pressure is 0 at every Kleene assignment with {slot} unresolved"


def zero_contribution_report(sigma, decls) -> dict:
    out = {}
    for name, d in decls.items():
        by = d.by_name()
        rows = {}
        for s in sorted(d.consequence.slots()):
            sl = by.get(s)
            if sl is None:
                continue
            ok, why = subject_strict(d, s)
            rows[s] = {"sort": sl.sort,
                       "totality": sigma.totality(sl.sort),
                       "subject_strict_certified": ok,
                       "reason": why}
        out[name] = rows
    return out
