from __future__ import annotations

from typing import Iterable

from .core import (And, Const, Decl, InScope, Linked, Made, NodeId, Not, Or_,
                   Positional, Present, Resolves, Sigma, Slot, Struct, Term)
from .strictness import atoms
from .syntax import BASE_ATOMS, encode


def _positional_atoms(t: Term):
    return [a for a in atoms(t) if isinstance(a, Positional)]


def traversal(struct: Struct, locus: NodeId, slot: Slot, tier: str) -> set[NodeId]:
    order = list(struct.nodes(tier))
    if locus not in order:
        return set(order)
    i = order.index(locus)
    admitted = [n for n in order if slot.scope.admits(struct, locus, n)]
    if not admitted:
        return set(order[i + 1:] if slot.direction > 0 else order[:i])
    idx = [order.index(n) for n in admitted]
    if slot.direction > 0:
        far = max(idx)
        if slot.policy == "dynamic_in_scope":
            return {n for n in admitted if order.index(n) > i}
        return set(order[i + 1:far + 1])
    near = min(idx)
    if slot.policy == "dynamic_in_scope":
        return {n for n in admitted if order.index(n) < i}
    return set(order[near:i])


def images(struct: Struct, locus: NodeId, tier: str = "seg") -> set[NodeId]:
    if struct.corr is None:
        return set()
    return {n for n in struct.nodes(tier) if locus in struct.correspondents(n)}


def used_slots(decl: Decl) -> tuple[Slot, ...]:
    terms = (decl.activation, decl.consequence)
    if decl.definedness_override is not None:
        terms += (decl.definedness_override,)
    names = set().union(*(term.slots() for term in terms))
    by_name = decl.by_name()
    pending = list(names)
    while pending:
        name = pending.pop()
        if name not in by_name:
            raise ValueError("undeclared slot: " + name)
        base = by_name[name].of
        if base is not None and base not in names:
            names.add(base)
            pending.append(base)
    return tuple(slot for slot in decl.slots if slot.name in names)


def footprint_profile(struct: Struct, decl: Decl, tier: str = "seg") -> str:
    terms = (decl.activation, decl.consequence)
    if decl.definedness_override is not None:
        terms += (decl.definedness_override,)
    for term in terms:
        encode(term)
    aa = [a for term in terms for a in atoms(term)]
    if struct.corr is not None or any(type(a) not in BASE_ATOMS for a in aa):
        return "full_fixed_frame_support"
    if any(s.kind not in ("anchor", "step", "search") or
           (s.kind == "step" and (s.policy not in ("dynamic", "dynamic_in_scope")
                                  or s.tier not in (None, tier))) or
           (s.kind == "search" and (s.of is not None or s.where != "current"
                                    or s.tier not in (None, tier))) for s in used_slots(decl)):
        return "full_fixed_frame_support"
    by_name = decl.by_name()
    if any(isinstance(a, Positional) and
           (a.slot not in by_name or by_name[a.slot].kind != "anchor") for a in aa):
        return "full_fixed_frame_support"
    return "direct_step_fixed_frame_support"


def same_frame(left: Struct, right: Struct) -> bool:
    return (left.order == right.order and left.dom == right.dom
            and left.assoc == right.assoc and left.corr == right.corr
            and left.real.keys() == right.real.keys())


def footprint(sigma: Sigma, struct: Struct, decl: Decl, locus: NodeId,
              tier: str = "seg") -> set[NodeId]:
    if footprint_profile(struct, decl, tier) == "full_fixed_frame_support":
        return {locus} | set(struct.real) | {n for ns in struct.order.values() for n in ns}
    F = {locus} | images(struct, locus, tier)
    for slot in used_slots(decl):
        if slot.kind == "anchor":
            continue
        if slot.kind == "assoc":
            for t, ns in struct.order.items():
                F |= {n for n in ns if n.sort == slot.sort}
            continue
        if slot.policy in ("origin_bound", "witness"):
            F |= traversal(struct, locus, slot, tier)
            continue
        F |= traversal(struct, locus, slot, tier)
    terms = (decl.activation, decl.consequence)
    if decl.definedness_override is not None:
        terms += (decl.definedness_override,)
    for term in terms:
        for a in _positional_atoms(term):
            d = struct.dom.get(locus, {}).get(a.domain)
            if d is None:
                continue
            F |= {n for n in struct.nodes(tier)
                  if struct.dom.get(n, {}).get(a.domain) == d}
    return F


def narrow_footprint(sigma: Sigma, struct: Struct, decl: Decl, locus: NodeId,
                     tier: str = "seg") -> set[NodeId]:
    F = {locus} | images(struct, locus, tier)
    for slot in decl.slots:
        if slot.kind == "anchor":
            continue
        if slot.kind == "assoc":
            for t, ns in struct.order.items():
                F |= {n for n in ns if n.sort == slot.sort}
            continue
        F |= {n for n in struct.nodes(tier) if slot.scope.admits(struct, locus, n)}
    for term in (decl.activation, decl.consequence):
        for a in _positional_atoms(term):
            d = struct.dom.get(locus, {}).get(a.domain)
            if d is None:
                continue
            F |= {n for n in struct.nodes(tier)
                  if struct.dom.get(n, {}).get(a.domain) == d}
    return F
