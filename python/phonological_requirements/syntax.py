from __future__ import annotations

from dataclasses import fields
from fractions import Fraction
from functools import lru_cache
from importlib import import_module

from . import core


EXTENSIONS = (
    ("frag_apocope", "_RefSuccPresent", ("slot",)),
    ("frag_contact", "_SideIs", ("slot", "value")),
    ("frag_harmony", "_SideIs", ("slot", "value")),
    ("frag_lith", "DomIs", ("slot", "domain", "value")),
    ("frag_morphaccent", "_CoordIs", ("slot", "coord", "value")),
    ("frag_nuer", "_PosOrder", ("a", "b")),
    ("frag_nuer", "_CoordIs", ("slot", "coord", "value")),
    ("frag_phase", "_AspectIs", ("slot", "value")),
    ("frag_phase", "_LinkedIntoWord", ("slot", "delta")),
    ("frag_redup", "_CoordIs", ("slot", "coord", "value")),
    ("frag_redup", "_PrevOpen", ("slot",)),
    ("frag_schwa", "_Made", ("slot",)),
    ("frag_stratal", "_CoordIs", ("slot", "coord", "value")),
    ("frag_stratal", "_RefNext", ("slot", "coord", "value")),
    ("frag_stratal", "_RefAnyMorphV", ("slot",)),
    ("frag_stratal", "_SonDrop", ("a", "b")),
    ("frag_stratal", "_Fused", ("slot",)),
    ("frag_stratal", "_LostSlots", ("slot", "k")),
    ("generator_operations", "_RefBefore", ("first", "second")),
)

BASE_ATOMS = (core.Resolves, core.Present, core.Feat, core.SameFeat,
              core.SameSeg, core.Positional, core.InScope, core.Linked, core.Made)


@lru_cache(maxsize=1)
def atom_catalogue():
    out = {cls: ("core." + cls.__name__, tuple(f.name for f in fields(cls)))
           for cls in BASE_ATOMS}
    for module, name, names in EXTENSIONS:
        cls = getattr(import_module("." + module, __package__), name)
        out[cls] = (module + "." + name, names)
    return out


def literal(value):
    if value is core.UNDEF:
        return ["undefined"]
    if value is None or type(value) in (str, int, bool):
        return value
    if type(value) is Fraction:
        return ["rational", value.numerator, value.denominator]
    if type(value) is tuple:
        return ["tuple", [literal(v) for v in value]]
    if type(value) is core.Scope:
        return ["scope", literal(value.same),
                [[k, literal(v)] for k, v in sorted(value.delta.items())],
                [[k, literal(v)] for k, v in sorted(value.min_delta.items())],
                value.label]
    raise TypeError("unsupported predicate parameter: " + type(value).__qualname__)


def encode(term):
    cls = type(term)
    if cls is core.Const:
        if term.value is not None and type(term.value) is not bool:
            raise TypeError("non-Kleene constant")
        return ["core.Const", term.value]
    if cls is core.Not:
        return ["core.Not", encode(term.a)]
    if cls in (core.And, core.Or_):
        if type(term.parts) is not tuple:
            raise TypeError("formula parts must be a tuple")
        return ["core." + cls.__name__, [encode(p) for p in term.parts]]
    entry = atom_catalogue().get(cls)
    if entry is None:
        raise TypeError("unregistered predicate: " + cls.__module__ + "." + cls.__qualname__)
    name, names = entry
    if set(vars(term)) != set(names):
        raise TypeError("unexpected predicate fields: " + name)
    return [name, [[key, literal(getattr(term, key))] for key in names]]


def faults(term):
    try:
        encode(term)
    except (TypeError, ValueError, AttributeError) as exc:
        return (str(exc),)
    return ()


def undefined_slots(atom):
    encode(atom)
    if type(atom) is core.Resolves:
        return frozenset()
    name = atom_catalogue()[type(atom)][0]
    if name == "frag_redup._PrevOpen":
        return frozenset({"p1", "pv"})
    return atom.slots()
