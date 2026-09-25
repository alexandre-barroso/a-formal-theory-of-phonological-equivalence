from __future__ import annotations

from dataclasses import dataclass, field
from typing import Callable, Iterable, Literal, Mapping, Sequence

K = bool | None


def k_not(a: K) -> K:
    return None if a is None else (not a)


def k_and(*args: K) -> K:
    if any(a is False for a in args):
        return False
    if any(a is None for a in args):
        return None
    return True


def k_or(*args: K) -> K:
    if any(a is True for a in args):
        return True
    if any(a is None for a in args):
        return None
    return False


def k_eq(a, b) -> K:
    if a is UNDEF or b is UNDEF:
        return None
    return a == b


class _Undef:
    __slots__ = ()

    def __repr__(self) -> str:
        return "UNDEF"

    def __bool__(self) -> bool:
        raise TypeError("UNDEF has no truth value")


UNDEF = _Undef()


def collapse(a: K) -> bool:
    return a is True


@dataclass(frozen=True)
class OriginRecord:

    index: int
    word: int
    phrase: int
    reference: str


@dataclass(frozen=True)
class Signature:

    origins: tuple[OriginRecord, ...]
    features: Mapping[str, Mapping[str, object]]
    default_features: Mapping[str, object]
    absent: str = "∅"

    def ft(self, segment: str, name: str):
        row = self.features.get(segment, self.default_features)
        v = row.get(name, "undefined")
        return UNDEF if v is None or v == "undefined" else v

    def present(self, segment: str) -> bool:
        row = self.features.get(segment, self.default_features)
        return bool(row.get("present", True))


State = tuple[str, ...]


Policy = Literal["dynamic", "dynamic_in_scope", "origin_bound", "witness"]
Role = Literal["subject", "trigger"]


@dataclass(frozen=True)
class Scope:

    same_phrase: bool = True
    word_delta: int | None = None
    min_word_delta: int | None = None
    label: str = ""

    def admits(self, sig: Signature, anchor: int, other: int) -> bool:
        a, b = sig.origins[anchor], sig.origins[other]
        if self.same_phrase and a.phrase != b.phrase:
            return False
        if self.word_delta is not None and b.word - a.word != self.word_delta:
            return False
        if self.min_word_delta is not None and b.word - a.word < self.min_word_delta:
            return False
        return True


UNSCOPED = Scope(same_phrase=False, word_delta=None, min_word_delta=None,
                 label="unscoped")


@dataclass(frozen=True)
class SlotDecl:

    name: str
    kind: Literal["anchor", "relatum", "searched"]
    role: Role
    scope: Scope = UNSCOPED
    direction: int = 1
    filter: str | None = None
    policy: Policy = "dynamic"
    filter_mode: Literal["skip", "stop"] = "skip"


@dataclass(frozen=True)
class Declaration:

    name: str
    slots: tuple[SlotDecl, ...]
    activation: "Term"
    consequence: "Term"
    scope: Scope = UNSCOPED
    definedness_override: "Term | None" = None

    def subject_slots(self) -> tuple[str, ...]:
        return tuple(s.name for s in self.slots if s.role == "subject")

    def declared_slots(self) -> Mapping[str, SlotDecl]:
        return {s.name: s for s in self.slots}

    def consequence_slots(self) -> frozenset[str]:
        return self.consequence.slots()

    def well_typed(self) -> tuple[bool, tuple[str, ...]]:
        faults: list[str] = []
        decl = self.declared_slots()
        for s in self.consequence.slots() | self.activation.slots():
            if s not in decl:
                faults.append(f"undeclared-slot:{s}")
        for s in self.consequence.slots():
            if s in decl and decl[s].role != "subject":
                faults.append(f"trigger-slot-in-consequence:{s}")
        for s in self.consequence.slots():
            d = decl.get(s)
            if d is not None and d.kind == "relatum" and d.scope == UNSCOPED:
                faults.append(f"unscoped-relational-subject:{s}")
        seen: dict[tuple, tuple] = {}
        for d in self.slots:
            if d.kind == "anchor":
                continue
            key = (d.kind, d.direction)
            how = (d.scope, d.policy, d.filter_mode, d.filter)
            if key in seen and seen[key] != how:
                faults.append(f"resolution-split:{d.kind}{d.direction:+d}")
            seen.setdefault(key, how)
        if self.definedness_override is not None:
            faults.append("definedness-override")
        return (not faults), tuple(sorted(set(faults)))

    def relational(self) -> bool:
        decl = self.declared_slots()
        return any(decl[s].kind == "relatum" for s in self.consequence.slots()
                   if s in decl)


class Term:

    def slots(self) -> frozenset[str]:
        raise NotImplementedError

    def eval(self, ctx: "EvalContext") -> K:
        raise NotImplementedError

    def depth(self) -> int:
        raise NotImplementedError


@dataclass(frozen=True)
class Not(Term):
    a: Term

    def slots(self):
        return self.a.slots()

    def eval(self, ctx):
        return k_not(self.a.eval(ctx))

    def depth(self):
        return 1 + self.a.depth()


@dataclass(frozen=True)
class And(Term):
    parts: tuple[Term, ...]

    def slots(self):
        return frozenset().union(*[p.slots() for p in self.parts]) if self.parts else frozenset()

    def eval(self, ctx):
        return k_and(*[p.eval(ctx) for p in self.parts])

    def depth(self):
        return 1 + max((p.depth() for p in self.parts), default=0)


@dataclass(frozen=True)
class Or(Term):
    parts: tuple[Term, ...]

    def slots(self):
        return frozenset().union(*[p.slots() for p in self.parts]) if self.parts else frozenset()

    def eval(self, ctx):
        return k_or(*[p.eval(ctx) for p in self.parts])

    def depth(self):
        return 1 + max((p.depth() for p in self.parts), default=0)


@dataclass(frozen=True)
class Const(Term):
    value: K

    def slots(self):
        return frozenset()

    def eval(self, ctx):
        return self.value

    def depth(self):
        return 0


TRUE = Const(True)
FALSE = Const(False)


@dataclass(frozen=True)
class Resolves(Term):

    slot: str

    def slots(self):
        return frozenset({self.slot})

    def eval(self, ctx):
        return ctx.resolve(self.slot) is not None

    def depth(self):
        return 1


@dataclass(frozen=True)
class Present(Term):

    slot: str
    where: Literal["current", "reference"] = "current"

    def slots(self):
        return frozenset({self.slot})

    def eval(self, ctx):
        o = ctx.resolve(self.slot)
        if o is None:
            return None
        return ctx.sig.present(ctx.realisation(o, self.where))

    def depth(self):
        return 1


@dataclass(frozen=True)
class Feat(Term):

    feature: str
    slot: str
    value: object
    where: Literal["current", "reference"] = "current"

    def slots(self):
        return frozenset({self.slot})

    def eval(self, ctx):
        o = ctx.resolve(self.slot)
        if o is None:
            return None
        v = ctx.sig.ft(ctx.realisation(o, self.where), self.feature)
        return k_eq(v, self.value)

    def depth(self):
        return 1


@dataclass(frozen=True)
class SameFeat(Term):

    feature: str
    left: tuple[str, str]
    right: tuple[str, str]

    def slots(self):
        return frozenset({self.left[0], self.right[0]})

    def eval(self, ctx):
        lo, ro = ctx.resolve(self.left[0]), ctx.resolve(self.right[0])
        if lo is None or ro is None:
            return None
        a = ctx.sig.ft(ctx.realisation(lo, self.left[1]), self.feature)
        b = ctx.sig.ft(ctx.realisation(ro, self.right[1]), self.feature)
        return k_eq(a, b)

    def depth(self):
        return 1


@dataclass(frozen=True)
class SameSeg(Term):

    left: tuple[str, str]
    right: tuple[str, str]

    def slots(self):
        return frozenset({self.left[0], self.right[0]})

    def eval(self, ctx):
        lo, ro = ctx.resolve(self.left[0]), ctx.resolve(self.right[0])
        if lo is None or ro is None:
            return None
        return ctx.realisation(lo, self.left[1]) == ctx.realisation(ro, self.right[1])

    def depth(self):
        return 1


@dataclass(frozen=True)
class Positional(Term):

    kind: Literal["first_of_word", "last_nucleus_of_word"]
    slot: str

    def slots(self):
        return frozenset({self.slot})

    def eval(self, ctx):
        o = ctx.resolve(self.slot)
        if o is None:
            return None
        return ctx.positional(self.kind, o)

    def depth(self):
        return 1


@dataclass(frozen=True)
class InScope(Term):

    slot: str
    scope: Scope
    anchor: str = "t"

    def slots(self):
        return frozenset({self.slot, self.anchor})

    def eval(self, ctx):
        a, o = ctx.resolve(self.anchor), ctx.resolve(self.slot)
        if a is None or o is None:
            return None
        return self.scope.admits(ctx.sig, a, o)

    def depth(self):
        return 1


FILTERS: dict[str, Callable[[Signature, str], bool]] = {
    "present": lambda sig, seg: sig.present(seg),
    "nuclear": lambda sig, seg: sig.ft(seg, "nuclear") is True,
    "nuclear_nonhigh": lambda sig, seg: (sig.ft(seg, "nuclear") is True
                                         and sig.ft(seg, "high") is not True),
    "obstruent": lambda sig, seg: sig.ft(seg, "obstruent") is True,
}


class EvalContext:

    def __init__(self, sig: Signature, reference: State, state: State,
                 decl: Declaration, locus: int):
        self.sig = sig
        self.reference = reference
        self.state = state
        self.decl = decl
        self.locus = locus
        self._slots = decl.declared_slots()
        self._cache: dict[str, int | None] = {}
        self._live = tuple(i for i, s in enumerate(state) if sig.present(s))
        self._live_ref = tuple(i for i, s in enumerate(reference) if sig.present(s))

    def realisation(self, origin: int, where: str) -> str:
        return self.reference[origin] if where == "reference" else self.state[origin]

    def positional(self, kind: str, origin: int) -> K:
        rec = self.sig.origins[origin]
        if kind == "first_of_word":
            return origin == 0 or self.sig.origins[origin - 1].word != rec.word
        if kind == "last_nucleus_of_word":
            nuclei = [i for i in self._live
                      if self.sig.origins[i].word == rec.word
                      and self.sig.ft(self.state[i], "nuclear") is True]
            return bool(nuclei) and nuclei[-1] == origin
        raise KeyError(kind)

    def resolve(self, name: str) -> int | None:
        if name in self._cache:
            return self._cache[name]
        self._cache[name] = value = self._resolve(self._slots[name])
        return value

    def _step_candidates(self, seq: Sequence[int], anchor: int, direction: int) -> list[int]:
        if direction > 0:
            return [i for i in seq if i > anchor]
        return [i for i in reversed(seq) if i < anchor]

    def _first_match(self, seq: Sequence[int], anchor: int, slot: SlotDecl,
                     use_reference: bool) -> int | None:
        seg = self.reference if use_reference else self.state
        for i in self._step_candidates(seq, anchor, slot.direction):
            if slot.filter is not None and not FILTERS[slot.filter](self.sig, seg[i]):
                if slot.filter_mode == "stop":
                    return None
                continue
            return i
        return None

    def _resolve(self, slot: SlotDecl) -> int | None:
        if slot.kind == "anchor":
            return self.locus
        anchor = self.locus
        if slot.kind == "searched":
            live = self._live
            for i in self._step_candidates(live, anchor, slot.direction):
                if not slot.scope.admits(self.sig, anchor, i):
                    continue
                if slot.filter is not None and not FILTERS[slot.filter](self.sig, self.state[i]):
                    continue
                return i
            return None
        if slot.policy == "dynamic":
            partner = self._first_match(self._live, anchor, slot, use_reference=False)
            if partner is None or not slot.scope.admits(self.sig, anchor, partner):
                return None
            return partner
        if slot.policy == "dynamic_in_scope":
            live = [i for i in self._live if slot.scope.admits(self.sig, anchor, i)]
            partner = self._first_match(live, anchor, slot, use_reference=False)
            return partner
        partner = self._first_match(self._live_ref, anchor, slot, use_reference=True)
        if partner is None or not slot.scope.admits(self.sig, anchor, partner):
            return None
        if not self.sig.present(self.state[anchor]) or not self.sig.present(self.state[partner]):
            return None
        if slot.policy == "origin_bound":
            return partner
        lo, hi = (anchor, partner) if anchor < partner else (partner, anchor)
        for i in range(lo + 1, hi):
            if self.sig.present(self.state[i]):
                return None
        return partner


@dataclass(frozen=True)
class Readers:
    context: bool
    defined: bool
    good: bool

    @property
    def pressure(self) -> int:
        return int(self.defined and not self.good)

    @property
    def marked(self) -> int:
        return int(self.context and self.defined and not self.good)

    def triple(self) -> tuple[bool, bool, bool]:
        return (self.context, self.defined, self.good)


def read(sig: Signature, reference: State, state: State,
         decl: Declaration, locus: int) -> Readers:
    ctx = EvalContext(sig, reference, state, decl, locus)
    value = decl.consequence.eval(ctx)
    if decl.definedness_override is None:
        defined = value is not None
    else:
        defined = collapse(decl.definedness_override.eval(ctx))
    good = value is True
    context = collapse(decl.activation.eval(ctx))
    return Readers(context=context, defined=defined, good=good)


__all__ = [
    "K", "UNDEF", "k_and", "k_or", "k_not", "k_eq", "collapse",
    "OriginRecord", "Signature", "State", "Scope", "UNSCOPED",
    "SlotDecl", "Declaration", "Term", "Not", "And", "Or", "Const",
    "TRUE", "FALSE", "Resolves", "Present", "Feat", "SameFeat", "SameSeg",
    "Positional", "InScope", "EvalContext", "Readers", "read", "FILTERS",
]
