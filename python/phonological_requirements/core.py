from __future__ import annotations

from dataclasses import dataclass, field, replace
from fractions import Fraction
from typing import Callable, Iterable, Literal, Mapping, Optional, Sequence

K = Optional[bool]


def k_not(a: K) -> K:
    return None if a is None else (not a)


def k_and(*xs: K) -> K:
    if any(x is False for x in xs):
        return False
    if any(x is None for x in xs):
        return None
    return True


def k_or(*xs: K) -> K:
    if any(x is True for x in xs):
        return True
    if any(x is None for x in xs):
        return None
    return False


class _Undef:
    __slots__ = ()
    def __repr__(self): return "UNDEF"
    def __bool__(self): raise TypeError("UNDEF has no truth value")


UNDEF = _Undef()


def k_eq(a, b) -> K:
    if a is UNDEF or b is UNDEF:
        return None
    return a == b


def collapse(a: K) -> bool:
    return a is True


ABSENT = "∅"

Totality = Literal["total", "derived"]


@dataclass(frozen=True)
class SortDecl:
    name: str
    totality: Totality
    tier: str | None = None
    comment: str = ""


@dataclass(frozen=True)
class RelDecl:
    name: str
    mode: Literal["succession", "association", "domination", "correspondence"]
    source: str
    target: str
    instance_sort: str


@dataclass(frozen=True)
class Sigma:
    sorts: Mapping[str, SortDecl]
    relations: Mapping[str, RelDecl]
    features: Mapping[str, Mapping[str, object]]
    default_features: Mapping[str, object]
    domains: tuple[str, ...] = ()

    def totality(self, sort: str) -> Totality:
        return self.sorts[sort].totality

    def ft(self, segment: str, name: str):
        row = self.features.get(segment, self.default_features)
        v = row.get(name, "undefined")
        return UNDEF if v is None or v == "undefined" else v

    def present(self, segment: str) -> bool:
        row = self.features.get(segment, self.default_features)
        return bool(row.get("present", True))


@dataclass(frozen=True)
class NodeId:
    sort: str
    kind: Literal["lex", "made"]
    index: int

    def __repr__(self):
        return f"{self.sort}{'' if self.kind=='lex' else '*'}{self.index}"


@dataclass(frozen=True)
class Struct:
    order: Mapping[str, tuple[NodeId, ...]]
    real: Mapping[NodeId, str]
    dom: Mapping[NodeId, Mapping[str, int]]
    assoc: frozenset = frozenset()
    corr: Mapping[NodeId, tuple] | None = None

    def correspondents(self, node: NodeId) -> tuple:
        if self.corr is None:
            return () if node.kind == "made" else (node,)
        return tuple(self.corr.get(node, ()))

    def nodes(self, tier: str) -> tuple[NodeId, ...]:
        return self.order.get(tier, ())

    def well_formed(self, reference: "Struct | None" = None) -> tuple[bool, tuple[str, ...]]:
        faults: list[str] = []
        ref = self if reference is None else reference
        all_nodes = [n for ns in self.order.values() for n in ns]
        for t, ns in self.order.items():
            if len(set(ns)) != len(ns):
                faults.append(f"duplicate-node:{t}")
        for n in all_nodes:
            if n not in self.real:
                faults.append(f"unrealised:{n!r}")
        node_set = set(all_nodes)
        for a, b in self.assoc:
            if a not in node_set or b not in node_set:
                faults.append(f"association-off-structure:{a!r}-{b!r}")
        ref_nodes = {n for ns in ref.order.values() for n in ns}
        for n in all_nodes:
            if n.kind == "lex" and n not in ref_nodes:
                faults.append(f"lexical-node-not-in-reference:{n!r}")
        if self.corr is None:
            for r in ref_nodes:
                if r not in node_set:
                    faults.append(f"reference-node-lost:{r!r}")
        else:
            for n, cs in self.corr.items():
                for c in cs:
                    if c not in ref_nodes:
                        faults.append(f"correspondent-not-in-reference:{n!r}->{c!r}")
        return (not faults), tuple(sorted(set(faults)))

    def with_real(self, node: NodeId, value: str) -> "Struct":
        r = dict(self.real); r[node] = value
        return replace(self, real=r)


@dataclass(frozen=True)
class Scope:
    same: tuple[str, ...] = ()
    delta: Mapping[str, int] = field(default_factory=dict)
    min_delta: Mapping[str, int] = field(default_factory=dict)
    label: str = ""

    def admits(self, s: Struct, anchor: NodeId, other: NodeId) -> bool:
        a, b = s.dom.get(anchor, {}), s.dom.get(other, {})
        for c in self.same:
            if a.get(c) != b.get(c):
                return False
        for c, d in self.delta.items():
            if b.get(c) is None or a.get(c) is None or b[c] - a[c] != d:
                return False
        for c, d in self.min_delta.items():
            if b.get(c) is None or a.get(c) is None or b[c] - a[c] < d:
                return False
        return True


UNSCOPED = Scope(label="unscoped")

Policy = Literal["dynamic", "dynamic_in_scope", "origin_bound", "witness", "reference"]
Role = Literal["subject", "trigger"]


@dataclass(frozen=True)
class Slot:
    name: str
    sort: str
    role: Role
    kind: Literal["anchor", "step", "stepof", "search", "assoc", "assocof",
                  "corr"] = "anchor"
    relation: str | None = None
    scope: Scope = UNSCOPED
    direction: int = 1
    filter: str | None = None
    filter_mode: Literal["skip", "stop"] = "skip"
    policy: Policy = "dynamic"
    tier: str | None = None
    of: str | None = None
    where: Literal["current", "reference"] = "current"
    coord: tuple[tuple[str, object], ...] = ()

    def total(self, sigma: "Sigma") -> bool:
        return self.kind == "anchor" and sigma.totality(self.sort) == "total"


class Term:
    def slots(self) -> frozenset[str]: raise NotImplementedError
    def eval(self, ctx) -> K: raise NotImplementedError
    def depth(self) -> int: raise NotImplementedError


@dataclass(frozen=True)
class Not(Term):
    a: Term
    def slots(self): return self.a.slots()
    def eval(self, ctx): return k_not(self.a.eval(ctx))
    def depth(self): return 1 + self.a.depth()


@dataclass(frozen=True)
class And(Term):
    parts: tuple[Term, ...]
    def slots(self): return frozenset().union(*[p.slots() for p in self.parts]) if self.parts else frozenset()
    def eval(self, ctx): return k_and(*[p.eval(ctx) for p in self.parts])
    def depth(self): return 1 + max((p.depth() for p in self.parts), default=0)


@dataclass(frozen=True)
class Or_(Term):
    parts: tuple[Term, ...]
    def slots(self): return frozenset().union(*[p.slots() for p in self.parts]) if self.parts else frozenset()
    def eval(self, ctx): return k_or(*[p.eval(ctx) for p in self.parts])
    def depth(self): return 1 + max((p.depth() for p in self.parts), default=0)


@dataclass(frozen=True)
class Const(Term):
    value: K
    def slots(self): return frozenset()
    def eval(self, ctx): return self.value
    def depth(self): return 0


TRUE, FALSE = Const(True), Const(False)


@dataclass(frozen=True)
class Resolves(Term):
    slot: str
    def slots(self): return frozenset({self.slot})
    def eval(self, ctx): return ctx.resolve(self.slot) is not None
    def depth(self): return 1


@dataclass(frozen=True)
class Present(Term):
    slot: str
    where: Literal["current", "reference"] = "current"
    def slots(self): return frozenset({self.slot})
    def eval(self, ctx):
        o = ctx.resolve(self.slot)
        if o is None: return None
        r = ctx.realisation(o, self.where)
        return None if r is None else ctx.sigma.present(r)
    def depth(self): return 1


@dataclass(frozen=True)
class Feat(Term):
    feature: str
    slot: str
    value: object
    where: Literal["current", "reference"] = "current"
    def slots(self): return frozenset({self.slot})
    def eval(self, ctx):
        o = ctx.resolve(self.slot)
        if o is None: return None
        r = ctx.realisation(o, self.where)
        if r is None: return None
        return k_eq(ctx.sigma.ft(r, self.feature), self.value)
    def depth(self): return 1


@dataclass(frozen=True)
class SameFeat(Term):
    feature: str
    left: tuple[str, str]
    right: tuple[str, str]
    def slots(self): return frozenset({self.left[0], self.right[0]})
    def eval(self, ctx):
        lo, ro = ctx.resolve(self.left[0]), ctx.resolve(self.right[0])
        if lo is None or ro is None: return None
        a, b = ctx.realisation(lo, self.left[1]), ctx.realisation(ro, self.right[1])
        if a is None or b is None: return None
        return k_eq(ctx.sigma.ft(a, self.feature), ctx.sigma.ft(b, self.feature))
    def depth(self): return 1


@dataclass(frozen=True)
class SameSeg(Term):
    left: tuple[str, str]
    right: tuple[str, str]
    def slots(self): return frozenset({self.left[0], self.right[0]})
    def eval(self, ctx):
        lo, ro = ctx.resolve(self.left[0]), ctx.resolve(self.right[0])
        if lo is None or ro is None: return None
        a, b = ctx.realisation(lo, self.left[1]), ctx.realisation(ro, self.right[1])
        if a is None or b is None: return None
        return a == b
    def depth(self): return 1


@dataclass(frozen=True)
class Positional(Term):
    kind: Literal["first_of", "last_live_of"]
    slot: str
    domain: str
    filter: str | None = None
    def slots(self): return frozenset({self.slot})
    def eval(self, ctx):
        o = ctx.resolve(self.slot)
        if o is None: return None
        return ctx.positional(self.kind, o, self.domain, self.filter)
    def depth(self): return 1


@dataclass(frozen=True)
class InScope(Term):
    slot: str
    scope: Scope
    anchor: str = "t"
    def slots(self): return frozenset({self.slot, self.anchor})
    def eval(self, ctx):
        a, o = ctx.resolve(self.anchor), ctx.resolve(self.slot)
        if a is None or o is None: return None
        return self.scope.admits(ctx.state, a, o)
    def depth(self): return 1


@dataclass(frozen=True)
class Linked(Term):
    left: str
    right: str
    where: Literal["current", "reference"] = "current"
    def slots(self): return frozenset({self.left, self.right})
    def eval(self, ctx):
        a, b = ctx.resolve(self.left), ctx.resolve(self.right)
        if a is None or b is None: return None
        src = ctx.reference if self.where == "reference" else ctx.state
        return (a, b) in src.assoc or (b, a) in src.assoc
    def depth(self): return 1


@dataclass(frozen=True)
class Made(Term):
    slot: str
    def slots(self): return frozenset({self.slot})
    def eval(self, ctx):
        o = ctx.resolve(self.slot)
        if o is None: return None
        return o.kind == "made"
    def depth(self): return 1


@dataclass(frozen=True)
class Decl:
    name: str
    anchor_sort: str
    slots: tuple[Slot, ...]
    activation: Term
    consequence: Term
    scope: Scope = UNSCOPED
    kind: Literal["markedness", "faithfulness"] = "markedness"
    definedness_override: Term | None = None
    locus_side: Literal["candidate", "reference"] = "candidate"

    def by_name(self) -> Mapping[str, Slot]:
        return {s.name: s for s in self.slots}

    def subject_slots(self) -> tuple[str, ...]:
        return tuple(sorted(self.consequence.slots()))

    def well_typed(self, sigma: Sigma) -> tuple[bool, tuple[str, ...]]:
        from .syntax import faults as term_faults
        faults: list[str] = []
        for term in (self.activation, self.consequence, self.definedness_override):
            if term is not None:
                faults.extend(term_faults(term))
        if faults:
            return False, tuple(sorted(set(faults)))
        decl = self.by_name()
        for s in self.consequence.slots() | self.activation.slots():
            if s not in decl:
                faults.append(f"undeclared-slot:{s}")
        for s in self.consequence.slots():
            d = decl.get(s)
            if d is None:
                continue
            if d.role != "subject":
                faults.append(f"trigger-slot-in-consequence:{s}")
            if (not d.total(sigma)) and d.kind not in ("assoc", "assocof", "corr") and d.scope == UNSCOPED:
                faults.append(f"unscoped-nontotal-subject:{s}")
        seen: dict[tuple, tuple] = {}
        for d in self.slots:
            if d.kind == "anchor":
                continue
            key = (d.kind, d.relation, d.direction, d.filter)
            how = (d.scope, d.policy, d.filter_mode, d.coord)
            if key in seen and seen[key] != how:
                faults.append(f"resolution-split:{d.kind}:{d.relation}:{d.direction:+d}")
            seen.setdefault(key, how)
        if self.definedness_override is not None:
            faults.append("definedness-override")
        return (not faults), tuple(sorted(set(faults)))

    def derived_subject(self, sigma: Sigma) -> bool:
        decl = self.by_name()
        return any(not decl[s].total(sigma)
                   for s in self.consequence.slots() if s in decl)


FILTERS: dict[str, Callable[[Sigma, str], bool]] = {
    "present":         lambda g, x: g.present(x),
    "nuclear":         lambda g, x: g.ft(x, "nuclear") is True,
    "nuclear_nonhigh": lambda g, x: g.ft(x, "nuclear") is True and g.ft(x, "high") is not True,
    "nonhigh":         lambda g, x: g.ft(x, "high") is not True,
    "obstruent":       lambda g, x: g.ft(x, "obstruent") is True,
    "consonantal":     lambda g, x: g.ft(x, "nuclear") is not True,
    "atr_specified":   lambda g, x: g.ft(x, "atr") is not UNDEF,
    "atr_specified_or_high": lambda g, x: g.ft(x, "atr") is not UNDEF or g.ft(x, "high") is True,
    "stressed":        lambda g, x: g.ft(x, "stress") is True,
    "moraic":          lambda g, x: g.ft(x, "moraic") is True,
}


class Ctx:

    __slots__ = ("sigma", "reference", "state", "decl", "locus", "tier",
                 "_slots", "_cache", "_live", "_live_ref", "_inv", "_anchor", "_all")

    def __init__(self, sigma: Sigma, reference: Struct, state: Struct,
                 decl: Decl, locus: NodeId, tier: str = "seg"):
        self.sigma = sigma
        self.reference = reference
        self.state = state
        self.decl = decl
        self.locus = locus
        self.tier = tier
        self._slots = decl.by_name()
        self._cache: dict[str, NodeId | None] = {}
        self._live = tuple(n for n in state.nodes(tier)
                           if sigma.present(state.real.get(n, ABSENT)))
        self._live_ref = tuple(n for n in reference.nodes(tier)
                               if sigma.present(reference.real.get(n, ABSENT)))
        self._all = state
        inv: dict[NodeId, list[NodeId]] = {}
        if state.corr is not None:
            for nd in state.nodes(tier):
                for c in state.correspondents(nd):
                    inv.setdefault(c, []).append(nd)
        self._inv = {k: tuple(v) for k, v in inv.items()}
        if locus in state.real or state.corr is None:
            self._anchor = locus
        else:
            im = self._inv.get(locus, ())
            self._anchor = im[0] if len(im) == 1 else None

    def realisation(self, node: NodeId, where: str) -> str | None:
        if where != "reference":
            if node in self.state.real:
                return self.state.real[node]
            if self.state.corr is None:
                return None
            _ = None
            cs = self._inv.get(node, ())
            if len(cs) == 0:
                return ABSENT
            if len(cs) > 1:
                return None
            return self.state.real.get(cs[0])
        if node in self.reference.real and (self.state.corr is None
                                            or node not in self.state.real):
            return self.reference.real[node]
        cs = self.state.correspondents(node)
        if len(cs) != 1:
            return None
        return self.reference.real.get(cs[0])

    def positional(self, kind: str, node: NodeId, domain: str,
                   filt: str | None) -> K:
        d = self.state.dom.get(node, {}).get(domain)
        if d is None:
            return None
        if kind == "first_of":
            same = [n for n in self.state.nodes(self.tier)
                    if self.state.dom.get(n, {}).get(domain) == d]
            return bool(same) and same[0] == node
        if kind == "last_live_of":
            same = [n for n in self._live
                    if self.state.dom.get(n, {}).get(domain) == d
                    and (filt is None
                         or FILTERS[filt](self.sigma, self.state.real[n]))]
            return bool(same) and same[-1] == node
        raise KeyError(kind)

    def _coord_ok(self, slot: Slot, node: NodeId) -> bool:
        d = self.state.dom.get(node, {})
        return all(d.get(k) == v for k, v in slot.coord)

    def resolve(self, name: str) -> NodeId | None:
        if name in self._cache:
            return self._cache[name]
        self._cache[name] = v = self._resolve(self._slots[name])
        return v

    def _after(self, seq: Sequence[NodeId], anchor: NodeId, direction: int):
        try:
            i = seq.index(anchor) if isinstance(seq, list) else list(seq).index(anchor)
        except ValueError:
            full = list(self.state.nodes(self.tier))
            j = full.index(anchor)
            if direction > 0:
                return [n for n in seq if full.index(n) > j]
            return [n for n in reversed(list(seq)) if full.index(n) < j]
        s = list(seq)
        return s[i + 1:] if direction > 0 else list(reversed(s[:i]))

    def _first_match(self, seq, anchor, slot: Slot, use_reference: bool):
        src = self.reference if use_reference else self.state
        for n in self._after(seq, anchor, slot.direction):
            r = src.real.get(n)
            if slot.filter is not None and (r is None
                                            or not FILTERS[slot.filter](self.sigma, r)):
                if slot.filter_mode == "stop":
                    return None
                continue
            return n
        return None

    def _resolve(self, slot: Slot) -> NodeId | None:
        if slot.kind == "anchor":
            return self.locus
        anchor = self._anchor
        if anchor is None:
            return None
        if slot.kind == "assocof":
            base = self.resolve(slot.of) if slot.of else None
            if base is None:
                return None
            src = self.reference if slot.where == "reference" else self.state
            tier = slot.tier
            for a, b in sorted(src.assoc, key=repr):
                if a == base and (tier is None or b in self.state.nodes(tier)):
                    return b
                if b == base and (tier is None or a in self.state.nodes(tier)):
                    return a
            return None
        if slot.kind == "stepof":
            base = self.resolve(slot.of) if slot.of else None
            if base is None:
                return None
            tier = slot.tier or self.tier
            live = tuple(n for n in self.state.nodes(tier)
                         if self.sigma.present(self.state.real.get(n, ABSENT)))
            order = list(self.state.nodes(tier))
            if base not in order:
                return None
            i = order.index(base)
            after = [n for n in live if order.index(n) > i] if slot.direction > 0 \
                else [n for n in reversed(live) if order.index(n) < i]
            for n in after:
                if slot.filter is not None and not FILTERS[slot.filter](
                        self.sigma, self.state.real.get(n, ABSENT)):
                    if slot.filter_mode == "stop":
                        return None
                    continue
                if not slot.scope.admits(self.state, base, n) or not self._coord_ok(slot, n):
                    return None
                return n
            return None
        if slot.kind == "corr":
            base = self.resolve(slot.of) if slot.of else anchor
            if base is None:
                return None
            if slot.direction > 0:
                cs = tuple(self.state.correspondents(base))
                return cs[0] if len(cs) == 1 else None
            ims = [n for n in self._inv.get(base, ()) if n != base]
            return ims[0] if len(ims) == 1 else None
        if slot.kind == "assoc":
            src = self.reference if slot.where == "reference" else self.state
            tier = slot.tier
            def _ok(n):
                if tier is None:
                    return True
                return n in self.state.nodes(tier)
            for a, b in sorted(src.assoc, key=repr):
                if a == anchor and _ok(b):
                    return b
                if b == anchor and _ok(a):
                    return a
            return None
        if slot.kind == "search":
            src = self.reference if slot.where == "reference" else self.state
            start, live = anchor, self._live
            if slot.of:
                start = self.resolve(slot.of)
                if start is None:
                    return None
                tier = slot.tier or self.tier
                live = tuple(n for n in self.state.nodes(tier)
                             if self.sigma.present(self.state.real.get(n, ABSENT)))
            for n in self._after(live, start, slot.direction):
                if not slot.scope.admits(self.state, start, n):
                    continue
                r = src.real.get(n)
                if slot.filter is not None and (r is None
                                                or not FILTERS[slot.filter](self.sigma, r)):
                    continue
                if not self._coord_ok(slot, n):
                    continue
                return n
            return None
        if slot.policy == "dynamic":
            p = self._first_match(self._live, anchor, slot, False)
            if p is None or not slot.scope.admits(self.state, anchor, p) \
               or not self._coord_ok(slot, p):
                return None
            return p
        if slot.policy == "dynamic_in_scope":
            live = [n for n in self._live if slot.scope.admits(self.state, anchor, n)]
            p = self._first_match(live, anchor, slot, False)
            return p if p is not None and self._coord_ok(slot, p) else None
        p = self._first_match(self._live_ref, anchor, slot, True)
        if p is None or not slot.scope.admits(self.reference, anchor, p) \
           or not self._coord_ok(slot, p):
            return None
        if slot.policy == "reference":
            return p
        if not self.sigma.present(self.state.real.get(anchor, ABSENT)) or \
           not self.sigma.present(self.state.real.get(p, ABSENT)):
            return None
        if slot.policy == "origin_bound":
            return p
        full = list(self.state.nodes(self.tier))
        i, j = full.index(anchor), full.index(p)
        lo, hi = (i, j) if i < j else (j, i)
        for n in full[lo + 1:hi]:
            if self.sigma.present(self.state.real.get(n, ABSENT)):
                return None
        return p


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

    def triple(self): return (self.context, self.defined, self.good)


def read(sigma: Sigma, reference: Struct, state: Struct, decl: Decl,
         locus: NodeId, tier: str = "seg") -> Readers:
    ctx = Ctx(sigma, reference, state, decl, locus, tier)
    value = decl.consequence.eval(ctx)
    if decl.definedness_override is None:
        defined = value is not None
    else:
        defined = collapse(decl.definedness_override.eval(ctx))
    return Readers(context=collapse(decl.activation.eval(ctx)),
                   defined=defined, good=(value is True))
