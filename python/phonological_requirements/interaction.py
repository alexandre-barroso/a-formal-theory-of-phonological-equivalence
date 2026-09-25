from __future__ import annotations

from .core import (ABSENT, And, Const, Ctx, Decl, Feat, InScope, Linked, Made, Not, Or_, Positional,
                   Present, Resolves, SameFeat, SameSeg, Struct)
from .evaluate import loci, subject_tuple, tier_of
from .footprint import footprint, footprint_profile, used_slots
from .strictness import atoms

CORE_TERMS = (And, Or_, Not, Const, Resolves, Present, Feat, SameFeat, SameSeg, Positional, InScope, Linked, Made)


def custom_terms(decl: Decl):
    return sorted({type(a).__name__ for a in atoms(decl.activation) + atoms(decl.consequence) if not isinstance(a, CORE_TERMS)})


def _polarity(t, pos=True, acc=None):
    if acc is None:
        acc = []
    if isinstance(t, Not):
        _polarity(t.a, not pos, acc)
    elif isinstance(t, (And, Or_)):
        for p in t.parts:
            _polarity(p, pos, acc)
    else:
        acc.append((t, pos))
    return acc


def destroys(decl: Decl):
    subs = set(decl.consequence.slots())
    return sorted({a.slot for a, pos in _polarity(decl.consequence)
                   if isinstance(a, Present) and not pos and a.slot in subs})


def reads_reference(decl: Decl):
    if decl.locus_side == "reference":
        return True
    for a in atoms(decl.activation) + atoms(decl.consequence):
        if getattr(a, "where", None) == "reference":
            return True
        for side in ("left", "right"):
            v = getattr(a, side, None)
            if isinstance(v, tuple) and len(v) == 2 and v[1] == "reference":
                return True
        if type(a).__name__.startswith("_Ref"):
            return True
    return any(getattr(s, "policy", None) in ("reference", "origin_bound", "witness") for s in decl.slots)


def _passes(sigma, slot, r):
    from .core import FILTERS
    if slot.filter is None:
        return True
    return r is not None and FILTERS[slot.filter](sigma, r)


def read_set(sigma, ref: Struct, state: Struct, decl: Decl, locus, tier="seg"):
    if footprint_profile(state, decl, tier) == "full_fixed_frame_support":
        return footprint(sigma, state, decl, locus, tier), False
    if custom_terms(decl) or any(s.kind in ("assoc", "assocof", "corr") for s in used_slots(decl)) \
            or any(isinstance(a, Linked) for a in atoms(decl.activation) + atoms(decl.consequence)):
        return footprint(sigma, state, decl, locus, tier), False
    ctx = Ctx(sigma, ref, state, decl, locus, tier)
    anchor = ctx._anchor
    R = {locus}
    if anchor is None:
        return R, True
    R.add(anchor)
    for s in used_slots(decl):
        if s.kind == "anchor":
            continue
        dt = (s.tier or tier) if s.kind == "stepof" or (s.kind == "search" and s.of) else tier
        if s.kind == "stepof" or (s.kind == "search" and s.of):
            start = ctx.resolve(s.of)
            if start is None:
                continue
        else:
            start = anchor
        ordr = list(state.nodes(dt))
        if start not in ordr:
            continue
        i = ordr.index(start)
        side = ordr[i + 1:] if s.direction > 0 else ordr[:i][::-1]
        if s.kind == "step" and s.policy in ("reference", "origin_bound", "witness"):
            p = ctx._first_match(ctx._live_ref, anchor, s, True)
            if p is None or not s.scope.admits(ref, anchor, p):
                continue
            if s.policy == "reference":
                continue
            R.add(p)
            if s.policy == "witness":
                full = list(state.nodes(tier))
                a, b = sorted((full.index(anchor), full.index(p)))
                R |= set(full[a + 1:b])
            continue
        admitted = [n for n in side if s.scope.admits(state, start, n)]
        if s.kind == "search" or (s.kind == "step" and s.policy == "dynamic_in_scope"):
            src = ref if (s.kind == "search" and getattr(s, "where", None) == "reference") else state
            for n in admitted:
                R.add(n)
                if sigma.present(state.real.get(n, ABSENT)) and _passes(sigma, s, src.real.get(n)) and ctx._coord_ok(s, n):
                    break
            continue
        far = max((side.index(n) for n in admitted), default=-1)
        for k, n in enumerate(side):
            if k > far:
                break
            R.add(n)
            if sigma.present(state.real.get(n, ABSENT)):
                if _passes(sigma, s, state.real.get(n)) or s.filter_mode == "stop":
                    break
    terms = (decl.activation, decl.consequence)
    if decl.definedness_override is not None:
        terms += (decl.definedness_override,)
    for term in terms:
        for a in atoms(term):
            if isinstance(a, Positional):
                d = state.dom.get(locus, {}).get(a.domain)
                if d is not None:
                    R |= {n for n in state.nodes(tier) if state.dom.get(n, {}).get(a.domain) == d}
    return R, True


def effects(sigma, ref: Struct, state: Struct, decls, tier="seg"):
    out = {}
    for name, d in decls.items():
        dt = tier_of(sigma, d, tier)
        for l in loci(state, d, dt, ref):
            R, exact = read_set(sigma, ref, state, d, l, dt)
            subs = {x for x in subject_tuple(sigma, ref, state, d, l, dt) if x is not None}
            out[(name, repr(l))] = (R, subs, exact)
    return out


def locus_graph(sigma, ref: Struct, states, decls, tier="seg"):
    edges, shared, keys, inexact = set(), set(), set(), set()
    for st in states:
        E = effects(sigma, ref, st, decls, tier)
        items = list(E.items())
        keys |= set(E)
        for ka, (Ra, Sa, ea) in items:
            if not ea:
                inexact.add(ka[0])
            if not Sa:
                continue
            if decls[ka[0]].kind == "faithfulness":
                for kb, (Rb, Sb, eb) in items:
                    if ka != kb and (Sa & Sb) and ka < kb:
                        shared.add((ka, kb))
                continue
            for kb, (Rb, Sb, eb) in items:
                if ka == kb:
                    continue
                if Sa & Rb:
                    edges.add((ka, kb))
                if Sa & Sb and ka < kb:
                    shared.add((ka, kb))
    return keys, edges, shared, inexact


def sccs(nodes, edges):
    succ = {}
    for a, b in edges:
        succ.setdefault(a, set()).add(b)
    reach = {}
    for a in nodes:
        seen, stack = set(), [a]
        while stack:
            x = stack.pop()
            for y in succ.get(x, ()):
                if y not in seen:
                    seen.add(y); stack.append(y)
        reach[a] = seen
    comps, done = [], set()
    for a in nodes:
        if a in done:
            continue
        comp = {a} | {b for b in reach[a] if a in reach[b]}
        done |= comp
        if len(comp) >= 2:
            comps.append(sorted(comp))
    return comps


CLASSES = ("independent", "one_way", "reciprocal", "shared_subject", "creation_destruction", "cyclic")
RANK = {c: i for i, c in enumerate(CLASSES)}


def classify(decls, keys, edges, shared):
    names = sorted(decls)
    comps = sccs(sorted(keys), edges)
    incomp = {k: i for i, c in enumerate(comps) if len(c) >= 3 for k in c}
    des = {a: destroys(decls[a]) for a in names}
    refs = {a: reads_reference(decls[a]) for a in names}
    by_decl = {a: sorted(k for k in keys if k[0] == a) for a in names}
    out = {}
    for i, a in enumerate(names):
        for b in names[i:]:
            cnt = {c: 0 for c in CLASSES}
            strongest = "independent"
            for ka in by_decl[a]:
                for kb in by_decl[b]:
                    if a == b and ka >= kb:
                        continue
                    ab, ba = (ka, kb) in edges, (kb, ka) in edges
                    sh = (min(ka, kb), max(ka, kb)) in shared
                    cyc = ka in incomp and incomp[ka] == incomp.get(kb)
                    cd = (ab and bool(des[a])) or (ba and bool(des[b]))
                    cls = ("cyclic" if cyc else "creation_destruction" if cd else "shared_subject" if sh
                           else "reciprocal" if (ab and ba) else "one_way" if (ab or ba) else "independent")
                    cnt[cls] += 1
                    if RANK[cls] > RANK[strongest]:
                        strongest = cls
            n = sum(cnt.values())
            out[f"{a}|{b}"] = {"locus_pairs": n, "counts": cnt, "strongest": strongest,
                               "interacting_fraction": (round((n - cnt["independent"]) / n, 3) if n else None),
                               "reference_sensitive": refs[a] or refs[b]}
    return out, comps, refs, des
