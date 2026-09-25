from __future__ import annotations

from fractions import Fraction
from typing import Mapping, Sequence

from .core import Decl, NodeId, Sigma, Struct, read


def tier_of(sigma, decl: Decl, default: str = "seg") -> str:
    sd = sigma.sorts.get(decl.anchor_sort)
    return (sd.tier if sd is not None and sd.tier else default)


def loci(struct: Struct, decl: Decl, tier: str = "seg",
         reference: Struct | None = None) -> tuple[NodeId, ...]:
    src = struct
    if decl.locus_side == "reference" and reference is not None:
        src = reference
    out = [n for n in src.nodes(tier) if n.sort == decl.anchor_sort]
    if not out:
        for t, ns in src.order.items():
            out.extend(n for n in ns if n.sort == decl.anchor_sort)
    return tuple(out)


def subject_tuple(sigma: Sigma, reference: Struct, state: Struct, decl: Decl,
                  locus: NodeId, tier: str = "seg"):
    from .core import Ctx
    ctx = Ctx(sigma, reference, state, decl, locus, tier)
    return tuple(ctx.resolve(nm) for nm in sorted(decl.consequence.slots()))


def activation(sigma: Sigma, reference: Struct, decls: Mapping[str, Decl],
               tier: str = "seg", key: str = "M"):
    out = {}
    for name, d in decls.items():
        row = {}
        dt = tier_of(sigma, d, tier)
        for n in loci(reference, d, dt, reference):
            r = read(sigma, reference, reference, d, n, dt)
            if key == "M":
                row[n] = bool(r.marked)
            elif key == "C":
                row[n] = bool(r.context)
            else:
                raise ValueError(key)
        out[name] = row
    return out


def marked_subjects(sigma: Sigma, reference: Struct, decls: Mapping[str, Decl],
                    tier: str = "seg"):
    out = {}
    for name, d in decls.items():
        S = set()
        dt = tier_of(sigma, d, tier)
        for n in loci(reference, d, dt, reference):
            if read(sigma, reference, reference, d, n, dt).marked:
                S.add(subject_tuple(sigma, reference, reference, d, n, dt))
        out[name] = S
    return out


def t_correspondent(state: Struct, node):
    if node is None:
        return None
    if state.corr is None:
        return node
    cs = state.correspondents(node)
    return cs[0] if len(cs) == 1 else None


def _keys(state: Struct, node, mode: str):
    if node is None:
        return ()
    if state.corr is None:
        return (node,)
    if mode == "self":
        return () if node.kind == "made" else (node,)
    cs = state.correspondents(node)
    if mode == "unique":
        return cs if len(cs) == 1 else ()
    return cs


def coefficients(sigma: Sigma, reference: Struct, state: Struct,
                 decls: Mapping[str, Decl], acts, tier: str = "seg",
                 retain_faithfulness: bool = False, subjects=None,
                 keying: str = "unique"):
    out = {}
    for name, d in decls.items():
        old = new = 0
        dt = tier_of(sigma, d, tier)
        for n in loci(state, d, dt, reference):
            r = read(sigma, reference, state, d, n, dt)
            p, c = r.pressure, r.context
            if subjects is None:
                ks = _keys(state, n, keying)
                vals = [acts[name].get(k, False) for k in ks]
                a = (any(vals) if keying in ("unique", "existential")
                     else (bool(vals) and all(vals)))
            else:
                st = subject_tuple(sigma, reference, state, d, n, dt)
                if keying == "unique":
                    a = tuple(t_correspondent(state, x) for x in st) in subjects[name]
                else:
                    import itertools as _it
                    opts = [_keys(state, x, keying) or (None,) for x in st]
                    combos = [tuple(c) for c in _it.product(*opts)]
                    hits = [c in subjects[name] for c in combos]
                    a = (any(hits) if keying == "existential"
                         else (bool(hits) and all(hits)))
            if d.kind == "faithfulness" and not retain_faithfulness:
                old += int(p and c)
            else:
                old += int(p and a)
                new += int(p and (not a) and c)
        out[name] = (old, new)
    return out


def score(coeffs, weights: Mapping[str, int], lam: Fraction) -> Fraction:
    return sum(Fraction(weights[k]) * (Fraction(o) + lam * Fraction(n))
               for k, (o, n) in coeffs.items())
