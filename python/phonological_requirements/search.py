from __future__ import annotations

import itertools
from fractions import Fraction
from typing import Mapping, Sequence

from .core import ABSENT, Decl, NodeId, Sigma, Struct
from .evaluate import activation, coefficients, score, tier_of


def _sc(sigma, ref, s, decls, acts, weights, lam):
    return score(coefficients(sigma, ref, s, decls, acts), weights, lam)


def _faith_only(sigma, ref, s, decls, acts, weights, lam):
    f = {n: d for n, d in decls.items() if d.kind == "faithfulness"}
    return score(coefficients(sigma, ref, s, f, acts), weights, lam)


def deltas(sigma: Sigma, ref: Struct, decls, weights, lam, alphabet,
           tier: str = "seg"):
    acts = activation(sigma, ref, decls)
    base = _faith_only(sigma, ref, ref, decls, acts, weights, lam)
    sub = None
    for p in ref.nodes(tier):
        for v in alphabet:
            if ref.real.get(p) == v:
                continue
            c = _faith_only(sigma, ref, ref.with_real(p, v), decls, acts,
                            weights, lam) - base
            sub = c if sub is None else min(sub, c)
    ins = None
    ia = tuple(v for v in alphabet if v != ABSENT)
    for s in _insert(ref, ia, 1, tier):
        c = _faith_only(sigma, ref, s, decls, acts, weights, lam) - base
        ins = c if ins is None else min(ins, c)
    return sub, ins


def _insert(ref: Struct, alphabet, k: int, tier: str):
    if ABSENT in alphabet:
        raise ValueError("the insertion alphabet must not contain ABSENT")
    base = list(ref.nodes(tier))
    for places in itertools.combinations_with_replacement(range(len(base) + 1), k):
        for vals in itertools.product(alphabet, repeat=k):
            order, real, dom = [], dict(ref.real), dict(ref.dom)
            made = 0
            counts = {}
            for p in places:
                counts[p] = counts.get(p, 0) + 1
            for i in range(len(base) + 1):
                for _ in range(counts.get(i, 0)):
                    nd = NodeId("Or", "made", 10000 + made)
                    order.append(nd); real[nd] = vals[made]
                    host = base[min(i, len(base) - 1)]
                    dom[nd] = dict(ref.dom.get(host, {}))
                    made += 1
                if i < len(base):
                    order.append(base[i])
            yield Struct(order={**ref.order, tier: tuple(order)}, real=real,
                         dom=dom, assoc=ref.assoc, corr=ref.corr)


def enumerate_within(sigma: Sigma, ref: Struct, decls, alphabet,
                     dmax: int, k: int, tier: str = "seg"):
    base = list(ref.nodes(tier))
    ia = tuple(v for v in alphabet if v != ABSENT)
    if True:
        for st in (_insert(ref, ia, k, tier) if k else (ref,)):
            for d in range(dmax + 1):
                for ps in itertools.combinations(base, d):
                    alts = [tuple(v for v in alphabet if v != ref.real.get(p))
                            for p in ps]
                    for vals in itertools.product(*alts):
                        t = st
                        for p, v in zip(ps, vals):
                            t = t.with_real(p, v)
                        yield t


def complete_search(sigma: Sigma, ref: Struct, decls: Mapping[str, Decl],
                    weights, lam, alphabet: Sequence[str], tier: str = "seg",
                    incumbent: Struct | None = None):
    acts = activation(sigma, ref, decls)
    sub, ins = deltas(sigma, ref, decls, weights, lam, alphabet, tier)
    if sub is None or sub <= 0 or ins is None or ins <= 0:
        return None, {"status": "UNBOUNDED", "delta_sub": str(sub),
                      "delta_ins": str(ins)}
    B = _sc(sigma, ref, ref, decls, acts, weights, lam)
    if incumbent is not None:
        B = min(B, _sc(sigma, ref, incumbent, decls, acts, weights, lam))
    dmax, kmax = int(B / sub), int(B / ins)
    best, minima, n = None, [], 0
    for k in range(kmax + 1):
        if k * ins > B:
            break
        dlim = int((B - k * ins) / sub)
        for s in enumerate_within(sigma, ref, decls, alphabet, dlim, k, tier):
            n += 1
            v = _sc(sigma, ref, s, decls, acts, weights, lam)
            if best is None or v < best:
                best, minima = v, [s]
            elif v == best:
                minima.append(s)
    return minima, {"status": "COMPLETE", "delta_sub": str(sub),
                    "delta_ins": str(ins), "incumbent_bound": str(B),
                    "dmax": dmax, "kmax": kmax, "candidates_scored": n,
                    "best": str(best)}


def features_read(decls) -> tuple[str, ...]:
    from .core import Feat, SameFeat
    names = set()

    def walk(t):
        if isinstance(t, (Feat, SameFeat)):
            names.add(t.feature)
        for f in getattr(t, "__dataclass_fields__", {}):
            v = getattr(t, f)
            if isinstance(v, tuple):
                for x in v:
                    if hasattr(x, "eval"):
                        walk(x)
            elif hasattr(v, "eval"):
                walk(v)
    for d in decls.values():
        walk(d.activation); walk(d.consequence)
    return tuple(sorted(names | {"present"}))


def quotient_alphabet(sigma: Sigma, decls, alphabet, ref_value):
    ph = features_read(decls)
    def row(v):
        return tuple(sigma.ft(v, f) for f in ph)
    classes: dict[tuple, list[str]] = {}
    for v in alphabet:
        classes.setdefault(row(v), []).append(v)
    out = []
    rr = row(ref_value)
    for r, vs in classes.items():
        if r == rr:
            out.append(ref_value)
            other = [v for v in vs if v != ref_value]
            if other:
                out.append(other[0])
        else:
            out.append(vs[0])
    return tuple(out)


def bb_search(sigma: Sigma, ref: Struct, decls: Mapping[str, Decl],
              weights, lam, alphabet: Sequence[str], tier: str = "seg",
              incumbent: Struct | None = None, quotient: bool = True):
    from .core import Ctx, read
    acts = activation(sigma, ref, decls)
    sub, ins = deltas(sigma, ref, decls, weights, lam, alphabet, tier)
    if sub is None or sub <= 0 or ins is None or ins <= 0:
        return None, {"status": "UNBOUNDED", "delta_sub": str(sub),
                      "delta_ins": str(ins)}
    B = _sc(sigma, ref, ref, decls, acts, weights, lam)
    if incumbent is not None:
        B = min(B, _sc(sigma, ref, incumbent, decls, acts, weights, lam))
    kmax = int(B / ins)
    ia = tuple(v for v in alphabet if v != ABSENT)
    faith = {n: d for n, d in decls.items() if d.kind == "faithfulness"}
    mark = {n: d for n, d in decls.items() if d.kind == "markedness"}

    best, minima, seen = None, [], 0

    def _cell(base: Struct, node: NodeId, d, nm) -> Fraction:
        w = Fraction(weights.get(nm, 0))
        if w == 0:
            return Fraction(0)
        dt = tier_of(sigma, d, tier)
        src = ref if d.locus_side == "reference" else base
        if node not in src.nodes(dt):
            return Fraction(0)
        r = read(sigma, ref, base, d, node, dt)
        p, c = r.pressure, r.context
        a = acts[nm].get(node, False)
        if d.kind == "faithfulness":
            return w * Fraction(int(p and c))
        return w * (Fraction(int(p and a)) + lam * Fraction(int(p and (not a) and c)))

    def one_pos(base: Struct, node: NodeId) -> Fraction:
        return sum((_cell(base, node, d, nm) for nm, d in faith.items()),
                   Fraction(0))

    def locus_cost(base: Struct, node: NodeId) -> Fraction:
        return sum((_cell(base, node, d, nm) for nm, d in mark.items()),
                   Fraction(0))

    for k in range(kmax + 1):
        for skel in (_insert(ref, ia, k, tier) if k else (ref,)):
            order = list(skel.nodes(tier))
            m = len(order)
            free = [i for i, n in enumerate(order) if n.kind != "made"]

            def dfs(idx: int, cur: Struct, cost: Fraction, closed: int):
                nonlocal best, minima, seen
                if best is not None and cost > best:
                    return
                if idx == m:
                    c = cost
                    for j in range(closed, m):
                        c += locus_cost(cur, order[j])
                        if best is not None and c > best:
                            return
                    seen += 1
                    if best is None or c < best:
                        exact = _sc(sigma, ref, cur, decls, acts, weights, lam)
                        if exact != c:
                            raise AssertionError(
                                f"incremental {c} != exact {exact}")
                        best, minima = c, [cur]
                    elif c == best:
                        minima.append(cur)
                    return
                node = order[idx]
                vals = ([cur.real[node]] if node.kind == "made"
                        else (quotient_alphabet(sigma, decls, alphabet,
                                                ref.real[node])
                              if quotient else alphabet))
                for v in vals:
                    nxt = cur if cur.real.get(node) == v else cur.with_real(node, v)
                    c = cost + one_pos(nxt, node)
                    if best is not None and c > best:
                        continue
                    nc = closed
                    if sigma.present(v):
                        while nc < idx:
                            c += locus_cost(nxt, order[nc])
                            nc += 1
                            if best is not None and c > best:
                                break
                    if best is not None and c > best:
                        continue
                    dfs(idx + 1, nxt, c, nc)

            start = skel
            for i, n in enumerate(order):
                if n.kind != "made":
                    start = start.with_real(n, ref.real[n])
            dfs(0, start, Fraction(0), 0)
    return minima, {"status": "COMPLETE", "delta_sub": str(sub),
                    "delta_ins": str(ins), "incumbent_bound": str(B),
                    "kmax": kmax, "leaves_scored": seen, "best": str(best),
                    "quotient": quotient}
