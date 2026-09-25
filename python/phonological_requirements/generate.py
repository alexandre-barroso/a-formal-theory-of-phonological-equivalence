from __future__ import annotations

import itertools
from dataclasses import replace
from fractions import Fraction
from typing import Iterable, Mapping, Sequence

from .core import ABSENT, Decl, NodeId, Sigma, Struct
from .evaluate import activation, coefficients, marked_subjects, score


def rename_created(s: Struct, perm: Mapping[int, int]) -> Struct:
    def f(n: NodeId) -> NodeId:
        return NodeId(n.sort, n.kind, perm.get(n.index, n.index)) if n.kind == "made" else n
    order = {t: tuple(f(n) for n in ns) for t, ns in s.order.items()}
    real = {f(n): v for n, v in s.real.items()}
    dom = {f(n): v for n, v in s.dom.items()}
    assoc = frozenset((f(a), f(b)) for a, b in s.assoc)
    corr = None if s.corr is None else {f(n): v for n, v in s.corr.items()}
    return Struct(order=order, real=real, dom=dom, assoc=assoc, corr=corr)


def canonical(s: Struct, tier: str = "seg") -> tuple:
    seq = []
    made = 0
    for n in s.nodes(tier):
        if n.kind == "made":
            seq.append(("made", made, s.real.get(n), tuple(sorted(s.dom.get(n, {}).items()))))
            made += 1
        else:
            seq.append((n.kind, n.index, s.real.get(n), tuple(sorted(s.dom.get(n, {}).items()))))
    return tuple(seq)


def insertions(ref: Struct, alphabet: Sequence[str], k: int, tier: str = "seg",
               dom_of=lambda ref, i: None):
    if ABSENT in alphabet:
        raise ValueError("the insertion alphabet must not contain ABSENT: an "
                         "unrealised created position is not a distinct structure")
    base = list(ref.nodes(tier))
    sites = range(len(base) + 1)
    for places in itertools.combinations_with_replacement(sites, k):
        for vals in itertools.product(alphabet, repeat=k):
            order, real, dom = [], dict(ref.real), dict(ref.dom)
            made = 0
            counts = {p: 0 for p in set(places)}
            for p in places:
                counts[p] += 1
            for i in range(len(base) + 1):
                for _ in range(counts.get(i, 0)):
                    nd = NodeId("Or", "made", 10000 + made)
                    v = vals[made]
                    order.append(nd); real[nd] = v
                    host = base[min(i, len(base) - 1)]
                    dom[nd] = dict(ref.dom.get(host, {}))
                    made += 1
                if i < len(base):
                    order.append(base[i])
            yield Struct(order={**ref.order, tier: tuple(order)}, real=real,
                         dom=dom, assoc=ref.assoc, corr=ref.corr)


def productive(sigma: Sigma, ref: Struct, decls: Mapping[str, Decl],
               weights, lam, alphabet: Sequence[str], eligible,
               dep_name: str = "DEP", tier: str = "seg",
               insert_alphabet: Sequence[str] | None = None):
    if insert_alphabet is None:
        insert_alphabet = tuple(v for v in alphabet if v != ABSENT)
    acts = activation(sigma, ref, decls)
    delta = Fraction(weights.get(dep_name, 0))

    def sc(s):
        return score(coefficients(sigma, ref, s, decls, acts), weights, lam)

    incumbent = sc(ref)
    cur = ref
    improved = True
    while improved:
        improved = False
        for p in eligible(cur):
            for v in alphabet:
                if cur.real.get(p) == v:
                    continue
                t = cur.with_real(p, v)
                if sc(t) < sc(cur):
                    cur = t; improved = True
    incumbent = min(incumbent, sc(cur))
    if delta <= 0:
        return None, None, {"status": "UNBOUNDED",
                            "reason": f"the {dep_name} weight is 0, so the number of "
                                      "created positions is not bounded by the incumbent"}
    kmax = int(incumbent / delta)
    best, minima, n = None, [], 0
    seen = set()
    for k in range(kmax + 1):
        for base in insertions(ref, insert_alphabet, k, tier):
            for combo in itertools.product(alphabet, repeat=len(eligible(base))):
                s = base
                for p, v in zip(eligible(base), combo):
                    s = s.with_real(p, v)
                key = canonical(s, tier)
                if key in seen:
                    continue
                seen.add(key)
                n += 1
                v = sc(s)
                if best is None or v < best:
                    best, minima = v, [s]
                elif v == best:
                    minima.append(s)
    cert = {"status": "CERTIFIED", "incumbent_bound": str(incumbent),
            "delta": str(delta), "max_created_positions": kmax,
            "structures_enumerated_up_to_renaming": n,
            "argument": ("every created position charges at least delta, faithfulness is a "
                         "sum of nonnegative per-object terms and markedness is nonnegative, "
                         "so a candidate with more than floor(B/delta) created positions "
                         "scores above B")}
    return best, minima, cert


def _fresh(s: Struct, tier: str = "seg") -> int:
    made = [n.index for n in s.nodes(tier) if n.kind == "made"]
    return (max(made) + 1) if made else 10000


def _with_order(s: Struct, tier: str, order):
    return Struct(order={**s.order, tier: tuple(order)}, real=s.real, dom=s.dom, assoc=s.assoc, corr=s.corr)


def swap(s: Struct, a: NodeId, b: NodeId, tier: str = "seg") -> Struct:
    order = list(s.nodes(tier))
    i, j = order.index(a), order.index(b)
    if abs(i - j) != 1:
        raise ValueError("swap: the nodes are not adjacent")
    order[i], order[j] = order[j], order[i]
    return _with_order(s, tier, order)


def _corr_of(s: Struct, n: NodeId):
    return () if s.corr is None or n.kind == "made" and n not in (s.corr or {}) else tuple(s.correspondents(n))


def fuse(s: Struct, a: NodeId, b: NodeId, v: str, tier: str = "seg") -> Struct:
    if s.corr is None:
        raise ValueError("fuse: fusion needs the correspondence regime (corr is None)")
    order = list(s.nodes(tier))
    i, j = order.index(a), order.index(b)
    if j != i + 1:
        raise ValueError("fuse: the nodes are not adjacent in that order")
    n = NodeId(a.sort, "made", _fresh(s, tier))
    order = order[:i] + [n] + order[j + 1:]
    real = {k: x for k, x in s.real.items() if k not in (a, b)}; real[n] = v
    dom = {k: x for k, x in s.dom.items() if k not in (a, b)}; dom[n] = dict(s.dom.get(a, {}))
    rep = lambda x: n if x in (a, b) else x
    assoc = frozenset((rep(x), rep(y)) for x, y in s.assoc)
    corr = {k: x for k, x in s.corr.items() if k not in (a, b)}
    corr[n] = tuple(s.correspondents(a)) + tuple(s.correspondents(b))
    return Struct(order={**s.order, tier: tuple(order)}, real=real, dom=dom, assoc=assoc, corr=corr)


def split(s: Struct, a: NodeId, v1: str, v2: str, tier: str = "seg") -> Struct:
    if s.corr is None:
        raise ValueError("split: fission needs the correspondence regime (corr is None)")
    order = list(s.nodes(tier)); i = order.index(a)
    f = _fresh(s, tier)
    n1, n2 = NodeId(a.sort, "made", f), NodeId(a.sort, "made", f + 1)
    order = order[:i] + [n1, n2] + order[i + 1:]
    real = {k: x for k, x in s.real.items() if k != a}; real[n1] = v1; real[n2] = v2
    dom = {k: x for k, x in s.dom.items() if k != a}; dom[n1] = dict(s.dom.get(a, {})); dom[n2] = dict(s.dom.get(a, {}))
    rep = lambda x: n1 if x == a else x
    assoc = frozenset((rep(x), rep(y)) for x, y in s.assoc)
    corr = {k: x for k, x in s.corr.items() if k != a}
    corr[n1] = tuple(s.correspondents(a)); corr[n2] = tuple(s.correspondents(a))
    return Struct(order={**s.order, tier: tuple(order)}, real=real, dom=dom, assoc=assoc, corr=corr)


def copy(s: Struct, a: NodeId, at: int, v: str, tier: str = "seg") -> Struct:
    if s.corr is None:
        raise ValueError("copy: copying needs the correspondence regime (corr is None)")
    order = list(s.nodes(tier))
    n = NodeId(a.sort, "made", _fresh(s, tier))
    order = order[:at] + [n] + order[at:]
    real = dict(s.real); real[n] = v
    dom = dict(s.dom); dom[n] = dict(s.dom.get(a, {}))
    corr = dict(s.corr); corr[n] = tuple(s.correspondents(a))
    return Struct(order={**s.order, tier: tuple(order)}, real=real, dom=dom, assoc=s.assoc, corr=corr)


def canonical_corr(s: Struct, tier: str = "seg") -> tuple:
    seq, made = [], 0
    for n in s.nodes(tier):
        if n.kind == "made":
            seq.append(("made", made, s.real.get(n), tuple(sorted(s.dom.get(n, {}).items())), tuple(s.correspondents(n)) if s.corr is not None else ()))
            made += 1
        else:
            seq.append((n.kind, n.index, s.real.get(n), tuple(sorted(s.dom.get(n, {}).items()))))
    return tuple(seq)


def closure(ref: Struct, ops: Sequence[str], alphabet: Sequence[str], insert_alphabet: Sequence[str],
            max_made: int, tier: str = "seg", max_structures: int = 200000):
    if ABSENT in insert_alphabet:
        raise ValueError("the insertion alphabet must not contain ABSENT")
    key = canonical_corr if ref.corr is not None else canonical
    seen = {key(ref, tier): ref}
    frontier = [ref]
    while frontier:
        nxt = []
        for s in frontier:
            order = list(s.nodes(tier))
            made = sum(1 for n in order if n.kind == "made")
            succ = []
            if "set" in ops:
                for p in order:
                    if p.kind == "made":
                        continue
                    for v in alphabet:
                        if s.real.get(p) != v:
                            succ.append(s.with_real(p, v))
            if "insert" in ops and made < max_made:
                for i in range(len(order) + 1):
                    hosts = [order[j] for j in (i - 1, i) if 0 <= j < len(order)]
                    doms = []
                    for h in hosts:
                        d = dict(s.dom.get(h, {}))
                        if d not in doms:
                            doms.append(d)
                    if not doms:
                        doms = [{}]
                    for v in insert_alphabet:
                        for d in doms:
                            n = NodeId(order[0].sort if order else "Or", "made", _fresh(s, tier))
                            o2 = order[:i] + [n] + order[i:]
                            real = dict(s.real); real[n] = v
                            dom = dict(s.dom); dom[n] = dict(d)
                            corr = None if s.corr is None else {**s.corr, n: ()}
                            succ.append(Struct(order={**s.order, tier: tuple(o2)}, real=real, dom=dom, assoc=s.assoc, corr=corr))
            if "swap" in ops:
                for i in range(len(order) - 1):
                    succ.append(swap(s, order[i], order[i + 1], tier))
            if "fuse" in ops and s.corr is not None and made < max_made:
                for i in range(len(order) - 1):
                    for v in insert_alphabet:
                        succ.append(fuse(s, order[i], order[i + 1], v, tier))
            if "split" in ops and s.corr is not None and made + 1 < max_made:
                for p in order:
                    for v1 in insert_alphabet:
                        for v2 in insert_alphabet:
                            succ.append(split(s, p, v1, v2, tier))
            if "copy" in ops and s.corr is not None and made < max_made:
                for p in order:
                    if p.kind == "made":
                        continue
                    for i in range(len(order) + 1):
                        for v in insert_alphabet:
                            succ.append(copy(s, p, i, v, tier))
            for t in succ:
                k = key(t, tier)
                if k not in seen:
                    seen[k] = t; nxt.append(t)
                    if len(seen) > max_structures:
                        raise RuntimeError("closure: the bound on enumerated structures was exceeded")
        frontier = nxt
    return list(seen.values())


def productive_ext(sigma: Sigma, ref: Struct, decls: Mapping[str, Decl], weights, lam,
                   ops: Sequence[str], alphabet: Sequence[str], insert_alphabet: Sequence[str],
                   dep_name: str = "DEP", tier: str = "seg", incumbent: str = "reference"):
    acts = activation(sigma, ref, decls)
    def sc(s):
        return score(coefficients(sigma, ref, s, decls, acts), weights, lam)
    delta = Fraction(weights.get(dep_name, 0))
    if delta <= 0 and any(o in ops for o in ("insert", "fuse", "split", "copy")):
        return None, None, {"status": "UNBOUNDED", "reason": f"the {dep_name} weight is 0, so the number of created nodes is not bounded"}
    if incumbent == "creation_free":
        free = [o for o in ops if o in ("set", "swap")]
        B = min(sc(s) for s in closure(ref, free, alphabet, insert_alphabet, 0, tier))
    else:
        B = sc(ref)
    kmax = int(B / delta) if delta > 0 else 0
    structs = closure(ref, ops, alphabet, insert_alphabet, kmax, tier)
    best, minima = None, []
    for s in structs:
        v = sc(s)
        if best is None or v < best:
            best, minima = v, [s]
        elif v == best:
            minima.append(s)
    cert = {"status": "CERTIFIED", "incumbent_bound": str(B), "incumbent": incumbent, "delta": str(delta), "max_created_nodes": kmax,
            "operations": list(ops), "structures_enumerated_up_to_renaming": len(structs),
            "argument": "every created node (inserted, fused, split, copied) charges at least delta and every other charge is nonnegative, so a candidate with more than floor(B/delta) created nodes scores above the reference's score B; swaps create nothing and the structures over a fixed node set are finitely many; the closure within the bound is enumerated exhaustively up to renaming"}
    return best, minima, cert
