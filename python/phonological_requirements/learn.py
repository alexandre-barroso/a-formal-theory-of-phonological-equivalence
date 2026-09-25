from __future__ import annotations

import itertools
from fractions import Fraction
from typing import Iterable, Mapping, Sequence

from .core import Decl, NodeId, Sigma, Struct, read
from .evaluate import activation, coefficients, loci, score


def outputs(sigma, ref, cands, decls, weights, lam, observe):
    acts = activation(sigma, ref, decls)
    best, mins = None, []
    for key, c in cands:
        v = score(coefficients(sigma, ref, c, decls, acts), weights, lam)
        if best is None or v < best:
            best, mins = v, [c]
        elif v == best:
            mins.append(c)
    return frozenset(observe(m) for m in mins)


def separating_inputs(sigma, hypotheses, inputs, weights, lam):
    table = {}
    for iid, ref, cands, observe in inputs:
        for hname, decls in hypotheses.items():
            table[(iid, hname)] = outputs(sigma, ref, cands, decls, weights, lam, observe)
    sep = {}
    names = list(hypotheses)
    for i, a in enumerate(names):
        for b in names[i + 1:]:
            sep[(a, b)] = [iid for iid, *_ in inputs
                           if table[(iid, a)] != table[(iid, b)]]
    return table, sep


def minimal_characteristic_sample(sep, inputs):
    ids = [iid for iid, *_ in inputs]
    pairs = [p for p, v in sep.items() if v]
    unseparated = [p for p, v in sep.items() if not v]
    for k in range(1, len(ids) + 1):
        for combo in itertools.combinations(ids, k):
            if all(any(i in sep[p] for i in combo) for p in pairs):
                return list(combo), unseparated
    return None, unseparated
