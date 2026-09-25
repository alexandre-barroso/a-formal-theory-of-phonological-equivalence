from __future__ import annotations

from fractions import Fraction
from typing import Iterable, Sequence

from .indep_gua import (ALPHABET, MARKEDNESS, SCHEMATA, WEIGHTS, LAMBDA,
                        Product, ft, present, nuclear, quality, atr, high)

FAITH = tuple(k for k in range(len(SCHEMATA)) if k not in MARKEDNESS)


def eligible_origins(prod: Product) -> tuple[int, ...]:
    return tuple(q for q in range(prod.n)
                 if nuclear(prod.reference[q]) or prod.reference[q] in ("j", "w"))


def faith_cost_table(prod: Product, weights=WEIGHTS) -> dict[int, dict[str, Fraction]]:
    out: dict[int, dict[str, Fraction]] = {}
    wMax, wATR, wQual, wNuc, _, _, _, _, wInit = weights
    for q in range(prod.n):
        ref = prod.reference[q]
        init_ctx = nuclear(ref) and (q == 0 or prod.words[q - 1] != prod.words[q])
        row = {}
        for v in ALPHABET:
            c = Fraction(0)
            if not present(v):
                c += wMax
            if nuclear(v) and nuclear(ref) and atr(v) != atr(ref):
                c += wATR
            if present(v) and quality(v) is not None and quality(ref) is not None \
               and quality(v) != quality(ref):
                c += wQual
            if present(v) and nuclear(v) != nuclear(ref):
                c += wNuc
            if init_ctx and present(v) and quality(v) is not None:
                good = (quality(v) == quality(ref)
                        and ((not nuclear(v)) or atr(v) == atr(ref)))
                if not good:
                    c += wInit
            row[v] = c
        out[q] = row
    return out


class ProductiveSearch:

    def __init__(self, prod: Product, weights=WEIGHTS, lam=LAMBDA,
                 eligible: Sequence[int] | None = None,
                 activation_key: str = "M"):
        self.prod = prod
        self.weights = tuple(Fraction(w) for w in weights)
        self.lam = Fraction(lam)
        self.eligible = tuple(eligible) if eligible is not None else eligible_origins(prod)
        self.faith = faith_cost_table(prod, weights)
        self.activation_key = activation_key
        C0, D0, G0 = prod.readers(prod.reference)
        if activation_key == "M":
            self.a = [[bool(C0[k][q] and D0[k][q] and not G0[k][q])
                       for q in range(prod.n)] for k in range(len(SCHEMATA))]
        elif activation_key == "C":
            self.a = [[bool(C0[k][q]) for q in range(prod.n)]
                      for k in range(len(SCHEMATA))]
        elif activation_key == "schema":
            per = [[bool(C0[k][q] and D0[k][q] and not G0[k][q])
                    for q in range(prod.n)] for k in range(len(SCHEMATA))]
            self.a = [[any(per[k])] * prod.n for k in range(len(SCHEMATA))]
        elif activation_key == "none":
            self.a = [[False] * prod.n for _ in range(len(SCHEMATA))]
        else:
            raise ValueError(activation_key)
        self._order = sorted(self.eligible,
                             key=lambda q: -min(v for k, v in self.faith[q].items()
                                                if k != prod.reference[q]))

    def score_state(self, s) -> Fraction:
        cs = self.prod.coefficients(s, self.a)
        return sum(w * (Fraction(o) + self.lam * Fraction(nn))
                   for w, (o, nn) in zip(self.weights, cs))

    def markedness_only(self, s) -> Fraction:
        cs = self.prod.coefficients(s, self.a)
        return sum(self.weights[k] * (Fraction(cs[k][0]) + self.lam * Fraction(cs[k][1]))
                   for k in MARKEDNESS)

    def enumerate_upto(self, bound: Fraction, collect: bool = True):
        prod = self.prod
        order = self._order
        base = list(prod.reference)
        found = []
        stats = {"visited": 0, "pruned_subtrees": 0, "pruned_leaves_lower_bound": 0,
                 "scored": 0}

        def rec(i: int, prefix_cost: Fraction, state: list[str]):
            stats["visited"] += 1
            if i == len(order):
                stats["scored"] += 1
                sc = self.score_state(tuple(state))
                if sc <= bound and collect:
                    found.append((tuple(state), sc))
                elif sc <= bound:
                    found.append((None, sc))
                return
            q = order[i]
            row = self.faith[q]
            for v in ALPHABET:
                c = prefix_cost + row[v]
                if c > bound:
                    stats["pruned_subtrees"] += 1
                    stats["pruned_leaves_lower_bound"] += len(ALPHABET) ** (len(order) - i - 1)
                    continue
                state[q] = v
                rec(i + 1, c, state)
            state[q] = prod.reference[q]

        rec(0, Fraction(0), base)
        stats["search_space"] = len(ALPHABET) ** len(order)
        return found, stats

    def minimise(self):
        incumbent = self.score_state(tuple(self.prod.reference))
        state = list(self.prod.reference)
        improved = True
        while improved:
            improved = False
            for q in self.eligible:
                cur = state[q]
                best_v, best_s = cur, self.score_state(tuple(state))
                for v in ALPHABET:
                    if v == cur:
                        continue
                    state[q] = v
                    s = self.score_state(tuple(state))
                    if s < best_s:
                        best_v, best_s = v, s
                state[q] = best_v
                if best_v != cur:
                    improved = True
            incumbent = min(incumbent, self.score_state(tuple(state)))
        found, stats = self.enumerate_upto(incumbent)
        best = min(s for _, s in found)
        minima = [st for st, s in found if s == best]
        if best < incumbent:
            found, stats = self.enumerate_upto(best)
            minima = [st for st, s in found if s == best]
        cert = {
            "product": self.prod.id,
            "eligible_origins": list(self.eligible),
            "search_space": stats["search_space"],
            "nodes_visited": stats["visited"],
            "leaves_scored": stats["scored"],
            "leaves_excluded_by_lower_bound": stats["pruned_leaves_lower_bound"],
            "bound": str(best),
            "coverage_identity": stats["scored"] + stats["pruned_leaves_lower_bound"] == stats["search_space"],
            "argument": ("faithfulness is a sum of per-origin terms and markedness is "
                         "nonnegative, so a prefix whose faithfulness already exceeds the "
                         "bound cannot be completed to a candidate at or below it"),
        }
        return best, minima, found, cert
