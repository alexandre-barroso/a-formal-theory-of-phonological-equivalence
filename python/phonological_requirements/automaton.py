from __future__ import annotations
from phonological_requirements import paths

from fractions import Fraction as F
from functools import lru_cache

from .core import ABSENT, NodeId, Struct, read
from .evaluate import activation, tier_of
from .frag_seq import surface


class Compiled:
    def __init__(self, sigma, decls, weights, lam, options):
        self.sigma, self.decls, self.W, self.lam, self.options = sigma, decls, weights, lam, options
        self._memo = {}

    def _window_struct(self, refwin, real, left, right):
        nodes, real_map, i = [], {}, 0
        def add(sym, r):
            nonlocal i
            n = NodeId("Or", "lex", i); i += 1
            nodes.append(n); real_map[n] = r
            return n
        for s in reversed(left):
            add(s, s)
        for k in (0, 1):
            if refwin[k] is not None:
                add(refwin[k], ABSENT)
        t = add(refwin[2], real)
        for k in (3, 4):
            if refwin[k] is not None:
                add(refwin[k], ABSENT)
        for s in right:
            add(s, s)
        ref_syms = [ABSENT] * len(left) + [refwin[k] for k in (0, 1) if refwin[k] is not None] + [refwin[2]] \
            + [refwin[k] for k in (3, 4) if refwin[k] is not None] + [ABSENT] * len(right)
        ref = Struct(order={"seg": tuple(nodes)}, real={n: s for n, s in zip(nodes, ref_syms)}, dom={n: {"word": 0} for n in nodes})
        st = Struct(order={"seg": tuple(nodes)}, real=real_map, dom=ref.dom)
        return ref, st, t

    def contrib(self, refwin, real, left, right):
        key = (refwin, real, left, right)
        if key in self._memo:
            return self._memo[key]
        ref, st, t = self._window_struct(refwin, real, left, right)
        acts = activation(self.sigma, ref, self.decls)
        total = F(0)
        for name, d in self.decls.items():
            r = read(self.sigma, ref, st, d, t, tier_of(self.sigma, d, "seg"))
            p, c = r.pressure, r.context
            a = acts[name].get(t, False)
            if d.kind == "faithfulness":
                old, new = int(p and c), 0
            else:
                old, new = int(p and a), int(p and (not a) and c)
            total += F(self.W[name]) * (F(old) + self.lam * F(new))
        self._memo[key] = total
        return total

    def best(self, syms, layer_mins=False, paths=True):
        n = len(syms)
        mins = []
        def refwin(i):
            return tuple(syms[j] if 0 <= j < n else None for j in range(i - 2, i + 3))
        start = (None, None)
        paths_on = paths
        layer = {start: (F(0), [()])}
        for i in range(n):
            nxt = {}
            for (rec2, rec1), (cost, paths) in layer.items():
                for r in self.options.get(syms[i], [syms[i]]):
                    c = cost
                    if r == ABSENT:
                        c += self.contrib(refwin(i), ABSENT, (), ())
                        state = (rec2, rec1)
                    else:
                        if rec2 is not None:
                            c += self.contrib(rec2[0], rec2[1], rec2[2], (rec1[1], r))
                        left = tuple(x for x in ((rec1[1] if rec1 else None), (rec2[1] if rec2 else None)) if x is not None)
                        state = (rec1, (refwin(i), r, left))
                    new_paths = [p + (r,) for p in paths] if paths_on else [()]
                    if state not in nxt or c < nxt[state][0]:
                        nxt[state] = (c, new_paths)
                    elif c == nxt[state][0] and paths_on:
                        nxt[state][1].extend(new_paths)
            layer = nxt
            mins.append(min((v[0] for v in layer.values()), default=None))
        best, out = None, []
        for (rec2, rec1), (cost, paths) in layer.items():
            c = cost
            if rec2 is not None:
                c += self.contrib(rec2[0], rec2[1], rec2[2], (rec1[1],))
            if rec1 is not None:
                c += self.contrib(rec1[0], rec1[1], rec1[2], ())
            if best is None or c < best:
                best, out = c, list(paths)
            elif c == best:
                out.extend(paths)
        result = (best, sorted(set(out)) if paths_on else None, len(layer))
        return result + ((mins,) if layer_mins else ())

    def replay(self, syms, seq):
        n = len(syms)
        def refwin(i):
            return tuple(syms[j] if 0 <= j < n else None for j in range(i - 2, i + 3))
        rec2 = rec1 = None; c = F(0); out = []
        for i, r in enumerate(seq):
            if r == ABSENT:
                c += self.contrib(refwin(i), ABSENT, (), ())
            else:
                if rec2 is not None:
                    c += self.contrib(rec2[0], rec2[1], rec2[2], (rec1[1], r))
                left = tuple(x for x in ((rec1[1] if rec1 else None), (rec2[1] if rec2 else None)) if x is not None)
                rec2, rec1 = rec1, (refwin(i), r, left)
            out.append(c)
        return out

    def n_states_bound(self):
        A = sorted({s for opts in self.options.values() for s in opts} | set(self.options) | set(self.sigma.features))
        per = (len(A) + 1) ** 5 * (len(A) + 1) * (len(A) + 1) ** 2
        return per * per
