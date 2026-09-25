from __future__ import annotations

from dataclasses import dataclass, field
from fractions import Fraction
from typing import Iterable, Mapping, Sequence

Num = Fraction | int


def _frac(x: Num) -> Fraction:
    return x if isinstance(x, Fraction) else Fraction(x)


@dataclass(frozen=True)
class LinForm:

    coeff: Mapping[str, Fraction] = field(default_factory=dict)
    const: Fraction = Fraction(0)

    @staticmethod
    def var(name: str) -> "LinForm":
        return LinForm({name: Fraction(1)}, Fraction(0))

    @staticmethod
    def num(c: Num) -> "LinForm":
        return LinForm({}, _frac(c))

    def __add__(self, other: "LinForm | Num") -> "LinForm":
        if not isinstance(other, LinForm):
            other = LinForm.num(other)
        out = dict(self.coeff)
        for k, v in other.coeff.items():
            nv = out.get(k, Fraction(0)) + v
            if nv:
                out[k] = nv
            else:
                out.pop(k, None)
        return LinForm(out, self.const + other.const)

    __radd__ = __add__

    def __neg__(self) -> "LinForm":
        return LinForm({k: -v for k, v in self.coeff.items()}, -self.const)

    def __sub__(self, other: "LinForm | Num") -> "LinForm":
        if not isinstance(other, LinForm):
            other = LinForm.num(other)
        return self + (-other)

    def __rsub__(self, other: "LinForm | Num") -> "LinForm":
        return (-self) + other

    def __mul__(self, k: Num) -> "LinForm":
        k = _frac(k)
        if k == 0:
            return LinForm({}, Fraction(0))
        return LinForm({a: b * k for a, b in self.coeff.items()}, self.const * k)

    __rmul__ = __mul__

    def variables(self) -> set[str]:
        return set(self.coeff)

    def evaluate(self, env: Mapping[str, Num]) -> Fraction:
        total = self.const
        for k, v in self.coeff.items():
            if k not in env:
                raise KeyError(f"unbound parameter {k!r}")
            total += v * _frac(env[k])
        return total

    def is_constant(self) -> bool:
        return not self.coeff

    def __str__(self) -> str:
        parts = []
        for k in sorted(self.coeff):
            parts.append(f"{self.coeff[k]}*{k}")
        if self.const or not parts:
            parts.append(str(self.const))
        return " + ".join(parts)


@dataclass(frozen=True)
class Ineq:

    form: LinForm
    strict: bool
    tag: str = ""

    def holds(self, env: Mapping[str, Num]) -> bool:
        v = self.form.evaluate(env)
        return v > 0 if self.strict else v >= 0

    def __str__(self) -> str:
        return f"{self.form} {'>' if self.strict else '>='} 0" + (f"   [{self.tag}]" if self.tag else "")


class Infeasible(Exception):

    def __init__(self, message: str, trace: Sequence[str]):
        super().__init__(message)
        self.trace = list(trace)


def _normalise(system: Iterable[Ineq]) -> list[Ineq]:
    out: list[Ineq] = []
    for r in system:
        if r.form.is_constant():
            ok = r.form.const > 0 if r.strict else r.form.const >= 0
            if not ok:
                raise Infeasible(f"constant contradiction: {r}", [str(r)])
            continue
        out.append(r)
    return out


def eliminate(system: Sequence[Ineq], order: Sequence[str]) -> list[Ineq]:
    cur = _normalise(system)
    for v in order:
        pos: list[Ineq] = []
        neg: list[Ineq] = []
        rest: list[Ineq] = []
        for r in cur:
            c = r.form.coeff.get(v, Fraction(0))
            if c > 0:
                pos.append(r)
            elif c < 0:
                neg.append(r)
            else:
                rest.append(r)
        combined: list[Ineq] = list(rest)
        for a in pos:
            ca = a.form.coeff[v]
            for b in neg:
                cb = -b.form.coeff[v]
                form = a.form * cb + b.form * ca
                combined.append(Ineq(form, a.strict or b.strict, f"FM({a.tag}|{b.tag})"))
        cur = _normalise(combined)
        cur = _dedupe(cur)
    return cur


def _dedupe(system: Sequence[Ineq]) -> list[Ineq]:
    seen: dict[tuple, Ineq] = {}
    for r in system:
        items = sorted(r.form.coeff.items())
        scale = None
        for _, c in items:
            if c:
                scale = abs(c)
                break
        if scale is None:
            scale = abs(r.form.const) or Fraction(1)
        key = (tuple((k, c / scale) for k, c in items), r.form.const / scale, r.strict)
        if key not in seen:
            seen[key] = r
    return list(seen.values())


def feasible_witness(
    system: Sequence[Ineq],
    variables: Sequence[str],
    *,
    grid: Sequence[Fraction] | None = None,
) -> dict[str, Fraction] | None:
    order = list(variables)
    projections: list[list[Ineq]] = [list(_normalise(system))]
    for v in reversed(order[1:]):
        projections.append(eliminate(projections[-1], [v]))
    projections.reverse()
    env: dict[str, Fraction] = {}
    for i, v in enumerate(order):
        rows = projections[i]
        lo: Fraction | None = None
        lo_strict = False
        hi: Fraction | None = None
        hi_strict = False
        for r in rows:
            c = r.form.coeff.get(v, Fraction(0))
            if c == 0:
                continue
            rest = LinForm({k: x for k, x in r.form.coeff.items() if k != v}, r.form.const)
            val = rest.evaluate(env)
            bound = -val / c
            if c > 0:
                if lo is None or bound > lo or (bound == lo and r.strict):
                    if lo is None or bound > lo:
                        lo, lo_strict = bound, r.strict
                    else:
                        lo_strict = lo_strict or r.strict
            else:
                if hi is None or bound < hi or (bound == hi and r.strict):
                    if hi is None or bound < hi:
                        hi, hi_strict = bound, r.strict
                    else:
                        hi_strict = hi_strict or r.strict
        pick = _pick_in_interval(lo, lo_strict, hi, hi_strict, grid)
        if pick is None:
            return None
        env[v] = pick
    return env


def _pick_in_interval(
    lo: Fraction | None,
    lo_strict: bool,
    hi: Fraction | None,
    hi_strict: bool,
    grid: Sequence[Fraction] | None,
) -> Fraction | None:
    if lo is not None and hi is not None:
        if lo > hi:
            return None
        if lo == hi:
            return None if (lo_strict or hi_strict) else lo
        if grid:
            for g in grid:
                if (g > lo if lo_strict else g >= lo) and (g < hi if hi_strict else g <= hi):
                    return g
        return (lo + hi) / 2
    if lo is not None:
        if grid:
            for g in grid:
                if g > lo if lo_strict else g >= lo:
                    return g
        return lo + 1 if lo_strict else lo
    if hi is not None:
        if grid:
            for g in reversed(list(grid)):
                if g < hi if hi_strict else g <= hi:
                    return g
        return hi - 1 if hi_strict else hi
    if grid:
        return grid[0]
    return Fraction(1)


def verify(system: Sequence[Ineq], env: Mapping[str, Num]) -> list[Ineq]:
    return [r for r in system if not r.holds(env)]
