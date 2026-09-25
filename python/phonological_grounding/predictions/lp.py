from __future__ import annotations

from fractions import Fraction
from typing import Sequence

from .exact import Ineq


class LPResult:
    def __init__(self, status: str, witness: dict[str, Fraction] | None = None,
                 detail: str = ""):
        self.status = status
        self.witness = witness
        self.detail = detail


def _simplex_phase1(A: list[list[Fraction]], b: list[Fraction], n: int,
                    max_iter: int = 20000) -> tuple[str, list[Fraction] | None]:
    m = len(A)
    total = n + 2 * m
    T: list[list[Fraction]] = []
    for i in range(m):
        row = [Fraction(0)] * (total + 1)
        for j in range(n):
            row[j] = A[i][j]
        row[n + i] = Fraction(-1)
        row[n + m + i] = Fraction(1)
        row[total] = b[i]
        T.append(row)
    obj = [Fraction(0)] * (total + 1)
    for i in range(m):
        for j in range(total + 1):
            obj[j] -= T[i][j]
    for i in range(m):
        obj[n + m + i] = Fraction(0)
    basis = [n + m + i for i in range(m)]
    for _ in range(max_iter):
        enter = -1
        for j in range(total):
            if obj[j] < 0:
                enter = j
                break
        if enter < 0:
            break
        leave = -1
        best: Fraction | None = None
        for i in range(m):
            if T[i][enter] > 0:
                ratio = T[i][total] / T[i][enter]
                if best is None or ratio < best or (ratio == best and basis[i] < basis[leave]):
                    best, leave = ratio, i
        if leave < 0:
            return "UNBOUNDED_ITER", None
        piv = T[leave][enter]
        T[leave] = [v / piv for v in T[leave]]
        for i in range(m):
            if i != leave and T[i][enter] != 0:
                f = T[i][enter]
                T[i] = [a - f * c for a, c in zip(T[i], T[leave])]
        if obj[enter] != 0:
            f = obj[enter]
            obj = [a - f * c for a, c in zip(obj, T[leave])]
        basis[leave] = enter
    else:
        return "UNBOUNDED_ITER", None
    if -obj[total] > 0:
        return "INFEASIBLE", None
    x = [Fraction(0)] * n
    for i, bcol in enumerate(basis):
        if bcol < n:
            x[bcol] = T[i][total]
    return "FEASIBLE", x


def feasible(system: Sequence[Ineq], variables: Sequence[str],
             margin: Fraction = Fraction(1)) -> LPResult:
    vs = list(variables)
    A: list[list[Fraction]] = []
    b: list[Fraction] = []
    for r in system:
        if r.form.const != 0:
            raise ValueError("feasible() expects a homogeneous system")
        row = [r.form.coeff.get(v, Fraction(0)) for v in vs]
        if all(c == 0 for c in row):
            if r.strict:
                return LPResult("INFEASIBLE", None, f"zero row required to be positive: {r.tag}")
            continue
        A.append(row)
        b.append(margin if r.strict else Fraction(0))
    status, x = _simplex_phase1(A, b, len(vs))
    if status != "FEASIBLE":
        return LPResult("INFEASIBLE" if status == "INFEASIBLE" else "UNBOUNDED_ITER",
                        None, status)
    return LPResult("FEASIBLE", {v: xi for v, xi in zip(vs, x)})
