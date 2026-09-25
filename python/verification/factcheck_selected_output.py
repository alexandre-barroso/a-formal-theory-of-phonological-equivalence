from __future__ import annotations

import sys
from fractions import Fraction as Q
from itertools import combinations, product

RESULTS: list[tuple[str, bool, str]] = []


def check(label: str, ok: bool, detail: str = "") -> None:
    RESULTS.append((label, bool(ok), detail))


F = [[20, -17], [3, 17]]
M = [[0, -1], [-1, 0]]
x, w = (1, 0), (0, 1)
OUTPUTS = {"0": (0, 0), "y": (1, 0), "u": (0, 1), "z": (1, 1)}


def bilinear(u, A, v):
    return sum(u[i] * A[i][j] * v[j] for i in range(2) for j in range(2))


def harmony(inp, out):
    return bilinear(inp, F, out) + bilinear(out, M, out)


row_x = [harmony(x, OUTPUTS[k]) for k in ("0", "y", "u", "z")]
row_w = [harmony(w, OUTPUTS[k]) for k in ("0", "y", "u", "z")]
check("eq:apph-gd-score-rows: H_G(x,.) = (0,20,-17,1)", row_x == [0, 20, -17, 1], str(row_x))
check("eq:apph-gd-score-rows: H_G(w,.) = (0,3,17,18)", row_w == [0, 3, 17, 18], str(row_w))
check("selection: y is the unique intact winner for x", row_x.index(max(row_x)) == 1 and row_x.count(max(row_x)) == 1)
check("selection: z is the unique intact winner for w", row_w.index(max(row_w)) == 3 and row_w.count(max(row_w)) == 1)

check("selection: xFy = 20 = wFz", bilinear(x, F, OUTPUTS["y"]) == 20 == bilinear(w, F, OUTPUTS["z"]))
check("selection: xFz = 3 = wFy", bilinear(x, F, OUTPUTS["z"]) == 3 == bilinear(w, F, OUTPUTS["y"]))
check("selection: yMy = 0 and zMz = -2",
      bilinear(OUTPUTS["y"], M, OUTPUTS["y"]) == 0 and bilinear(OUTPUTS["z"], M, OUTPUTS["z"]) == -2)
check("selection: the named intact margins are 19 and 15",
      row_x[1] - row_x[3] == 19 and row_w[3] - row_w[1] == 15,
      f"{row_x[1] - row_x[3]}, {row_w[3] - row_w[1]}")
check("selection: representational-difference normal squares are 5 and 5",
      1 ** 2 + 2 ** 2 == 5 and (-1) ** 2 + (-2) ** 2 == 5)

def first_region(p, strict=True):
    A, B, C, D, E = p
    rel = (lambda a, b: a < b) if strict else (lambda a, b: a <= b)
    return rel(0, 1 + A + B + 2 * E) and rel(19, B + 2 * E) and rel(0, 18 + A + 2 * E)


def second_region(p, strict=True):
    A, B, C, D, E = p
    rel = (lambda a, b: a < b) if strict else (lambda a, b: a <= b)
    return rel(-3, C) and rel(14, C - D) and rel(15, -D - 2 * E)


v_x = (Q(0), Q(19, 5), Q(0), Q(0), Q(38, 5))
v_w = (Q(0), Q(0), Q(55, 9), Q(-71, 9), Q(-32, 9))


def sq(p):
    return sum(c * c for c in p)


def sqF(p):
    A, B, C, D, E = p
    return A * A + B * B + C * C + D * D + 2 * E * E


check("eq:apph-gd-euclidean-first: ||v_x||^2 = 361/5", sq(v_x) == Q(361, 5), str(sq(v_x)))
check("eq:apph-gd-euclidean-second: ||v_w||^2 = 1010/9", sq(v_w) == Q(1010, 9), str(sq(v_w)))
check("selection: v_x lies in the closed first region with B + 2E = 19 active",
      first_region(v_x, strict=False) and v_x[1] + 2 * v_x[4] == 19)
check("selection: the other two first-region inequalities are strict at v_x",
      0 < 1 + v_x[0] + v_x[1] + 2 * v_x[4] and 0 < 18 + v_x[0] + 2 * v_x[4])
check("selection: v_w activates C - D = 14 and -D - 2E = 15, with C > -3 strict",
      v_w[2] - v_w[3] == 14 and -v_w[3] - 2 * v_w[4] == 15 and v_w[2] > -3)

lam1, lam2 = Q(55, 9), Q(16, 9)
check("selection: the multiplier system (2,1;1,5)(l1,l2) = (14,15) gives 55/9 and 16/9",
      2 * lam1 + lam2 == 14 and lam1 + 5 * lam2 == 15 and lam1 > 0 and lam2 > 0)
a1, a2 = (0, 0, 1, -1, 0), (0, 0, 0, -1, -2)
combo = tuple(lam1 * a1[i] + lam2 * a2[i] for i in range(5))
check("selection: v_w = 55/9 * a1 + 16/9 * a2", combo == v_w, str(combo))
check("selection: ||v_w||^2 = 14 l1 + 15 l2 = 1010/9", 14 * lam1 + 15 * lam2 == Q(1010, 9))

FIRST = [((1, 1, 0, 0, 2), -1), ((0, 1, 0, 0, 2), 19), ((1, 0, 0, 0, 2), -18)]
SECOND = [((0, 0, 1, 0, 0), -3), ((0, 0, 1, -1, 0), 14), ((0, 0, 0, -1, -2), 15)]
EUCLID = [[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]]
FROB = [[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 2]]


def perturbed_harmony(inp, out, delta):
    A, B, C, D, E = delta
    fp = [[F[0][0] + A, F[0][1] + B], [F[1][0] + C, F[1][1] + D]]
    mp = [[0, M[0][1] + E], [M[1][0] + E, 0]]
    return bilinear(inp, fp, out) + bilinear(out, mp, out)


for inp, target, rivals, rows in [
    (x, "z", ["0", "y", "u"], FIRST),
    (w, "y", ["0", "u", "z"], SECOND),
]:
    for rival, (normal, threshold) in zip(rivals, rows, strict=True):
        intercept = harmony(inp, OUTPUTS[target]) - harmony(inp, OUTPUTS[rival])
        derived = []
        for coordinate in range(5):
            delta = [int(i == coordinate) for i in range(5)]
            margin = perturbed_harmony(inp, OUTPUTS[target], delta) - perturbed_harmony(inp, OUTPUTS[rival], delta)
            derived.append(margin - intercept)
        check(f"selection: source affine comparison {inp}: {target}>{rival}",
              tuple(derived) == normal and -intercept == threshold)


def solve(mat, rhs):
    n = len(mat)
    aug = [[Q(v) for v in row] + [Q(rhs[i])] for i, row in enumerate(mat)]
    for col in range(n):
        piv = next((r for r in range(col, n) if aug[r][col] != 0), None)
        if piv is None:
            return None
        aug[col], aug[piv] = aug[piv], aug[col]
        inv = Q(1) / aug[col][col]
        aug[col] = [v * inv for v in aug[col]]
        for r in range(n):
            if r != col and aug[r][col] != 0:
                f = aug[r][col]
                aug[r] = [a - f * b for a, b in zip(aug[r], aug[col])]
    return [aug[r][n] for r in range(n)]


def projection(constraints, metric):
    ginv = [[Q(1, metric[i][i]) if i == j else Q(0) for j in range(5)] for i in range(5)]
    best = None
    for size in range(len(constraints) + 1):
        for active in combinations(range(len(constraints)), size):
            if not active:
                point = tuple(Q(0) for _ in range(5))
                if all(sum(Q(a[i]) * point[i] for i in range(5)) >= b for a, b in constraints):
                    cand = (sum(metric[i][i] * point[i] * point[i] for i in range(5)), point)
                    if best is None or cand[0] < best[0]:
                        best = cand
                continue
            rows = [constraints[i][0] for i in active]
            gram = [[sum(Q(rows[r][i]) * ginv[i][i] * Q(rows[c][i]) for i in range(5))
                     for c in range(len(rows))] for r in range(len(rows))]
            lam = solve(gram, [constraints[i][1] for i in active])
            if lam is None or any(v < 0 for v in lam):
                continue
            point = tuple(sum(lam[r] * ginv[i][i] * Q(rows[r][i]) for r in range(len(rows)))
                          for i in range(5))
            if not all(sum(Q(a[i]) * point[i] for i in range(5)) >= b for a, b in constraints):
                continue
            value = sum(metric[i][i] * point[i] * point[i] for i in range(5))
            if best is None or value < best[0]:
                best = (value, point)
    return best


pf = projection(FIRST, EUCLID)
ps = projection(SECOND, EUCLID)
check("selection: the exact Euclidean projection onto the closed first region is v_x with squared norm 361/5",
      pf is not None and pf[0] == Q(361, 5) and pf[1] == v_x, str(pf))
check("selection: the exact Euclidean projection onto the closed second region is v_w with squared norm 1010/9",
      ps is not None and ps[0] == Q(1010, 9) and ps[1] == v_w, str(ps))
check("selection: Cauchy-Schwarz gives (B+2E)^2 <= 5(B^2+E^2), the appendix's own lower bound",
      all((B + 2 * E) ** 2 <= 5 * (B * B + E * E)
          for B in (Q(k, 3) for k in range(-30, 31))
          for E in (Q(k, 3) for k in range(-30, 31))))

check("eq:apph-gd-euclidean-reversal: 361/5 < 1010/9 with difference 1801/45",
      Q(361, 5) < Q(1010, 9) and Q(1010, 9) - Q(361, 5) == Q(1801, 45))

v_xF = (Q(0), Q(19, 3), Q(0), Q(0), Q(19, 3))
v_wF = (Q(0), Q(0), Q(27, 5), Q(-43, 5), Q(-16, 5))
check("selection: ||v_x^F||_F^2 = 361/3", sqF(v_xF) == Q(361, 3), str(sqF(v_xF)))
check("selection: ||v_w^F||_F^2 = 618/5", sqF(v_wF) == Q(618, 5), str(sqF(v_wF)))
check("selection: v_x^F lies on B + 2E = 19", v_xF[1] + 2 * v_xF[4] == 19)
check("selection: v_w^F activates both second-region faces and keeps C > -3 strict",
      v_wF[2] - v_wF[3] == 14 and -v_wF[3] - 2 * v_wF[4] == 15 and v_wF[2] > -3)
lam1F, lam2F = Q(27, 5), Q(16, 5)
check("selection: the Frobenius Gram system (2,1;1,3)(l1,l2) = (14,15) gives 27/5 and 16/5",
      2 * lam1F + lam2F == 14 and lam1F + 3 * lam2F == 15 and lam1F > 0 and lam2F > 0)
check("eq:apph-gd-frobenius-reversal: 361/3 < 618/5 with difference 49/15",
      Q(361, 3) < Q(618, 5) and Q(618, 5) - Q(361, 3) == Q(49, 15))
pfF = projection(FIRST, FROB)
psF = projection(SECOND, FROB)
check("selection: the exact Frobenius projection onto the first region is v_x^F with squared norm 361/3",
      pfF is not None and pfF[0] == Q(361, 3) and pfF[1] == v_xF, str(pfF))
check("selection: the exact Frobenius projection onto the second region is v_w^F with squared norm 618/5",
      psF is not None and psF[0] == Q(618, 5) and psF[1] == v_wF, str(psF))

n_x = (Q(0), Q(4), Q(0), Q(0), Q(8))
check("selection: n_x = (0,4,0,0,8) has squared norm 80 and lies strictly in the first event",
      sq(n_x) == 80 and first_region(n_x))
check("selection: 361/5 < 80 < 1010/9", Q(361, 5) < 80 < Q(1010, 9))
check("selection: a coordinate neighbourhood of radius 1/4 around n_x stays in the first event",
      all(first_region(tuple(n_x[i] + d[i] for i in range(5)))
          for d in product([Q(-1, 4), Q(0), Q(1, 4)], repeat=5)))
check("selection: the second event is empty on the shell of squared radius 80, since its closure's minimum is 1010/9 > 80",
      Q(1010, 9) > 80)

check("tab:app-gd-two-orders: pairwise 19 > 15 but onset 361/5 < 1010/9 and 361/3 < 618/5",
      19 > 15 and Q(361, 5) < Q(1010, 9) and Q(361, 3) < Q(618, 5))


def main() -> int:
    failed = [r for r in RESULTS if not r[1]]
    for label, ok, detail in RESULTS:
        if not ok:
            print(f"FAIL  {label}   [{detail}]")
    print(f"\n{len(RESULTS) - len(failed)}/{len(RESULTS)} selected-output claims verified")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
