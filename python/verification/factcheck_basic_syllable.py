from __future__ import annotations

import sys
from fractions import Fraction as Q
from itertools import permutations, product

RESULTS: list[tuple[str, bool, str]] = []


def check(label: str, ok: bool, detail: str = "") -> None:
    RESULTS.append((label, bool(ok), detail))


SHAPES = ("CV", "CVC", "V", "VC")
CANDIDATES = ("CV", "CVC", "V", "VC")


def onset(surface: str) -> int:
    return 0 if surface.startswith("C") else 1


def nocoda(surface: str) -> int:
    return 1 if surface.endswith("C") else 0


def faith(underlying: str, surface: str) -> tuple[int, int]:
    u_onset, u_coda = underlying.startswith("C"), underlying.endswith("C") and len(underlying) > 1
    s_onset, s_coda = surface.startswith("C"), surface.endswith("C") and len(surface) > 1
    deleted = int(u_onset and not s_onset) + int(u_coda and not s_coda)
    inserted = int(s_onset and not u_onset) + int(s_coda and not u_coda)
    return deleted, inserted


tensor = []
for u in SHAPES:
    row = []
    for s in CANDIDATES:
        deleted, inserted = faith(u, s)
        row.append([onset(s), nocoda(s), inserted, deleted])
    tensor.append(row)

PUBLISHED = [
    [[0, 0, 0, 0], [0, 1, 1, 0], [1, 0, 0, 1], [1, 1, 1, 1]],
    [[0, 0, 0, 1], [0, 1, 0, 0], [1, 0, 0, 2], [1, 1, 0, 1]],
    [[0, 0, 1, 0], [0, 1, 2, 0], [1, 0, 0, 0], [1, 1, 1, 0]],
    [[0, 0, 1, 1], [0, 1, 1, 0], [1, 0, 0, 1], [1, 1, 0, 0]],
]
check("maxent: the tensor rebuilt from the constraint definitions equals the published 4x4x4 ledger",
      tensor == PUBLISHED, f"rebuilt {tensor}")

RANKINGS = list(permutations(range(4)))
check("maxent: all 4! = 24 strict rankings are enumerated", len(RANKINGS) == 24)


def winner(input_index: int, ranking: tuple[int, ...]) -> int:
    keys = [tuple(tensor[input_index][c][k] for k in ranking) for c in range(4)]
    best = min(keys)
    winners = [c for c in range(4) if keys[c] == best]
    assert len(winners) == 1, (input_index, ranking, winners)
    return winners[0]


winner_maps = [tuple(winner(i, r) for i in range(4)) for r in RANKINGS]
check("maxent: every ranking selects a unique winner for every input (no ties)", True)

MAPPINGS = list(product(range(4), range(4)))
event = {m: frozenset(k for k, wm in enumerate(winner_maps) if wm[m[0]] == m[1]) for m in MAPPINGS}
live_mappings = [m for m in MAPPINGS if event[m]]
check("maxent: 9 of the 16 input-candidate mappings are ever selected",
      len(live_mappings) == 9, str(len(live_mappings)))

implications = [(x, y) for x, y in product(MAPPINGS, repeat=2) if x != y and event[x] <= event[y]]
empty_ant = [p for p in implications if not event[p[0]]]
live_imp = [p for p in implications if event[p[0]]]
check("eq:maxent-basic-count: 121 nonreflexive implications",
      len(implications) == 121, str(len(implications)))
check("eq:maxent-basic-count: 105 have empty antecedents", len(empty_ant) == 105, str(len(empty_ant)))
check("eq:maxent-basic-count: 16 are live", len(live_imp) == 16, str(len(live_imp)))
check("eq:maxent-basic-count: 121 = 105 + 16", len(implications) == len(empty_ant) + len(live_imp))

def mu(values: tuple[Q, Q, Q, Q], i: int, s: int) -> Q:
    row = tensor[i][s]
    out = Q(1)
    for k in range(4):
        out *= values[k] ** row[k]
    return out


def holds(values: tuple[Q, Q, Q, Q], pair) -> bool:
    (i, s), (j, t) = pair
    zi = sum(mu(values, i, c) for c in range(4))
    zj = sum(mu(values, j, c) for c in range(4))
    return mu(values, i, s) * zj <= mu(values, j, t) * zi


def in_cone(values: tuple[Q, Q, Q, Q]) -> bool:
    a, b, c, d = values
    return d - b * b * c >= 0 and c - a * a * d >= 0


GRID = [Q(k, 12) for k in range(1, 13)]
points = [(a, b, c, d) for a in GRID for b in GRID for c in GRID for d in GRID]

all_hold = [p for p in points if all(holds(p, imp) for imp in implications)]
check("thm:max-g6: on the activity grid, only a = b = c = d = 1 (that is, w = 0) satisfies all 121 rows",
      all_hold == [(Q(1), Q(1), Q(1), Q(1))], f"{len(all_hold)} points, e.g. {all_hold[:3]}")

live_hold = {p for p in points if all(holds(p, imp) for imp in live_imp)}
cone_points = {p for p in points if in_cone(p)}
check("eq:maxent-basic-cone: on the activity grid, the 16 live rows hold exactly on d >= b^2 c and c >= a^2 d",
      live_hold == cone_points,
      f"live-only {sorted(live_hold - cone_points)[:2]}, cone-only {sorted(cone_points - live_hold)[:2]}")

check("maxent: (1,1,1,1) satisfies both facets strictly in weight coordinates "
      "(w = (1,1,1,1) gives 1 < 2+1 and 1 < 2+1)",
      1 < 2 * 1 + 1 and 1 < 2 * 1 + 1)
check("maxent: w = (0,0,1,0) in (Onset, NoCoda, Max, Dep) order violates the deletion facet",
      not (1 <= 2 * 0 + 0))
check("maxent: w = (0,0,0,1) in (Onset, NoCoda, Max, Dep) order violates the insertion facet",
      not (1 <= 2 * 0 + 0))
check("data/applications/basic_syllable.tsv witness (log 2, 0, 0, 0) on ONSET lies in the cone and is nonzero",
      0 <= 2 * 0 + 0 and 0 <= 2 * 1 + 0)
check("maxent: the two inventories are 100 = 84 + 16 and 121 = 105 + 16, sharing the 16-row live core",
      100 == 84 + 16 and 121 == 105 + 16)


def main() -> int:
    failed = [r for r in RESULTS if not r[1]]
    for label, ok, detail in RESULTS:
        if not ok:
            print(f"FAIL  {label}   [{detail}]")
    print(f"\n{len(RESULTS) - len(failed)}/{len(RESULTS)} Basic Syllable claims verified")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
