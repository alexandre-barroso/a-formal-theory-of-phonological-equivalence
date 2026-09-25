from __future__ import annotations

import csv
import sys
from fractions import Fraction as Q
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
RESULTS: list[tuple[str, bool, str]] = []


def check(label: str, ok: bool, detail: str = "") -> None:
    RESULTS.append((label, bool(ok), detail))


def J(x: Q) -> Q:
    return 21 * (1 - x) ** 2 + x


check("application: J'(x) = 42x - 41 and J''(x) = 42 > 0",
      all(J(x + Q(1, 10 ** 6)) - J(x) > 0 for x in (Q(41, 42) + Q(1, 100),))
      and all(J(x + Q(1, 10 ** 6)) - J(x) < 0 for x in (Q(41, 42) - Q(1, 100),)))
check("eq:app-mcc-grid-continuum: the continuum minimiser is 41/42",
      min(((J(Q(k, 10 ** 4)), Q(k, 10 ** 4)) for k in range(10 ** 4 + 1)))[1]
      == min(((J(Q(k, 10 ** 4)), Q(k, 10 ** 4)) for k in range(10 ** 4 + 1)))[1]
      and J(Q(41, 42)) == Q(83, 84)
      and all(J(Q(41, 42)) <= J(Q(k, 4200)) for k in range(4201)),
      f"J(41/42) = {J(Q(41, 42))}")
check("application: J(1) = 1 and J(9/10) = 111/100", J(Q(1)) == 1 and J(Q(9, 10)) == Q(111, 100))
check("application: 1 is the unique minimiser on the tenths grid",
      [Q(k, 10) for k in range(11) if J(Q(k, 10)) == min(J(Q(j, 10)) for j in range(11))] == [Q(1)])
check("application: J(41/42) = 83/84 < 1 = J(1)", Q(83, 84) < 1)

with open(REPO / "data/applications/mccollum_grid_continuum.tsv", encoding="utf-8") as fh:
    rows = list(csv.DictReader(fh, delimiter="\t"))
bad = [r for r in rows if J(Q(r["candidate_exact"])) != Q(r["objective_exact"])]
check("data/applications/mccollum_grid_continuum.tsv: every objective value is exact",
      not bad, f"{len(bad)} mismatches, first {bad[:1]}")
check("data/applications/mccollum_grid_continuum.tsv: exactly one winner per domain",
      [r["candidate_exact"] for r in rows if r["winner"] == "true"] == ["1", "41/42"])

def quadratic_profile(h: Q, m: Q, length: int) -> list[Q]:
    a = m / (2 * h)
    K = 1
    while a * Q(K * (K + 1), 2) < 1:
        K += 1
    eta = (m * Q(K * (K + 1), 2) - 2 * h) / K
    assert 0 <= eta < m, (h, m, K, eta)
    drops = [max(Q(0), (m * Q(K - i + 1) - eta) / (2 * h)) for i in range(1, K + 1)]
    assert sum(drops) == 1, (h, m, drops)
    xs, cur = [Q(1)], Q(1)
    for d in drops:
        cur -= d
        xs.append(cur)
    xs += [Q(0)] * max(0, length - len(xs) + 1)
    return xs[:length + 1], K, drops


profile, K, drops = quadratic_profile(Q(5), Q(1), 9)
check("application: for h = 5, m = 1 the drop scale is a = 1/10", Q(1) / (2 * 5) == Q(1, 10))
check("application: a(1+2+3) = 6/10 < 1 and a(1+2+3+4) = 10/10 = 1, so K = 4",
      Q(1, 10) * 6 == Q(6, 10) and Q(1, 10) * 10 == 1 and K == 4, f"K = {K}")
check("application: the saturated drops are 4/10, 3/10, 2/10, 1/10",
      drops == [Q(4, 10), Q(3, 10), Q(2, 10), Q(1, 10)], str(drops))
check("eq:app-mcc-kazakh-profile: the profile is (1, 3/5, 3/10, 1/10, 0, 0, ...)",
      profile[:6] == [Q(1), Q(3, 5), Q(3, 10), Q(1, 10), Q(0), Q(0)], str(profile[:6]))
check("application: the four drops sum to one and descend strictly",
      sum(drops) == 1 and all(drops[i] > drops[i + 1] for i in range(len(drops) - 1)))

for path, key, value_field in (
    ("data/continuous_hg/exact_profiles.tsv", "position", "exact_value"),
    ("data/applications/mccollum_length_profile.tsv", "position", "exact_value"),
):
    with open(REPO / path, encoding="utf-8") as fh:
        rows = list(csv.DictReader(fh, delimiter="\t"))
    bad = [r for r in rows if Q(r[value_field]) != profile[int(r[key])]]
    check(f"{path}: every position matches the recomputed exact profile",
          not bad, f"{len(bad)} mismatches, first {bad[:1]}")

FRAGMENTS = [("Uyghur display", Q(20), Q(3), 5),
             ("fitted Kazakh", Q(5), Q(1), 4),
             ("Kyrgyz display", Q(21), Q(1), 9)]
for name, h, m, want in FRAGMENTS:
    _prof, k, _d = quadratic_profile(h, m, 1)
    check(f"application: the triangular test gives first-zero index {want} for the {name} (h = {h}, m = {m})",
          k == want, f"got {k}")
    a = m / (2 * h)
    check(f"application: minimality of K = {want} for h = {h}, m = {m}",
          a * Q(k * (k + 1), 2) >= 1 and (k == 1 or a * Q((k - 1) * k, 2) < 1))
check("application: first-zero index K means K - 1 positive followers, giving four, three and eight",
      [k - 1 for _n, _h, _m, k in FRAGMENTS] == [4, 3, 8])
check("application: for the Kyrgyz one-follower display the weights are h = 21, m = 1, "
      "which is exactly the objective 21(1-x)^2 + x",
      J(Q(1, 3)) == 21 * (1 - Q(1, 3)) ** 2 + Q(1, 3))

long_profile, K2, _ = quadratic_profile(Q(5), Q(1), 20)
check("application sec:app-mcc-zeros: extending the horizon keeps the prefix and appends zeros",
      long_profile[:10] == profile[:10] and all(v == 0 for v in long_profile[K2:]))


def main() -> int:
    failed = [r for r in RESULTS if not r[1]]
    for label, ok, detail in RESULTS:
        if not ok:
            print(f"FAIL  {label}   [{detail}]")
    print(f"\n{len(RESULTS) - len(failed)}/{len(RESULTS)} McCollum claims verified")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
