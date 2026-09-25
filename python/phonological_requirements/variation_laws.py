from __future__ import annotations
from phonological_requirements import certificate, paths

import itertools
import json
import math
import random
from fractions import Fraction as F
from pathlib import Path

from .recon_anttila import (STRATA, count_law, linear_extensions, ot_winner,
                            violations, volume_law)

OUT = paths.CERTIFICATES


def finnish():
    from .observations import ANTTILA_FINNISH as D, ANTTILA_PRINTED as P
    rows = {}
    for item, (weak, strong, obs_w, obs_s, n_w, n_s, sv) in D.items():
        vw = violations(weak, sv, strong=False)
        vs = violations(strong, sv, strong=True)
        cl = count_law(vw, vs)
        vl, stratum = volume_law(vw, vs)
        rows[item] = {"weak": weak, "strong": strong,
                      "violations_weak": vw, "violations_strong": vs,
                      "count_law_weak_pct": round(float(cl["a"]) * 100, 2),
                      "count_law_tie": str(cl["tie"]),
                      "printed_SG_weak_pct": P[item][0], "printed_CRG_weak_pct": P[item][1],
                      "volume_law_weak_pct": round(float(vl["a"]) * 100, 2),
                      "deciding_stratum": stratum,
                      "observed_weak_pct": obs_w, "tokens": [n_w, n_s],
                      "SG_reproduced": abs(float(cl["a"]) * 100 - P[item][0]) < 1.0}
    return rows


def equal_pattern_groups(rows):
    groups = {}
    for item, r in rows.items():
        d = tuple(r["violations_strong"][c] - r["violations_weak"][c]
                  for s in STRATA for c in s)
        groups.setdefault(d, []).append(item)
    out = []
    for d, items in groups.items():
        if len(items) < 2:
            continue
        obs = {i: (rows[i]["observed_weak_pct"], rows[i]["tokens"]) for i in items}
        pairs = []
        for a, b in itertools.combinations(items, 2):
            (pa, (na1, na2)), (pb, (nb1, nb2)) = obs[a], obs[b]
            na, nb = na1 + na2, nb1 + nb2
            if na == 0 or nb == 0:
                continue
            p = (na1 + nb1) / (na + nb)
            se = math.sqrt(p * (1 - p) * (1 / na + 1 / nb)) if 0 < p < 1 else 0
            z = (na1 / na - nb1 / nb) / se if se else float("nan")
            pairs.append({"pair": [a, b], "observed_weak_pct": [round(100 * na1 / na, 1), round(100 * nb1 / nb, 1)],
                          "tokens": [na, nb], "z": round(z, 2)})
        out.append({"difference_vector": list(d), "items": items,
                    "count_law_weak_pct": rows[items[0]]["count_law_weak_pct"],
                    "pairs": pairs})
    return out


TD_CONS = ["*CxOns", "*CxCod", "Onset", "Align", "Max(t)"]
TD = {"V": {"cost.V": {"*CxCod": 1, "Onset": 1}, "cos.V": {"Onset": 1, "Max(t)": 1},
            "cos.tV": {"Align": 1}},
      "C": {"cost.C": {"*CxCod": 1}, "cos.C": {"Max(t)": 1},
            "cos.tC": {"*CxOns": 1, "Align": 1}}}


def td_winner(order, cands):
    alive = list(cands)
    for c in order:
        m = min(cands[x].get(c, 0) for x in alive)
        alive = [x for x in alive if cands[x].get(c, 0) == m]
        if len(alive) == 1:
            return alive[0]
    return "tie:" + "/".join(sorted(alive))


def td_typology():
    from .observations import ANTTILA_TD_PATTERNS as PAT, ANTTILA_TD_COUNTS as CNT
    patterns, counts = {}, {"V": {}, "C": {}}
    for order in itertools.permutations(TD_CONS):
        wv, wc = td_winner(order, TD["V"]), td_winner(order, TD["C"])
        patterns[(wv, wc)] = patterns.get((wv, wc), 0) + 1
        counts["V"][wv] = counts["V"].get(wv, 0) + 1
        counts["C"][wc] = counts["C"].get(wc, 0) + 1
    rng = random.Random(3); N = 400000
    vol = {"V": {}, "C": {}}
    for _ in range(N):
        w = {c: rng.expovariate(1.0) for c in TD_CONS}
        for env in ("V", "C"):
            sc = {x: sum(w[c] * v for c, v in TD[env][x].items()) for x in TD[env]}
            m = min(sc.values()); win = [x for x in sc if sc[x] == m]
            k = win[0] if len(win) == 1 else "tie"
            vol[env][k] = vol[env].get(k, 0) + 1
    return {"patterns_from_120_rankings": {f"{k[0]} | {k[1]}": v for k, v in patterns.items()},
            "n_patterns": len(patterns),
            "source_patterns": {str(k): list(v) for k, v in PAT.items()},
            "ranking_counts": counts, "source_counts": CNT,
            "counts_agree": all(counts[e].get(x, 0) == n for e in CNT for x, n in CNT[e].items()),
            "weight_volume_pct": {e: {x: round(100 * n / N, 2) for x, n in vol[e].items()} for e in vol},
            "ranking_count_pct": {e: {x: round(100 * n / 120, 2) for x, n in counts[e].items()} for e in counts}}


def main():
    rows = finnish()
    rec = {"finnish": rows, "equal_pattern_groups": equal_pattern_groups(rows),
           "td": td_typology()}
    rec["SG_reproduced_all"] = all(r["SG_reproduced"] for r in rows.values())
    OUT.mkdir(parents=True, exist_ok=True)
    certificate.write("variation_laws.json", rec)
    print("1-2. Finnish: count law (source's SG) vs printed, and the volume law")
    print(f"   {'item':15s} {'count':>6s} {'SG':>5s} {'CRG':>6s} {'volume':>7s} {'obs':>6s} tokens  stratum")
    for item, r in rows.items():
        print(f"   {item:15s} {r['count_law_weak_pct']:6.1f} {r['printed_SG_weak_pct']:5.0f} "
              f"{r['printed_CRG_weak_pct']:6.2f} {r['volume_law_weak_pct']:7.2f} {r['observed_weak_pct']:6.1f} "
              f"{str(r['tokens']):10s} {r['deciding_stratum']}")
    print("   SG reproduced for every item:", rec["SG_reproduced_all"])
    print("3. equal-pattern groups")
    for g in rec["equal_pattern_groups"]:
        print("  ", g["items"], "count law", g["count_law_weak_pct"], "| pairs:", g["pairs"])
    print("4. t,d-deletion:", json.dumps({k: rec["td"][k] for k in ("n_patterns", "counts_agree", "ranking_count_pct", "weight_volume_pct")}, indent=1))


if __name__ == "__main__":
    main()
