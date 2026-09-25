from __future__ import annotations

import sys
from fractions import Fraction as Fr

from phonological_opacity.fragments.gua import GuaFragment, load_spec, SCHEMAS
from phonological_opacity.fragments import lithuanian as L

FAILS: list[str] = []
COUNT = 0


def check(label: str, ok: bool, detail: str = "") -> None:
    global COUNT
    COUNT += 1
    if not ok:
        FAILS.append(f"{label}: {detail}")


def main() -> int:
    spec = load_spec()
    invariant = {"G34a", "N7", "C24ei", "C21b", "C23UE"}
    bounded = {"G34b": 1126, "G37c": 1753, "OR38": 1430}
    for u in spec["inputs"]:
        fr = GuaFragment(spec, u["id"])
        O, N, obs = [], [], []
        for _i, cand in fr.all_candidates():
            t = fr.locus_terms(cand)
            O.append(sum(fr.weights[s] * t[s][0] for s in SCHEMAS))
            N.append(sum(fr.weights[s] * t[s][1] for s in SCHEMAS))
            obs.append(fr.observe(cand))

        def argmin(lam: Fr) -> list[int]:
            vals = [o + lam * n for o, n in zip(O, N)]
            m = min(vals)
            return [i for i, v in enumerate(vals) if v == m]

        base = argmin(Fr(1, 8))
        check(f"{u['id']}: singleton minimiser at 1/8", len(base) == 1, str(base))
        w = base[0]
        check(f"{u['id']}: minimiser realises the documented observation",
              obs[w] == u["observation"], f"{obs[w]} vs {u['observation']}")
        interval_ok = all(O[i] > O[w] and 4 * O[i] + N[i] >= 4 * O[w] + N[w]
                          for i in range(len(O)) if i != w)
        check(f"{u['id']}: selection invariant on lambda in [0, 1/4)", interval_ok)
        for lam in (Fr(0), Fr(1, 16), Fr(1, 8), Fr(3, 16), Fr(24, 100)):
            check(f"{u['id']}: argmin at lambda={lam} is [{w}]", argmin(lam) == [w], str(argmin(lam)))
        if u["id"] in invariant:
            check(f"{u['id']}: selected candidate has no new violation (N = 0)", N[w] == 0, str(N[w]))
            check(f"{u['id']}: argmin at lambda=1 unchanged", argmin(Fr(1)) == [w], str(argmin(Fr(1))))
        else:
            rival = bounded[u["id"]]
            check(f"{u['id']}: N_w - N_rival = w_H = 4", N[w] - N[rival] == 4, f"{N[w]} {N[rival]}")
            check(f"{u['id']}: O_rival - O_w = w_ATR = 1", O[rival] - O[w] == 1, f"{O[rival]} {O[w]}")
            check(f"{u['id']}: tie at lambda = 1/4 is exactly {{w, rival}}",
                  sorted(argmin(Fr(1, 4))) == sorted([w, rival]), str(argmin(Fr(1, 4))))
            check(f"{u['id']}: rival wins alone at lambda = 1", argmin(Fr(1)) == [rival], str(argmin(Fr(1))))
            tw, tr = fr.locus_terms(fr.candidate(w)), fr.locus_terms(fr.candidate(rival))
            check(f"{u['id']}: the new violation is a harmony (H) violation",
                  tw["H"] == (0, 1) and tr["H"] == (0, 0), f"{tw['H']} {tr['H']}")
            check(f"{u['id']}: the rival differs by one more IDENT_ATR",
                  tr["IDENT_ATR"][0] - tw["IDENT_ATR"][0] == 1, f"{tr['IDENT_ATR']} {tw['IDENT_ATR']}")
            check(f"{u['id']}: rival realises a harmonised, incorrect observation",
                  obs[rival] != u["observation"], obs[rival])

    lspec = L.load_spec()
    wts, lam_decl = L.reference_weights(lspec)
    c, d, a, n = wts["c"], wts["d"], wts["a"], wts["n"]
    lower = max((d - c) / n, (d - c) / a)
    check("Lithuanian: d < c + lambda n and d < c + lambda a give lambda > 1/16", lower == Fr(1, 16), str(lower))
    check("declared lambda = 1/8", lam_decl == Fr(1, 8), str(lam_decl))
    for lam, expect in ((Fr(1, 8), True), (Fr(1, 16), False), (Fr(0), False), (Fr(1, 4), True), (Fr(1), True)):
        ok_all = all(L.evaluate(rec, "RR", wts, lam)["exclusively_correct"] for rec in lspec["inputs"])
        check(f"Lithuanian RR at lambda={lam}: all three exclusively correct = {expect}", ok_all == expect)
    out0 = {rec["id"]: L.evaluate(rec, "RR", wts, Fr(0))["outputs"] for rec in lspec["inputs"]}
    check("Lithuanian RR at lambda=0 selects [abberti] for /ap-berti/", out0["PB"] == ["abberti"], str(out0["PB"]))
    check("Lithuanian RR at lambda=0 selects [adtaiki:ti] for /at-taiki:ti/", out0["TT"] == ["adtaiki:ti"], str(out0["TT"]))
    check("joint interval (1/16, 1/4) contains 1/8", Fr(1, 16) < Fr(1, 8) < Fr(1, 4))

    for f in FAILS:
        print("FAIL", f, file=sys.stderr)
    print(f"{COUNT - len(FAILS)}/{COUNT} attenuation-parameter claims verified")
    return 1 if FAILS else 0


if __name__ == "__main__":
    raise SystemExit(main())
