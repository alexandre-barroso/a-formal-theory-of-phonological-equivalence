from __future__ import annotations

import json
from fractions import Fraction
from itertools import product
from typing import Mapping, Sequence

from phonological_opacity.fragments.lithuanian import load_spec

from . import lith_decls as LD

PARAMS = ("c", "r", "d", "a", "n")


def variants() -> dict[str, tuple]:
    return {
        "witness": (LD.agree("witness", "stop"), LD.nogem("witness", "stop")),
        "dynamic_stop": (LD.agree("dynamic", "stop"), LD.nogem("dynamic", "stop")),
        "dynamic_skip": (LD.agree("dynamic", "skip"), LD.nogem("dynamic", "skip")),
        "origin_bound": (LD.agree("origin_bound", "skip"),
                         LD.nogem("origin_bound", "skip")),
        "override_SR": (LD.agree_surviving_origins(), LD.nogem("witness", "stop")),
        "override_RS": (LD.agree("witness", "stop"), LD.nogem_surviving_origins()),
        "override_SS": (LD.agree_surviving_origins(), LD.nogem_surviving_origins()),
    }


def symbolic_rows(record: Mapping, a_decl, n_decl) -> list[tuple[int, ...]]:
    return [LD.coefficients(record, j, a_decl, n_decl) for j in range(8)]


def _value(coeffs: Sequence[int], w: Mapping, lam) -> Fraction:
    c, r, d, ao, an, no, nn = coeffs
    return (w["c"] * c + w["r"] * r + w["d"] * d
            + w["a"] * (ao + lam * an) + w["n"] * (no + lam * nn))


def evaluate_point(a_decl, n_decl, w: Mapping, lam, spec=None) -> dict:
    spec = spec or load_spec()
    out = {}
    for rec in spec["inputs"]:
        rows = symbolic_rows(rec, a_decl, n_decl)
        vals = [_value(r, w, lam) for r in rows]
        obs = [LD.__dict__["state_of"](rec, j) for j in range(8)]
        del obs
        from phonological_opacity.fragments.lithuanian import observation
        strings = [observation(rec, j) for j in range(8)]
        fiber = [j for j in range(8) if strings[j] == rec["observation"]]
        best = min(vals)
        minima = [j for j in range(8) if vals[j] == best]
        out[rec["id"]] = {
            "fiber": fiber, "minima": minima,
            "exclusively_correct": bool(minima) and set(minima) <= set(fiber),
            "scores8": [str(v * 8) for v in vals],
        }
    return out


def difference_forms(record: Mapping, a_decl, n_decl) -> dict[int, list[tuple]]:
    from phonological_opacity.fragments.lithuanian import observation
    rows = symbolic_rows(record, a_decl, n_decl)
    strings = [observation(record, j) for j in range(8)]
    fiber = [j for j in range(8) if strings[j] == record["observation"]]
    out = {}
    for j in fiber:
        out[j] = [tuple(rows[i][k] - rows[j][k] for k in range(7))
                  for i in range(8) if i not in fiber]
    return out


def infeasible_by_sign(forms: Sequence[tuple]) -> list[tuple]:
    bad = []
    for f in forms:
        dc, dr, dd, dao, dan, dno, dnn = f
        if all(x <= 0 for x in f):
            bad.append(f)
    return bad


def report(spec=None) -> dict:
    spec = spec or load_spec()
    from phonological_opacity.fragments.lithuanian import reference_weights
    w, lam = reference_weights(spec)
    out = {}
    for name, (a_decl, n_decl) in variants().items():
        pt = evaluate_point(a_decl, n_decl, w, lam, spec)
        excl = {}
        for rec in spec["inputs"]:
            forms = difference_forms(rec, a_decl, n_decl)
            per_branch = {}
            for j, rows in forms.items():
                bad = infeasible_by_sign(rows)
                per_branch[j] = {
                    "rows": len(rows),
                    "sign_infeasible_rows": [list(b) for b in bad],
                }
            excl[rec["id"]] = {
                "fiber": list(forms.keys()),
                "branches": per_branch,
                "excluded_for_all_nonnegative_parameters":
                    all(v["sign_infeasible_rows"] for v in per_branch.values()),
            }
        fa = a_decl.well_typed(); fn = n_decl.well_typed()
        out[name] = {
            "well_typed": fa[0] and fn[0],
            "faults": sorted(set(fa[1]) | set(fn[1])),
            "at_reference_point": pt,
            "exclusion": excl,
            "jointly_selective_at_reference_point":
                all(v["exclusively_correct"] for v in pt.values()),
            "excluded_everywhere":
                any(v["excluded_for_all_nonnegative_parameters"]
                    for v in excl.values()),
        }
    return out


if __name__ == "__main__":
    print(json.dumps(report(), ensure_ascii=False, indent=1))
