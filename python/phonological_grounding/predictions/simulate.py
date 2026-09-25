from __future__ import annotations
from phonological_grounding.results import bare

import json
import random
from fractions import Fraction
from pathlib import Path

from .design_length import EXPOSED_CELLS, battery, prospective_battery


def ratio(v1: int, v3: int) -> Fraction:
    return Fraction(v1, (1 + v3) * (v1 + 1 + v3))


ALL_CELLS = [(c.inp.id, c.v1, c.v3, ratio(c.v1, c.v3)) for c in battery()]
CELLS = [(c.inp.id, c.v1, c.v3, ratio(c.v1, c.v3)) for c in prospective_battery()]
EXPOSED = [c for c in ALL_CELLS if c[0] in EXPOSED_CELLS]
DEV_BOUND = Fraction(1, 12)
INFORMATIVE = [c for c in CELLS if c[3] < DEV_BOUND]
FORCED = [c for c in CELLS if c[3] >= DEV_BOUND]


def _latent(model: str, r: Fraction, v1: int, v3: int, rng: random.Random) -> str:
    if model in ("RETAINED", "RULE-SERIAL"):
        return "+ATR"
    if model == "SHARED-ACTIVITY":
        return "+ATR" if r < ratio(v1, v3) else "-ATR"
    if model == "MISSPEC_length_on_junction":
        return "+ATR"
    if model == "MISSPEC_v1_only":
        return "+ATR" if v1 == 2 else "-ATR"
    if model == "MISSPEC_random":
        return rng.choice(["+ATR", "-ATR"])
    raise ValueError(model)


ORDERING_MARGIN = 0.25


def one_study(model: str, r: Fraction, speakers: int, reps: int, noise: float,
              indeterminate: float, rng: random.Random) -> dict:
    per_cell: dict[str, dict[str, int]] = {cid: {"+ATR": 0, "-ATR": 0, "excl": 0}
                                           for cid, *_ in CELLS}
    modal_transparent: dict[str, int] = {cid: 0 for cid, *_ in CELLS}
    speakers_with_data: dict[str, int] = {cid: 0 for cid, *_ in CELLS}
    for _ in range(speakers):
        for cid, v1, v3, _r in CELLS:
            tally = {"+ATR": 0, "-ATR": 0}
            for _ in range(reps):
                if rng.random() < indeterminate:
                    per_cell[cid]["excl"] += 1
                    continue
                if model == "MISSPEC_length_on_junction" and v3 >= 4:
                    per_cell[cid]["excl"] += 1
                    continue
                v = _latent(model, r, v1, v3, rng)
                if rng.random() < noise:
                    v = "-ATR" if v == "+ATR" else "+ATR"
                per_cell[cid][v] += 1
                tally[v] += 1
            if tally["+ATR"] + tally["-ATR"] > 0:
                speakers_with_data[cid] += 1
                if tally["-ATR"] > tally["+ATR"]:
                    modal_transparent[cid] += 1
    readable = all(speakers_with_data[cid] >= max(1, speakers // 2)
                   for cid, *_ in CELLS)
    fired = any(speakers_with_data[cid] > 0
                and modal_transparent[cid] * 2 > speakers_with_data[cid]
                for cid, *_ in INFORMATIVE)
    fired_per_token = any(per_cell[cid]["-ATR"] > 0 for cid, *_ in INFORMATIVE)

    def rate(cid: str) -> float | None:
        d = per_cell[cid]
        n = d["+ATR"] + d["-ATR"]
        return None if n == 0 else d["+ATR"] / n

    violation = False
    for v1 in (1, 2):
        rs = [rate(cid) for cid, a, _b, _c in CELLS if a == v1]
        if any(x is None for x in rs):
            continue
        if any(rs[i] < rs[i + 1] - ORDERING_MARGIN for i in range(len(rs) - 1)):
            violation = True
    forced_ids = {c[0] for c in FORCED}
    forced_ok = all(not (speakers_with_data[cid] > 0
                         and modal_transparent[cid] * 2 > speakers_with_data[cid])
                    for cid in forced_ids)
    return {"per_cell": per_cell, "readable": readable, "primary_fired": fired,
            "rejected_per_token_fired": fired_per_token,
            "ordering_violated": violation,
            "forced_opaque_respected": forced_ok,
            "modal_transparent": modal_transparent}


def run(out: Path | None = None, studies: int = 400, speakers: int = 8,
        reps: int = 3, seed: int = 20260916) -> dict:
    rng = random.Random(seed)
    report: dict = {
        "standing_statement": (
            "These are properties of the listed generative assumptions, not of "
            "Gua. No speaker response exists in this repository. Nothing here "
            "is a power calculation for a real study."),
        "prospective_cells": [{"id": c[0], "v1": c[1], "v3": c[2],
                               "threshold_ratio": str(c[3]),
                               "role": ("informative" if c[3] < DEV_BOUND else "forced-opaque")}
                              for c in CELLS],
        "exposed_cells_excluded_from_every_count": [
            {"id": c[0], "v1": c[1], "v3": c[2], "threshold_ratio": str(c[3]),
             "why": "reproduces Obiri-Yeboah & Rasin (34a) = the G34a development "
                    "product; a positive control, never prospective evidence"}
            for c in EXPOSED],
        "development_bound": str(DEV_BOUND),
        "settings": {"studies": studies, "speakers": speakers, "reps": reps,
                     "seed": seed},
        "scenarios": [],
    }
    scenarios = [
        ("RETAINED", Fraction(0), 0.02, 0.05),
        ("RETAINED", Fraction(0), 0.10, 0.05),
        ("RULE-SERIAL", Fraction(0), 0.02, 0.05),
        ("SHARED-ACTIVITY", Fraction(1, 21), 0.02, 0.05),
        ("SHARED-ACTIVITY", Fraction(1, 21), 0.10, 0.05),
        ("SHARED-ACTIVITY", Fraction(1, 25), 0.02, 0.05),
        ("SHARED-ACTIVITY", Fraction(1, 100), 0.02, 0.05),
        ("MISSPEC_length_on_junction", Fraction(0), 0.02, 0.05),
        ("MISSPEC_v1_only", Fraction(0), 0.02, 0.05),
        ("MISSPEC_random", Fraction(0), 0.02, 0.05),
    ]
    for model, r, noise, indet in scenarios:
        fired = unreadable = ordering = forced = token = 0
        for _ in range(studies):
            s = one_study(model, r, speakers, reps, noise, indet, rng)
            fired += s["primary_fired"]
            token += s["rejected_per_token_fired"]
            unreadable += not s["readable"]
            ordering += s["ordering_violated"]
            forced += not s["forced_opaque_respected"]
        report["scenarios"].append({
            "generating_model": model,
            "ratio": str(r),
            "transcription_error_rate": noise,
            "indeterminate_rate": indet,
            "primary_contrast_fires": fired / studies,
            "rejected_per_token_rule_fires": token / studies,
            "pipeline_unreadable": unreadable / studies,
            "ordering_constraint_violated": ordering / studies,
            "forced_opaque_cells_violated": forced / studies,
            "reading": _reading(model, r, noise),
        })
    if out:
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(json.dumps(bare(report), indent=2, ensure_ascii=False))
    return report


def _reading(model: str, r: Fraction, noise: float) -> str:
    if model in ("RETAINED", "RULE-SERIAL"):
        return ("the primary contrast fires only through transcription error; "
                "its rate here is the FALSE-ALARM rate of the design at that "
                "error rate, and at 10% error it is high enough that a single "
                "transparent token cannot be decisive without replication")
    if model == "SHARED-ACTIVITY":
        return ("the primary contrast fires when the model's own ratio exceeds "
                "some informative cell's threshold; at ratio 1/100 it never "
                "does, which is the observational-equivalence corner")
    if model == "MISSPEC_length_on_junction":
        return ("a misspecified alternative in which length destroys the "
                "junction instead of the ATR value: the manipulation check "
                "excludes the longest cells and the design becomes unreadable")
    if model == "MISSPEC_v1_only":
        return ("a misspecified alternative sensitive to the subject only: it "
                "fires the primary contrast but VIOLATES the ordering "
                "constraint, which is how the design detects it")
    return "pure noise: both the contrast and the ordering constraint misbehave"


if __name__ == "__main__":
    import sys
    out = Path(sys.argv[1]) if len(sys.argv) > 1 else None
    rep = run(out)
    for s in rep["scenarios"]:
        print(f"{s['generating_model']:28s} r={s['ratio']:6s} err={s['transcription_error_rate']:.2f} "
              f"| fires={s['primary_contrast_fires']:.3f} unreadable={s['pipeline_unreadable']:.3f} "
              f"order_viol={s['ordering_constraint_violated']:.3f} "
              f"forced_viol={s['forced_opaque_cells_violated']:.3f}")
