from __future__ import annotations

import copy
import json
from fractions import Fraction
from pathlib import Path
from typing import Sequence

from phonological_opacity.fragments import lithuanian_fragment

PARAMS = ("c", "r", "d", "a_old", "a_new", "n_old", "n_new")
CONFIGS = ("O", "RR", "SR", "RS", "SS", "RR0")


def load_spec() -> dict:
    return copy.deepcopy(lithuanian_fragment.SPEC)


def bits(j: int) -> tuple[int, int, int]:
    return (j // 4, (j // 2) % 2, j % 2)


def markedness(h: int, j: int) -> tuple[int, int]:
    x, y, z = bits(j)
    return ((1 - z) * int(x != y), (1 - z) * h * int(x == y))


def reader(h: int, defined_mode: str, k: str, j: int) -> tuple[int, int, int, int, int]:
    x, y, z = bits(j)
    c = 1 - z
    d = 1 if defined_mode == "S" else 1 - z
    g = int(x == y) if k == "A" else int(not (h and x == y))
    p = d * (1 - g)
    return (c, d, g, p, c * p)


def config_modes(config: str) -> tuple[str, str]:
    if config in ("O", "RR", "RR0"):
        return ("R", "R")
    return {"SR": ("S", "R"), "RS": ("R", "S"), "SS": ("S", "S")}[config]


def coefficient_vector(record: dict, config: str, j: int) -> tuple[int, int, int, int, int, int, int]:
    x, y, z = bits(j)
    h = record["h"]
    y_u = record["reference_bits"][1]
    ref = 4 * record["reference_bits"][0] + 2 * y_u + record["reference_bits"][2]
    m_ref = markedness(h, ref)
    mode_a, mode_n = config_modes(config)
    ra = reader(h, mode_a, "A", j)
    rn = reader(h, mode_n, "N", j)
    if config == "O":
        m_cur = markedness(h, j)
        return (int(x != 0), int(y != y_u), z, m_cur[0], 0, m_cur[1], 0)
    return (
        int(x != 0), int(y != y_u), z,
        m_ref[0] * ra[3], (1 - m_ref[0]) * ra[4],
        m_ref[1] * rn[3], (1 - m_ref[1]) * rn[4],
    )


def score(coeffs: Sequence[int], weights: dict, lam) -> Fraction:
    c, r, d, ao, an, no, nn = coeffs
    lam = Fraction(0) if lam is None else Fraction(lam)
    return (Fraction(weights["c"]) * c + Fraction(weights["r"]) * r + Fraction(weights["d"]) * d
            + Fraction(weights["a"]) * (ao + lam * an)
            + Fraction(weights["n"]) * (no + lam * nn))


def observation(record: dict, j: int) -> str:
    x, y, z = bits(j)
    return "a" + record["prefix"][x] + ("i" if z else "") + record["stem"][y] + record["tail"]


def evaluate(record: dict, config: str, weights: dict, lam) -> dict:
    lam_used = None if config == "O" else (Fraction(0) if config == "RR0" else lam)
    values = [score(coefficient_vector(record, config, j), weights, lam_used) for j in range(8)]
    obs = [observation(record, j) for j in range(8)]
    fiber = [j for j in range(8) if obs[j] == record["observation"]]
    best = min(values)
    minima = [j for j in range(8) if values[j] == best]
    return {
        "id": record["id"], "config": config,
        "fiber": fiber, "minima": minima,
        "minimum8": int(best * 8) if (best * 8).denominator == 1 else None,
        "outputs": sorted({obs[j] for j in minima}),
        "exclusively_correct": bool(minima) and set(minima) <= set(fiber),
        "scores8": [int(v * 8) if (v * 8).denominator == 1 else str(v) for v in values],
    }


def reference_weights(spec: dict) -> tuple[dict, Fraction]:
    p = spec["reference_point"]
    return ({k: Fraction(p[k]) for k in ("c", "r", "d", "a", "n")},
            Fraction(p["lambda"][0], p["lambda"][1]))
