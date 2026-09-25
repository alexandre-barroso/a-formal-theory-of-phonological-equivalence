from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import Callable, Iterable, Optional, Sequence

from phonological_opacity.fragments.gua import MARKEDNESS, SCHEMAS, GuaFragment

from .structures import GuaContext, Skeleton, State

MODE_RETAINED = "retained"
MODE_CURRENT = "current"
MODE_OFF = "off"


@dataclass(frozen=True)
class LocusVector:

    old: tuple[int, ...]
    new: tuple[int, ...]
    current: tuple[int, ...]


def locus_vector(fragment: GuaFragment, segments: Sequence[str]) -> LocusVector:
    cur = fragment.readers(segments)
    ref = getattr(fragment, "_ref_readers", None) or fragment.readers(fragment.reference)
    old: list[int] = []
    new: list[int] = []
    current: list[int] = []
    for schema in SCHEMAS:
        o = n = c = 0
        for q in range(fragment.n):
            p = fragment.pressure(cur[schema][q])
            m = fragment.marked(cur[schema][q])
            c += m
            if schema in MARKEDNESS:
                a = fragment.marked(ref[schema][q])
                o += p if a else 0
                n += m if not a else 0
            else:
                o += m
        old.append(o)
        new.append(n)
        current.append(c)
    return LocusVector(tuple(old), tuple(new), tuple(current))


def score8_variant(vector: LocusVector, weights: dict[str, Fraction],
                   lam: Fraction, modes: dict[str, str]) -> int:
    total = Fraction(0)
    for i, schema in enumerate(SCHEMAS):
        mode = modes.get(schema, MODE_RETAINED)
        w = weights[schema]
        if mode == MODE_OFF:
            continue
        if mode == MODE_CURRENT:
            total += w * Fraction(vector.current[i])
        else:
            total += w * (Fraction(vector.old[i]) + lam * Fraction(vector.new[i]))
    scaled = total * 8
    if scaled.denominator != 1:
        raise ValueError(f"non-integer scaled score {scaled}")
    return int(scaled)


@dataclass(frozen=True)
class ModelInstance:
    id: str
    provenance: str
    description: str
    weights: dict[str, Fraction]
    lam: Fraction
    modes: dict[str, str]

    def score8(self, vector: LocusVector) -> int:
        return score8_variant(vector, self.weights, self.lam, self.modes)


def model_instances(ctx: GuaContext) -> list[ModelInstance]:
    base = {s: Fraction(ctx.shared["weights"][s]) for s in SCHEMAS}
    lam = Fraction(ctx.shared["lambda"]["num"], ctx.shared["lambda"]["den"])
    out: list[ModelInstance] = [
        ModelInstance(
            "RET", "DISSERTATION_BASELINE",
            "the retained construction of eq:opacity-retention with the declared "
            "weight vector eq:opacity-gua-weights and lambda = 1/8",
            base, lam, {s: MODE_RETAINED for s in SCHEMAS}),
        ModelInstance(
            "CUR", "DISSERTATION_COMPARATOR",
            "strictly current markedness: every markedness schema charges only "
            "current violations (sec:opacity-obstructions), faithfulness unchanged",
            base, lam, {s: (MODE_CURRENT if s in MARKEDNESS else MODE_RETAINED)
                        for s in SCHEMAS}),
        ModelInstance(
            "RET_lam0", "DISSERTATION_BOUNDARY",
            "the retained construction with lambda = 0: no charge for a violation "
            "absent from the reference",
            base, Fraction(0), {s: MODE_RETAINED for s in SCHEMAS}),
        ModelInstance(
            "RET_lam1", "DISSERTATION_BOUNDARY",
            "the retained construction with lambda = 1: old and new violations "
            "weighted alike (thm:opacity-lt-region records that lambda = 1 in RR "
            "recovers every ordinary score of the Lithuanian product)",
            base, Fraction(1), {s: MODE_RETAINED for s in SCHEMAS}),
    ]
    for schema in MARKEDNESS:
        modes = {s: MODE_RETAINED for s in SCHEMAS}
        modes[schema] = MODE_CURRENT
        out.append(ModelInstance(
            f"CUR_{schema}", "ABLATION",
            f"retention withdrawn at {schema} only: that schema charges current "
            "violations, every other schema is retained",
            base, lam, modes))
        modes_off = {s: MODE_RETAINED for s in SCHEMAS}
        modes_off[schema] = MODE_OFF
        out.append(ModelInstance(
            f"OFF_{schema}", "ABLATION",
            f"{schema} removed from the grammar entirely",
            base, lam, modes_off))
    return out


@dataclass(frozen=True)
class ModelProtocol:

    base_input: str
    frame: str
    licence: str
    skeleton: Skeleton
    bridge: str
    cost: Fraction

    def describe(self) -> str:
        return f"{self.base_input}|{self.frame}|{self.bridge}"


def observation_of(ctx: GuaContext, instance: ModelInstance, skeleton: Skeleton,
                   bridge_fn: Callable[[GuaContext, State], object],
                   vectors: Sequence[LocusVector],
                   candidates: Sequence[State]) -> tuple:
    best: Optional[int] = None
    minima: list[int] = []
    for i, vector in enumerate(vectors):
        value = instance.score8(vector)
        if best is None or value < best:
            best, minima = value, [i]
        elif value == best:
            minima.append(i)
    return tuple(sorted({repr(bridge_fn(ctx, candidates[i])) for i in minima}))
