from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
from typing import Callable, Iterable, Optional, Sequence

from .structures import (
    GuaContext,
    OPERATION_TABLE,
    Skeleton,
    State,
    Undefined,
)


ATR_CODE = {True: "+", False: "-", None: "0"}


def bridge_seg(ctx: GuaContext, state: State) -> str:
    return "".join(s for s in state.values if ctx.is_present(s))


def bridge_segtone(ctx: GuaContext, state: State) -> tuple[tuple[str, Optional[str]], ...]:
    out: list[tuple[str, Optional[str]]] = []
    for seg, tone in zip(state.values, state.skeleton.tones):
        if not ctx.is_present(seg):
            continue
        out.append((seg, tone if ctx.is_nuclear(seg) else None))
    return tuple(out)


def bridge_atr(ctx: GuaContext, state: State) -> tuple[str, ...]:
    out: list[str] = []
    for seg in state.values:
        if ctx.is_present(seg) and ctx.is_nuclear(seg):
            out.append(ATR_CODE[ctx.features.get(seg, ctx.default)["atr"]])
    return tuple(out)


def bridge_count(ctx: GuaContext, state: State) -> int:
    return sum(1 for s in state.values if ctx.is_present(s))


def bridge_score8(ctx: GuaContext, state: State) -> int:
    fragment = ctx.fragment(state.skeleton, "bridge_score8")
    return fragment.score8(list(state.values))


BRIDGES: dict[str, Callable[[GuaContext, State], object]] = {
    "B_seg": bridge_seg,
    "B_segtone": bridge_segtone,
    "B_atr": bridge_atr,
    "B_count": bridge_count,
    "B_score8": bridge_score8,
}

BRIDGE_LICENCE = {
    "B_seg": "ATTESTED",
    "B_atr": "ATTESTED",
    "B_count": "ATTESTED",
    "B_segtone": "ATTESTED",
    "B_score8": "MODEL_INTERNAL",
}

BRIDGE_COST = {
    "B_seg": Fraction(0),
    "B_atr": Fraction(0),
    "B_count": Fraction(0),
    "B_segtone": Fraction(1),
    "B_score8": None,
}


@dataclass(frozen=True)
class Step:

    op: str
    args: tuple

    def licence(self) -> str:
        if self.op in ("project_phrase", "weight_derivative"):
            return "MODEL_INTERNAL"
        if self.op == "insert_word_at":
            return "PROPOSED_ELICITATION"
        return "ATTESTED"

    def describe(self) -> str:
        return f"{self.op}{self.args}"


@dataclass(frozen=True)
class Context:

    steps: tuple[Step, ...] = ()

    @property
    def depth(self) -> int:
        return len(self.steps)

    def extend(self, step: Step) -> "Context":
        return Context(self.steps + (step,))

    def licence(self) -> str:
        order = {"ATTESTED": 0, "PROPOSED_ELICITATION": 1, "MODEL_INTERNAL": 2}
        worst = "ATTESTED"
        for step in self.steps:
            if order[step.licence()] > order[worst]:
                worst = step.licence()
        return worst

    def describe(self) -> str:
        return "[-]" if not self.steps else "[-]" + "".join("." + s.describe() for s in self.steps)

    def evaluate(self, ctx: GuaContext, state: State) -> Optional[State]:
        current = state
        for step in self.steps:
            fn = OPERATION_TABLE[step.op]
            try:
                current = fn(ctx, current, *step.args)
            except Undefined:
                return None
            except KeyError:
                return None
        return current


IDENTITY = Context()


@dataclass(frozen=True)
class Protocol:
    context: Context
    bridge: str

    def licence(self) -> str:
        order = {"ATTESTED": 0, "PROPOSED_ELICITATION": 1, "MODEL_INTERNAL": 2}
        a, b = self.context.licence(), BRIDGE_LICENCE[self.bridge]
        return a if order[a] >= order[b] else b

    def observe(self, ctx: GuaContext, state: State):
        target = self.context.evaluate(ctx, state)
        if target is None:
            return None
        return (BRIDGES[self.bridge](ctx, target),)

    def cost(self, ctx: GuaContext, skeleton: Skeleton) -> Optional[Fraction]:
        bridge_cost = BRIDGE_COST[self.bridge]
        if bridge_cost is None:
            return None
        current = Skeleton(skeleton.words, skeleton.phrases, skeleton.tones)
        state = State.reference_state(current)
        target = self.context.evaluate(ctx, state)
        if target is None:
            return None
        words = len(target.skeleton.words)
        return Fraction(1) + Fraction(max(0, words - 1)) + bridge_cost

    def describe(self) -> str:
        return f"{self.context.describe()} | {self.bridge}"


LICENCE_ORDER = {"ATTESTED": 0, "PROPOSED_ELICITATION": 1, "MODEL_INTERNAL": 2}


def enumerate_steps(ctx: GuaContext, skeleton: Skeleton) -> list[Step]:
    steps: list[Step] = []
    word_count = len(skeleton.words)
    for i in range(word_count):
        steps.append(Step("isolate_word", (i,)))
    if word_count > 1:
        for i in range(word_count):
            steps.append(Step("drop_word", (i,)))
    for wid in ctx.words_for_frames:
        steps.append(Step("prefix_word", (wid,)))
        steps.append(Step("suffix_word", (wid,)))
        for i in range(word_count):
            steps.append(Step("substitute_word", (i, wid)))
        for i in range(word_count + 1):
            steps.append(Step("insert_word_at", (i, wid)))
    for p in sorted(set(skeleton.phrases)):
        steps.append(Step("project_phrase", (p,)))
    steps.append(Step("rephrase_by_length", ()))
    reference = State.reference_state(skeleton)
    live: list[Step] = []
    for step in steps:
        if Context((step,)).evaluate(ctx, reference) is not None:
            live.append(step)
    return live


def enumerate_contexts(ctx: GuaContext, skeleton: Skeleton, max_depth: int,
                       licence_ceiling: str = "MODEL_INTERNAL") -> list[Context]:
    ceiling = LICENCE_ORDER[licence_ceiling]
    frontier: list[tuple[Context, Skeleton]] = [(IDENTITY, skeleton)]
    out: list[Context] = [IDENTITY]
    for _ in range(max_depth):
        nxt: list[tuple[Context, Skeleton]] = []
        for context, current in frontier:
            for step in enumerate_steps(ctx, current):
                if LICENCE_ORDER[step.licence()] > ceiling:
                    continue
                extended = context.extend(step)
                result = extended.evaluate(ctx, State.reference_state(skeleton))
                if result is None:
                    continue
                out.append(extended)
                nxt.append((extended, result.skeleton))
        frontier = nxt
        if not frontier:
            break
    return out


def enumerate_protocols(ctx: GuaContext, skeleton: Skeleton, max_depth: int,
                        licence_ceiling: str = "MODEL_INTERNAL",
                        bridges: Sequence[str] | None = None) -> list[Protocol]:
    bridges = list(bridges) if bridges is not None else list(BRIDGES)
    ceiling = LICENCE_ORDER[licence_ceiling]
    out: list[Protocol] = []
    for context in enumerate_contexts(ctx, skeleton, max_depth, licence_ceiling):
        for bridge in bridges:
            if LICENCE_ORDER[BRIDGE_LICENCE[bridge]] > ceiling:
                continue
            out.append(Protocol(context, bridge))
    return out
