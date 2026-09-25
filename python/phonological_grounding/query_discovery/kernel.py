from __future__ import annotations

import heapq
import itertools
from dataclasses import dataclass
from fractions import Fraction
from typing import Callable, Iterable, Optional, Sequence

from .protocols import (
    BRIDGE_COST,
    BRIDGE_LICENCE,
    BRIDGES,
    Context,
    LICENCE_ORDER,
    Protocol,
    Step,
    enumerate_contexts,
)
from .structures import GuaContext, Skeleton, State


@dataclass(frozen=True)
class Trace:

    target: Skeleton
    slots: tuple

    def apply(self, values: Sequence[str]) -> tuple[str, ...]:
        return tuple(values[q] if kind == "base" else q for kind, q in self.slots)


def context_trace(ctx: GuaContext, context: Context, skeleton: Skeleton) -> Optional[Trace]:
    tagged = State(skeleton, tuple(range(skeleton.size)))
    result = context.evaluate(ctx, tagged)
    if result is None:
        return None
    slots = tuple(("base", v) if isinstance(v, int) else ("new", v) for v in result.values)
    return Trace(result.skeleton, slots)


def assert_trace_sound(ctx: GuaContext, context: Context, skeleton: Skeleton,
                       states: Sequence[State]) -> None:
    trace = context_trace(ctx, context, skeleton)
    for state in states:
        direct = context.evaluate(ctx, state)
        if trace is None:
            assert direct is None, "trace says undefined, direct evaluation succeeded"
            continue
        assert direct is not None, "trace says defined, direct evaluation failed"
        assert direct.skeleton == trace.target, "trace target skeleton mismatch"
        assert direct.values == trace.apply(state.values), "trace value mismatch"


@dataclass
class Family:

    ctx: GuaContext
    skeleton: Skeleton
    contexts: list[Context]
    traces: list[Optional[Trace]]
    bridges: list[str]

    bridge_depth_limit: dict[str, int] | None = None

    @staticmethod
    def build(ctx: GuaContext, skeleton: Skeleton, max_depth: int,
              licence_ceiling: str, bridges: Sequence[str],
              bridge_depth_limit: dict[str, int] | None = None) -> "Family":
        contexts = enumerate_contexts(ctx, skeleton, max_depth, licence_ceiling)
        traces = [context_trace(ctx, c, skeleton) for c in contexts]
        keep = [i for i, t in enumerate(traces) if t is not None]
        return Family(ctx, skeleton,
                      [contexts[i] for i in keep],
                      [traces[i] for i in keep],
                      [b for b in bridges
                       if LICENCE_ORDER[BRIDGE_LICENCE[b]] <= LICENCE_ORDER[licence_ceiling]],
                      bridge_depth_limit or {})

    def _pairs(self) -> list[tuple[int, str]]:
        limits = self.bridge_depth_limit or {}
        out: list[tuple[int, str]] = []
        for k, context in enumerate(self.contexts):
            for bridge in self.bridges:
                if context.depth > limits.get(bridge, 10 ** 9):
                    continue
                out.append((k, bridge))
        return out

    def protocols(self) -> list[Protocol]:
        return [Protocol(self.contexts[k], b) for k, b in self._pairs()]

    def observations(self, states: Sequence[State]) -> list[list]:
        cache: dict[int, list[State]] = {}
        out: list[list] = []
        for k, bridge in self._pairs():
            targets = cache.get(k)
            if targets is None:
                trace = self.traces[k]
                assert trace is not None
                targets = [State(trace.target, trace.apply(s.values)) for s in states]
                cache[k] = targets
            fn = BRIDGES[bridge]
            out.append([fn(self.ctx, t) for t in targets])
        return out

    def costs(self) -> list[Optional[Fraction]]:
        out: list[Optional[Fraction]] = []
        for k, bridge in self._pairs():
            trace = self.traces[k]
            assert trace is not None
            words = len(trace.target.words)
            bc = BRIDGE_COST[bridge]
            out.append(None if bc is None
                       else Fraction(1) + Fraction(max(0, words - 1)) + bc)
        return out


def partition_of(column: Sequence) -> tuple[int, ...]:
    seen: dict = {}
    out: list[int] = []
    for value in column:
        key = repr(value)
        if key not in seen:
            seen[key] = len(seen)
        out.append(seen[key])
    return tuple(out)


def join(*vectors: Sequence[int]) -> tuple[int, ...]:
    if not vectors:
        raise ValueError("join of no vectors")
    n = len(vectors[0])
    return partition_of([tuple(v[i] for v in vectors) for i in range(n)])


def block_count(vector: Sequence[int]) -> int:
    return len(set(vector))


def kernel_partition(columns: Sequence[Sequence]) -> tuple[int, ...]:
    if not columns:
        raise ValueError("empty protocol family")
    vectors = [partition_of(c) for c in columns]
    return join(*vectors)


@dataclass
class BatteryResult:
    status: str
    minimum_cost: Optional[Fraction]
    optima: list[tuple[int, ...]]
    explored: int
    note: str = ""


def minimum_cost_battery(columns: Sequence[Sequence], costs: Sequence[Optional[Fraction]],
                         node_cap: int = 400_000) -> BatteryResult:
    usable = [i for i, c in enumerate(costs) if c is not None]
    if not usable:
        return BatteryResult("EXACT", None, [], 0, "no protocol has a declared cost")
    vectors = {i: partition_of(columns[i]) for i in usable}
    target = join(*[vectors[i] for i in usable])
    n = len(target)
    start = tuple([0] * n)

    by_partition: dict[tuple[int, ...], list[int]] = {}
    for i in usable:
        by_partition.setdefault(vectors[i], []).append(i)
    reps: list[tuple[tuple[int, ...], Fraction, list[int]]] = []
    for vector, members in by_partition.items():
        best = min(costs[i] for i in members)
        reps.append((vector, best, [i for i in members if costs[i] == best]))
    reps = [r for r in reps if block_count(r[0]) > 1]
    if not reps:
        return BatteryResult("EXACT", Fraction(0), [()], 0,
                             "the family separates nothing; the empty battery is optimal")
    if start == target:
        return BatteryResult("EXACT", Fraction(0), [()], 0, "nothing to separate")

    dist: dict[tuple[int, ...], Fraction] = {start: Fraction(0)}
    preds: dict[tuple[int, ...], list[tuple[tuple[int, ...], int]]] = {start: []}
    heap: list[tuple[Fraction, int, tuple[int, ...]]] = [(Fraction(0), 0, start)]
    counter = itertools.count(1)
    explored = 0
    settled: set[tuple[int, ...]] = set()
    while heap:
        cost, _, node = heapq.heappop(heap)
        if node in settled:
            continue
        settled.add(node)
        explored += 1
        if explored > node_cap:
            return BatteryResult("UNKNOWN", None, [], explored, "node cap reached")
        if node == target:
            break
        for vector, price, members in reps:
            nxt = join(node, vector)
            if nxt == node:
                continue
            new_cost = cost + price
            old = dist.get(nxt)
            if old is None or new_cost < old:
                dist[nxt] = new_cost
                preds[nxt] = [(node, m) for m in members]
                heapq.heappush(heap, (new_cost, next(counter), nxt))
            elif new_cost == old:
                preds[nxt].extend((node, m) for m in members)
    if target not in dist:
        return BatteryResult("EXACT", None, [], explored,
                             "unreachable: the costed subfamily does not attain the family kernel")

    optima: set[tuple[int, ...]] = set()
    stack: list[tuple[tuple[int, ...], tuple[int, ...]]] = [(target, ())]
    guard = 0
    while stack:
        node, chosen = stack.pop()
        guard += 1
        if guard > node_cap:
            return BatteryResult("UNKNOWN", dist[target], sorted(optima), explored,
                                 "optimum enumeration cap reached")
        if node == start:
            optima.add(tuple(sorted(chosen)))
            continue
        for previous, member in preds.get(node, []):
            if dist[previous] + min(c for v, c, ms in reps if member in ms) == dist[node]:
                stack.append((previous, chosen + (member,)))
    return BatteryResult("EXACT", dist[target], sorted(optima), explored)


@dataclass
class Witness:

    depth: int
    context: Context
    bridge: str
    reason: str
    left: object
    right: object


@dataclass
class GradedRefinement:

    depths: list[int]
    partitions: list[tuple[int, ...]]
    block_counts: list[int]
                                                                             
                                                                
    stabilised_at: Optional[int]
    witnesses: dict[tuple[int, int], Witness]
    first_adjacent_plateau_at: Optional[int] = None


def graded_refinement(ctx: GuaContext, skeleton: Skeleton, states: Sequence[State],
                      bridges: Sequence[str], licence_ceiling: str,
                      max_depth: int,
                      witness_pairs: Optional[Sequence[tuple[int, int]]] = None
                      ) -> GradedRefinement:
    usable = [b for b in bridges
              if LICENCE_ORDER[BRIDGE_LICENCE[b]] <= LICENCE_ORDER[licence_ceiling]]
    if not usable:
        raise ValueError("no licensed bridge under this ceiling")

    contexts_by_depth: list[list[Context]] = []
    all_contexts = enumerate_contexts(ctx, skeleton, max_depth, licence_ceiling)
    for d in range(max_depth + 1):
        contexts_by_depth.append([c for c in all_contexts if c.depth == d])

    partitions: list[tuple[int, ...]] = []
    witnesses: dict[tuple[int, int], Witness] = {}
    running: Optional[tuple[int, ...]] = None
    n = len(states)
    pairs = list(witness_pairs) if witness_pairs is not None else [
        (i, j) for i in range(n) for j in range(i + 1, n)]

    for d in range(max_depth + 1):
        columns: list[tuple[int, ...]] = []
        per_protocol: list[tuple[Context, str, list]] = []
        for context in contexts_by_depth[d]:
            trace = context_trace(ctx, context, skeleton)
            if trace is None:
                continue
            targets = [State(trace.target, trace.apply(s.values)) for s in states]
            for bridge in usable:
                fn = BRIDGES[bridge]
                column = [fn(ctx, t) for t in targets]
                columns.append(partition_of(column))
                per_protocol.append((context, bridge, column))
        if running is None:
            running = join(*columns) if columns else tuple([0] * n)
        elif columns:
            running = join(running, *columns)
        partitions.append(running)
        for i, j in pairs:
            key = (i, j)
            if key in witnesses or running[i] == running[j]:
                continue
            for context, bridge, column in per_protocol:
                if column[i] != column[j]:
                    witnesses[key] = Witness(d, context, bridge, "value",
                                             column[i], column[j])
                    break

    counts = [block_count(p) for p in partitions]
    plateau = None
    for d in range(len(partitions) - 1):
        if partitions[d] == partitions[d + 1]:
            plateau = d
            break
    return GradedRefinement(list(range(max_depth + 1)), partitions, counts,
                            None, witnesses, plateau)
