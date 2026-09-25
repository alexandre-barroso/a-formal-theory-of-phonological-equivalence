from __future__ import annotations

import json
from fractions import Fraction
from itertools import product
from typing import Any, Mapping

from .rational import ParseRational


UNDEFINED = ("undefined",)


def CanonicalKey(value: Any) -> str:
    def Normalize(child: Any) -> Any:
        if isinstance(child, Fraction):
            return {"fraction": [child.numerator, child.denominator]}
        if isinstance(child, tuple):
            return [Normalize(item) for item in child]
        if isinstance(child, list):
            return [Normalize(item) for item in child]
        if isinstance(child, dict):
            return {str(key): Normalize(item) for key, item in child.items()}
        return child

    return json.dumps(Normalize(value), ensure_ascii=False, sort_keys=True, separators=(",", ":"))


def Unique(values: list[Any]) -> list[Any]:
    by_key = {CanonicalKey(value): value for value in values}
    return [by_key[key] for key in sorted(by_key)]


def MapEntries(value: Any, environment: Mapping[str, Any]) -> list[tuple[Any, Any]]:
    if not isinstance(value, dict) or value.get("node") != "finite_map":
        raise ValueError("Finite-model map is not a finite_map node")
    entries = [(EvaluateFiniteModel(row["key"], environment), EvaluateFiniteModel(row["value"], environment)) for row in value["entries"]]
    keys = [CanonicalKey(key) for key, _ in entries]
    if len(keys) != len(set(keys)):
        raise ValueError("Finite-model map has duplicate keys")
    return entries


def Lookup(value: Any, key: Any, environment: Mapping[str, Any]) -> Any:
    matches = [result for candidate, result in MapEntries(value, environment) if candidate == key]
    return matches[0] if matches else UNDEFINED


def PartitionByMaps(domain: list[Any], observers: list[Any], contexts: list[Any], environment: Mapping[str, Any]) -> list[list[Any]]:
    signatures: dict[str, tuple[Any, list[Any]]] = {}
    for state in domain:
        answers = []
        for context in contexts:
            contextual_state = Lookup(context, state, environment)
            for observer in observers:
                answers.append(Lookup(observer, contextual_state, environment))
        signature = CanonicalKey(answers)
        if signature not in signatures:
            signatures[signature] = (answers, [])
        signatures[signature][1].append(state)
    blocks = [sorted(states, key=CanonicalKey) for _, states in signatures.values()]
    return sorted(blocks, key=CanonicalKey)


def HasReachableCycle(starts: list[Any], edges: list[list[Any]], stops: list[Any]) -> bool:
    adjacency: dict[str, list[Any]] = {}
    values: dict[str, Any] = {}
    for edge in edges:
        source, target = edge[0], edge[-1]
        key = CanonicalKey(source)
        values[key] = source
        adjacency.setdefault(key, []).append(target)
    stop_keys = {CanonicalKey(value) for value in stops}
    reachable: set[str] = set()
    stack = list(starts)
    while stack:
        state = stack.pop()
        key = CanonicalKey(state)
        if key in reachable or key in stop_keys:
            continue
        reachable.add(key)
        stack.extend(adjacency.get(key, []))
    visiting: set[str] = set()
    visited: set[str] = set()

    def Visit(key: str) -> bool:
        if key in visiting:
            return True
        if key in visited or key not in reachable:
            return False
        visiting.add(key)
        for target in adjacency.get(key, []):
            if Visit(CanonicalKey(target)):
                return True
        visiting.remove(key)
        visited.add(key)
        return False

    return any(Visit(key) for key in sorted(reachable))


def BellNumber(size: int) -> int:
    if size < 0:
        raise ValueError("Bell number requires a nonnegative integer")
    row = [1]
    for _ in range(size):
        next_row = [row[-1]]
        for index in range(len(row)):
            next_row.append(next_row[-1] + row[index])
        row = next_row
    return row[0]


def EvaluateFiniteModel(expression: Any, environment: Mapping[str, Any] | None = None) -> Any:
    local = {} if environment is None else environment
    if isinstance(expression, (bool, str)) or expression is None:
        return expression
    if isinstance(expression, int) and not isinstance(expression, bool):
        return Fraction(expression)
    if isinstance(expression, list):
        return [EvaluateFiniteModel(value, local) for value in expression]
    if not isinstance(expression, dict) or "node" not in expression:
        raise ValueError("Finite-model expression is not a declared AST node")
    node = expression["node"]
    if node == "rational":
        return ParseRational(expression["value"])
    if node == "variable":
        if expression["name"] not in local:
            raise ValueError("Finite-model variable is unbound")
        return local[expression["name"]]
    if node == "list":
        return [EvaluateFiniteModel(value, local) for value in expression["values"]]
    if node == "finite_set":
        return Unique([EvaluateFiniteModel(value, local) for value in expression["values"]])
    if node == "finite_map":
        return MapEntries(expression, local)
    if node == "lookup":
        return Lookup(expression["map"], EvaluateFiniteModel(expression["key"], local), local)
    if node == "values":
        return [value for _, value in MapEntries(expression["map"], local)]
    if node == "unique":
        return Unique(EvaluateFiniteModel(expression["value"], local))
    if node == "cardinality":
        return Fraction(len(EvaluateFiniteModel(expression["value"], local)))
    if node in {"add", "multiply"}:
        values = [EvaluateFiniteModel(value, local) for value in expression["arguments"]]
        result = Fraction(0) if node == "add" else Fraction(1)
        for value in values:
            result = result + value if node == "add" else result * value
        return result
    if node == "subtract":
        return EvaluateFiniteModel(expression["left"], local) - EvaluateFiniteModel(expression["right"], local)
    if node in {"equal", "not_equal", "less", "less_equal", "greater", "greater_equal"}:
        left = EvaluateFiniteModel(expression["left"], local)
        right = EvaluateFiniteModel(expression["right"], local)
        return {"equal": left == right, "not_equal": left != right, "less": left < right, "less_equal": left <= right, "greater": left > right, "greater_equal": left >= right}[node]
    if node == "not":
        value = EvaluateFiniteModel(expression["argument"], local)
        if not isinstance(value, bool):
            raise TypeError("Finite-model negation requires Boolean input")
        return not value
    if node in {"and", "or"}:
        values = [EvaluateFiniteModel(value, local) for value in expression["arguments"]]
        if any(not isinstance(value, bool) for value in values):
            raise TypeError("Finite-model connective requires Boolean inputs")
        return all(values) if node == "and" else any(values)
    if node == "conditional":
        condition = EvaluateFiniteModel(expression["condition"], local)
        if not isinstance(condition, bool):
            raise TypeError("Finite-model conditional requires a Boolean condition")
        return EvaluateFiniteModel(expression["then"] if condition else expression["else"], local)
    if node == "set_difference":
        left = EvaluateFiniteModel(expression["left"], local)
        right = {CanonicalKey(value) for value in EvaluateFiniteModel(expression["right"], local)}
        return [value for value in left if CanonicalKey(value) not in right]
    if node == "map_image":
        values = EvaluateFiniteModel(expression["domain"], local)
        return Unique([Lookup(expression["map"], value, local) for value in values])
    if node == "map_set":
        values = EvaluateFiniteModel(expression["set"], local)
        return Unique([Lookup(expression["map"], value, local) for value in values])
    if node == "kernel_partition":
        return PartitionByMaps(EvaluateFiniteModel(expression["domain"], local), expression["observers"], expression["contexts"], local)
    if node == "map_kernel":
        domain = EvaluateFiniteModel(expression["domain"], local)
        return [[left, right] for left in domain for right in domain if Lookup(expression["map"], left, local) == Lookup(expression["map"], right, local)]
    if node == "collision_pairs":
        domain = EvaluateFiniteModel(expression["domain"], local)
        return [[left, right] for index, left in enumerate(domain) for right in domain[index + 1:] if Lookup(expression["map"], left, local) == Lookup(expression["map"], right, local)]
    if node == "frontier":
        domain = EvaluateFiniteModel(expression["domain"], local)
        edges = EvaluateFiniteModel(expression["strict_edges"], local)
        return [value for value in domain if not any(edge[0] == value for edge in edges)]
    if node == "outbound_edges":
        image = {CanonicalKey(value) for value in EvaluateFiniteModel(expression["image"], local)}
        edges = EvaluateFiniteModel(expression["edges"], local)
        return [edge for edge in edges if CanonicalKey(edge[-2]) in image and CanonicalKey(edge[-1]) not in image]
    if node == "graph_has_reachable_cycle":
        return HasReachableCycle(EvaluateFiniteModel(expression["starts"], local), EvaluateFiniteModel(expression["edges"], local), EvaluateFiniteModel(expression["stops"], local))
    if node == "pushforward_sum":
        rows = expression["rows"]
        totals: dict[str, tuple[Any, Fraction]] = {}
        for row in rows:
            key = EvaluateFiniteModel(row["key"], local)
            weight = EvaluateFiniteModel(row["weight"], local)
            canonical = CanonicalKey(key)
            previous = totals.get(canonical, (key, Fraction(0)))[1]
            totals[canonical] = (key, previous + weight)
        return [[key, value] for key, value in (totals[canonical] for canonical in sorted(totals))]
    if node == "select":
        domain = EvaluateFiniteModel(expression["domain"], local)
        variable = expression["variable"]
        return [value for value in domain if EvaluateFiniteModel(expression["predicate"], {**local, variable: value}) is True]
    if node == "bell_number":
        size = EvaluateFiniteModel(expression["size"], local)
        if not isinstance(size, Fraction) or size.denominator != 1:
            raise ValueError("Bell-number argument is not an integer")
        return Fraction(BellNumber(size.numerator))
    if node == "many_sorted_valid":
        structure = expression["structure"]
        carriers = structure["carriers"]
        for operation in structure["operations"]:
            if any(value not in carriers for value in operation["input_sorts"]) or operation["output_sort"] not in carriers:
                return False
            expected = 1
            for value in operation["input_sorts"]:
                expected *= len(carriers[value])
            if len(operation["table"]) != expected:
                return False
            inputs = [tuple(row["inputs"]) for row in operation["table"]]
            complete = list(product(*(carriers[value] for value in operation["input_sorts"])))
            if len(inputs) != len(set(inputs)) or set(inputs) != set(complete):
                return False
            if any(row["output"] not in carriers[operation["output_sort"]] for row in operation["table"]):
                return False
        return True
    if node == "finite_decision":
        contract = expression["contract"]
        required = ["formed", "admitted", "matched_rows", "transport_defined", "scientific_status"]
        if any(value not in contract for value in required) or not contract["formed"] or not contract["admitted"] or not contract["matched_rows"] or not contract["transport_defined"]:
            return ["NOT EVALUATED", contract.get("failure_reason", "MALFORMED CONTRACT"), contract.get("scientific_status", "INCOMPLETE")]
        mismatch = [row for row in contract["matched_rows"] if row["source_answer"] != row["transported_target_answer"]]
        return ["Q-CONSERVATIVE" if not mismatch else "Q-NONCONSERVATIVE", "", contract["scientific_status"]]
    raise ValueError(f"Unknown finite-model node: {node}")
