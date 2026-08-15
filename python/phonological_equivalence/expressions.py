from __future__ import annotations

from fractions import Fraction
from itertools import product
from typing import Any, Mapping

from .rational import ParseRational


def EvaluateExpression(expression: Any, environment: Mapping[str, Any]) -> Any:
    if isinstance(expression, bool):
        return expression
    if isinstance(expression, int) and not isinstance(expression, bool):
        return Fraction(expression)
    if isinstance(expression, str):
        if expression in environment:
            return environment[expression]
        return expression
    if not isinstance(expression, dict) or "node" not in expression:
        raise ValueError("Expression is not a declared AST node")
    node = expression["node"]
    if node == "rational":
        return ParseRational(expression["value"])
    if node == "variable":
        name = expression["name"]
        if name not in environment:
            raise ValueError(f"Undeclared variable: {name}")
        return environment[name]
    if node == "list":
        return [EvaluateExpression(value, environment) for value in expression["values"]]
    if node == "set":
        return frozenset(EvaluateExpression(value, environment) for value in expression["values"])
    if node in {"add", "multiply"}:
        values = [EvaluateExpression(value, environment) for value in expression["arguments"]]
        initial = Fraction(0) if node == "add" else Fraction(1)
        for value in values:
            initial = initial + value if node == "add" else initial * value
        return initial
    if node == "subtract":
        return EvaluateExpression(expression["left"], environment) - EvaluateExpression(expression["right"], environment)
    if node == "divide":
        denominator = EvaluateExpression(expression["right"], environment)
        if denominator == 0:
            raise ZeroDivisionError("Exact AST division by zero")
        return EvaluateExpression(expression["left"], environment) / denominator
    if node == "power":
        base = EvaluateExpression(expression["base"], environment)
        exponent = EvaluateExpression(expression["exponent"], environment)
        if not isinstance(exponent, Fraction) or exponent.denominator != 1:
            raise ValueError("Exact evaluator supports integer powers")
        return base ** exponent.numerator
    if node in {"equal", "not_equal", "less", "less_equal", "greater", "greater_equal"}:
        left = EvaluateExpression(expression["left"], environment)
        right = EvaluateExpression(expression["right"], environment)
        return {"equal": left == right, "not_equal": left != right, "less": left < right, "less_equal": left <= right, "greater": left > right, "greater_equal": left >= right}[node]
    if node == "not":
        return not RequireBoolean(EvaluateExpression(expression["argument"], environment))
    if node in {"and", "or"}:
        values = [RequireBoolean(EvaluateExpression(value, environment)) for value in expression["arguments"]]
        return all(values) if node == "and" else any(values)
    if node == "implies":
        return not RequireBoolean(EvaluateExpression(expression["antecedent"], environment)) or RequireBoolean(EvaluateExpression(expression["consequent"], environment))
    if node == "iff":
        return RequireBoolean(EvaluateExpression(expression["left"], environment)) == RequireBoolean(EvaluateExpression(expression["right"], environment))
    if node == "in":
        return EvaluateExpression(expression["element"], environment) in EvaluateExpression(expression["set"], environment)
    if node == "cardinality":
        return Fraction(len(EvaluateExpression(expression["value"], environment)))
    if node == "sum":
        name = expression["variable"]
        domain = EvaluateFiniteDomain(expression["domain"], environment)
        return sum((EvaluateExpression(expression["body"], {**environment, name: value}) for value in domain), Fraction(0))
    if node in {"forall", "exists"}:
        bindings = expression["bindings"]
        domains = [EvaluateFiniteDomain(binding["domain"], environment) for binding in bindings]
        results = []
        for values in product(*domains):
            local = dict(environment)
            local.update({binding["variable"]: value for binding, value in zip(bindings, values, strict=True)})
            results.append(RequireBoolean(EvaluateExpression(expression["body"], local)))
        return all(results) if node == "forall" else any(results)
    raise ValueError(f"Unknown expression node: {node}")


def EvaluateFiniteDomain(domain: Any, environment: Mapping[str, Any]) -> list[Any]:
    value = EvaluateExpression(domain, environment)
    if not isinstance(value, (list, tuple, frozenset)):
        raise ValueError("Quantifier domain is not finite")
    return sorted(value, key=repr) if isinstance(value, frozenset) else list(value)


def RequireBoolean(value: Any) -> bool:
    if not isinstance(value, bool):
        raise TypeError("Logical expression did not evaluate to Boolean")
    return value


def Variables(expression: Any) -> set[str]:
    if isinstance(expression, list):
        result: set[str] = set()
        for value in expression:
            result.update(Variables(value))
        return result
    if not isinstance(expression, dict):
        return set()
    if expression.get("node") == "variable":
        return {expression["name"]}
    result = set()
    for value in expression.values():
        result.update(Variables(value))
    return result


def FreeVariables(expression: Any, bound: frozenset[str] = frozenset()) -> set[str]:
    if isinstance(expression, list):
        result: set[str] = set()
        for value in expression:
            result.update(FreeVariables(value, bound))
        return result
    if not isinstance(expression, dict):
        return set()
    if expression.get("node") == "variable":
        return set() if expression["name"] in bound else {expression["name"]}
    if expression.get("node") in {"forall", "exists"}:
        names = frozenset(binding["variable"] for binding in expression["bindings"])
        domain_variables: set[str] = set()
        for binding in expression["bindings"]:
            domain_variables.update(FreeVariables(binding["domain"], bound))
        return domain_variables | FreeVariables(expression["body"], bound | names)
    result = set()
    for value in expression.values():
        result.update(FreeVariables(value, bound))
    return result


def Substitute(expression: Any, variable: str, replacement: Any) -> Any:
    if isinstance(expression, list):
        return [Substitute(value, variable, replacement) for value in expression]
    if not isinstance(expression, dict):
        return expression
    if expression.get("node") == "variable" and expression["name"] == variable:
        return replacement
    if expression.get("node") in {"forall", "exists"} and any(binding["variable"] == variable for binding in expression["bindings"]):
        return expression
    replacement_variables = FreeVariables(replacement)
    if expression.get("node") in {"forall", "exists"} and any(binding["variable"] in replacement_variables for binding in expression["bindings"]):
        raise ValueError("Substitution would capture a free variable")
    return {key: Substitute(value, variable, replacement) for key, value in expression.items()}
