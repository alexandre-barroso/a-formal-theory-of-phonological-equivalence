from __future__ import annotations

from fractions import Fraction
from typing import Any, Iterable

from .rational import ParseRational, RationalText


Monomial = tuple[int, ...]
Polynomial = dict[Monomial, Fraction]


def NormalizePolynomial(value: dict[Monomial, Fraction]) -> Polynomial:
    return {monomial: coefficient for monomial, coefficient in sorted(value.items()) if coefficient != 0}


def ParsePolynomial(value: dict[str, Any], variables: list[str]) -> Polynomial:
    if set(value) != {"variables", "terms"}:
        raise ValueError("Polynomial fields are not canonical")
    if value["variables"] != variables or len(set(variables)) != len(variables):
        raise ValueError("Polynomial variable declaration mismatch")
    result: Polynomial = {}
    for term in value["terms"]:
        if set(term) != {"coefficient", "powers"} or len(term["powers"]) != len(variables):
            raise ValueError("Malformed sparse polynomial term")
        powers = tuple(term["powers"])
        if any(not isinstance(power, int) or isinstance(power, bool) or power < 0 for power in powers):
            raise ValueError("Polynomial powers must be nonnegative integers")
        coefficient = ParseRational(term["coefficient"])
        result[powers] = result.get(powers, Fraction(0)) + coefficient
    return NormalizePolynomial(result)


def EncodePolynomial(value: Polynomial, variables: list[str]) -> dict[str, Any]:
    normalized = NormalizePolynomial(value)
    return {"variables": variables, "terms": [{"coefficient": RationalText(coefficient), "powers": list(monomial)} for monomial, coefficient in normalized.items()]}


def Add(left: Polynomial, right: Polynomial) -> Polynomial:
    result = dict(left)
    for monomial, coefficient in right.items():
        result[monomial] = result.get(monomial, Fraction(0)) + coefficient
    return NormalizePolynomial(result)


def Negate(value: Polynomial) -> Polynomial:
    return NormalizePolynomial({monomial: -coefficient for monomial, coefficient in value.items()})


def Multiply(left: Polynomial, right: Polynomial) -> Polynomial:
    result: Polynomial = {}
    for left_monomial, left_coefficient in left.items():
        for right_monomial, right_coefficient in right.items():
            monomial = tuple(a + b for a, b in zip(left_monomial, right_monomial, strict=True))
            result[monomial] = result.get(monomial, Fraction(0)) + left_coefficient * right_coefficient
    return NormalizePolynomial(result)


def Power(value: Polynomial, exponent: int) -> Polynomial:
    if exponent < 0:
        raise ValueError("Polynomial exponent must be nonnegative")
    dimension = len(next(iter(value), ()))
    result: Polynomial = {(0,) * dimension: Fraction(1)}
    factor = value
    remaining = exponent
    while remaining:
        if remaining % 2:
            result = Multiply(result, factor)
        factor = Multiply(factor, factor)
        remaining //= 2
    return result


def Evaluate(value: Polynomial, point: Iterable[Fraction]) -> Fraction:
    coordinates = tuple(point)
    return sum(coefficient * Product(coordinate ** power for coordinate, power in zip(coordinates, monomial, strict=True)) for monomial, coefficient in value.items())


def Product(values: Iterable[Fraction]) -> Fraction:
    result = Fraction(1)
    for value in values:
        result *= value
    return result


def Derivative(value: Polynomial, index: int) -> Polynomial:
    result: Polynomial = {}
    for monomial, coefficient in value.items():
        power = monomial[index]
        if power:
            derived = list(monomial)
            derived[index] -= 1
            key = tuple(derived)
            result[key] = result.get(key, Fraction(0)) + coefficient * power
    return NormalizePolynomial(result)
