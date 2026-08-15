from __future__ import annotations

from fractions import Fraction
import re
from typing import Any


def ParseRational(value: Any) -> Fraction:
    if isinstance(value, bool):
        raise TypeError("Boolean is not a rational literal")
    if isinstance(value, int):
        return Fraction(value)
    if isinstance(value, str):
        if any(token in value.lower() for token in [".", "e", "nan", "inf"]):
            raise ValueError("Hidden floating-point literal")
        return Fraction(value)
    raise TypeError("Rational literal must be an integer or exact fraction string")


def RationalText(value: Fraction) -> str:
    return str(value.numerator) if value.denominator == 1 else f"{value.numerator}/{value.denominator}"


def ParseDecimalRational(value: str) -> Fraction:
    match = re.fullmatch(r"([+-]?)(\d+)(?:\.(\d+))?(?:[eE]([+-]?\d+))?", value)
    if match is None:
        raise ValueError("Invalid exact decimal literal")
    sign, whole, fractional, exponent = match.groups()
    digits = whole + (fractional or "")
    scale = len(fractional or "") - int(exponent or "0")
    result = Fraction(int(digits), 10 ** scale) if scale >= 0 else Fraction(int(digits) * 10 ** (-scale))
    return -result if sign == "-" else result
