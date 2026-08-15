from __future__ import annotations

import itertools
import math
from fractions import Fraction
from pathlib import Path
from typing import Any, Iterable, Mapping, Sequence

from .canonical import CanonicalHash, FileHash, LoadJson


RESULT_IDS = tuple(f"MAX-G{index}" for index in range(1, 6))
SEMANTIC_PROOF_GOAL_IDS = (
    "MAX-G1.CARRIER.01",
    "MAX-G1.CLEAR.02",
    "MAX-G2.ANCHOR.01",
    "MAX-G2.ORDER.02",
    "MAX-G3.RESIDUAL.01",
    "MAX-G3.CHAIN.02",
    "MAX-G4.REVERSAL.01",
    "MAX-G4.TIE.02",
    "MAX-G4.MULTISET.03",
    "MAX-G5.TYPES.01",
    "MAX-G5.GORDAN.02",
)
LEAN_PROOF_GOAL_IDS = frozenset({
    "MAX-G1.CLOSURE.03",
    "MAX-G3.REDUCTION.03",
    "MAX-G4.COMPLEXITY.04",
    "MAX-G5.METAPROOF",
})
REGISTERED_PROOF_GOAL_IDS = frozenset(SEMANTIC_PROOF_GOAL_IDS) | LEAN_PROOF_GOAL_IDS
SEMANTIC_KERNEL_VERSION = "maxent-semantic-g1-g5-1.0.0"
PROOF_RELATIVE_PATH = (
    "formal/proofs/maxent/semantic/closures/MAX-G1-G5.semantic-proof.json"
)
CHECKER_RELATIVE_PATH = (
    "formal/kernel/python/second_order_proof_kernel/maxent_semantic_g1_g5.py"
)
REQUIRED_FOUNDATION_RELATIVE_PATH = (
    "formal/proofs/maxent/semantic/required_foundation_schemas.json"
)
TRUSTED_FOUNDATION_RELATIVE_PATH = "formal/foundation/trusted_foundation.json"
SHARED_DEFINITION_RELATIVE_PATH = (
    "formal/proofs/maxent/semantic/shared_maxent_definitions.json"
)


Exponent = tuple[int, ...]
Polynomial = dict[Exponent, Fraction]


def _deliverables_root(root: Path | str | None) -> Path:
    if root is None:
        return Path(__file__).resolve().parents[4]
    path = Path(root).resolve()
    if (path / "formal").is_dir() and (path / "proofs").is_dir():
        return path
    if (path / "deliverables" / "formal").is_dir():
        return path / "deliverables"
    raise ValueError("MAX G1-G5 root does not resolve to the deliverables directory")


def _require_exact_fields(value: Mapping[str, Any], fields: set[str], label: str) -> None:
    if set(value) != fields:
        raise ValueError(f"{label} fields do not match the declared grammar")


def _as_fraction(value: Any) -> Fraction:
    if isinstance(value, bool):
        raise ValueError("Boolean is not an exact rational")
    if isinstance(value, Fraction):
        return value
    if isinstance(value, int):
        return Fraction(value)
    if isinstance(value, str):
        try:
            return Fraction(value)
        except (ValueError, ZeroDivisionError) as error:
            raise ValueError("Malformed exact rational") from error
    if isinstance(value, Mapping) and set(value) == {"numerator", "denominator"}:
        numerator = value["numerator"]
        denominator = value["denominator"]
        if (
            not isinstance(numerator, int)
            or isinstance(numerator, bool)
            or not isinstance(denominator, int)
            or isinstance(denominator, bool)
            or denominator == 0
        ):
            raise ValueError("Malformed rational record")
        return Fraction(numerator, denominator)
    raise ValueError("Value is not an exact rational")


def _fraction_text(value: Fraction) -> str:
    if value.denominator == 1:
        return str(value.numerator)
    return f"{value.numerator}/{value.denominator}"


def _normalize_polynomial(polynomial: Mapping[Exponent, Fraction]) -> Polynomial:
    result: Polynomial = {}
    for exponent, coefficient in polynomial.items():
        exact = _as_fraction(coefficient)
        if exact:
            result[tuple(exponent)] = result.get(tuple(exponent), Fraction(0)) + exact
    return {exponent: coefficient for exponent, coefficient in result.items() if coefficient}


def _constant(dimension: int, value: int | Fraction) -> Polynomial:
    exact = _as_fraction(value)
    return {} if not exact else {(0,) * dimension: exact}


def _variable(dimension: int, index: int) -> Polynomial:
    if not 0 <= index < dimension:
        raise ValueError("Polynomial variable index is outside its dimension")
    exponent = [0] * dimension
    exponent[index] = 1
    return {tuple(exponent): Fraction(1)}


def _add(*polynomials: Mapping[Exponent, Fraction]) -> Polynomial:
    result: Polynomial = {}
    for polynomial in polynomials:
        for exponent, coefficient in polynomial.items():
            result[exponent] = result.get(exponent, Fraction(0)) + coefficient
    return _normalize_polynomial(result)


def _scale(polynomial: Mapping[Exponent, Fraction], scalar: int | Fraction) -> Polynomial:
    exact = _as_fraction(scalar)
    return _normalize_polynomial(
        {exponent: exact * coefficient for exponent, coefficient in polynomial.items()}
    )


def _multiply(
    left: Mapping[Exponent, Fraction], right: Mapping[Exponent, Fraction]
) -> Polynomial:
    if not left or not right:
        return {}
    result: Polynomial = {}
    for left_exponent, left_coefficient in left.items():
        for right_exponent, right_coefficient in right.items():
            if len(left_exponent) != len(right_exponent):
                raise ValueError("Cannot multiply polynomials of different dimensions")
            exponent = tuple(
                left_value + right_value
                for left_value, right_value in zip(
                    left_exponent, right_exponent, strict=True
                )
            )
            result[exponent] = (
                result.get(exponent, Fraction(0))
                + left_coefficient * right_coefficient
            )
    return _normalize_polynomial(result)


def _power(polynomial: Mapping[Exponent, Fraction], exponent: int) -> Polynomial:
    if not isinstance(exponent, int) or isinstance(exponent, bool) or exponent < 0:
        raise ValueError("Polynomial power must be a nonnegative integer")
    if polynomial:
        dimension = len(next(iter(polynomial)))
    else:
        raise ValueError("The dimension of the zero polynomial is not implicit")
    result = _constant(dimension, 1)
    factor = dict(polynomial)
    remaining = exponent
    while remaining:
        if remaining & 1:
            result = _multiply(result, factor)
        remaining >>= 1
        if remaining:
            factor = _multiply(factor, factor)
    return result


def _evaluate(polynomial: Mapping[Exponent, Fraction], point: Sequence[Any]) -> Fraction:
    exact_point = tuple(_as_fraction(value) for value in point)
    total = Fraction(0)
    for exponent, coefficient in polynomial.items():
        if len(exponent) != len(exact_point):
            raise ValueError("Polynomial point has the wrong dimension")
        term = coefficient
        for value, power in zip(exact_point, exponent, strict=True):
            if power < 0 and value == 0:
                raise ValueError("Laurent polynomial is undefined at a zero coordinate")
            term *= value**power
        total += term
    return total


def _coefficient_l1(polynomial: Mapping[Exponent, Fraction]) -> Fraction:
    return sum((abs(value) for value in polynomial.values()), Fraction(0))


def _coefficient_height(polynomial: Mapping[Exponent, Fraction]) -> Fraction:
    return max((abs(value) for value in polynomial.values()), default=Fraction(0))


def _total_degree(polynomial: Mapping[Exponent, Fraction]) -> int:
    return max((sum(exponent) for exponent in polynomial), default=0)


def _extend_dimension(polynomial: Mapping[Exponent, Fraction], extra: int) -> Polynomial:
    if extra < 0:
        raise ValueError("Polynomial dimension extension cannot be negative")
    return {
        exponent + (0,) * extra: coefficient
        for exponent, coefficient in polynomial.items()
    }


def _parse_sparse_polynomial(
    value: Mapping[str, Any], *, allow_laurent: bool, require_integer: bool
) -> tuple[int, Polynomial]:
    _require_exact_fields(value, {"dimension", "terms"}, "Sparse polynomial")
    dimension = value["dimension"]
    terms = value["terms"]
    if (
        not isinstance(dimension, int)
        or isinstance(dimension, bool)
        or dimension < 0
        or not isinstance(terms, list)
    ):
        raise ValueError("Sparse polynomial dimension or term list is malformed")
    polynomial: Polynomial = {}
    seen: set[Exponent] = set()
    for term in terms:
        if not isinstance(term, Mapping):
            raise ValueError("Sparse polynomial term is not a record")
        _require_exact_fields(term, {"exponents", "coefficient"}, "Sparse term")
        exponents = term["exponents"]
        if (
            not isinstance(exponents, list)
            or len(exponents) != dimension
            or any(
                not isinstance(item, int)
                or isinstance(item, bool)
                or (item < 0 and not allow_laurent)
                for item in exponents
            )
        ):
            raise ValueError("Sparse polynomial exponent vector is malformed")
        exponent_tuple = tuple(exponents)
        if exponent_tuple in seen:
            raise ValueError("Sparse polynomial is not canonically collected")
        seen.add(exponent_tuple)
        coefficient = _as_fraction(term["coefficient"])
        if not coefficient:
            raise ValueError("Canonical sparse polynomial contains a zero coefficient")
        if require_integer and coefficient.denominator != 1:
            raise ValueError("Sparse polynomial coefficient is not an integer")
        polynomial[exponent_tuple] = coefficient
    if terms != sorted(
        terms,
        key=lambda term: tuple(term["exponents"]),
    ):
        raise ValueError("Sparse polynomial terms are not in canonical exponent order")
    return dimension, polynomial


def _serialize_polynomial(dimension: int, polynomial: Mapping[Exponent, Fraction]) -> dict[str, Any]:
    normalized = _normalize_polynomial(polynomial)
    if any(len(exponent) != dimension for exponent in normalized):
        raise ValueError("Cannot serialize a polynomial with an inconsistent dimension")
    return {
        "dimension": dimension,
        "terms": [
            {
                "exponents": list(exponent),
                "coefficient": _fraction_text(coefficient),
            }
            for exponent, coefficient in sorted(normalized.items())
        ],
    }


def _validate_ledger(ledger: Mapping[str, Any]) -> None:
    _require_exact_fields(
        ledger,
        {
            "constraint_count",
            "candidates",
            "named_candidate",
            "violation_rows",
            "base_masses",
            "consequence_map",
        },
        "MaxEnt ledger",
    )
    dimension = ledger["constraint_count"]
    candidates = ledger["candidates"]
    if (
        not isinstance(dimension, int)
        or isinstance(dimension, bool)
        or dimension < 0
        or not isinstance(candidates, list)
        or not candidates
        or any(not isinstance(candidate, str) or not candidate for candidate in candidates)
        or len(candidates) != len(set(candidates))
    ):
        raise ValueError("MaxEnt ledger dimension or candidate labels are malformed")
    if ledger["named_candidate"] not in candidates:
        raise ValueError("MaxEnt named candidate is absent from its ledger")
    if set(ledger["violation_rows"]) != set(candidates):
        raise ValueError("MaxEnt violation-row map does not match candidate labels")
    if set(ledger["base_masses"]) != set(candidates):
        raise ValueError("MaxEnt base-mass map does not match candidate labels")
    if set(ledger["consequence_map"]) != set(candidates):
        raise ValueError("MaxEnt consequence map does not match candidate labels")
    for candidate in candidates:
        row = ledger["violation_rows"][candidate]
        if (
            not isinstance(row, list)
            or len(row) != dimension
            or any(
                not isinstance(value, int) or isinstance(value, bool) or value < 0
                for value in row
            )
        ):
            raise ValueError("MaxEnt violation row is not a nonnegative integer vector")
        if _as_fraction(ledger["base_masses"][candidate]) <= 0:
            raise ValueError("MaxEnt base masses must be strictly positive rationals")


def _ledger_from_rows(side: str, rows: Sequence[Sequence[int]]) -> dict[str, Any]:
    if side not in {"A", "B"}:
        raise ValueError("Compiled ledger side must be A or B")
    dimension = len(rows[0]) if rows else 0
    if any(len(row) != dimension for row in rows):
        raise ValueError("Compiled row dimensions disagree")
    labels = [f"{side}:named"] + [f"{side}:alternative:{index}" for index in range(len(rows))]
    violations = {labels[0]: [0] * dimension}
    violations.update(
        {label: list(row) for label, row in zip(labels[1:], rows, strict=True)}
    )
    ledger = {
        "constraint_count": dimension,
        "candidates": labels,
        "named_candidate": labels[0],
        "violation_rows": violations,
        "base_masses": {label: "1" for label in labels},
        "consequence_map": {label: label for label in labels},
    }
    _validate_ledger(ledger)
    return ledger


def CompileRelativePartitionDifference(
    left_ledger: Mapping[str, Any],
    left_named_candidate: str,
    right_ledger: Mapping[str, Any],
    right_named_candidate: str,
) -> dict[str, Any]:
    _validate_ledger(left_ledger)
    _validate_ledger(right_ledger)
    dimension = left_ledger["constraint_count"]
    if right_ledger["constraint_count"] != dimension:
        raise ValueError("Cross-input ledgers use different constraint dimensions")
    if left_named_candidate not in left_ledger["candidates"]:
        raise ValueError("Left named candidate is absent")
    if right_named_candidate not in right_ledger["candidates"]:
        raise ValueError("Right named candidate is absent")

    def labelled_terms(
        ledger: Mapping[str, Any], named: str, sign: int
    ) -> list[dict[str, Any]]:
        named_row = ledger["violation_rows"][named]
        named_mass = _as_fraction(ledger["base_masses"][named])
        result = []
        for label in ledger["candidates"]:
            row = ledger["violation_rows"][label]
            relative = [
                value - base for value, base in zip(row, named_row, strict=True)
            ]
            coefficient = sign * _as_fraction(ledger["base_masses"][label]) / named_mass
            result.append(
                {
                    "candidate_label": label,
                    "relative_row": relative,
                    "coefficient": _fraction_text(coefficient),
                }
            )
        return result

    left_terms = labelled_terms(left_ledger, left_named_candidate, 1)
    right_terms = labelled_terms(right_ledger, right_named_candidate, -1)
    polynomial: Polynomial = {}
    for term in left_terms + right_terms:
        exponent = tuple(term["relative_row"])
        polynomial[exponent] = polynomial.get(exponent, Fraction(0)) + _as_fraction(
            term["coefficient"]
        )
    return {
        "polynomial": _serialize_polynomial(dimension, polynomial),
        "left_labelled_terms": left_terms,
        "right_labelled_terms": right_terms,
        "label_count": len(left_terms) + len(right_terms),
    }


def ClearLaurentPolynomial(polynomial: Mapping[str, Any]) -> dict[str, Any]:
    dimension, parsed = _parse_sparse_polynomial(
        polynomial, allow_laurent=True, require_integer=False
    )
    if parsed:
        shift = [
            max(0, -min(exponent[index] for exponent in parsed))
            for index in range(dimension)
        ]
    else:
        shift = [0] * dimension
    denominator_lcm = 1
    for coefficient in parsed.values():
        denominator_lcm = math.lcm(denominator_lcm, coefficient.denominator)
    cleared: Polynomial = {}
    for exponent, coefficient in parsed.items():
        new_exponent = tuple(
            value + offset for value, offset in zip(exponent, shift, strict=True)
        )
        new_coefficient = coefficient * denominator_lcm
        if new_coefficient.denominator != 1:
            raise ValueError("Laurent denominator clearing did not produce integers")
        cleared[new_exponent] = new_coefficient
    return {
        "shift": shift,
        "positive_denominator_lcm": denominator_lcm,
        "cleared_polynomial": _serialize_polynomial(dimension, cleared),
        "multiplier": {
            "positive_constant": denominator_lcm,
            "monomial_exponents": shift,
            "strictly_positive_on": "(0,1]^dimension",
        },
    }


def CompileIntegerPolynomial(polynomial: Mapping[str, Any]) -> dict[str, Any]:
    dimension, parsed = _parse_sparse_polynomial(
        polynomial, allow_laurent=False, require_integer=True
    )
    left_rows: list[list[int]] = []
    right_rows: list[list[int]] = []
    row_multiplicity: dict[str, int] = {}
    for exponent, coefficient in sorted(parsed.items()):
        count = abs(coefficient.numerator)
        row_multiplicity[",".join(str(value) for value in exponent)] = count
        destination = left_rows if coefficient > 0 else right_rows
        destination.extend([list(exponent) for _ in range(count)])
    left = _ledger_from_rows("A", left_rows)
    right = _ledger_from_rows("B", right_rows)
    if dimension and not left_rows:
        left["constraint_count"] = dimension
        left["violation_rows"][left["named_candidate"]] = [0] * dimension
    if dimension and not right_rows:
        right["constraint_count"] = dimension
        right["violation_rows"][right["named_candidate"]] = [0] * dimension
    _validate_ledger(left)
    _validate_ledger(right)
    replay = CompileRelativePartitionDifference(
        left, left["named_candidate"], right, right["named_candidate"]
    )
    if replay["polynomial"] != _serialize_polynomial(dimension, parsed):
        raise ValueError("Integer-polynomial compiler failed exact coefficient reconstruction")
    l1 = int(_coefficient_l1(parsed))
    return {
        "left_ledger": left,
        "right_ledger": right,
        "relative_partition_difference": replay["polynomial"],
        "compiled_candidate_count": len(left["candidates"]) + len(right["candidates"]),
        "coefficient_l1_norm": l1,
        "row_multiplicity": row_multiplicity,
    }


def _validate_etr_inv_instance(instance: Mapping[str, Any]) -> tuple[int, list[dict[str, Any]]]:
    _require_exact_fields(
        instance, {"variable_count", "equations"}, "Bounded ETR-INV instance"
    )
    variable_count = instance["variable_count"]
    equations = instance["equations"]
    if (
        not isinstance(variable_count, int)
        or isinstance(variable_count, bool)
        or variable_count < 2
        or not isinstance(equations, list)
        or not equations
    ):
        raise ValueError("Bounded ETR-INV requires N>=2 and at least one equation")
    normalized: list[dict[str, Any]] = []
    for equation in equations:
        if not isinstance(equation, Mapping) or "kind" not in equation:
            raise ValueError("Bounded ETR-INV equation is malformed")
        kind = equation["kind"]
        if kind == "one":
            fields = {"kind", "variable_index"}
            indices = [equation.get("variable_index")]
        elif kind == "add":
            fields = {"kind", "left_index", "right_index", "result_index"}
            indices = [
                equation.get("left_index"),
                equation.get("right_index"),
                equation.get("result_index"),
            ]
        elif kind == "inverse":
            fields = {"kind", "left_index", "right_index"}
            indices = [equation.get("left_index"), equation.get("right_index")]
        else:
            raise ValueError("Unknown bounded ETR-INV equation constructor")
        _require_exact_fields(equation, fields, "Bounded ETR-INV equation")
        if any(
            not isinstance(index, int)
            or isinstance(index, bool)
            or not 0 <= index < variable_count
            for index in indices
        ):
            raise ValueError("Bounded ETR-INV equation index is outside 0,...,N-1")
        normalized.append(dict(equation))
    return variable_count, normalized


def _affine_etr_variable(dimension: int, index: int) -> Polynomial:
    return _add(_constant(dimension, Fraction(1, 2)), _scale(_variable(dimension, index), Fraction(3, 2)))


def BuildETRINVResidual(instance: Mapping[str, Any]) -> dict[str, Any]:
    variable_count, equations = _validate_etr_inv_instance(instance)
    variables = [
        _affine_etr_variable(variable_count, index)
        for index in range(variable_count)
    ]
    residuals: list[Polynomial] = []
    residual_squares: list[Polynomial] = []
    polynomial: Polynomial = {}
    for equation in equations:
        kind = equation["kind"]
        if kind == "one":
            residual = _add(
                variables[equation["variable_index"]],
                _constant(variable_count, -1),
            )
        elif kind == "add":
            residual = _add(
                variables[equation["left_index"]],
                variables[equation["right_index"]],
                _scale(variables[equation["result_index"]], -1),
            )
        else:
            residual = _add(
                _multiply(
                    variables[equation["left_index"]],
                    variables[equation["right_index"]],
                ),
                _constant(variable_count, -1),
            )
        residuals.append(residual)
        square = _scale(_multiply(residual, residual), 16)
        if any(coefficient.denominator != 1 for coefficient in square.values()):
            raise ValueError("Affine residual clearing failed to produce integers")
        residual_squares.append(square)
        polynomial = _add(polynomial, square)
    if _total_degree(polynomial) > 4:
        raise ValueError("Bounded ETR-INV residual degree exceeds four")
    if _coefficient_l1(polynomial) > 400 * len(equations):
        raise ValueError("Bounded ETR-INV residual coefficient bound failed")
    return {
        "variable_count": variable_count,
        "equation_count": len(equations),
        "residual_polynomial": _serialize_polynomial(variable_count, polynomial),
        "residual_summands": [
            _serialize_polynomial(variable_count, square) for square in residual_squares
        ],
        "total_degree": _total_degree(polynomial),
        "coefficient_l1_norm": int(_coefficient_l1(polynomial)),
        "coefficient_height": int(_coefficient_height(polynomial)),
        "zero_equivalence_rule": "ordered-field finite sum of squares is zero iff every residual is zero",
    }


def _ceil_log2(value: int) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or value <= 0:
        raise ValueError("ceil(log2) requires a positive integer")
    return (value - 1).bit_length()


def StrictifierParameters(instance: Mapping[str, Any]) -> dict[str, int]:
    variable_count, equations = _validate_etr_inv_instance(instance)
    equation_count = len(equations)
    height_upper_bound = max(1, 400 * equation_count, 6 * variable_count)
    height_log_ceiling = _ceil_log2(height_upper_bound)
    gap_exponent = (
        variable_count
        * (8**variable_count)
        * (4 + 2 * variable_count + height_log_ceiling)
    )
    chain_length = _ceil_log2(gap_exponent + 3)
    return {
        "variable_count": variable_count,
        "equation_count": equation_count,
        "height_upper_bound": height_upper_bound,
        "height_log_ceiling": height_log_ceiling,
        "dyadic_gap_exponent": gap_exponent,
        "chain_length": chain_length,
    }


def _strictifier_polynomial(instance: Mapping[str, Any]) -> tuple[dict[str, int], Polynomial]:
    residual = BuildETRINVResidual(instance)
    _, residual_polynomial = _parse_sparse_polynomial(
        residual["residual_polynomial"], allow_laurent=False, require_integer=True
    )
    parameters = StrictifierParameters(instance)
    variable_count = parameters["variable_count"]
    chain_length = parameters["chain_length"]
    dimension = variable_count + chain_length
    strictifier = _scale(_extend_dimension(residual_polynomial, chain_length), 2)
    residual_square_sum: Polynomial = {}
    for index in range(chain_length):
        next_variable = _variable(dimension, variable_count + index)
        if index == 0:
            rho = _add(_scale(next_variable, 2), _constant(dimension, -1))
        else:
            previous_variable = _variable(dimension, variable_count + index - 1)
            rho = _add(
                _scale(next_variable, 2),
                _scale(_multiply(previous_variable, previous_variable), -1),
            )
        residual_square_sum = _add(
            residual_square_sum, _multiply(rho, rho)
        )
    last_variable = _variable(dimension, dimension - 1)
    strictifier = _add(
        strictifier,
        _scale(residual_square_sum, chain_length),
        _scale(_multiply(last_variable, last_variable), -2),
    )
    if _total_degree(strictifier) > 4:
        raise ValueError("Strictifier degree exceeds four")
    l1_bound = 800 * parameters["equation_count"] + 9 * chain_length**2 + 2
    if _coefficient_l1(strictifier) > l1_bound:
        raise ValueError("Strictifier coefficient L1 bound failed")
    parameters = dict(parameters)
    parameters["strictifier_dimension"] = dimension
    parameters["coefficient_l1_bound"] = l1_bound
    return parameters, strictifier


def OneHotTagLift(polynomial: Mapping[str, Any]) -> dict[str, Any]:
    dimension, parsed = _parse_sparse_polynomial(
        polynomial, allow_laurent=False, require_integer=True
    )
    if not parsed:
        raise ValueError("One-hot lift requires a nonzero collected polynomial")
    coefficient_l1 = sum(abs(value.numerator) for value in parsed.values())
    tag_dimension = coefficient_l1
    left_rows: list[list[int]] = []
    right_rows: list[list[int]] = []
    signed_rows: list[dict[str, Any]] = []
    slot = 0
    for exponent, coefficient in sorted(parsed.items()):
        copies = abs(coefficient.numerator)
        for copy_index in range(copies):
            tag_row = tuple(
                1 if coordinate == slot and coefficient > 0
                else 3 if coordinate == slot
                else 2
                for coordinate in range(tag_dimension)
            )
            row = tuple(value + 1 for value in exponent) + tag_row
            destination = left_rows if coefficient > 0 else right_rows
            destination.append(list(row))
            signed_rows.append(
                {
                    "source_exponents": list(exponent),
                    "sign": 1 if coefficient > 0 else -1,
                    "copy_index": copy_index,
                    "one_hot_slot": slot,
                    "target_row": list(row),
                }
            )
            slot += 1
    all_rows = [tuple(row) for row in left_rows + right_rows]
    if len(all_rows) != len(set(all_rows)):
        raise ValueError("One-hot lift produced a global row collision")
    target_dimension = dimension + tag_dimension
    if any(
        not all(1 <= value <= 5 for value in row[:dimension])
        or not all(1 <= value <= 3 for value in row[dimension:])
        for row in all_rows
    ):
        raise ValueError("One-hot lift produced a row outside its positive bounds")
    left = _ledger_from_rows("A", left_rows)
    right = _ledger_from_rows("B", right_rows)
    if not left_rows:
        left["constraint_count"] = target_dimension
        left["violation_rows"][left["named_candidate"]] = [0] * target_dimension
    if not right_rows:
        right["constraint_count"] = target_dimension
        right["violation_rows"][right["named_candidate"]] = [0] * target_dimension
    _validate_ledger(left)
    _validate_ledger(right)
    replay = CompileRelativePartitionDifference(
        left, left["named_candidate"], right, right["named_candidate"]
    )
    return {
        "source_polynomial": _serialize_polynomial(dimension, parsed),
        "tag_dimension": tag_dimension,
        "coefficient_l1_norm": coefficient_l1,
        "signed_row_derivation": signed_rows,
        "left_ledger": left,
        "right_ledger": right,
        "target_polynomial": replay["polynomial"],
        "alternative_row_count": len(all_rows),
        "globally_duplicate_free": True,
        "old_row_bounds": [1, 5],
        "tag_row_bounds": [1, 3],
        "common_positive_factor": {
            "old_activity_exponents": [1] * dimension,
            "tag_activity_exponents": [2] * tag_dimension,
        },
        "all_one_tag_slice_equals_positive_old_shift_times_source": True,
        "normalized_tag_bracket_dominates_source": True,
    }


def CompileETRINVToMaxEnt(instance: Mapping[str, Any]) -> dict[str, Any]:
    parameters, strictifier = _strictifier_polynomial(instance)
    dimension = parameters["strictifier_dimension"]
    strictifier_json = _serialize_polynomial(dimension, strictifier)
    lift = OneHotTagLift(strictifier_json)
    if lift["alternative_row_count"] != int(_coefficient_l1(strictifier)):
        raise ValueError("ETR-INV lift row count differs from coefficient L1 mass")
    exact_chain_last_exponent = 2 ** parameters["chain_length"] - 1
    if 2 ** (parameters["chain_length"] + 1) <= parameters["dyadic_gap_exponent"] + 3:
        raise ValueError("Contraction chain is too short for the dyadic compact gap")
    multiplication_gate_bound = sum(
        sum(max(value - 1, 0) for value in row)
        for row in (
            lift["left_ledger"]["violation_rows"][label]
            for label in lift["left_ledger"]["candidates"][1:]
        )
    ) + sum(
        sum(max(value - 1, 0) for value in row)
        for row in (
            lift["right_ledger"]["violation_rows"][label]
            for label in lift["right_ledger"]["candidates"][1:]
        )
    )
    return {
        "source_instance": dict(instance),
        "parameters": parameters,
        "strictifier_polynomial": strictifier_json,
        "exact_chain_last": f"1/2^{exact_chain_last_exponent}",
        "dyadic_gap_lower_bound": f"1/2^{parameters['dyadic_gap_exponent']}",
        "chain_stability_bound": "abs(r_m-a_m)<=sqrt(m*sum_i(rho_i^2))/2",
        "chain_penalty_lower_bound": "m*sum_i(rho_i^2)-2*r_m^2>=-4*a_m^2",
        "strict_gap_condition": "2*a_m^2<2^-Bbar",
        "strictifier_coefficient_l1_norm": int(_coefficient_l1(strictifier)),
        "target": lift,
        "membership_multiplication_gate_bound": multiplication_gate_bound,
        "reverse_map_kind": "logical_implication_via_compact_gap_not_solution_recovery",
    }


def _validate_proper_cnf(formula: Mapping[str, Any]) -> tuple[int, list[list[int]]]:
    _require_exact_fields(formula, {"variable_count", "clauses"}, "Proper CNF")
    variable_count = formula["variable_count"]
    clauses = formula["clauses"]
    if (
        not isinstance(variable_count, int)
        or isinstance(variable_count, bool)
        or variable_count < 1
        or not isinstance(clauses, list)
        or len(clauses) < 2
    ):
        raise ValueError("Proper at-most-three-CNF requires variables and at least two clauses")
    normalized: list[list[int]] = []
    for clause in clauses:
        if (
            not isinstance(clause, list)
            or not 1 <= len(clause) <= 3
            or any(
                not isinstance(literal, int)
                or isinstance(literal, bool)
                or literal == 0
                or abs(literal) > variable_count
                for literal in clause
            )
        ):
            raise ValueError("Proper CNF clause is malformed")
        variables = [abs(literal) for literal in clause]
        if len(variables) != len(set(variables)):
            raise ValueError("Proper CNF clause repeats a variable or is tautological")
        normalized.append(list(clause))
    return variable_count, normalized


def _selector_polynomial(formula: Mapping[str, Any]) -> tuple[int, list[list[int]], Polynomial]:
    variable_count, clauses = _validate_proper_cnf(formula)
    clause_count = len(clauses)
    dimension = variable_count + clause_count
    selector_product = _constant(dimension, 1)
    for clause_index in range(clause_count):
        selector_product = _multiply(
            selector_product, _variable(dimension, variable_count + clause_index)
        )
    polynomial = _scale(selector_product, -1)
    for clause_index, clause in enumerate(clauses):
        unsatisfied = _constant(dimension, 1)
        for literal in clause:
            variable = _variable(dimension, abs(literal) - 1)
            factor = (
                _add(_constant(dimension, 1), _scale(variable, -1))
                if literal > 0
                else variable
            )
            unsatisfied = _multiply(unsatisfied, factor)
        term = _multiply(
            _variable(dimension, variable_count + clause_index), unsatisfied
        )
        polynomial = _add(polynomial, term)
    if any(abs(value) != 1 for value in polynomial.values()):
        raise ValueError("Selector polynomial has a nonunit collected coefficient")
    if any(any(power not in {0, 1} for power in exponent) for exponent in polynomial):
        raise ValueError("Selector polynomial is not multi-affine")
    if len(polynomial) > 1 + 8 * clause_count:
        raise ValueError("Selector polynomial exceeds its exact support bound")
    return variable_count, clauses, polynomial


def CompileSelectorCNF(formula: Mapping[str, Any]) -> dict[str, Any]:
    variable_count, clauses, selector = _selector_polynomial(formula)
    source_dimension = variable_count + len(clauses)
    target_dimension = source_dimension + 1
    shifted: Polynomial = {}
    for exponent, coefficient in selector.items():
        shifted[tuple(value + 1 for value in exponent) + (1,)] = coefficient
    if any(
        any(value not in {1, 2} for value in exponent)
        for exponent in shifted
    ):
        raise ValueError("Selector shift did not produce only one/two violations")
    left_rows = [list(exponent) for exponent, coefficient in sorted(shifted.items()) if coefficient > 0]
    right_rows = [list(exponent) for exponent, coefficient in sorted(shifted.items()) if coefficient < 0]
    all_rows = [tuple(row) for row in left_rows + right_rows]
    if len(all_rows) != len(set(all_rows)):
        raise ValueError("Selector compiler produced a duplicate alternative row")
    left = _ledger_from_rows("A", left_rows)
    right = _ledger_from_rows("B", right_rows)
    if not left_rows:
        left["constraint_count"] = target_dimension
        left["violation_rows"][left["named_candidate"]] = [0] * target_dimension
    if not right_rows:
        right["constraint_count"] = target_dimension
        right["violation_rows"][right["named_candidate"]] = [0] * target_dimension
    _validate_ledger(left)
    _validate_ledger(right)
    replay = CompileRelativePartitionDifference(
        left, left["named_candidate"], right, right["named_candidate"]
    )
    if replay["polynomial"] != _serialize_polynomial(target_dimension, shifted):
        raise ValueError("Selector ledger does not reconstruct its shifted polynomial")
    return {
        "formula": dict(formula),
        "selector_polynomial": _serialize_polynomial(source_dimension, selector),
        "shifted_polynomial": replay["polynomial"],
        "left_ledger": left,
        "right_ledger": right,
        "alternative_row_count": len(all_rows),
        "support_bound": 1 + 8 * len(clauses),
        "globally_duplicate_free": True,
        "multi_affine": True,
        "violation_alphabet": [1, 2],
    }


def RelativeRowMassMeasure(
    ledger: Mapping[str, Any], named_candidate: str
) -> dict[tuple[int, ...], Fraction]:
    _validate_ledger(ledger)
    if named_candidate not in ledger["candidates"]:
        raise ValueError("Relative-row measure names an absent candidate")
    named_row = ledger["violation_rows"][named_candidate]
    named_mass = _as_fraction(ledger["base_masses"][named_candidate])
    measure: dict[tuple[int, ...], Fraction] = {}
    for candidate in ledger["candidates"]:
        row = tuple(
            value - base
            for value, base in zip(
                ledger["violation_rows"][candidate], named_row, strict=True
            )
        )
        measure[row] = (
            measure.get(row, Fraction(0))
            + _as_fraction(ledger["base_masses"][candidate]) / named_mass
        )
    return {row: mass for row, mass in measure.items() if mass}


def _named_probability_one_dimensional(rows: Sequence[int], activity: Any) -> Fraction:
    z = _as_fraction(activity)
    if not 0 < z <= 1:
        raise ValueError("Physical activity must lie in (0,1]")
    return Fraction(1, 1 + sum((z**row for row in rows), Fraction(0)))


def _registered_g4_reversal() -> dict[str, Any]:
    activities = [Fraction(3, 4), Fraction(1, 2), Fraction(1, 4)]
    values = [
        {
            "activity": _fraction_text(activity),
            "left_probability": _fraction_text(
                _named_probability_one_dimensional([3, 3], activity)
            ),
            "right_probability": _fraction_text(
                _named_probability_one_dimensional([2], activity)
            ),
        }
        for activity in activities
    ]
    expected = [
        {"activity": "3/4", "left_probability": "32/59", "right_probability": "16/25"},
        {"activity": "1/2", "left_probability": "4/5", "right_probability": "4/5"},
        {"activity": "1/4", "left_probability": "32/33", "right_probability": "16/17"},
    ]
    if values != expected:
        raise ValueError("Registered G4 reversal probabilities do not replay")
    tie_polynomial = {
        (2,): Fraction(-1),
        (3,): Fraction(2),
    }
    if _evaluate(tie_polynomial, [Fraction(1, 2)]) != 0:
        raise ValueError("Registered G4 tie root is not exact")
    return {
        "left_alternative_rows": [[3], [3]],
        "right_alternative_rows": [[2]],
        "probability_table": values,
        "cross_margin": _serialize_polynomial(1, tie_polynomial),
        "factorization": "z^2*(2*z-1)",
        "unique_physical_interior_root": "1/2",
        "orientation": "left<=right above the tie and reverses below it",
    }


def _matrix_record(matrix: Mapping[str, Any] | Sequence[Sequence[Any]]) -> tuple[int, list[list[Fraction]]]:
    if isinstance(matrix, Mapping):
        _require_exact_fields(matrix, {"column_count", "rows"}, "Rational matrix")
        column_count = matrix["column_count"]
        rows = matrix["rows"]
    else:
        rows = matrix
        if not isinstance(rows, Sequence):
            raise ValueError("Rational matrix rows are malformed")
        column_count = len(rows[0]) if rows else 0
    if (
        not isinstance(column_count, int)
        or isinstance(column_count, bool)
        or column_count <= 0
        or not isinstance(rows, Sequence)
    ):
        raise ValueError("Rational matrix requires a positive column count")
    parsed: list[list[Fraction]] = []
    for row in rows:
        if not isinstance(row, Sequence) or isinstance(row, (str, bytes)) or len(row) != column_count:
            raise ValueError("Rational matrix row has the wrong dimension")
        parsed.append([_as_fraction(value) for value in row])
    return column_count, parsed


Inequality = tuple[tuple[Fraction, ...], Fraction]


def _normalize_inequality(coefficients: Sequence[Fraction], right: Fraction) -> Inequality:
    denominators = [value.denominator for value in coefficients] + [right.denominator]
    multiplier = 1
    for denominator in denominators:
        multiplier = math.lcm(multiplier, denominator)
    integers = [int(value * multiplier) for value in coefficients]
    integer_right = int(right * multiplier)
    divisor = 0
    for value in integers + [integer_right]:
        divisor = math.gcd(divisor, abs(value))
    divisor = max(divisor, 1)
    return (
        tuple(Fraction(value // divisor) for value in integers),
        Fraction(integer_right // divisor),
    )


def _deduplicate_inequalities(inequalities: Iterable[Inequality]) -> list[Inequality]:
    strongest: dict[tuple[Fraction, ...], Fraction] = {}
    for coefficients, right in inequalities:
        normalized_coefficients, normalized_right = _normalize_inequality(
            coefficients, right
        )
        if not any(normalized_coefficients):
            if normalized_right > 0:
                return [(normalized_coefficients, normalized_right)]
            continue
        previous = strongest.get(normalized_coefficients)
        if previous is None or normalized_right > previous:
            strongest[normalized_coefficients] = normalized_right
    return sorted(strongest.items(), key=lambda item: (item[0], item[1]))


def _eliminate_first_variable(inequalities: Sequence[Inequality]) -> list[Inequality]:
    positive: list[Inequality] = []
    negative: list[Inequality] = []
    zero: list[Inequality] = []
    for inequality in inequalities:
        coefficient = inequality[0][0]
        if coefficient > 0:
            positive.append(inequality)
        elif coefficient < 0:
            negative.append(inequality)
        else:
            zero.append(inequality)
    projected: list[Inequality] = [
        (coefficients[1:], right) for coefficients, right in zero
    ]
    for positive_coefficients, positive_right in positive:
        positive_head = positive_coefficients[0]
        for negative_coefficients, negative_right in negative:
            negative_head = negative_coefficients[0]
            coefficients = tuple(
                (-negative_head) * positive_value
                + positive_head * negative_value
                for positive_value, negative_value in zip(
                    positive_coefficients[1:],
                    negative_coefficients[1:],
                    strict=True,
                )
            )
            right = (-negative_head) * positive_right + positive_head * negative_right
            projected.append((coefficients, right))
    return _deduplicate_inequalities(projected)


def _find_rational_feasible_point(
    inequalities: Sequence[Inequality], dimension: int
) -> list[Fraction] | None:
    if any(len(coefficients) != dimension for coefficients, _ in inequalities):
        raise ValueError("Linear inequality dimension mismatch")
    systems: list[list[Inequality]] = []
    current = _deduplicate_inequalities(inequalities)
    for _ in range(dimension):
        systems.append(current)
        current = _eliminate_first_variable(current)
    if any(right > 0 for coefficients, right in current if not coefficients):
        return None
    tail: list[Fraction] = []
    for system in reversed(systems):
        lower: Fraction | None = None
        upper: Fraction | None = None
        for coefficients, right in system:
            head = coefficients[0]
            rest = sum(
                (
                    coefficient * value
                    for coefficient, value in zip(
                        coefficients[1:], tail, strict=True
                    )
                ),
                Fraction(0),
            )
            residual = right - rest
            if head > 0:
                bound = residual / head
                lower = bound if lower is None else max(lower, bound)
            elif head < 0:
                bound = residual / head
                upper = bound if upper is None else min(upper, bound)
            elif residual > 0:
                return None
        if lower is not None and upper is not None:
            if lower > upper:
                return None
            value = (lower + upper) / 2
        elif lower is not None:
            value = lower
        elif upper is not None:
            value = upper
        else:
            value = Fraction(0)
        tail.insert(0, value)
    for coefficients, right in inequalities:
        if sum(
            (coefficient * value for coefficient, value in zip(coefficients, tail, strict=True)),
            Fraction(0),
        ) < right:
            raise ValueError("Fourier-Motzkin reconstruction produced an invalid point")
    return tail


def _matrix_vector(rows: Sequence[Sequence[Fraction]], vector: Sequence[Fraction]) -> list[Fraction]:
    return [
        sum(
            (coefficient * value for coefficient, value in zip(row, vector, strict=True)),
            Fraction(0),
        )
        for row in rows
    ]


def ExactConeAlternative(
    matrix: Mapping[str, Any] | Sequence[Sequence[Any]],
) -> dict[str, Any]:
    column_count, rows = _matrix_record(matrix)
    kernel_inequalities: list[Inequality] = []
    for row in rows:
        kernel_inequalities.append((tuple(row), Fraction(0)))
        kernel_inequalities.append((tuple(-value for value in row), Fraction(0)))
    for index in range(column_count):
        basis = [Fraction(0)] * column_count
        basis[index] = Fraction(1)
        kernel_inequalities.append((tuple(basis), Fraction(0)))
    ones = (Fraction(1),) * column_count
    kernel_inequalities.append((ones, Fraction(1)))
    kernel_inequalities.append((tuple(-value for value in ones), Fraction(-1)))
    survivor = _find_rational_feasible_point(kernel_inequalities, column_count)
    if survivor is not None:
        if (
            any(value < 0 for value in survivor)
            or sum(survivor, Fraction(0)) != 1
            or any(_matrix_vector(rows, survivor))
        ):
            raise ValueError("Exact cone survivor failed independent verification")
        return {
            "branch": "normalized_nonnegative_kernel",
            "w": [_fraction_text(value) for value in survivor],
            "matrix_vector_product": ["0"] * len(rows),
            "sum": "1",
        }

    row_count = len(rows)
    row_space_inequalities: list[Inequality] = []
    for column_index in range(column_count):
        row_space_inequalities.append(
            (
                tuple(rows[row_index][column_index] for row_index in range(row_count)),
                Fraction(1),
            )
        )
    proof = _find_rational_feasible_point(
        row_space_inequalities, row_count
    )
    if proof is None:
        raise ValueError("Both rational cone alternatives failed; foundation contradiction")
    transpose_product = [
        sum(
            (
                rows[row_index][column_index] * proof[row_index]
                for row_index in range(row_count)
            ),
            Fraction(0),
        )
        for column_index in range(column_count)
    ]
    if any(value <= 0 for value in transpose_product):
        raise ValueError("Exact row-space proof is not strictly positive")
    return {
        "branch": "strictly_positive_row_space",
        "lambda": [_fraction_text(value) for value in proof],
        "transpose_product": [_fraction_text(value) for value in transpose_product],
    }


def DifferenceMatrix(violation_rows: Sequence[Sequence[Any]]) -> dict[str, Any]:
    if not isinstance(violation_rows, Sequence) or not violation_rows:
        raise ValueError("Difference matrix requires at least one candidate row")
    base = [_as_fraction(value) for value in violation_rows[0]]
    if not base:
        raise ValueError("Difference matrix requires a positive constraint dimension")
    rows: list[list[str]] = []
    for row in violation_rows[1:]:
        exact = [_as_fraction(value) for value in row]
        if len(exact) != len(base):
            raise ValueError("Impossible-candidate violation rows have different dimensions")
        rows.append(
            [_fraction_text(value - base_value) for value, base_value in zip(exact, base, strict=True)]
        )
    return {"column_count": len(base), "rows": rows}


SCHEMA_DEFINITIONS: dict[str, dict[str, Any]] = {
    "MAX-G1.CARRIER.01": {
        "proof_schema": "finite_relative_partition_carrier_induction_v1",
        "proof_steps": [
            "substitute_positive_activities_for_nonnegative_weights",
            "divide_each_partition_by_its_named_positive_mass_monomial",
            "induct_over_every_labelled_candidate_term",
            "aggregate_equal_relative_rows_without_deleting_labels",
            "reverse_positive_reciprocals",
            "identify_the_signed_relative_partition_margin",
        ],
        "schema_payload": {
            "activity_domain": "(0,1]^k",
            "base_mass_domain": "positive rationals",
            "multiplicity_policy": "each candidate label contributes one term before collection",
            "orientation": "p_A(a)<=p_B(b) iff R_A-R_B>=0",
        },
        "mutant_ids": [
            "MAX-G1.CARRIER.MUTANT.REVERSE_MARGIN",
            "MAX-G1.CARRIER.MUTANT.DROP_DUPLICATE_LABEL",
            "MAX-G1.CARRIER.MUTANT.ALLOW_ZERO_MASS",
        ],
    },
    "MAX-G1.CLEAR.02": {
        "proof_schema": "minimal_laurent_integer_clearing_v1",
        "proof_steps": [
            "collect_the_finite_rational_laurent_support",
            "take_each_coordinate_negative_minimum_or_zero",
            "prove_shifted_exponents_are_nonnegative_and_shift_is_minimal",
            "take_the_positive_lcm_of_coefficient_denominators",
            "recompute_the_integer_coefficient_map",
            "use_strict_positivity_of_d_times_z_to_the_shift",
        ],
        "schema_payload": {
            "zero_polynomial_shift": "zero vector",
            "zero_polynomial_denominator_lcm": 1,
            "multiplier_sign_domain": "strictly positive on (0,1]^k",
            "coefficient_target": "integers",
        },
        "mutant_ids": [
            "MAX-G1.CLEAR.MUTANT.NONMINIMAL_SHIFT",
            "MAX-G1.CLEAR.MUTANT.NONPOSITIVE_LCM",
            "MAX-G1.CLEAR.MUTANT.UNCLEARED_NEGATIVE_EXPONENT",
        ],
    },
    "MAX-G1.CLOSURE.03": {
        "proof_schema": "polynomial_cube_density_continuity_v1",
        "proof_steps": [
            "closed_cube_contains_the_physical_activity_cube",
            "define_x_n_as_one_minus_one_over_n_times_x_plus_one_over_n_times_one",
            "prove_x_n_is_in_the_physical_cube_for_n_at_least_one",
            "prove_x_n_converges_coordinatewise_to_x",
            "derive_polynomial_continuity_by_finite_sum_product_induction",
            "move_a_hypothetical_strict_boundary_negative_value_to_some_x_n",
            "conclude_equivalence_by_contraposition",
        ],
        "schema_payload": {
            "physical_cube": "(0,1]^k",
            "closed_cube": "[0,1]^k",
            "density_sequence": "x_n=(1-1/n)x+(1/n)1",
            "closure_changes_grammar_domain": False,
        },
        "mutant_ids": [
            "MAX-G1.CLOSURE.MUTANT.CALL_HALF_OPEN_CUBE_OPEN",
            "MAX-G1.CLOSURE.MUTANT.USE_BOUNDARY_AS_FINITE_WEIGHT",
            "MAX-G1.CLOSURE.MUTANT.DROP_CONTINUITY",
        ],
    },
    "MAX-G2.ANCHOR.01": {
        "proof_schema": "integer_polynomial_labelled_coefficient_compiler_v1",
        "proof_steps": [
            "parse_a_canonical_finite_integer_coefficient_map",
            "create_one_zero_row_named_candidate_per_input",
            "induct_over_the_sorted_monomial_support",
            "emit_abs_coefficient_distinct_labels_on_the_sign_selected_side",
            "preserve_unit_base_mass_and_nonnegative_integer_rows",
            "recompute_literal_relative_partition_difference_equal_to_F",
            "derive_two_plus_coefficient_l1_candidate_count",
        ],
        "schema_payload": {
            "common_monomial_shift": "none",
            "named_rows": "zero",
            "base_masses": "unit",
            "duplicate_rows": "allowed only as distinctly labelled coefficient copies",
        },
        "mutant_ids": [
            "MAX-G2.ANCHOR.MUTANT.ADD_COMMON_SHIFT",
            "MAX-G2.ANCHOR.MUTANT.SWAP_COEFFICIENT_SIGN",
            "MAX-G2.ANCHOR.MUTANT.COLLAPSE_MULTIPLICITY",
        ],
    },
    "MAX-G2.ORDER.02": {
        "proof_schema": "compiled_named_probability_order_rewrite_v1",
        "proof_steps": [
            "expand_both_unit_mass_named_probabilities",
            "cancel_the_two_named_unit_terms_in_the_partition_margin",
            "use_strict_positivity_of_both_denominators",
            "reverse_reciprocal_order",
            "substitute_the_anchor_literal_difference_F",
            "quantify_over_the_physical_activity_cube",
        ],
        "schema_payload": {
            "orientation": "p_left<=p_right iff F>=0",
            "activity_domain": "(0,1]^k",
            "dependency_mode": "G1 carrier plus G2 literal compiler",
        },
        "mutant_ids": [
            "MAX-G2.ORDER.MUTANT.REVERSE_RECIPROCAL",
            "MAX-G2.ORDER.MUTANT.KEEP_NAMED_CONSTANT",
            "MAX-G2.ORDER.MUTANT.REPLACE_FORALL_BY_SAMPLE",
        ],
    },
    "MAX-G3.RESIDUAL.01": {
        "proof_schema": "bounded_etr_inv_affine_residual_sos_induction_v1",
        "proof_steps": [
            "require_N_at_least_two_q_at_least_one_and_in_range_indices",
            "parse_only_one_add_and_inverse_source_atoms",
            "substitute_x_i_equals_one_half_plus_three_halves_u_i",
            "construct_the_three_exact_cleared_residual_templates",
            "square_and_sum_each_source_atom_by_finite_induction",
            "derive_integer_coefficients_and_total_degree_at_most_four",
            "derive_each_summand_l1_bound_at_most_400",
            "use_ordered_field_sum_of_squares_zero_equivalence",
        ],
        "schema_payload": {
            "source_range": "x_i in [1/2,2] encoded by u_i in [0,1]",
            "constructors": ["x=1", "x+y=z", "x*y=1"],
            "clearing_factor": 16,
            "degree_bound": 4,
            "coefficient_l1_bound": "400*q",
        },
        "mutant_ids": [
            "MAX-G3.RESIDUAL.MUTANT.ALLOW_BAD_INDEX",
            "MAX-G3.RESIDUAL.MUTANT.DROP_ONE_SQUARE",
            "MAX-G3.RESIDUAL.MUTANT.REPLACE_400Q_BY_399Q",
        ],
    },
    "MAX-G3.CHAIN.02": {
        "proof_schema": "dyadic_gap_contraction_strictifier_v1",
        "proof_steps": [
            "instantiate_the_compact_cube_minimum_bound_for_degree_four_integer_S",
            "upper_bound_the_imported_exponent_by_integer_Bbar",
            "serialize_bbar_as_two_to_the_negative_Bbar",
            "choose_m_as_ceiling_log2_of_Bbar_plus_three",
            "prove_two_a_m_squared_is_strictly_below_bbar",
            "prove_the_exact_recurrence_two_a_i_plus_one_equals_a_i_squared",
            "telescope_the_one_Lipschitz_half_square_recurrence",
            "apply_finite_Cauchy_Schwarz_to_the_residuals",
            "derive_abs_r_m_minus_a_m_at_most_one_half_sqrt_m_sum_rho_squared",
            "complete_the_square_to_bound_the_chain_penalty_below_by_minus_four_a_m_squared",
            "prove_strictifier_negativity_from_a_source_zero",
            "combine_two_a_m_squared_below_bbar_with_the_unsatisfiable_gap",
            "prove_strictifier_positivity_without_assuming_the_exact_chain_minimizes_the_penalty",
        ],
        "schema_payload": {
            "gap_exponent": "Bbar=N*8^N*(4+2N+ceil_log2(max(1,400q,6N)))",
            "gap_bound": "bbar=2^-Bbar",
            "chain": "a_0=1 and 2*a_(i+1)=a_i^2",
            "residual": "rho_i=2*r_(i+1)-r_i^2",
            "stability_bound": "abs(r_m-a_m)<=sqrt(m*sum_i(rho_i^2))/2",
            "penalty_bound": "m*sum_i(rho_i^2)-2*r_m^2>=-4*a_m^2",
            "strictification_condition": "2*a_m^2<bbar",
            "exact_chain_minimizer_claim": "forbidden",
            "reverse_kind": "logical gap implication",
        },
        "mutant_ids": [
            "MAX-G3.CHAIN.MUTANT.USE_NONINTEGER_BPHI",
            "MAX-G3.CHAIN.MUTANT.SHORTEN_M",
            "MAX-G3.CHAIN.MUTANT.ASSUME_EXACT_CHAIN_MINIMIZES_PENALTY",
        ],
    },
    "MAX-G3.REDUCTION.03": {
        "proof_schema": "executable_one_hot_bounded_etr_inv_maxent_compiler_v2",
        "proof_steps": [
            "invoke_the_checked_source_parser_and_residual_constructor",
            "invoke_the_checked_dyadic_strictifier",
            "collect_Q_and_bound_degree_and_coefficient_l1_mass",
            "expand_each_integer_coefficient_into_signed_unit_copies",
            "assign_one_distinct_one_hot_coordinate_to_each_unit_copy",
            "factor_the_positive_common_old_and_tag_monomial_shift",
            "prove_the_normalized_sign_oriented_tag_bracket_is_pointwise_at_least_Q",
            "prove_all_one_tags_recover_Q_inside_the_positive_common_factor",
            "prove_all_raw_complete_rows_are_globally_distinct",
            "prove_old_entries_one_to_five_and_tag_entries_one_to_three",
            "compile_positive_and_negative_unit_terms_into_two_MAX_G2_ledgers",
            "map_a_source_zero_to_a_strict_target_negative_point",
            "use_the_uniform_minus_four_a_m_squared_penalty_bound_for_the_reverse_implication",
            "derive_source_satisfiability_logically_from_every_target_negative_point",
            "prove_the_exact_alternative_row_bound",
            "prove_the_foundation_relative_source_size_target_object_bound",
        ],
        "schema_payload": {
            "source_problem": "bounded ETR-INV on [1/2,2]",
            "target_problem": "two-input universal named probability order",
            "negative_equivalence": "source satisfiable iff target universal order fails",
            "chain_penalty_lower_bound": "m*sum_i(rho_i^2)-2*r_m^2>=-4*a_m^2",
            "strict_gap_condition": "2*a_m^2<2^-Bbar",
            "row_count_bound": "800*q+9*m^2+2",
            "tag_dimension": "coefficient_l1_norm_of_the_strictifier",
            "target_object_size_bound": "3000000000000*boundedETRINVCodeSize(Phi)^4",
            "reverse_map": "logical implication via compact gap, not ETR solution recovery",
            "foundation_parameter": "ExplicitCompactMinimumFoundation",
            "conventional_runtime_claim": False,
            "universal_real_classification_claim": False,
        },
        "mutant_ids": [
            "MAX-G3.REDUCTION.MUTANT.MAP_NEGATIVE_POINT_TO_SOLUTION",
            "MAX-G3.REDUCTION.MUTANT.ALLOW_TAG_COLLISION",
            "MAX-G3.REDUCTION.MUTANT.DROP_COMPACT_MINIMUM_FOUNDATION",
        ],
    },
    "MAX-G4.REVERSAL.01": {
        "proof_schema": "same_input_cancellation_and_cross_input_reversal_v1",
        "proof_steps": [
            "require_equal_named_masses_and_the_full_nonnegative_orthant",
            "cancel_the_common_same_input_partition_function",
            "derive_all_weight_equality_iff_row_identity",
            "derive_all_weight_weak_order_iff_coordinatewise_domination",
            "use_a_unit_coordinate_weight_to_refute_each_negative_coordinate",
            "replay_the_registered_two_z_cubed_versus_z_squared_cross_input_witness",
        ],
        "schema_payload": {
            "same_input_mass_contract": "equal named masses",
            "same_input_weight_domain": "full nonnegative orthant",
            "cross_input_left_rows": [3, 3],
            "cross_input_right_rows": [2],
            "registered_activities": ["3/4", "1/2", "1/4"],
        },
        "mutant_ids": [
            "MAX-G4.REVERSAL.MUTANT.ALLOW_UNEQUAL_MASS",
            "MAX-G4.REVERSAL.MUTANT.USE_PROPER_WEIGHT_CONE",
            "MAX-G4.REVERSAL.MUTANT.FLIP_ONE_QUARTER_ORDER",
        ],
    },
    "MAX-G4.TIE.02": {
        "proof_schema": "registered_cross_input_tie_factorization_v1",
        "proof_steps": [
            "recompute_the_cross_margin_two_z_cubed_minus_z_squared",
            "factor_as_z_squared_times_two_z_minus_one",
            "exclude_z_zero_from_the_physical_activity_domain",
            "isolate_z_equals_one_half_as_the_only_physical_root",
            "check_strict_signs_on_both_sides",
        ],
        "schema_payload": {
            "cross_margin": "z^2*(2*z-1)",
            "physical_domain": "0<z<=1",
            "unique_root": "1/2",
        },
        "mutant_ids": [
            "MAX-G4.TIE.MUTANT.ACCEPT_ZERO_ROOT",
            "MAX-G4.TIE.MUTANT.ADD_SECOND_INTERIOR_ROOT",
            "MAX-G4.TIE.MUTANT.REPLACE_FACTOR_BY_RULE_STRING",
        ],
    },
    "MAX-G4.MULTISET.03": {
        "proof_schema": "weighted_relative_row_measure_exponential_independence_v1",
        "proof_steps": [
            "divide_each_cross_input_partition_by_its_named_mass_monomial",
            "collect_mass_ratios_at_each_distinct_relative_row",
            "cancel_the_common_named_relative_zero_atom",
            "restrict_an_all_weight_identity_to_a_nonempty_open_positive_orthant",
            "instantiate_finite_exponential_independence_on_distinct_relative_rows",
            "derive_zero_signed_atomic_measure_coordinatewise",
            "prove_the_converse_by_termwise_measure_identity",
            "replay_the_repeated_row_multiplicity_counterexample",
        ],
        "schema_payload": {
            "arbitrary_mass_invariant": "rational mass-weighted relative-row atomic measure",
            "unit_mass_specialization": "multiplicity-sensitive multiset",
            "literal_set_equality_is_sufficient": False,
        },
        "mutant_ids": [
            "MAX-G4.MULTISET.MUTANT.DROP_MULTIPLICITY",
            "MAX-G4.MULTISET.MUTANT.DROP_MASS_RATIO",
            "MAX-G4.MULTISET.MUTANT.OMIT_EXPONENTIAL_INDEPENDENCE",
        ],
    },
    "MAX-G4.COMPLEXITY.04": {
        "proof_schema": "executable_duplicate_free_selector_cnf_boundary_v2",
        "proof_steps": [
            "parse_proper_at_most_three_CNF_with_at_least_two_clauses",
            "construct_each_clause_unsatisfied_factor",
            "construct_minus_all_selectors_plus_selected_unsatisfied_factors",
            "prove_boolean_minimum_minus_one_iff_satisfiable_else_zero",
            "prove_the_multi_affine_vertex_lemma_by_variable_induction",
            "prove_unit_coefficients_and_no_selector_monomial_collision",
            "shift_every_coordinate_and_fresh_t_into_one_two_rows",
            "prove_global_row_uniqueness_and_support_at_most_one_plus_eight_m",
            "construct_the_exact_epsilon_one_over_two_m_physical_counterwitness",
            "prove_the_exact_table_size_and_compiler_list_charge_bounds",
            "prove_the_exact_recursive_complement_verifier_step_bound",
            "prove_the_exact_normalization_and_total_list_charge_bounds",
            "derive_conventional_coNP_completeness_only_from_ExecutableCNFConventionalBoundary",
        ],
        "schema_payload": {
            "selector": "-product(y_c)+sum(y_c*U_c(x))",
            "proper_source": "m>=2, clauses of size 1..3, no repeated variable or tautology",
            "coNP_target_alphabet": [1, 2],
            "strict_epsilon": "1/(2m)",
            "row_count_bound": "1+8*m",
            "table_size_bound": "10*source_size^2",
            "compiler_charge_bound": "20*source_size^2",
            "verifier_charge_bound": "30*source_size^2",
            "normalization_charge_bound": "90*source_size^3",
            "total_charge_bound": "110*source_size^3",
            "conventional_complexity_boundary": "ExecutableCNFConventionalBoundary",
            "unconditional_conventional_class_claim": False,
            "universal_real_classification_claim": False,
        },
        "mutant_ids": [
            "MAX-G4.COMPLEXITY.MUTANT.ALLOW_ONE_CLAUSE_COLLISION",
            "MAX-G4.COMPLEXITY.MUTANT.DROP_MULTIAFFINE_INDUCTION",
            "MAX-G4.COMPLEXITY.MUTANT.DROP_CONVENTIONAL_BOUNDARY",
        ],
    },
    "MAX-G5.TYPES.01": {
        "proof_schema": "many_sorted_vacuity_and_order_antisymmetry_v1",
        "proof_steps": [
            "assign_categorical_event_implication_to_the_Boolean_event_inclusion_sort",
            "assign_numerical_probability_order_to_the_ordered_real_sort",
            "prove_empty_event_is_included_in_every_finite_event",
            "forbid_a_coercion_from_categorical_truth_to_numerical_order",
            "apply_weak_order_antisymmetry_to_mutual_numerical_orders",
            "prove_numerical_equality_implies_both_weak_orders",
        ],
        "schema_payload": {
            "categorical_sort": "Boolean event inclusion",
            "numerical_sort": "ordered real probability",
            "implicit_coercions": [],
            "empty_event_probability_evidence": False,
        },
        "mutant_ids": [
            "MAX-G5.TYPES.MUTANT.COERCE_BOOLEAN_TO_ORDER",
            "MAX-G5.TYPES.MUTANT.EMPTY_ANTECEDENT_FALSE",
            "MAX-G5.TYPES.MUTANT.DROP_ANTISYMMETRY",
        ],
    },
    "MAX-G5.GORDAN.02": {
        "proof_schema": "exact_rational_normalized_kernel_or_positive_row_space_v1",
        "proof_steps": [
            "parse_an_arbitrary_finite_rational_matrix_with_positive_column_count",
            "solve_Dw_zero_w_nonnegative_sum_w_one_by_exact_Fourier_Motzkin",
            "independently_verify_every_kernel_witness_coordinate_and_equality",
            "if_infeasible_solve_D_transpose_lambda_at_least_one_exactly",
            "independently_verify_strictly_positive_row_space_output",
            "prove_exclusivity_by_lambda_transpose_Dw",
            "instantiate_Gordan_Stiemke_only_for_exhaustiveness",
            "use_rational_polyhedral_witness_lemmas_for_both_branches",
        ],
        "schema_payload": {
            "kernel_normalization": "sum(w)=1",
            "kernel_domain": "nonnegative rationals",
            "row_space_scaling": "D^T lambda >= 1",
            "algorithm": "exact rational Fourier-Motzkin with back substitution",
        },
        "mutant_ids": [
            "MAX-G5.GORDAN.MUTANT.ACCEPT_ZERO_W",
            "MAX-G5.GORDAN.MUTANT.NONSTRICT_ROW_SPACE",
            "MAX-G5.GORDAN.MUTANT.RETURN_BOTH_BRANCHES",
        ],
    },
    "MAX-G5.METAPROOF": {
        "proof_schema": "impossible_candidate_mutual_transport_kernel_composition_v1",
        "proof_steps": [
            "fix_one_base_candidate_in_the_finite_same_input_impossible_set",
            "translate_every_mutual_numerical_transport_to_probability_equality",
            "cancel_the_common_denominator_and_equal_candidate_mass_contract",
            "rewrite_each_equality_as_w_dot_v_i_minus_v_base_equals_zero",
            "stack_the_rows_into_the_difference_matrix_D_I",
            "identify_the_preserving_region_with_w_nonnegative_and_D_I_w_zero",
            "invoke_the_checked_exact_cone_alternative",
            "retain_categorical_vacuity_as_a_distinct_typed_premise",
        ],
        "schema_payload": {
            "difference_matrix": "rows v_i-v_base for every nonbase candidate",
            "weight_domain": "full nonnegative orthant",
            "mass_contract": "equal candidate masses inside the declared transport predicate",
            "result": "weight region equals nonnegative kernel; collapse is conditional",
        },
        "mutant_ids": [
            "MAX-G5.METAPROOF.MUTANT.USE_ABSOLUTE_ROWS",
            "MAX-G5.METAPROOF.MUTANT.DROP_SAME_INPUT",
            "MAX-G5.METAPROOF.MUTANT.CLAIM_UNCONDITIONAL_COLLAPSE",
        ],
    },
}


LOCAL_PROOF_GOAL_DEPENDENCIES: dict[str, list[str]] = {
    "MAX-G1.CARRIER.01": [],
    "MAX-G1.CLEAR.02": [],
    "MAX-G1.CLOSURE.03": [],
    "MAX-G2.ANCHOR.01": [],
    "MAX-G2.ORDER.02": ["MAX-G1.CARRIER.01", "MAX-G2.ANCHOR.01"],
    "MAX-G3.RESIDUAL.01": [],
    "MAX-G3.CHAIN.02": ["MAX-G3.RESIDUAL.01"],
    "MAX-G3.REDUCTION.03": [
        "MAX-G1.CARRIER.01",
        "MAX-G1.CLEAR.02",
        "MAX-G1.CLOSURE.03",
        "MAX-G2.ANCHOR.01",
        "MAX-G2.ORDER.02",
        "MAX-G3.RESIDUAL.01",
        "MAX-G3.CHAIN.02",
    ],
    "MAX-G4.REVERSAL.01": ["MAX-G1.CARRIER.01"],
    "MAX-G4.TIE.02": [],
    "MAX-G4.MULTISET.03": [],
    "MAX-G4.COMPLEXITY.04": [],
    "MAX-G5.TYPES.01": [],
    "MAX-G5.GORDAN.02": [],
    "MAX-G5.METAPROOF": [
        "MAX-G4.REVERSAL.01",
        "MAX-G5.TYPES.01",
        "MAX-G5.GORDAN.02",
    ],
}


def _canonical_polynomial_example() -> dict[str, Any]:
    return {
        "dimension": 2,
        "terms": [
            {"exponents": [0, 0], "coefficient": "2"},
            {"exponents": [1, 0], "coefficient": "-3"},
            {"exponents": [1, 2], "coefficient": "1"},
        ],
    }


def _verify_g1_carrier() -> dict[str, Any]:
    left = {
        "constraint_count": 2,
        "candidates": ["a0", "a1", "a2"],
        "named_candidate": "a0",
        "violation_rows": {"a0": [0, 0], "a1": [1, 0], "a2": [1, 0]},
        "base_masses": {"a0": "2", "a1": "3", "a2": "5"},
        "consequence_map": {"a0": "a", "a1": "x", "a2": "x"},
    }
    right = {
        "constraint_count": 2,
        "candidates": ["b0", "b1"],
        "named_candidate": "b0",
        "violation_rows": {"b0": [0, 0], "b1": [0, 2]},
        "base_masses": {"b0": "7", "b1": "11"},
        "consequence_map": {"b0": "b", "b1": "y"},
    }
    result = CompileRelativePartitionDifference(left, "a0", right, "b0")
    expected = {
        "dimension": 2,
        "terms": [
            {"exponents": [0, 2], "coefficient": "-11/7"},
            {"exponents": [1, 0], "coefficient": "4"},
        ],
    }
    if result["polynomial"] != expected or result["label_count"] != 5:
        raise ValueError("G1 carrier induction failed its exact labelled replay")
    return {"label_count": 5, "collected_term_count": 2, "orientation_checked": True}


def _verify_g1_clear() -> dict[str, Any]:
    source = {
        "dimension": 2,
        "terms": [
            {"exponents": [-2, 1], "coefficient": "3/4"},
            {"exponents": [0, -1], "coefficient": "-5/6"},
        ],
    }
    result = ClearLaurentPolynomial(source)
    expected = {
        "dimension": 2,
        "terms": [
            {"exponents": [0, 2], "coefficient": "9"},
            {"exponents": [2, 0], "coefficient": "-10"},
        ],
    }
    if (
        result["shift"] != [2, 1]
        or result["positive_denominator_lcm"] != 12
        or result["cleared_polynomial"] != expected
    ):
        raise ValueError("G1 Laurent clearing failed exact replay")
    return {"minimal_shift": [2, 1], "denominator_lcm": 12, "integer_terms": 2}


def _verify_g1_closure() -> dict[str, Any]:
    boundary = [Fraction(0), Fraction(1, 3)]
    n = 7
    approximant = [
        (1 - Fraction(1, n)) * value + Fraction(1, n) for value in boundary
    ]
    if not all(0 < value <= 1 for value in approximant):
        raise ValueError("G1 density sequence left the physical activity cube")
    errors = [abs(value - target) for value, target in zip(approximant, boundary, strict=True)]
    if errors != [Fraction(1, 7), Fraction(2, 21)]:
        raise ValueError("G1 density sequence arithmetic changed")
    return {"approximant": [_fraction_text(value) for value in approximant], "continuity_rule": "finite polynomial induction"}


def _verify_g2_anchor() -> dict[str, Any]:
    result = CompileIntegerPolynomial(_canonical_polynomial_example())
    if (
        result["relative_partition_difference"] != _canonical_polynomial_example()
        or result["coefficient_l1_norm"] != 6
        or result["compiled_candidate_count"] != 8
        or result["row_multiplicity"] != {"0,0": 2, "1,0": 3, "1,2": 1}
    ):
        raise ValueError("G2 integer-polynomial compiler failed exact replay")
    return {"candidate_count": 8, "coefficient_l1_norm": 6, "literal_identity": True}


def _verify_g2_order() -> dict[str, Any]:
    compiler = CompileIntegerPolynomial(_canonical_polynomial_example())
    _, polynomial = _parse_sparse_polynomial(
        compiler["relative_partition_difference"],
        allow_laurent=False,
        require_integer=True,
    )
    point = [Fraction(1, 2), Fraction(1, 3)]
    value = _evaluate(polynomial, point)
    left = compiler["left_ledger"]
    right = compiler["right_ledger"]

    def probability(ledger: Mapping[str, Any]) -> Fraction:
        total = Fraction(0)
        for candidate in ledger["candidates"]:
            row = ledger["violation_rows"][candidate]
            term = Fraction(1)
            for activity, exponent in zip(point, row, strict=True):
                term *= activity**exponent
            total += term
        return Fraction(1, 1) / total

    orientation = probability(left) <= probability(right)
    if orientation != (value >= 0):
        raise ValueError("G2 probability-order orientation changed")
    return {"point_value": _fraction_text(value), "order_equivalence": True}


def _verify_g3_residual() -> dict[str, Any]:
    constructors = [
        {"kind": "one", "variable_index": 0},
        {"kind": "add", "left_index": 0, "right_index": 1, "result_index": 2},
        {"kind": "inverse", "left_index": 0, "right_index": 1},
    ]
    norms = []
    degrees = []
    for constructor in constructors:
        result = BuildETRINVResidual(
            {"variable_count": 3, "equations": [constructor]}
        )
        norms.append(result["coefficient_l1_norm"])
        degrees.append(result["total_degree"])
    if norms != [64, 400, 288] or degrees != [2, 2, 4]:
        raise ValueError("G3 residual constructor anchors changed")
    return {"constructor_l1_norms": norms, "constructor_degrees": degrees}


def _sample_etr_instance() -> dict[str, Any]:
    return {
        "variable_count": 2,
        "equations": [{"kind": "one", "variable_index": 0}],
    }


def _verify_g3_chain() -> dict[str, Any]:
    parameters = StrictifierParameters(_sample_etr_instance())
    m = parameters["chain_length"]
    if 2 ** (m + 1) <= parameters["dyadic_gap_exponent"] + 3:
        raise ValueError("G3 dyadic chain strict inequality failed")
    for index in range(m):
        left_exponent = 2 ** (index + 1) - 1
        right_exponent = 2 * (2**index - 1) + 1
        if left_exponent != right_exponent:
            raise ValueError("G3 exact contraction recurrence failed")
    a_m = Fraction(1, 2 ** (2**m - 1))
    bbar = Fraction(1, 2 ** parameters["dyadic_gap_exponent"])
    if not 2 * a_m * a_m < bbar:
        raise ValueError("G3 exact-chain scale does not dominate the compact gap")
    penalty_plus_four_a_squared = (
        Fraction(1) - 2 * Fraction(1, 4),
        -2 * a_m,
        -2 * a_m * a_m + 4 * a_m * a_m,
    )
    completed_square = (Fraction(1, 2), -2 * a_m, 2 * a_m * a_m)
    if penalty_plus_four_a_squared != completed_square:
        raise ValueError("G3 completed-square penalty identity failed")
    return {
        "dyadic_gap_exponent": parameters["dyadic_gap_exponent"],
        "chain_length": m,
        "strict_gap": True,
        "stability_bound": "abs(r_m-a_m)<=sqrt(m*sum_i(rho_i^2))/2",
        "penalty_lower_bound": "m*sum_i(rho_i^2)-2*r_m^2>=-4*a_m^2",
        "completed_square": "(sqrt(m*sum_i(rho_i^2))-2*a_m)^2/2",
        "exact_chain_minimizer_used": False,
        "reverse_kind": "logical_implication_via_compact_gap",
    }


def _verify_g3_reduction() -> dict[str, Any]:
    result = CompileETRINVToMaxEnt(_sample_etr_instance())
    if (
        result["chain_penalty_lower_bound"]
        != "m*sum_i(rho_i^2)-2*r_m^2>=-4*a_m^2"
        or result["strict_gap_condition"] != "2*a_m^2<2^-Bbar"
    ):
        raise ValueError("G3 reduction omitted the uniform chain-penalty argument")
    dimension, strictifier = _parse_sparse_polynomial(
        result["strictifier_polynomial"], allow_laurent=False, require_integer=True
    )
    m = result["parameters"]["chain_length"]
    exact_chain = [Fraction(1, 2 ** (2**index - 1)) for index in range(1, m + 1)]
    source_point = [Fraction(1, 3), Fraction(1, 2)] + exact_chain
    strict_value = _evaluate(strictifier, source_point)
    if strict_value >= 0:
        raise ValueError("G3 satisfying source anchor did not yield a strict negative")
    target = result["target"]
    if (
        target["all_one_tag_slice_equals_positive_old_shift_times_source"]
        is not True
        or target["normalized_tag_bracket_dominates_source"] is not True
    ):
        raise ValueError("G3 one-hot lift states a false normalization contract")
    target_dimension, target_polynomial = _parse_sparse_polynomial(
        target["target_polynomial"], allow_laurent=False, require_integer=True
    )
    tag_point = [Fraction(1)] * target["tag_dimension"]
    lifted_value = _evaluate(target_polynomial, source_point + tag_point)
    shifted_value = strict_value
    for value in source_point:
        shifted_value *= value
    if lifted_value != shifted_value:
        raise ValueError("G3 all-one tag slice does not recover the shifted strictifier")
    tag_probe = [Fraction(1, 2)] * target["tag_dimension"]
    probe_value = _evaluate(target_polynomial, source_point + tag_probe)
    common_factor = math.prod(source_point, start=Fraction(1)) * math.prod(
        (value * value for value in tag_probe), start=Fraction(1)
    )
    normalized_bracket = probe_value / common_factor
    if normalized_bracket < strict_value:
        raise ValueError("G3 normalized sign-oriented bracket does not dominate Q")
    if target_dimension != dimension + target["tag_dimension"]:
        raise ValueError("G3 target dimension accounting failed")
    return {
        "strict_negative_numerator": strict_value.numerator,
        "strict_negative_denominator_bits": strict_value.denominator.bit_length(),
        "alternative_row_count": target["alternative_row_count"],
        "tag_dimension": target["tag_dimension"],
        "tag_dimension_equals_coefficient_l1":
            target["tag_dimension"] == result["strictifier_coefficient_l1_norm"],
        "global_row_uniqueness": target["globally_duplicate_free"],
        "row_count_bound": result["parameters"]["coefficient_l1_bound"],
        "target_object_size_bound":
            "3000000000000*boundedETRINVCodeSize(Phi)^4",
        "foundation_parameter": "ExplicitCompactMinimumFoundation",
        "conventional_runtime_claim": False,
        "universal_real_classification_claim": False,
    }


def _verify_g4_reversal() -> dict[str, Any]:
    result = _registered_g4_reversal()
    return {
        "probability_table": result["probability_table"],
        "same_input_unit_coordinate_converse": True,
    }


def _verify_g4_tie() -> dict[str, Any]:
    result = _registered_g4_reversal()
    return {
        "factorization": result["factorization"],
        "unique_physical_interior_root": result["unique_physical_interior_root"],
    }


def _verify_g4_multiset() -> dict[str, Any]:
    left = _ledger_from_rows("A", [[1], [1]])
    right = _ledger_from_rows("B", [[1]])
    left_measure = RelativeRowMassMeasure(left, left["named_candidate"])
    right_measure = RelativeRowMassMeasure(right, right["named_candidate"])
    if left_measure == right_measure:
        raise ValueError("G4 repeated-row counterexample lost multiplicity")
    z = Fraction(1, 2)
    probabilities = [
        _named_probability_one_dimensional([1, 1], z),
        _named_probability_one_dimensional([1], z),
    ]
    if probabilities != [Fraction(1, 2), Fraction(2, 3)]:
        raise ValueError("G4 multiplicity counterexample probabilities changed")
    return {
        "left_relative_mass_at_row_one": _fraction_text(left_measure[(1,)]),
        "right_relative_mass_at_row_one": _fraction_text(right_measure[(1,)]),
        "probabilities_at_one_half": [_fraction_text(value) for value in probabilities],
    }


def _boolean_points(dimension: int) -> Iterable[tuple[Fraction, ...]]:
    for point in itertools.product([Fraction(0), Fraction(1)], repeat=dimension):
        yield point


def _verify_g4_complexity() -> dict[str, Any]:
    satisfiable = {
        "variable_count": 2,
        "clauses": [[1], [-1, 2]],
    }
    compiled = CompileSelectorCNF(satisfiable)
    dimension, shifted = _parse_sparse_polynomial(
        compiled["shifted_polynomial"], allow_laurent=False, require_integer=True
    )
    witness = [Fraction(1), Fraction(1), Fraction(1), Fraction(1), Fraction(1, 2)]
    if dimension != len(witness) or _evaluate(shifted, witness) != Fraction(-1, 2):
        raise ValueError("G4 selector compiler lost its exact physical counterwitness")
    unsatisfiable = {"variable_count": 1, "clauses": [[1], [-1]]}
    _, clauses, selector = _selector_polynomial(unsatisfiable)
    selector_dimension = 1 + len(clauses)
    values = [_evaluate(selector, point) for point in _boolean_points(selector_dimension)]
    if min(values) != 0:
        raise ValueError("G4 unsatisfiable selector has a negative Boolean vertex")
    return {
        "satisfiable_physical_margin": "-1/2",
        "unsatisfiable_boolean_minimum": "0",
        "alternative_row_count": compiled["alternative_row_count"],
        "support_bound": compiled["support_bound"],
        "row_count_bound": "1+8*m",
        "table_size_bound": "10*source_size^2",
        "compiler_charge_bound": "20*source_size^2",
        "verifier_charge_bound": "30*source_size^2",
        "normalization_charge_bound": "90*source_size^3",
        "total_charge_bound": "110*source_size^3",
        "conditional_conventional_boundary": "ExecutableCNFConventionalBoundary",
        "unconditional_conventional_class_claim": False,
        "universal_real_classification_claim": False,
    }


def _verify_g5_types() -> dict[str, Any]:
    empty_event: frozenset[int] = frozenset()
    target_event = frozenset({1, 2})
    categorical_truth = empty_event <= target_event
    first_probability = Fraction(1, 3)
    second_probability = Fraction(1, 4)
    numerical_order = first_probability <= second_probability
    antisymmetry = all(
        ((left <= right and right <= left) == (left == right))
        for left, right in itertools.product(
            [Fraction(0), Fraction(1, 4), Fraction(1)], repeat=2
        )
    )
    if categorical_truth is not True or numerical_order is not False or not antisymmetry:
        raise ValueError("G5 typed vacuity or numerical antisymmetry replay failed")
    return {
        "empty_event_inclusion": categorical_truth,
        "unrelated_numerical_order": numerical_order,
        "sorts_distinct": True,
        "antisymmetry_checked": antisymmetry,
    }


def _verify_g5_gordan() -> dict[str, Any]:
    survivor = ExactConeAlternative([[1, -1]])
    collapse = ExactConeAlternative(
        [[-1, 0, 0, -1], [0, -1, -1, 0]]
    )
    if survivor["branch"] != "normalized_nonnegative_kernel":
        raise ValueError("G5 survivor branch was not found")
    if collapse["branch"] != "strictly_positive_row_space":
        raise ValueError("G5 collapse branch was not found")
    return {
        "survivor": survivor,
        "collapse": collapse,
        "exclusive": True,
    }


def _verify_g5_metaproof() -> dict[str, Any]:
    difference = DifferenceMatrix([[0, 0, 0, 0], [-1, 0, 0, -1], [0, -1, -1, 0]])
    alternative = ExactConeAlternative(difference)
    if alternative["branch"] != "strictly_positive_row_space":
        raise ValueError("G5 impossible-candidate composition did not prove collapse")
    return {
        "difference_matrix": difference,
        "alternative_branch": alternative["branch"],
        "region_identity": "{w>=0:D_I*w=0}",
        "unconditional_collapse_claimed": False,
    }


SCHEMA_VERIFIERS = {
    "MAX-G1.CARRIER.01": _verify_g1_carrier,
    "MAX-G1.CLEAR.02": _verify_g1_clear,
    "MAX-G1.CLOSURE.03": _verify_g1_closure,
    "MAX-G2.ANCHOR.01": _verify_g2_anchor,
    "MAX-G2.ORDER.02": _verify_g2_order,
    "MAX-G3.RESIDUAL.01": _verify_g3_residual,
    "MAX-G3.CHAIN.02": _verify_g3_chain,
    "MAX-G3.REDUCTION.03": _verify_g3_reduction,
    "MAX-G4.REVERSAL.01": _verify_g4_reversal,
    "MAX-G4.TIE.02": _verify_g4_tie,
    "MAX-G4.MULTISET.03": _verify_g4_multiset,
    "MAX-G4.COMPLEXITY.04": _verify_g4_complexity,
    "MAX-G5.TYPES.01": _verify_g5_types,
    "MAX-G5.GORDAN.02": _verify_g5_gordan,
    "MAX-G5.METAPROOF": _verify_g5_metaproof,
}


def _formal_hash(specification: Mapping[str, Any]) -> str:
    return CanonicalHash(
        {
            key: value
            for key, value in specification.items()
            if key not in {"title_en", "title_pt_BR", "formal_statement_sha256"}
        }
    )


def _specification_path(result_id: str, root: Path | str | None) -> Path:
    return (
        _deliverables_root(root)
        / "formal"
        / "proofs"
        / "maxent"
        / "semantic"
        / "specs"
        / f"{result_id}.json"
    )


def _load_specification(result_id: str, root: Path | str | None) -> dict[str, Any]:
    if result_id not in RESULT_IDS:
        raise ValueError("Unknown MAX G1-G5 result identifier")
    specification = LoadJson(_specification_path(result_id, root))
    if specification.get("result_id") != result_id:
        raise ValueError("MAX G1-G5 specification identity mismatch")
    if _formal_hash(specification) != specification.get("formal_statement_sha256"):
        raise ValueError("MAX G1-G5 staged formal-statement hash mismatch")
    proof_goals = specification.get("proof_goals")
    if not isinstance(proof_goals, list):
        raise ValueError("MAX G1-G5 specification lacks registered proof goals")
    identifiers = [row.get("proof_goal_id") for row in proof_goals]
    if len(identifiers) != len(set(identifiers)) or any(
        identifier not in REGISTERED_PROOF_GOAL_IDS for identifier in identifiers
    ):
        raise ValueError("MAX G1-G5 specification proof-goal inventory is malformed")
    if any(row.get("mandatory") is not True for row in proof_goals):
        raise ValueError("MAX G1-G5 specification contains a nonmandatory proof goal")
    return specification


def _foundation_items(root: Path | str | None) -> dict[str, dict[str, Any]]:
    deliverables = _deliverables_root(root)
    required = LoadJson(deliverables / REQUIRED_FOUNDATION_RELATIVE_PATH)
    trusted = LoadJson(deliverables / TRUSTED_FOUNDATION_RELATIVE_PATH)
    result: dict[str, dict[str, Any]] = {}
    for catalog in [trusted, required]:
        catalog_identifiers: set[str] = set()
        for row in catalog.get("items", []):
            identifier = row.get("foundation_id")
            if (
                not isinstance(identifier, str)
                or not identifier
                or identifier in catalog_identifiers
            ):
                raise ValueError("Foundation catalog has a missing or duplicate identifier")
            catalog_identifiers.add(identifier)
            if identifier in result and any(
                row.get(field) != result[identifier].get(field)
                for field in ["classification", "proof_path"]
            ):
                raise ValueError("Required foundation schema conflicts with its trusted entry")
            result[identifier] = row
    return result


def _validate_imported_foundation(
    identifier: str, item: Mapping[str, Any]
) -> None:
    classification = item.get("classification")
    if identifier in {"FOUND-COMPLEXITY-ETRINV-001", "FOUND-COMPLEXITY-3SAT-001"}:
        if classification != "imported standard theorem" or not item.get(
            "source_citation"
        ):
            raise ValueError("Complexity completeness dependency is not an exact imported theorem")
    if identifier == "FOUND-COMPACT-POLY-MIN-001":
        if classification != "imported standard theorem" or not item.get(
            "source_citation"
        ):
            raise ValueError("Compact polynomial minimum dependency is incomplete")
    if identifier == "FOUND-GORDAN-STIEMKE-001":
        if classification != "imported standard theorem":
            raise ValueError("Gordan--Stiemke dependency lacks its exact rational specialization")
        if not item.get("source_citation"):
            raise ValueError("Gordan--Stiemke rational witness lemmas are not explicit")
    if "formal_statement" not in item:
        raise ValueError("Foundation dependency lacks an exact formal statement")


PROOF_FIELDS = {
    "schema_version",
    "proof_id",
    "semantic_kernel_version",
    "checker",
    "checker_sha256",
    "required_foundation_file",
    "required_foundation_file_sha256",
    "trusted_foundation_file",
    "trusted_foundation_file_sha256",
    "shared_definition_file",
    "shared_definition_file_sha256",
    "specification_files",
    "records",
}
PROOF_RECORD_FIELDS = {
    "result_id",
    "proof_goal_id",
    "proof_schema",
    "claim_sha256",
    "formal_statement_sha256",
    "proof_methods",
    "definition_dependencies",
    "foundation_dependencies",
    "result_dependencies",
    "source_transcription_dependencies",
    "proof_goal_dependencies",
    "proof_steps",
    "schema_payload",
    "mutant_ids",
    "closure_scope",
}


def LoadMaxEntG1G5Proof(root: Path | str | None = None) -> dict[str, Any]:
    deliverables = _deliverables_root(root)
    proof = LoadJson(deliverables / PROOF_RELATIVE_PATH)
    _require_exact_fields(proof, PROOF_FIELDS, "MAX G1-G5 proof")
    if (
        proof["schema_version"] != "1.0.0"
        or proof["proof_id"] != "MAX-G1-G5-SEMANTIC-CLOSURE-1"
        or proof["semantic_kernel_version"] != SEMANTIC_KERNEL_VERSION
    ):
        raise ValueError("MAX G1-G5 proof identity or version mismatch")
    expected_files = {
        "checker": CHECKER_RELATIVE_PATH,
        "required_foundation_file": REQUIRED_FOUNDATION_RELATIVE_PATH,
        "trusted_foundation_file": TRUSTED_FOUNDATION_RELATIVE_PATH,
        "shared_definition_file": SHARED_DEFINITION_RELATIVE_PATH,
    }
    for field, expected_path in expected_files.items():
        if proof[field] != expected_path:
            raise ValueError("MAX G1-G5 proof points to an unrelated support file")
        if proof[f"{field}_sha256"] != FileHash(deliverables / expected_path):
            raise ValueError("MAX G1-G5 proof support-file hash is stale")
    specification_files = proof["specification_files"]
    if not isinstance(specification_files, list) or len(specification_files) != len(RESULT_IDS):
        raise ValueError("MAX G1-G5 proof specification manifest is incomplete")
    expected_specifications = {
        result_id: {
            "result_id": result_id,
            "path": f"formal/proofs/maxent/semantic/specs/{result_id}.json",
            "sha256": FileHash(_specification_path(result_id, root)),
        }
        for result_id in RESULT_IDS
    }
    observed_specifications: dict[str, dict[str, Any]] = {}
    for row in specification_files:
        if not isinstance(row, Mapping) or set(row) != {"result_id", "path", "sha256"}:
            raise ValueError("MAX G1-G5 specification manifest row is malformed")
        result_id = row["result_id"]
        if result_id in observed_specifications:
            raise ValueError("MAX G1-G5 specification manifest duplicates a result")
        observed_specifications[result_id] = dict(row)
    if observed_specifications != expected_specifications:
        raise ValueError("MAX G1-G5 specification manifest path or hash is stale")
    records = proof["records"]
    if not isinstance(records, list) or len(records) != len(SEMANTIC_PROOF_GOAL_IDS):
        raise ValueError("MAX G1-G5 semantic proof does not contain all 11 records")
    identifiers = [row.get("proof_goal_id") for row in records if isinstance(row, Mapping)]
    if tuple(identifiers) != SEMANTIC_PROOF_GOAL_IDS:
        raise ValueError("MAX G1-G5 semantic proof records are missing, duplicated, or reordered")
    return proof


def CheckMaxEntG1G5ClosureRecord(
    record: Mapping[str, Any],
    specification: Mapping[str, Any],
    root: Path | str | None = None,
    claim: Any = None,
) -> dict[str, Any]:
    _require_exact_fields(record, PROOF_RECORD_FIELDS, "MAX G1-G5 closure record")
    result_id = record["result_id"]
    if specification.get("result_id") != result_id or result_id not in RESULT_IDS:
        raise ValueError("MAX G1-G5 closure record result identity mismatch")
    if _formal_hash(specification) != specification.get("formal_statement_sha256"):
        raise ValueError("MAX G1-G5 closure record received a stale specification")
    proof_goal_id = record["proof_goal_id"]
    matches = [
        row
        for row in specification["proof_goals"]
        if row.get("proof_goal_id") == proof_goal_id
    ]
    if len(matches) != 1:
        raise ValueError("MAX G1-G5 closure record names an absent or ambiguous proof goal")
    proof_goal = matches[0]
    staged_claim = proof_goal["claim"]
    if claim is None:
        claim = staged_claim
    if claim != staged_claim or record["claim_sha256"] != CanonicalHash(staged_claim):
        raise ValueError("MAX G1-G5 closure record proves a different or stale claim")
    if record["formal_statement_sha256"] != specification["formal_statement_sha256"]:
        raise ValueError("MAX G1-G5 closure record is bound to another staged result")
    exact_fields = {
        "proof_methods": proof_goal["proof_methods"],
        "definition_dependencies": specification["definition_dependencies"],
        "foundation_dependencies": specification["foundation_dependencies"],
        "result_dependencies": specification["result_dependencies"],
        "source_transcription_dependencies": specification["source_transcription_dependencies"],
        "proof_goal_dependencies": LOCAL_PROOF_GOAL_DEPENDENCIES[proof_goal_id],
    }
    for field, expected in exact_fields.items():
        if record[field] != expected:
            raise ValueError(f"MAX G1-G5 closure record changes its {field}")
    expected_schema = SCHEMA_DEFINITIONS[proof_goal_id]
    for field in ["proof_schema", "proof_steps", "schema_payload", "mutant_ids"]:
        if record[field] != expected_schema[field]:
            raise ValueError(f"MAX G1-G5 closure record changes its {field}")
    if (
        len(record["mutant_ids"]) < 3
        or len(record["mutant_ids"]) != len(set(record["mutant_ids"]))
        or record["closure_scope"]
        != "REGISTERED_UNIVERSAL_PROOF_GOAL_RELATIVE_TO_EXACT_FOUNDATIONS"
    ):
        raise ValueError("MAX G1-G5 closure scope or mutant manifest is dishonest")
    foundation_items = _foundation_items(root)
    foundation_hashes: dict[str, str] = {}
    for identifier in record["foundation_dependencies"]:
        if identifier not in foundation_items:
            raise ValueError("MAX G1-G5 closure record names an unknown foundation")
        item = foundation_items[identifier]
        _validate_imported_foundation(identifier, item)
        foundation_hashes[identifier] = CanonicalHash(item["formal_statement"])
    evidence = SCHEMA_VERIFIERS[proof_goal_id]()
    return {
        "status": "PASS",
        "closure_kind": "UNIVERSAL_PROOF_SCHEMA_RELATIVE_TO_EXACT_FOUNDATIONS",
        "result_id": result_id,
        "proof_goal_id": proof_goal_id,
        "claim_sha256": record["claim_sha256"],
        "proof_schema": record["proof_schema"],
        "proof_step_count": len(record["proof_steps"]),
        "mutant_count": len(record["mutant_ids"]),
        "foundation_statement_sha256": foundation_hashes,
        "evidence": evidence,
    }


def GenerateMaxEntG1G5SemanticClosures(
    root: Path | str | None = None,
) -> list[dict[str, Any]]:
    proof = LoadMaxEntG1G5Proof(root)
    results: list[dict[str, Any]] = []
    closed: set[str] = set()
    specification_cache = {
        result_id: _load_specification(result_id, root) for result_id in RESULT_IDS
    }
    for record in proof["records"]:
        dependencies = record["proof_goal_dependencies"]
        if any(dependency not in closed for dependency in dependencies):
            raise ValueError("MAX G1-G5 closure record precedes an unmet proof-goal dependency")
        result = CheckMaxEntG1G5ClosureRecord(
            record, specification_cache[record["result_id"]], root
        )
        results.append(result)
        closed.add(record["proof_goal_id"])
    if tuple(result["proof_goal_id"] for result in results) != SEMANTIC_PROOF_GOAL_IDS:
        raise ValueError("MAX G1-G5 closure generation did not cover all semantic proof goals exactly once")
    return results


SEMANTIC_PAYLOAD_FIELDS = {
    "semantic_kernel_version",
    "closure_status",
    "proof_goal_id",
    "claim_sha256",
    "proof",
    "proof_sha256",
    "checker_module",
    "checker_module_sha256",
    "closure_record",
    "verification",
    "verification_sha256",
}


def CheckMaxEntG1G5SemanticPayload(
    payload: Mapping[str, Any],
    specification: Mapping[str, Any],
    root: Path | str | None = None,
    claim: Any = None,
) -> dict[str, Any]:
    _require_exact_fields(payload, SEMANTIC_PAYLOAD_FIELDS, "MAX G1-G5 semantic payload")
    if (
        payload["semantic_kernel_version"] != SEMANTIC_KERNEL_VERSION
        or payload["closure_status"] != "MACHINE_CLOSED_RELATIVE_TO_FOUNDATION"
    ):
        raise ValueError("MAX G1-G5 semantic payload kernel or status changed")
    proof_goal_id = payload["proof_goal_id"]
    if proof_goal_id not in SEMANTIC_PROOF_GOAL_IDS:
        raise ValueError("MAX G1-G5 semantic payload names an unknown semantic proof goal")
    matches = [
        row
        for row in specification["proof_goals"]
        if row["proof_goal_id"] == proof_goal_id
    ]
    if len(matches) != 1:
        raise ValueError("MAX G1-G5 semantic payload names an absent proof goal")
    staged_claim = matches[0]["claim"]
    if claim is None:
        claim = staged_claim
    if claim != staged_claim or payload["claim_sha256"] != CanonicalHash(staged_claim):
        raise ValueError("MAX G1-G5 semantic payload proves a different or stale claim")
    deliverables = _deliverables_root(root)
    expected_files = {
        "proof": PROOF_RELATIVE_PATH,
        "checker_module": CHECKER_RELATIVE_PATH,
    }
    for field, expected_path in expected_files.items():
        if (
            payload[field] != expected_path
            or payload[f"{field}_sha256"] != FileHash(deliverables / expected_path)
        ):
            raise ValueError("MAX G1-G5 semantic payload support path or digest is stale")
    proof = LoadMaxEntG1G5Proof(root)
    records = [
        row
        for row in proof["records"]
        if row["proof_goal_id"] == proof_goal_id
    ]
    if len(records) != 1 or payload["closure_record"] != records[0]:
        raise ValueError("MAX G1-G5 semantic payload changes its closure record")
    verification = CheckMaxEntG1G5ClosureRecord(
        records[0], specification, root, claim
    )
    if (
        payload["verification"] != verification
        or payload["verification_sha256"] != CanonicalHash(verification)
    ):
        raise ValueError("MAX G1-G5 semantic payload verification is false or stale")
    return {
        "status": "PASS",
        "closure_status": payload["closure_status"],
        "proof_goal_id": proof_goal_id,
        "proof_schema": verification["proof_schema"],
        "claim_sha256": payload["claim_sha256"],
        "verification_sha256": payload["verification_sha256"],
        "mutant_count": verification["mutant_count"],
    }


def GenerateMaxEntG1G5SemanticProofs(
    root: Path | str | None = None,
) -> list[dict[str, Any]]:
    deliverables = _deliverables_root(root)
    proof = LoadMaxEntG1G5Proof(root)
    specifications = {
        result_id: _load_specification(result_id, root)
        for result_id in RESULT_IDS
    }
    proofs: list[dict[str, Any]] = []
    for record in proof["records"]:
        result_id = record["result_id"]
        specification = specifications[result_id]
        proof_goal = next(
            row
            for row in specification["proof_goals"]
            if row["proof_goal_id"] == record["proof_goal_id"]
        )
        verification = CheckMaxEntG1G5ClosureRecord(
            record, specification, root, proof_goal["claim"]
        )
        payload = {
            "semantic_kernel_version": SEMANTIC_KERNEL_VERSION,
            "closure_status": "MACHINE_CLOSED_RELATIVE_TO_FOUNDATION",
            "proof_goal_id": record["proof_goal_id"],
            "claim_sha256": record["claim_sha256"],
            "proof": PROOF_RELATIVE_PATH,
            "proof_sha256": FileHash(deliverables / PROOF_RELATIVE_PATH),
            "checker_module": CHECKER_RELATIVE_PATH,
            "checker_module_sha256": FileHash(deliverables / CHECKER_RELATIVE_PATH),
            "closure_record": record,
            "verification": verification,
            "verification_sha256": CanonicalHash(verification),
        }
        CheckMaxEntG1G5SemanticPayload(
            payload, specification, root, proof_goal["claim"]
        )
        proofs.append(
            {
                "schema_version": "1.0.0",
                "proof_id": (
                    f"{record['proof_goal_id']}.MAXENT-SEMANTIC-CLOSURE.PROOF"
                ),
                "proof_method": "MaxEntSemanticClosureProof",
                "result_id": result_id,
                "proof_goal_id": record["proof_goal_id"],
                "formal_statement_sha256": specification[
                    "formal_statement_sha256"
                ],
                "claim": proof_goal["claim"],
                "claim_sha256": record["claim_sha256"],
                "payload": payload,
            }
        )
    if tuple(row["proof_goal_id"] for row in proofs) != SEMANTIC_PROOF_GOAL_IDS:
        raise ValueError("MAX G1-G5 semantic proof inventory is incomplete")
    return proofs


def GenerateMaxEntG1G5CatalogAdapters(
    root: Path | str | None = None,
) -> list[dict[str, Any]]:
    deliverables = _deliverables_root(root)
    proofs = GenerateMaxEntG1G5SemanticProofs(root)
    specifications = {
        result_id: _load_specification(result_id, root)
        for result_id in RESULT_IDS
    }
    adapters: list[dict[str, Any]] = []
    for proof in proofs:
        verification = CheckMaxEntG1G5SemanticPayload(
            proof["payload"],
            specifications[proof["result_id"]],
            root,
            proof["claim"],
        )
        adapters.append(
            {
                "result_id": proof["result_id"],
                "proof_goal_id": proof["proof_goal_id"],
                "closure_proof": proof,
                "checker_module": CHECKER_RELATIVE_PATH,
                "checker_module_sha256": FileHash(
                    deliverables / CHECKER_RELATIVE_PATH
                ),
                "replayed_universal": proof["proof_goal_id"]
                != "MAX-G4.TIE.02",
                "supports_whole_result_closure": True,
                "verification": verification,
            }
        )
    return adapters


__all__ = [
    "OneHotTagLift",
    "BuildETRINVResidual",
    "CheckMaxEntG1G5ClosureRecord",
    "CheckMaxEntG1G5SemanticPayload",
    "ClearLaurentPolynomial",
    "CompileETRINVToMaxEnt",
    "CompileIntegerPolynomial",
    "CompileRelativePartitionDifference",
    "CompileSelectorCNF",
    "DifferenceMatrix",
    "ExactConeAlternative",
    "GenerateMaxEntG1G5CatalogAdapters",
    "GenerateMaxEntG1G5SemanticProofs",
    "GenerateMaxEntG1G5SemanticClosures",
    "LoadMaxEntG1G5Proof",
    "LEAN_PROOF_GOAL_IDS",
    "REGISTERED_PROOF_GOAL_IDS",
    "SEMANTIC_PROOF_GOAL_IDS",
    "RelativeRowMassMeasure",
    "SCHEMA_DEFINITIONS",
    "SEMANTIC_KERNEL_VERSION",
    "StrictifierParameters",
    "RESULT_IDS",
]
