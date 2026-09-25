from __future__ import annotations

import itertools
import math
from fractions import Fraction
from typing import Any

from .linear import Multiply as MatrixMultiply, ParseMatrix
from .polynomial import Add, Evaluate, Multiply, NormalizePolynomial, ParsePolynomial, Polynomial, Power
from .rational import ParseRational, RationalText


def _require_fields(value: dict[str, Any], required: set[str]) -> None:
    if set(value) != required:
        raise ValueError("Finite-MaxEnt witness fields do not match the declared grammar")


def _monomial(powers: tuple[int, ...]) -> Polynomial:
    return {powers: Fraction(1)}


def _sum(polynomials: list[Polynomial]) -> Polynomial:
    result: Polynomial = {}
    for polynomial in polynomials:
        result = Add(result, polynomial)
    return result


def _negate(polynomial: Polynomial) -> Polynomial:
    return NormalizePolynomial({powers: -coefficient for powers, coefficient in polynomial.items()})


def _subtract(left: Polynomial, right: Polynomial) -> Polynomial:
    return Add(left, _negate(right))


def _winner_map(ledger: list[list[list[int]]], ranking: tuple[int, ...]) -> tuple[int, ...]:
    winners: list[int] = []
    for input_rows in ledger:
        scores = [tuple(row[index] for index in ranking) for row in input_rows]
        minimum = min(scores)
        if scores.count(minimum) != 1:
            raise ValueError("Strict-ranking tensor produced a tie")
        winners.append(scores.index(minimum) + 1)
    return tuple(winners)


def _validate_ledger(ledger: Any) -> tuple[int, int, int]:
    if not isinstance(ledger, list) or not ledger:
        raise ValueError("Finite-MaxEnt ledger tensor is empty")
    input_count = len(ledger)
    candidate_count = len(ledger[0])
    if candidate_count == 0:
        raise ValueError("Finite-MaxEnt ledger has no candidate")
    constraint_count = len(ledger[0][0])
    if constraint_count == 0:
        raise ValueError("Finite-MaxEnt ledger has no constraint")
    for input_rows in ledger:
        if len(input_rows) != candidate_count:
            raise ValueError("Finite-MaxEnt candidate count is not rectangular")
        for row in input_rows:
            if len(row) != constraint_count or any(
                not isinstance(value, int) or isinstance(value, bool) or value < 0 for value in row
            ):
                raise ValueError("Finite-MaxEnt violation row is malformed")
    return input_count, candidate_count, constraint_count


def _event(ranking_maps: list[tuple[int, ...]], mapping: tuple[int, int]) -> frozenset[int]:
    input_index, candidate_index = mapping
    return frozenset(
        ranking_index
        for ranking_index, winner_map in enumerate(ranking_maps)
        if winner_map[input_index - 1] == candidate_index
    )


def _implication_polynomial(
    ledger: list[list[list[int]]],
    antecedent: tuple[int, int],
    consequent: tuple[int, int],
) -> Polynomial:
    dimension = len(ledger[0][0])
    left_rows = ledger[antecedent[0] - 1]
    right_rows = ledger[consequent[0] - 1]
    left_named = left_rows[antecedent[1] - 1]
    right_named = right_rows[consequent[1] - 1]
    relative_left = [tuple(value - base for value, base in zip(row, left_named, strict=True)) for row in left_rows]
    relative_right = [tuple(value - base for value, base in zip(row, right_named, strict=True)) for row in right_rows]
    shift = tuple(
        -min([0, *[row[index] for row in relative_left], *[row[index] for row in relative_right]])
        for index in range(dimension)
    )
    shifted_left = [tuple(value + offset for value, offset in zip(row, shift, strict=True)) for row in relative_left]
    shifted_right = [tuple(value + offset for value, offset in zip(row, shift, strict=True)) for row in relative_right]
    return _subtract(_sum([_monomial(row) for row in shifted_left]), _sum([_monomial(row) for row in shifted_right]))


def _parse_polynomial(value: dict[str, Any], variables: list[str]) -> Polynomial:
    return ParsePolynomial(value, variables)


def _factor_expression(expression: dict[str, Any], atoms: dict[str, Polynomial]) -> Polynomial:
    operation = expression.get("op")
    if operation == "atom":
        if set(expression) != {"op", "id"} or expression["id"] not in atoms:
            raise ValueError("Unknown finite-MaxEnt factor atom")
        return atoms[expression["id"]]
    if set(expression) != {"op", "arguments"} or operation not in {"add", "multiply"}:
        raise ValueError("Unknown finite-MaxEnt factorization operation")
    arguments = expression["arguments"]
    if not isinstance(arguments, list) or not arguments:
        raise ValueError("Empty finite-MaxEnt factorization operation")
    values = [_factor_expression(argument, atoms) for argument in arguments]
    if operation == "add":
        return _sum(values)
    result = values[0]
    for value in values[1:]:
        result = Multiply(result, value)
    return result


def _unit_vector_polynomial(dimension: int, index: int) -> Polynomial:
    powers = [0] * dimension
    powers[index] = 1
    return {tuple(powers): Fraction(1)}


def _validate_nonnegative_atom(
    identifier: str,
    polynomial: Polynomial,
    rule: str,
    variables: list[str],
    facets: set[frozenset[tuple[tuple[int, ...], Fraction]]],
) -> None:
    dimension = len(variables)
    zero = (0,) * dimension
    if rule == "positive_constant":
        if set(polynomial) != {zero} or polynomial[zero] <= 0:
            raise ValueError("Positive-constant atom is false")
        return
    if rule == "closed_unit_cube_coordinate":
        if identifier not in variables or polynomial != _unit_vector_polynomial(dimension, variables.index(identifier)):
            raise ValueError("Coordinate-sign atom is false")
        return
    if rule == "nonnegative_coordinate_monomial":
        if len(polynomial) != 1:
            raise ValueError("Coordinate-monomial atom is not a monomial")
        powers, coefficient = next(iter(polynomial.items()))
        if coefficient <= 0 or not any(powers):
            raise ValueError("Coordinate-monomial atom has invalid sign")
        return
    if rule == "unit_cube_one_minus_coordinate_monomial":
        if polynomial.get(zero) != 1 or len(polynomial) != 2:
            raise ValueError("Unit-cube complement atom is malformed")
        other = [(powers, coefficient) for powers, coefficient in polynomial.items() if powers != zero]
        if len(other) != 1 or other[0][1] != -1 or not any(other[0][0]):
            raise ValueError("Unit-cube complement atom is not one minus a coordinate monomial")
        return
    if rule == "registered_facet_assumption":
        if frozenset(polynomial.items()) not in facets:
            raise ValueError("Facet atom is not a registered facet")
        return
    raise ValueError(f"Unknown finite-MaxEnt atom-sign rule: {rule}")


def CheckBasicSyllableExactWitness(payload: dict[str, Any]) -> dict[str, Any]:
    _require_fields(
        payload,
        {
            "proof_design",
            "variables",
            "ledger",
            "ranking_to_winner_map",
            "distinct_winner_maps",
            "implication_counts",
            "live_implications",
            "factor_atoms",
            "facet_polynomials",
            "necessity",
            "strict_activity_interior_witness",
            "strict_facet_values",
            "collapse_matrix",
            "collapse_lambda",
            "collapse_product",
        },
    )
    if payload["proof_design"] != "MAX-G6 exact finite inventory and cone factorization":
        raise ValueError("Basic Syllable proof design changed")
    variables = payload["variables"]
    if variables != ["a", "b", "c", "d"]:
        raise ValueError("Basic Syllable activity-variable order changed")
    input_count, candidate_count, constraint_count = _validate_ledger(payload["ledger"])
    if (input_count, candidate_count, constraint_count) != (4, 4, 4):
        raise ValueError("Basic Syllable tensor dimensions changed")

    rankings = list(itertools.permutations(range(constraint_count)))
    ranking_maps = [_winner_map(payload["ledger"], ranking) for ranking in rankings]
    expected_ranking_rows = [
        {"ranking": [index + 1 for index in ranking], "winner_map": list(winner_map)}
        for ranking, winner_map in zip(rankings, ranking_maps, strict=True)
    ]
    if payload["ranking_to_winner_map"] != expected_ranking_rows:
        raise ValueError("Basic Syllable ranking enumeration is incomplete or incorrect")
    unique_maps = sorted(set(ranking_maps))
    if payload["distinct_winner_maps"] != [list(value) for value in unique_maps]:
        raise ValueError("Basic Syllable winner-map inventory is incorrect")

    mappings = list(itertools.product(range(1, input_count + 1), range(1, candidate_count + 1)))
    implications = [
        (left, right)
        for left, right in itertools.product(mappings, repeat=2)
        if left != right and _event(unique_maps, left) <= _event(unique_maps, right)
    ]
    empty = [(left, right) for left, right in implications if not _event(unique_maps, left)]
    live = [(left, right) for left, right in implications if _event(unique_maps, left)]
    expected_counts = {
        "all_with_reflexive": len(implications) + len(mappings),
        "nonreflexive": len(implications),
        "empty_antecedent": len(empty),
        "live": len(live),
    }
    if payload["implication_counts"] != expected_counts:
        raise ValueError("Basic Syllable implication partition is incorrect")

    facet_polynomials = {
        identifier: _parse_polynomial(value, variables) for identifier, value in payload["facet_polynomials"].items()
    }
    if set(facet_polynomials) != {"d_minus_b2c", "c_minus_a2d"}:
        raise ValueError("Basic Syllable registered facets changed")
    facet_values = set(frozenset(value.items()) for value in facet_polynomials.values())
    atoms: dict[str, Polynomial] = {}
    for identifier, row in payload["factor_atoms"].items():
        _require_fields(row, {"polynomial", "nonnegativity_rule"})
        polynomial = _parse_polynomial(row["polynomial"], variables)
        _validate_nonnegative_atom(identifier, polynomial, row["nonnegativity_rule"], variables, facet_values)
        atoms[identifier] = polynomial
    coordinates = {name: _unit_vector_polynomial(constraint_count, index) for index, name in enumerate(variables)}
    one = {(0,) * constraint_count: Fraction(1)}
    expected_atoms = {
        "one": one,
        **coordinates,
        "ad": Multiply(coordinates["a"], coordinates["d"]),
        "bc": Multiply(coordinates["b"], coordinates["c"]),
        "ab": Multiply(coordinates["a"], coordinates["b"]),
        "cd": Multiply(coordinates["c"], coordinates["d"]),
        "abcd": Multiply(Multiply(coordinates["a"], coordinates["b"]), Multiply(coordinates["c"], coordinates["d"])),
        "one_minus_cd": _subtract(one, Multiply(coordinates["c"], coordinates["d"])),
        "one_minus_ab": _subtract(one, Multiply(coordinates["a"], coordinates["b"])),
        "one_minus_a2d2": _subtract(one, Multiply(Power(coordinates["a"], 2), Power(coordinates["d"], 2))),
        "facet_d_minus_b2c": facet_polynomials["d_minus_b2c"],
        "facet_c_minus_a2d": facet_polynomials["c_minus_a2d"],
    }
    if atoms != expected_atoms:
        raise ValueError("Basic Syllable factor-atom dictionary changed")

    if len(payload["live_implications"]) != len(live):
        raise ValueError("Basic Syllable live implication list is incomplete")
    for expected_pair, row in zip(live, payload["live_implications"], strict=True):
        _require_fields(
            row,
            {
                "antecedent",
                "consequent",
                "antecedent_event",
                "consequent_event",
                "polynomial",
                "factorization",
            },
        )
        left, right = expected_pair
        if row["antecedent"] != list(left) or row["consequent"] != list(right):
            raise ValueError("Basic Syllable live implication order changed")
        if row["antecedent_event"] != sorted(_event(unique_maps, left)) or row["consequent_event"] != sorted(
            _event(unique_maps, right)
        ):
            raise ValueError("Basic Syllable event transcription is incorrect")
        polynomial = _parse_polynomial(row["polynomial"], variables)
        if polynomial != _implication_polynomial(payload["ledger"], left, right):
            raise ValueError("Basic Syllable cross-margin polynomial is incorrect")
        if _factor_expression(row["factorization"], atoms) != polynomial:
            raise ValueError("Basic Syllable factorization does not expand to its target")

    for row in payload["necessity"]:
        _require_fields(row, {"live_implication_index_one_based", "facet_atom", "strictly_positive_factor"})
        index = row["live_implication_index_one_based"] - 1
        if index < 0 or index >= len(payload["live_implications"]):
            raise ValueError("Basic Syllable necessity row is out of range")
        if row["facet_atom"] not in atoms:
            raise ValueError("Basic Syllable necessity facet is unknown")
        factor = _factor_expression(row["strictly_positive_factor"], atoms)
        zero = (0,) * constraint_count
        if factor.get(zero, Fraction(0)) <= 0 or any(coefficient < 0 for coefficient in factor.values()):
            raise ValueError("Basic Syllable necessity cofactor is not provably strictly positive")
        target = _parse_polynomial(payload["live_implications"][index]["polynomial"], variables)
        if Multiply(factor, atoms[row["facet_atom"]]) != target:
            raise ValueError("Basic Syllable necessity factorization is false")
    if {row["facet_atom"] for row in payload["necessity"]} != {
        "facet_d_minus_b2c",
        "facet_c_minus_a2d",
    }:
        raise ValueError("Basic Syllable necessity does not recover both facets")

    point = [ParseRational(value) for value in payload["strict_activity_interior_witness"]]
    if len(point) != constraint_count or any(not (0 < value < 1) for value in point):
        raise ValueError("Basic Syllable strict-interior point is outside the physical cube interior")
    observed_slacks = [Evaluate(facet_polynomials[identifier], point) for identifier in ["d_minus_b2c", "c_minus_a2d"]]
    if observed_slacks != [ParseRational(value) for value in payload["strict_facet_values"]] or any(
        value <= 0 for value in observed_slacks
    ):
        raise ValueError("Basic Syllable strict-interior facet slacks are incorrect")

    matrix = ParseMatrix(payload["collapse_matrix"])
    lam = [[ParseRational(value)] for value in payload["collapse_lambda"]]
    product = MatrixMultiply(list(map(list, zip(*matrix))), lam)
    flattened = [RationalText(row[0]) for row in product]
    if flattened != [str(value) for value in payload["collapse_product"]] or any(row[0] <= 0 for row in product):
        raise ValueError("Basic Syllable collapse row-space witness is false")

    return {
        "ranking_count": len(rankings),
        "winner_map_count": len(unique_maps),
        "nonreflexive_implication_count": len(implications),
        "empty_antecedent_count": len(empty),
        "live_implication_count": len(live),
        "distinct_live_polynomial_count": len(
            {frozenset(_implication_polynomial(payload["ledger"], left, right).items()) for left, right in live}
        ),
        "facet_slacks": [RationalText(value) for value in observed_slacks],
    }


def CheckExactConeAlternativeWitness(payload: dict[str, Any]) -> dict[str, Any]:
    _require_fields(
        payload,
        {"proof_design", "matrix", "alternative", "lambda", "transpose_product"},
    )
    if payload["proof_design"] != "MAX-G5 exact rational cone-alternative witness":
        raise ValueError("Cone-alternative proof design changed")
    matrix = ParseMatrix(payload["matrix"])
    if not matrix or not matrix[0] or any(len(row) != len(matrix[0]) for row in matrix):
        raise ValueError("Cone-alternative matrix is empty or nonrectangular")
    if payload["alternative"] != "strictly_positive_row_space":
        raise ValueError("Unsupported cone-alternative witness branch")
    lam = [ParseRational(value) for value in payload["lambda"]]
    if len(lam) != len(matrix):
        raise ValueError("Cone-alternative row-space witness has the wrong dimension")
    product = [
        sum(matrix[row][column] * lam[row] for row in range(len(matrix)))
        for column in range(len(matrix[0]))
    ]
    registered = [ParseRational(value) for value in payload["transpose_product"]]
    if product != registered or any(value <= 0 for value in product):
        raise ValueError("Cone-alternative row-space product is not strictly positive")
    return {
        "row_count": len(matrix),
        "column_count": len(matrix[0]),
        "alternative": payload["alternative"],
        "transpose_product": [RationalText(value) for value in product],
    }


def _univariate_factor(root: Fraction) -> Polynomial:
    return {(1,): Fraction(1), (0,): -root}


def _primitive_integer_polynomial(polynomial: Polynomial) -> Polynomial:
    denominator_lcm = math.lcm(*(coefficient.denominator for coefficient in polynomial.values()))
    integer = {powers: coefficient * denominator_lcm for powers, coefficient in polynomial.items()}
    coefficient_gcd = math.gcd(*(abs(coefficient.numerator) for coefficient in integer.values()))
    primitive = {powers: coefficient / coefficient_gcd for powers, coefficient in integer.items()}
    if primitive.get((1,), Fraction(0)) < 0:
        primitive = _negate(primitive)
    return NormalizePolynomial(primitive)


def CheckOrderedContactExactWitness(payload: dict[str, Any]) -> dict[str, Any]:
    _require_fields(payload, {"proof_design", "ordered_contact_example", "induction_schema"})
    if payload["proof_design"] != "MAX-G8 sharp exact construction and Rolle induction schema":
        raise ValueError("Ordered-contact proof design changed")
    expected_induction_schema = {
        "base": "q=1: a nonzero scalar multiple of one exponential has zero total root multiplicity",
        "derivative": "g'(t) is a collected nonzero sum of q-1 exponentials with distinct exponents lambda_j-lambda_1",
        "normalization": "g(t)=exp(lambda_1 t) f(t) preserves every zero and its multiplicity",
        "rolle_with_multiplicity": "Z(g) <= Z(g')+1 on an interval with analytic extension across its endpoints",
        "step": "Z(g')<=q-2 implies Z(f)=Z(g)<=q-1",
    }
    if payload["induction_schema"] != expected_induction_schema:
        raise ValueError("Ordered-contact induction schema changed")
    example = payload["ordered_contact_example"]
    _require_fields(
        example,
        {
            "contact_roots",
            "contact_multiplicities",
            "reversal_roots",
            "primitive_polynomial",
            "slice_count",
            "zero_budget",
        },
    )
    contacts = [ParseRational(value) for value in example["contact_roots"]]
    multiplicities = example["contact_multiplicities"]
    reversals = [ParseRational(value) for value in example["reversal_roots"]]
    if len(contacts) != len(multiplicities) or any(
        not isinstance(value, int) or isinstance(value, bool) or value <= 0 for value in multiplicities
    ):
        raise ValueError("Ordered-contact multiplicities are malformed")
    if len(set(contacts + reversals)) != len(contacts) + len(reversals) or any(
        not (0 < value < 1) for value in contacts + reversals
    ):
        raise ValueError("Ordered contacts and additional reversals are not disjoint interior roots")
    polynomial: Polynomial = {(1,): Fraction(1)}
    for root, multiplicity in zip(contacts, multiplicities, strict=True):
        polynomial = Multiply(polynomial, Power(_univariate_factor(root), multiplicity))
    for root in reversals:
        polynomial = Multiply(polynomial, _univariate_factor(root))
    polynomial = _primitive_integer_polynomial(polynomial)
    registered = _parse_polynomial(example["primitive_polynomial"], ["z"])
    if registered != polynomial:
        raise ValueError("Ordered-contact primitive polynomial is incorrect")
    zero_budget = sum(multiplicities) + len(reversals)
    if example["zero_budget"] != zero_budget or example["slice_count"] != len(polynomial) or len(polynomial) != zero_budget + 1:
        raise ValueError("Ordered-contact slice or zero-budget count is incorrect")
    ordered_coefficients = [polynomial.get((power,), Fraction(0)) for power in range(max(power[0] for power in polynomial) + 1)]
    if any(left * right >= 0 for left, right in zip(ordered_coefficients[1:], ordered_coefficients[2:])):
        raise ValueError("Ordered-contact nonzero coefficients do not alternate strictly")
    return {
        "contact_count": len(contacts),
        "registered_contact_multiplicity": sum(multiplicities),
        "additional_reversal_count": len(reversals),
        "zero_budget": zero_budget,
        "slice_count": len(polynomial),
        "primitive_coefficients": [RationalText(value) for value in ordered_coefficients],
    }


def _row_polynomial(rows: list[int]) -> Polynomial:
    if not rows or any(not isinstance(value, int) or isinstance(value, bool) or value < 0 for value in rows):
        raise ValueError("One-dimensional response ledger is malformed")
    result: Polynomial = {}
    for row in rows:
        result[(row,)] = result.get((row,), Fraction(0)) + 1
    return NormalizePolynomial(result)


def _response_envelope(ledger: dict[str, Any]) -> list[int]:
    if set(ledger) - {"A_rows", "B_rows", "common_factor"}:
        raise ValueError("Response-envelope ledger has unknown fields")
    a_rows = ledger["A_rows"]
    b_rows = ledger["B_rows"]
    _row_polynomial(a_rows)
    _row_polynomial(b_rows)
    return [min(b_rows) - max(a_rows), max(b_rows) - min(a_rows)]


def CheckResponseEnvelopeExactWitness(payload: dict[str, Any]) -> dict[str, Any]:
    _require_fields(
        payload,
        {
            "proof_design",
            "attained_set_statement",
            "closed_envelope_statement",
            "same_law_different_envelope",
            "same_envelope_different_law",
        },
    )
    if payload["proof_design"] != "MAX-G9 response-envelope characterization and nonfactorization witnesses":
        raise ValueError("Response-envelope proof design changed")
    if payload["attained_set_statement"] != "positive masses attain ri(conv(V_B)-conv(V_A))" or payload[
        "closed_envelope_statement"
    ] != "closure of the attained set is conv(V_B)-conv(V_A)":
        raise ValueError("Response-envelope attained/closed distinction changed")

    first = payload["same_law_different_envelope"]
    _require_fields(first, {"ledger_one", "ledger_two", "envelopes"})
    first_ledgers = [first["ledger_one"], first["ledger_two"]]
    observed_envelopes = [_response_envelope(ledger) for ledger in first_ledgers]
    if observed_envelopes != first["envelopes"] or observed_envelopes[0] == observed_envelopes[1]:
        raise ValueError("Same-law witness does not have the registered distinct envelopes")
    a1, b1 = (_row_polynomial(first_ledgers[0][key]) for key in ["A_rows", "B_rows"])
    a2, b2 = (_row_polynomial(first_ledgers[1][key]) for key in ["A_rows", "B_rows"])
    if Multiply(b1, Add(a2, b2)) != Multiply(b2, Add(a1, b1)):
        raise ValueError("Claimed same-law response ledgers have different normalized laws")

    second = payload["same_envelope_different_law"]
    _require_fields(
        second,
        {
            "ledger_one",
            "ledger_two",
            "common_envelope",
            "positive_difference_numerator",
            "positive_denominator_factors",
        },
    )
    second_ledgers = [second["ledger_one"], second["ledger_two"]]
    second_envelopes = [_response_envelope(ledger) for ledger in second_ledgers]
    if second_envelopes != [second["common_envelope"], second["common_envelope"]]:
        raise ValueError("Claimed same-envelope response ledgers have different envelopes")
    a1, b1 = (_row_polynomial(second_ledgers[0][key]) for key in ["A_rows", "B_rows"])
    a2, b2 = (_row_polynomial(second_ledgers[1][key]) for key in ["A_rows", "B_rows"])
    numerator = _subtract(Multiply(a1, Add(a2, b2)), Multiply(a2, Add(a1, b1)))
    registered_numerator = _parse_polynomial(second["positive_difference_numerator"], ["z"])
    if numerator != registered_numerator or numerator != {(4,): Fraction(1)}:
        raise ValueError("Same-envelope law-difference numerator is not exactly z^4")
    expected_denominators = ["1+z", "1+z^2", "1+z^2+z^3"]
    if second["positive_denominator_factors"] != expected_denominators:
        raise ValueError("Same-envelope law-difference denominator factors changed")
    return {
        "same_law_envelopes": observed_envelopes,
        "common_envelope": second["common_envelope"],
        "law_difference_numerator": "z^4",
    }
