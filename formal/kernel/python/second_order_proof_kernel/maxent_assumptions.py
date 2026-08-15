from __future__ import annotations

from copy import deepcopy
from fractions import Fraction
from typing import Any, Mapping

from .maxent_semantic_g1_g5 import (
    BuildETRINVResidual,
    CompileIntegerPolynomial,
    CompileRelativePartitionDifference,
)


MODEL_VERSION = "maxent-assumption-witness-1.0.0"
RESULT_IDS = tuple(f"MAX-G{index}" for index in range(1, 10))


EXPECTED_ASSUMPTIONS: dict[str, tuple[str, str]] = {
    "MAX-G1": (
        "MAX-G1.DOMAIN",
        "admitted_finite_cross_input_named_probability_contract",
    ),
    "MAX-G2": ("MAX-G2.DOMAIN", "canonical_finite_integer_polynomial"),
    "MAX-G3": ("MAX-G3.DOMAIN", "well_formed_bounded_etr_inv"),
    "MAX-G4": (
        "MAX-G4.DOMAIN",
        "full_nonnegative_weight_orthant_complete_finite_ledgers",
    ),
    "MAX-G5": (
        "MAX-G5.DOMAIN",
        "complete_finite_categorical_events_and_probability_transport",
    ),
    "MAX-G6": ("MAX-G6.DOMAIN", "exact_source_tensor_equality"),
    "MAX-G7": (
        "MAX-G7.DOMAIN",
        "complete_fixed_support_rational_mass_consequence_contract",
    ),
    "MAX-G8": (
        "MAX-G8.DOMAIN",
        "one_ray_collected_nonzero_distinct_exponential_response",
    ),
    "MAX-G9": (
        "MAX-G9.DOMAIN",
        "complete_nonempty_finite_fibres_positive_masses",
    ),
}


MAX_G3_FOUNDATION_SCHEMA: dict[str, Any] = {
    "fields": [
        {
            "binders": [
                {
                    "sort": "BoundedETRINVInstance",
                    "variable": "problem",
                }
            ],
            "conclusion_binders": [
                {
                    "sort": "vector",
                    "variable": "point",
                }
            ],
            "name": "paddedLowerBound",
            "premises": [
                "2 <= explicitPaddedDimension problem",
                "totalDegree (explicitPaddedResidualPolynomial problem) <= 4",
                "coefficientL1 (explicitPaddedResidualPolynomial problem) <= explicitResidualHeight problem",
                "6 * explicitPaddedDimension problem <= explicitResidualHeight problem",
                "not exists zeroPoint, ExplicitPaddedCubePoint problem zeroPoint and explicitPaddedResidual problem zeroPoint = 0",
            ],
            "conclusion": (
                "ExplicitPaddedCubePoint problem point -> "
                "dyadicCompactGap (explicitGapExponent problem) <= "
                "explicitPaddedResidual problem point"
            ),
        }
    ],
    "id": "MAX-G3.EXPLICIT-COMPACT-MINIMUM-FOUNDATION-SCHEMA",
    "instance": {"name": "foundation", "node": "variable"},
    "name": "ExplicitCompactMinimumFoundation",
    "node": "record_type",
}


MAX_G4_BOUNDARY_SCHEMA: dict[str, Any] = {
    "fields": [
        {
            "binders": [],
            "name": "source_complete",
            "type": "CompleteFor coNP executableProperCNFUnsatisfiability",
        },
        {
            "binders": [
                {
                    "sort": "ExecutableProperCNFCode",
                    "variable": "problem",
                }
            ],
            "name": "complementProof_mem",
            "type": "PolynomialComplementProof problem -> coNP problem",
        },
    ],
    "id": "MAX-G4.EXECUTABLE-CNF-CONVENTIONAL-BOUNDARY-SCHEMA",
    "instance": {"name": "boundary", "node": "variable"},
    "name": "ExecutableCNFConventionalBoundary",
    "node": "record_type",
    "parameter": {"name": "coNP", "node": "variable"},
}


SOURCE_TENSOR = [
    [[0, 0, 0, 0], [0, 1, 1, 0], [1, 0, 0, 1], [1, 1, 1, 1]],
    [[0, 0, 0, 1], [0, 1, 0, 0], [1, 0, 0, 2], [1, 1, 0, 1]],
    [[0, 0, 1, 0], [0, 1, 2, 0], [1, 0, 0, 0], [1, 1, 1, 0]],
    [[0, 0, 1, 1], [0, 1, 1, 0], [1, 0, 0, 1], [1, 1, 0, 0]],
]


def _ledger(
    prefix: str,
    rows: list[list[int]],
    masses: list[str],
    consequences: list[str],
) -> dict[str, Any]:
    labels = [f"{prefix}{index}" for index in range(len(rows))]
    return {
        "constraint_count": len(rows[0]),
        "candidates": labels,
        "named_candidate": labels[0],
        "violation_rows": dict(zip(labels, rows, strict=True)),
        "base_masses": dict(zip(labels, masses, strict=True)),
        "consequence_map": dict(zip(labels, consequences, strict=True)),
    }


MAXENT_ASSUMPTION_MODELS: dict[str, dict[str, Any]] = {
    "MAX-G1": {
        "schema_version": MODEL_VERSION,
        "assumption_id": "MAX-G1.DOMAIN",
        "assignment": {
            "A": _ledger("a", [[0, 0], [1, 0], [1, 0]], ["2", "3", "5"], ["a", "x", "x"]),
            "a": "a0",
            "B": _ledger("b", [[0, 0], [0, 2]], ["7", "11"], ["b", "y"]),
            "b": "b0",
        },
        "weight_domain": "all_nonnegative_real_vectors_of_declared_dimension",
    },
    "MAX-G2": {
        "schema_version": MODEL_VERSION,
        "assumption_id": "MAX-G2.DOMAIN",
        "assignment": {
            "F": {
                "dimension": 2,
                "terms": [
                    {"exponents": [0, 0], "coefficient": "2"},
                    {"exponents": [1, 0], "coefficient": "-3"},
                    {"exponents": [1, 2], "coefficient": "1"},
                ],
            }
        },
    },
    "MAX-G3": {
        "schema_version": MODEL_VERSION,
        "assumption_id": "MAX-G3.DOMAIN",
        "assignment": {
            "Phi": {
                "variable_count": 2,
                "equations": [{"kind": "one", "variable_index": 0}],
            }
        },
    },
    "MAX-G4": {
        "schema_version": MODEL_VERSION,
        "assumption_id": "MAX-G4.DOMAIN",
        "assignment": {
            "A": _ledger("a", [[0], [3], [3]], ["1", "1", "1"], ["a", "x", "x"]),
            "B": _ledger("b", [[0], [2]], ["1", "1"], ["b", "y"]),
        },
        "weight_domain": "full_nonnegative_real_orthant",
    },
    "MAX-G5": {
        "schema_version": MODEL_VERSION,
        "assumption_id": "MAX-G5.DOMAIN",
        "assignment": {
            "I": {
                "worlds": ["ranking_1", "ranking_2"],
                "categorical_events": {
                    "E": ["ranking_1"],
                    "F": ["ranking_1", "ranking_2"],
                },
                "probability_measure": {
                    "ranking_1": "1/3",
                    "ranking_2": "2/3",
                },
                "transport": {
                    "ranking_1": "grammar_1",
                    "ranking_2": "grammar_2",
                },
                "transported_probability_measure": {
                    "grammar_1": "1/3",
                    "grammar_2": "2/3",
                },
            }
        },
    },
    "MAX-G6": {
        "schema_version": MODEL_VERSION,
        "assumption_id": "MAX-G6.DOMAIN",
        "assignment": {"source_tensor": SOURCE_TENSOR},
    },
    "MAX-G7": {
        "schema_version": MODEL_VERSION,
        "assumption_id": "MAX-G7.DOMAIN",
        "assignment": {
            "A": _ledger("a", [[0], [1]], ["1", "2"], ["surface_0", "surface_1"]),
            "B": _ledger("b", [[0], [1]], ["2", "4"], ["surface_0", "surface_1"]),
            "w0": ["1/2"],
        },
        "fixed_support": [[0], [1]],
    },
    "MAX-G8": {
        "schema_version": MODEL_VERSION,
        "assumption_id": "MAX-G8.DOMAIN",
        "assignment": {
            "response": {
                "slices": [
                    {"coefficient": "1", "exponent": "0"},
                    {"coefficient": "-2", "exponent": "1"},
                ]
            },
            "I": {
                "left": "-1",
                "right": "1",
                "endpoint_policy": "closed",
                "analytic_extension": ["-2", "2"],
            },
        },
    },
    "MAX-G9": {
        "schema_version": MODEL_VERSION,
        "assumption_id": "MAX-G9.DOMAIN",
        "assignment": {
            "A": {"points": [[0], [2]], "base_masses": ["1", "2"]},
            "B": {"points": [[1], [3]], "base_masses": ["3", "4"]},
        },
        "mass_variation": "independent_strictly_positive_rational_fibre_masses",
    },
}


def _fraction(value: Any) -> Fraction:
    if isinstance(value, bool) or isinstance(value, float):
        raise ValueError("Assumption witnesses use exact rational values only")
    return Fraction(value)


def _exact_keys(value: Mapping[str, Any], expected: set[str]) -> bool:
    return isinstance(value, Mapping) and set(value) == expected


def _specification_matches(
    result_id: str,
    specification: Mapping[str, Any] | None,
) -> bool:
    if specification is None:
        return True
    if specification.get("result_id") != result_id:
        return False
    assumptions = specification.get("assumptions")
    if not isinstance(assumptions, list) or len(assumptions) != 1:
        return False
    assumption = assumptions[0]
    expected_id, expected_name = EXPECTED_ASSUMPTIONS[result_id]
    if assumption.get("id") != expected_id:
        return False
    if result_id in {"MAX-G3", "MAX-G4"}:
        expected_schema = (
            MAX_G3_FOUNDATION_SCHEMA
            if result_id == "MAX-G3"
            else MAX_G4_BOUNDARY_SCHEMA
        )
        domains = specification.get("domains")
        if (
            not isinstance(domains, list)
            or sum(domain == expected_schema for domain in domains) != 1
        ):
            return False
    if result_id == "MAX-G6":
        return (
            assumption.get("node") == "equal"
            and assumption.get("left") == {"name": "source_tensor", "node": "variable"}
            and assumption.get("right")
            == {"entries": SOURCE_TENSOR, "node": "tensor"}
        )
    return (
        assumption.get("node") == "predicate_application"
        and assumption.get("name") == expected_name
    )


def _valid_ledger_pair(
    left: Mapping[str, Any],
    right: Mapping[str, Any],
    left_named: str,
    right_named: str,
) -> bool:
    result = CompileRelativePartitionDifference(left, left_named, right, right_named)
    return (
        result["label_count"]
        == len(left["candidates"]) + len(right["candidates"])
        and left["constraint_count"] == right["constraint_count"]
    )


def _valid_finite_event_transport(instance: Mapping[str, Any]) -> bool:
    if not _exact_keys(
        instance,
        {
            "worlds",
            "categorical_events",
            "probability_measure",
            "transport",
            "transported_probability_measure",
        },
    ):
        return False
    worlds = instance["worlds"]
    if (
        not isinstance(worlds, list)
        or not worlds
        or any(not isinstance(world, str) or not world for world in worlds)
        or len(worlds) != len(set(worlds))
    ):
        return False
    world_set = set(worlds)
    events = instance["categorical_events"]
    if not _exact_keys(events, {"E", "F"}):
        return False
    if any(
        not isinstance(event, list)
        or len(event) != len(set(event))
        or not set(event) <= world_set
        for event in events.values()
    ):
        return False
    probabilities = instance["probability_measure"]
    transport = instance["transport"]
    transported = instance["transported_probability_measure"]
    if set(probabilities) != world_set or set(transport) != world_set:
        return False
    targets = list(transport.values())
    if (
        any(not isinstance(target, str) or not target for target in targets)
        or len(targets) != len(set(targets))
        or set(transported) != set(targets)
    ):
        return False
    masses = {world: _fraction(probabilities[world]) for world in worlds}
    if any(value <= 0 for value in masses.values()) or sum(masses.values()) != 1:
        return False
    pushed = {transport[world]: masses[world] for world in worlds}
    return pushed == {target: _fraction(value) for target, value in transported.items()}


def _valid_point_configuration(value: Mapping[str, Any]) -> tuple[bool, int]:
    if not _exact_keys(value, {"points", "base_masses"}):
        return False, 0
    points = value["points"]
    masses = value["base_masses"]
    if (
        not isinstance(points, list)
        or not points
        or not isinstance(masses, list)
        or len(points) != len(masses)
        or not isinstance(points[0], list)
        or not points[0]
    ):
        return False, 0
    dimension = len(points[0])
    if any(
        not isinstance(point, list)
        or len(point) != dimension
        or any(isinstance(coordinate, (bool, float)) for coordinate in point)
        for point in points
    ):
        return False, 0
    if any(_fraction(mass) <= 0 for mass in masses):
        return False, 0
    return True, dimension


def ValidateMaxEntAssumptionModel(
    result_id: str,
    model: Mapping[str, Any],
    specification: Mapping[str, Any] | None = None,
) -> bool:
    try:
        if result_id not in RESULT_IDS or not isinstance(model, Mapping):
            return False
        expected_id, _ = EXPECTED_ASSUMPTIONS[result_id]
        if model.get("schema_version") != MODEL_VERSION or model.get("assumption_id") != expected_id:
            return False
        if not _specification_matches(result_id, specification):
            return False
        assignment = model.get("assignment")
        if not isinstance(assignment, Mapping):
            return False

        if result_id == "MAX-G1":
            if not _exact_keys(model, {"schema_version", "assumption_id", "assignment", "weight_domain"}) or not _exact_keys(assignment, {"A", "a", "B", "b"}):
                return False
            return (
                model["weight_domain"] == "all_nonnegative_real_vectors_of_declared_dimension"
                and assignment["a"] == assignment["A"]["named_candidate"]
                and assignment["b"] == assignment["B"]["named_candidate"]
                and _valid_ledger_pair(assignment["A"], assignment["B"], assignment["a"], assignment["b"])
            )

        if result_id == "MAX-G2":
            if not _exact_keys(model, {"schema_version", "assumption_id", "assignment"}) or not _exact_keys(assignment, {"F"}):
                return False
            compiled = CompileIntegerPolynomial(assignment["F"])
            return compiled["relative_partition_difference"] == assignment["F"]

        if result_id == "MAX-G3":
            if not _exact_keys(model, {"schema_version", "assumption_id", "assignment"}) or not _exact_keys(assignment, {"Phi"}):
                return False
            replay = BuildETRINVResidual(assignment["Phi"])
            return replay["equation_count"] == len(assignment["Phi"]["equations"])

        if result_id == "MAX-G4":
            if not _exact_keys(model, {"schema_version", "assumption_id", "assignment", "weight_domain"}) or not _exact_keys(assignment, {"A", "B"}):
                return False
            return (
                model["weight_domain"] == "full_nonnegative_real_orthant"
                and _valid_ledger_pair(
                    assignment["A"],
                    assignment["B"],
                    assignment["A"]["named_candidate"],
                    assignment["B"]["named_candidate"],
                )
            )

        if result_id == "MAX-G5":
            return (
                _exact_keys(model, {"schema_version", "assumption_id", "assignment"})
                and _exact_keys(assignment, {"I"})
                and _valid_finite_event_transport(assignment["I"])
            )

        if result_id == "MAX-G6":
            return (
                _exact_keys(model, {"schema_version", "assumption_id", "assignment"})
                and _exact_keys(assignment, {"source_tensor"})
                and assignment["source_tensor"] == SOURCE_TENSOR
            )

        if result_id == "MAX-G7":
            if not _exact_keys(model, {"schema_version", "assumption_id", "assignment", "fixed_support"}) or not _exact_keys(assignment, {"A", "B", "w0"}):
                return False
            left, right = assignment["A"], assignment["B"]
            if not _valid_ledger_pair(left, right, left["named_candidate"], right["named_candidate"]):
                return False
            left_support = sorted(set(tuple(row) for row in left["violation_rows"].values()))
            right_support = sorted(set(tuple(row) for row in right["violation_rows"].values()))
            declared_support = sorted(tuple(row) for row in model["fixed_support"])
            return (
                left_support == right_support == declared_support
                and set(left["consequence_map"].values()) == set(right["consequence_map"].values())
                and len(assignment["w0"]) == left["constraint_count"]
                and all(_fraction(value) > 0 for value in assignment["w0"])
            )

        if result_id == "MAX-G8":
            if not _exact_keys(model, {"schema_version", "assumption_id", "assignment"}) or not _exact_keys(assignment, {"response", "I"}):
                return False
            response, interval = assignment["response"], assignment["I"]
            if not _exact_keys(response, {"slices"}) or not _exact_keys(interval, {"left", "right", "endpoint_policy", "analytic_extension"}):
                return False
            slices = response["slices"]
            if not isinstance(slices, list) or not slices:
                return False
            if any(not _exact_keys(value, {"coefficient", "exponent"}) for value in slices):
                return False
            coefficients = [_fraction(value["coefficient"]) for value in slices]
            exponents = [_fraction(value["exponent"]) for value in slices]
            extension = interval["analytic_extension"]
            if not isinstance(extension, list) or len(extension) != 2:
                return False
            left, right = _fraction(interval["left"]), _fraction(interval["right"])
            extension_left, extension_right = map(_fraction, extension)
            return (
                all(value != 0 for value in coefficients)
                and len(exponents) == len(set(exponents))
                and interval["endpoint_policy"] == "closed"
                and extension_left < left < right < extension_right
            )

        if result_id == "MAX-G9":
            if not _exact_keys(model, {"schema_version", "assumption_id", "assignment", "mass_variation"}) or not _exact_keys(assignment, {"A", "B"}):
                return False
            left_valid, left_dimension = _valid_point_configuration(assignment["A"])
            right_valid, right_dimension = _valid_point_configuration(assignment["B"])
            return (
                left_valid
                and right_valid
                and left_dimension == right_dimension
                and model["mass_variation"] == "independent_strictly_positive_rational_fibre_masses"
            )
    except (KeyError, TypeError, ValueError, ZeroDivisionError):
        return False
    return False


def MaxEntAssumptionModel(result_id: str) -> dict[str, Any]:
    if result_id not in MAXENT_ASSUMPTION_MODELS:
        raise KeyError(result_id)
    return deepcopy(MAXENT_ASSUMPTION_MODELS[result_id])


__all__ = [
    "EXPECTED_ASSUMPTIONS",
    "MAXENT_ASSUMPTION_MODELS",
    "MODEL_VERSION",
    "MaxEntAssumptionModel",
    "SOURCE_TENSOR",
    "RESULT_IDS",
    "ValidateMaxEntAssumptionModel",
]
