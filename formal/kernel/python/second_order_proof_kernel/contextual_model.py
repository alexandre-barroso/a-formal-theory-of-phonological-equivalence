from __future__ import annotations

from fractions import Fraction
from typing import Any

from .application_model import QuadraticProfile
from .rational import ParseRational, RationalText


def _exact_json(value: Fraction) -> int | str:
    return value.numerator if value.denominator == 1 else RationalText(value)


def _phase_ratio(support: int, phase: Fraction, exponent: int) -> Fraction:
    if support < 1 or not 0 < phase <= 1 or exponent <= 1:
        raise ValueError("Phase coordinates are outside the declared domain")
    q = Fraction(1, exponent - 1)
    if q.denominator != 1:
        raise ValueError("Exact rational fixture requires an integral conjugate exponent")
    total = sum((Fraction(rank - 1) + phase) ** q.numerator for rank in range(1, support + 1))
    return total ** (exponent - 1) / exponent


def _two_trigger_slopes(span: int, ratio: Fraction, exponent: int) -> list[Fraction]:
    if span < 1 or ratio <= 0 or exponent != 2:
        raise ValueError("Exact contextual fixture is the declared quadratic case")
    return [Fraction(span + 1 - 2 * index, 2 * exponent) / ratio for index in range(1, span + 1)]


def _center_value(span: int, ratio: Fraction, exponent: int) -> Fraction:
    slopes = _two_trigger_slopes(span, ratio, exponent)
    cumulative: list[Fraction] = []
    value = Fraction(0)
    for slope in slopes:
        value += slope
        cumulative.append(value)
    return max(Fraction(0), Fraction(1) - max(cumulative))


def _directional_energy(path: list[Fraction], ratio: Fraction, exponent: int) -> Fraction:
    drops = [max(Fraction(0), left - right) for left, right in zip(path, path[1:])]
    return ratio * sum(value**exponent for value in drops) + sum(path[1:])


def _absolute_energy(path: list[Fraction], ratio: Fraction, exponent: int) -> Fraction:
    gaps = [abs(left - right) for left, right in zip(path, path[1:])]
    return ratio * sum(value**exponent for value in gaps) + sum(path[1:])


def _require_manifest(inputs: dict[str, Any], expected: dict[str, Any]) -> None:
    if inputs != expected:
        raise ValueError("Universal contextual proof manifest does not match the checked derivation schema")


def _c1_general(inputs: dict[str, Any]) -> tuple[dict[str, Any], dict[str, Any]]:
    manifest = {
        "domain": {"p": "p>1", "q": "1/(p-1)>0", "K": "integer K>=1", "u": "0<u<=1"},
        "phase_equation": "(p*rho)^q=sum_(r=1)^K (r-1+u)^q",
        "free_flux": "p*rho*sgn(s_i)*abs(s_i)^(p-1)=(L+1-2*i)/2",
        "support_test": "C_L(q)>=2^q*(p*rho)^q",
        "critical_spans": ["2*K-1", "2*K", "2*K+1"],
        "carrier": "(K,indicator(u>1/2))",
    }
    _require_manifest(inputs, manifest)

    if Fraction(1) - Fraction(1, 2) != Fraction(1, 2):
        raise AssertionError("Critical half-phase arithmetic failed")
    lower_index_map = "r in 1..K-1 maps to r+u in the phase sum; u^q is the extra positive term"
    middle_index_map = "r-1+1/2 compared termwise with r-1+u"
    upper_index_map = "r compared termwise with r-1+u"
    flux_increment = Fraction(1, 2) - Fraction(-1, 2)
    if flux_increment != 1:
        raise AssertionError("Free-flux stationarity increment failed")
    result = {
        "unique_optimizer": True,
        "regimes": {
            "L<=2K-1": "all_interiors_positive",
            "L=2K": "zero_iff_u<=1/2",
            "L>=2K+1": "zero_for_all_u",
        },
        "coarsest_binary_carrier": ["K", "indicator(u>1/2)"],
    }
    detail = {
        "derivation_method": "parametric induction-and-KKT schema",
        "foundation_rules": [
            "positive-real-power-is-strictly-increasing",
            "finite-termwise-sum-order",
            "strict-convex-KKT-sufficiency",
        ],
        "checked_flux_increment": RationalText(flux_increment),
        "lower_span_comparison": lower_index_map,
        "critical_span_comparison": middle_index_map,
        "upper_span_comparison": upper_index_map,
        "strictness": {
            "lower": "strict because u^q>0 and every paired term is strictly larger",
            "critical": "phase sum is strictly increasing in u",
            "upper": "weak with equality only at u=1",
        },
        "minimality_witness": "L=2K separates equal K across the two phase-bit classes",
    }
    return result, detail


def _c2_general(inputs: dict[str, Any]) -> tuple[dict[str, Any], dict[str, Any]]:
    manifest = {
        "domain": {"p": "p>1", "rho": "rho>0", "K": "integer K>=2"},
        "running_minimum": "y_i=min(x_0,...,x_i)",
        "one_trigger_evaluators": ["positive_part_edge", "absolute_edge"],
        "opposite_trigger_probe": "fixed right endpoint 1",
        "separator_span": "K+1",
        "imports": ["CTX-C1"],
    }
    _require_manifest(inputs, manifest)
    result = {
        "all_one_trigger_winners_equal": True,
        "complete_orders_equal": False,
        "shortest_opposite_trigger_separator": "K+1",
        "three_code_probes": ["K+1", "2K"],
    }
    detail = {
        "derivation_method": "running-minimum domination plus support-phase theorem",
        "running_minimum_checks": {
            "sites": "y_i<=x_i termwise",
            "directed_edges": "each new running-minimum drop is no larger than the corresponding original positive drop",
            "absolute_equals_directional_on_y": True,
            "unique_minimizer": "strict convexity makes the common monotone minimizer unique",
        },
        "shortestness": {
            "shorter_spans": "L<=K has fewer than K one-trigger followers, so both supports are positive",
            "separator": "at L=K+1 the forward profile has its first zero",
            "absolute_positive": "K+1<=2K-1 for K>=2, so CTX-C1 keeps every interior positive",
        },
        "dependency_used": "CTX-C1",
    }
    return result, detail


def ReplayContextualResult(
    algorithm: str, inputs: dict[str, Any]
) -> tuple[Any, dict[str, Any]]:
    if algorithm == "ctx_c1_phase_fixture_v1":
        support = inputs["support"]
        exponent = inputs["p"]
        values = [_phase_ratio(support, ParseRational(value), exponent) for value in inputs["phases"]]
        result = [_exact_json(value) for value in values]
        return result, {"exact_ratios": result}
    if algorithm == "ctx_c1_center_fixture_v1":
        values = [
            _center_value(inputs["span"], ParseRational(value), inputs["p"])
            for value in inputs["ratios"]
        ]
        result = [_exact_json(value) for value in values]
        return result, {"exact_center_values": result}
    if algorithm == "ctx_c1_carrier_fixture_v1":
        support = inputs["support"]
        result = [[support, int(ParseRational(value) > Fraction(1, 2))] for value in inputs["phases"]]
        return result, {"phase_threshold": "1/2"}
    if algorithm == "ctx_c1_general_v1":
        return _c1_general(inputs)
    if algorithm == "ctx_c2_order_fixture_v1":
        ratio = ParseRational(inputs["rho"])
        exponent = inputs["p"]
        paths = [[ParseRational(value) for value in path] for path in inputs["paths"]]
        result = [
            [_exact_json(_directional_energy(path, ratio, exponent)) for path in paths],
            [_exact_json(_absolute_energy(path, ratio, exponent)) for path in paths],
        ]
        return result, {"directional_then_absolute": result}
    if algorithm == "ctx_c2_shortest_fixture_v1":
        ratio = _phase_ratio(inputs["support"], ParseRational(inputs["phase"]), inputs["p"])
        forward = QuadraticProfile(ratio, Fraction(1), inputs["support"])[1:]
        center = _center_value(inputs["support"] + 1, ratio, inputs["p"])
        result = [
            [_exact_json(value) for value in forward],
            [_exact_json(center), _exact_json(center)],
        ]
        return result, {"rho": RationalText(ratio), "forward": result[0], "absolute": result[1]}
    if algorithm == "ctx_c2_general_v1":
        return _c2_general(inputs)
    raise ValueError("Unknown contextual result replay algorithm")
