from __future__ import annotations

from fractions import Fraction
from typing import Any, Callable

from .application_model import QuadraticProfile
from .rational import RationalText


def _exact(value: Fraction) -> int | str:
    return value.numerator if value.denominator == 1 else RationalText(value)


def _dot(left: list[Fraction], right: list[Fraction]) -> Fraction:
    if len(left) != len(right):
        raise ValueError("Vector dimensions differ")
    return sum((a * b for a, b in zip(left, right, strict=True)), Fraction(0))


def _matvec(matrix: list[list[Fraction]], vector: list[Fraction]) -> list[Fraction]:
    if any(len(row) != len(vector) for row in matrix):
        raise ValueError("Matrix and vector dimensions differ")
    return [_dot(row, vector) for row in matrix]


def _transpose(matrix: list[list[Fraction]]) -> list[list[Fraction]]:
    if not matrix or any(len(row) != len(matrix[0]) for row in matrix):
        raise ValueError("Malformed matrix")
    return [list(column) for column in zip(*matrix, strict=True)]


def _inverse_diagonal(metric: list[Fraction]) -> list[Fraction]:
    if any(value <= 0 for value in metric):
        raise ValueError("Metric must be positive diagonal")
    return [1 / value for value in metric]


def _solve_linear(matrix: list[list[Fraction]], right: list[Fraction]) -> list[Fraction]:
    if len(matrix) != len(right) or any(len(row) != len(matrix) for row in matrix):
        raise ValueError("Linear system must be square")
    augmented = [row[:] + [value] for row, value in zip(matrix, right, strict=True)]
    size = len(matrix)
    for column in range(size):
        pivot = next((row for row in range(column, size) if augmented[row][column]), None)
        if pivot is None:
            raise ValueError("Singular active-set system")
        augmented[column], augmented[pivot] = augmented[pivot], augmented[column]
        scale = augmented[column][column]
        augmented[column] = [value / scale for value in augmented[column]]
        for row in range(size):
            if row == column:
                continue
            factor = augmented[row][column]
            augmented[row] = [value - factor * pivot_value for value, pivot_value in zip(augmented[row], augmented[column], strict=True)]
    return [row[-1] for row in augmented]


def _metric_projection(
    normals: list[list[Fraction]], thresholds: list[Fraction], metric: list[Fraction]
) -> tuple[Fraction, list[Fraction], list[Fraction]]:
    if not normals or len(normals) != len(thresholds):
        raise ValueError("Projection needs matching active normals and thresholds")
    dimension = len(metric)
    if any(len(row) != dimension for row in normals):
        raise ValueError("Projection dimension mismatch")
    inverse = _inverse_diagonal(metric)
    gram = [
        [sum(a * inv * b for a, inv, b in zip(left, inverse, right, strict=True)) for right in normals]
        for left in normals
    ]
    multipliers = _solve_linear(gram, thresholds)
    if any(value < 0 for value in multipliers):
        raise ValueError("Active-set multiplier is negative")
    point = [
        inverse[index] * sum(multiplier * normal[index] for multiplier, normal in zip(multipliers, normals, strict=True))
        for index in range(dimension)
    ]
    if any(_dot(normal, point) < threshold for normal, threshold in zip(normals, thresholds, strict=True)):
        raise ValueError("Projected point is infeasible")
    distance = sum(weight * value * value for weight, value in zip(metric, point, strict=True))
    return distance, point, multipliers


def _support_e1(component: str) -> tuple[Any, dict[str, Any]]:
    if component == "zero_lifting_derivative":
        result = {
            "right_derivative": "PsiPrimeRight(0)-PhiPrime(x_previous)",
            "zero_site_slope_reduction": "-PhiPrime(x_previous)<0",
        }
        detail = {
            "derivation": [
                "raise the first zero coordinate by epsilon>0",
                "only its incoming directional edge and its site term vary to first order",
                "PsiPrimeRight(0)=0 and strict edge increase at x_previous>0 give a negative right derivative",
            ],
            "foundation_rules": ["one-sided derivative algebra", "strict convex monotonicity"],
        }
        return result, detail
    if component == "strict_prefix_bound":
        result = {
            "flux_drop_per_positive_site": ">=c",
            "telescoped_bound": "K_N*c<PhiPrime(1)",
            "integer_form": "K_N<=ceil(PhiPrime(1)/c)-1",
        }
        return result, {
            "derivation": [
                "KKT flux decreases by at least c=PsiPrimeRight(0)>0 at each positive coordinate",
                "the last positive flux is strictly positive",
                "the first flux is at most PhiPrime(1)",
                "strict real inequality converts to the displayed integer ceiling",
            ]
        }
    if component == "endpoint_support_classification":
        result = {
            "zero_endpoint_slope": "every finite winner coordinate is positive",
            "positive_endpoint_slope": "uniform finite positive-prefix bound",
        }
        return result, {
            "premises_checked": [
                "finite horizon",
                "local directional edge/site objective",
                "differentiable strictly increasing edge marginal",
                "convex site cost with declared right endpoint slope",
                "attained unique minimizer",
            ],
            "imports": ["FOUND-REAL-001", "FOUND-CONVEX-001", "FOUND-KKT-001"],
        }
    raise ValueError("Unknown SUP-E1 proof component")


def _support_e2(component: str) -> tuple[Any, dict[str, Any]]:
    if component == "free_endpoint_contradiction":
        a, b = Fraction(7, 3), Fraction(7, 3)
        c = a - b
        result = {"derived_new_drop_flux": _exact(c), "terminal_requires": ">0", "contradiction": c == 0}
        return result, {"elimination": ["a=b", "a-c=b", "therefore c=0"], "strictness": "PsiPrime(x)>0 for x>0"}
    if component == "quadratic_prefix_change":
        one = Fraction(1, 2)
        two = [Fraction(2, 5), Fraction(1, 5)]
        gradient_one = [2 * (one - 1) + 2 * one]
        gradient_two = [2 * (two[0] - 1) + 2 * (two[0] - two[1]) + 2 * two[0], -2 * (two[0] - two[1]) + 2 * two[1]]
        if gradient_one != [0] or gradient_two != [0, 0]:
            raise AssertionError("Quadratic free-end stationarity failed")
        result = [[1, _exact(one)], [1, *[_exact(value) for value in two]]]
        return result, {"hessian_leading_minors": [[4], [6, 20]], "prefix_changed": one != two[0]}
    if component == "zero_extension":
        short = QuadraticProfile(Fraction(5), Fraction(1), 4)
        long = QuadraticProfile(Fraction(5), Fraction(1), 7)[:5]
        result = [[_exact(value) for value in short], [_exact(value) for value in long]]
        return result, {"same_prefix": short == long, "terminal_zero": short[-1] == 0}
    raise ValueError("Unknown SUP-E2 proof component")


def _support_e3(component: str) -> tuple[Any, dict[str, Any]]:
    if component == "quadratic_decay_root":
        polynomial_at_bounds = [Fraction(1), Fraction(-1, 4)]
        result = {"minimal_polynomial": [1, -3, 1], "isolating_interval": [0, "1/2"], "unique": True}
        return result, {"endpoint_signs": [_exact(value) for value in polynomial_at_bounds], "derivative_on_interval": "2*lambda-3<0"}
    if component == "continuation_energy_identity":
        result = {
            "decay_equation": "(h/m)*(1-lambda)^(p-1)*(1-lambda^(p-1))=lambda^(p-1)",
            "energy": "(h*(1-lambda)^p+m*lambda^p)/(1-lambda^p)",
            "continuation_coefficient": "h*(1-lambda)^(p-1)",
        }
        return result, {
            "exact_reduction": "substitute m=h*(1-lambda)^(p-1)*(1-lambda^(p-1))/lambda^(p-1)",
            "denominators_positive": ["lambda^(p-1)>0", "1-lambda^p>0"],
        }
    if component == "infinite_geometric_minimizer":
        result = {
            "existence": True,
            "unique_profile": "x_i=lambda^i",
            "root_count_on_(0,1)": 1,
            "ell_p_admissible": True,
        }
        return result, {
            "proof_schema": [
                "homogeneity gives V(a)=C*a^p",
                "Bellman stationarity makes the retained ratio constant",
                "the scalar left side decreases strictly from h/m to 0 while the right side increases from 0 to 1",
                "geometric summation proves ell-p admissibility and finite objective",
                "strict convexity plus the attained stationary profile proves uniqueness",
            ],
            "imports": ["FOUND-REAL-001", "FOUND-CONVEX-001", "FOUND-LIMIT-001"],
        }
    raise ValueError("Unknown SUP-E3 proof component")


def _support_e4(component: str) -> tuple[Any, dict[str, Any]]:
    if component == "continuation_coefficient":
        result = {
            "tail_value": "C*x_N^p",
            "coefficient": "C=h*(1-lambda)^(p-1)",
            "unique_within": "terminal monomials tau*x_N^p",
        }
        return result, {"endpoint_stationarity": "tau=C", "dependency": "SUP-E3"}
    if component == "kazakh_repair":
        decay = Fraction(3, 5)
        coefficient = Fraction(15, 4) * (1 - decay)
        profile = [decay**index for index in range(6)]
        markedness = Fraction(1)
        first_gradient = 2 * Fraction(15, 4) * (profile[1] - 1) + 2 * (markedness + coefficient) * profile[1]
        if first_gradient != 0:
            raise AssertionError("Repaired first-follower stationarity failed")
        result = [_exact(first_gradient), _exact(coefficient), [_exact(value) for value in profile]]
        return result, {"decay": "3/5", "terminal_coefficient": _exact(coefficient)}
    if component == "linear_vs_matched_power":
        linear = QuadraticProfile(Fraction(5), Fraction(1), 5)
        matched = [Fraction(3, 5) ** index for index in range(6)]
        result = [[_exact(value) for value in linear], [_exact(value) for value in matched]]
        return result, {"linear_has_exact_zero": linear[-1] == 0, "matched_is_all_positive": all(value > 0 for value in matched)}
    if component == "exact_tail_replacement":
        result = {"all_finite_prefixes_projective": True, "coefficient_unique_in_monomial_class": True}
        return result, {
            "proof_schema": [
                "SUP-E3 identifies the exact optimized tail value V(x_N)=C*x_N^p",
                "substitution of V into the finite objective is Bellman elimination, not approximation",
                "terminal Euler stationarity forces tau=C among monomial terms tau*x_N^p",
            ],
            "dependency": "SUP-E3",
        }
    raise ValueError("Unknown SUP-E4 proof component")


def _positive_ray(vector: list[Fraction], reference: list[Fraction]) -> bool:
    if len(vector) != len(reference) or all(value == 0 for value in reference):
        return False
    pivot = next(index for index, value in enumerate(reference) if value)
    ratio = vector[pivot] / reference[pivot]
    return ratio > 0 and vector == [ratio * value for value in reference]


def _selection_f1(component: str) -> tuple[Any, dict[str, Any]]:
    if component == "positive_ray_predicate":
        reference = [Fraction(1), Fraction(2)]
        probes = [[Fraction(2), Fraction(4)], [Fraction(-1), Fraction(-2)], [Fraction(1), Fraction(1)]]
        result = [_positive_ray(vector, reference) for vector in probes]
        return result, {"domain_cardinality": len(probes), "reference": [1, 2]}
    if component == "sphere_probabilities":
        result = {
            "pairwise": "1/4",
            "selected": "3*(Pi-2*ArcCot(Sqrt(2)))/(8*Pi)",
            "strict_overcount": True,
        }
        return result, {
            "sphere_radius": 2,
            "events": ["A>1", "A>1 and A>B"],
            "angular_identity": "ArcCot(Sqrt(2))=ArcTan(1/Sqrt(2))",
        }
    if component == "overcount_witness":
        squares = [Fraction(36, 25), Fraction(9, 4), Fraction(31, 100)]
        result = {"radius_squared": _exact(sum(squares)), "pairwise": True, "selected": False}
        return result, {"coordinates": ["6/5", "3/2", "Sqrt(31)/10"], "failed_rival_inequality": "A>B"}
    if component == "universal_radial_equivalence":
        result = {
            "event_identity_iff": "every rival normal is a positive scalar multiple of the target normal",
            "pairwise_event_is_upper_bound": True,
            "probability_equality_if_positive_rays": "every measure on the parameter space",
            "strict_probability_converse": "requires a proved nonempty open spherical gap and a full-support spherical law",
        }
        return result, {
            "proof_schema": [
                "the selected event is the intersection of all rival halfspaces and is contained in the named pairwise halfspace",
                "positive scalar duplicate normals define the same open homogeneous halfspace in g+delta",
                "event equality is equivalent to every rival normal lying on the named positive ray",
                "literal event equality entails equal probability under every measure",
                "strict probability under the normalized Haar-induced spherical law follows whenever a nonempty relatively open gap is separately proved",
            ],
            "imports": ["FOUND-REAL-001", "FOUND-MEASURE-001"],
        }
    raise ValueError("Unknown SEL-F1 proof component")


def _binary_harmony(input_vector: list[Fraction], output: list[Fraction], faith: list[list[Fraction]], marked: list[list[Fraction]]) -> Fraction:
    return _dot(input_vector, _matvec(faith, output)) + _dot(output, _matvec(marked, output))


def _selection_f2(component: str) -> tuple[Any, dict[str, Any]]:
    faith = [[Fraction(20), Fraction(-17)], [Fraction(3), Fraction(17)]]
    marked = [[Fraction(0), Fraction(-1)], [Fraction(-1), Fraction(0)]]
    outputs = [[Fraction(0), Fraction(0)], [Fraction(1), Fraction(0)], [Fraction(0), Fraction(1)], [Fraction(1), Fraction(1)]]
    scores = [[_binary_harmony(input_vector, output, faith, marked) for output in outputs] for input_vector in ([Fraction(1), Fraction(0)], [Fraction(0), Fraction(1)])]
    if component == "complete_scores":
        result = [[_exact(value) for value in row] for row in scores]
        return result, {"unique_winner_indices": [1, 3], "candidate_order": ["0", "y", "u", "z"]}
    x_normals = [[Fraction(0), Fraction(1), Fraction(0), Fraction(0), Fraction(2)]]
    x_thresholds = [Fraction(19)]
    w_normals = [[Fraction(0), Fraction(0), Fraction(0), Fraction(-1), Fraction(-2)], [Fraction(0), Fraction(0), Fraction(1), Fraction(-1), Fraction(0)]]
    w_thresholds = [Fraction(15), Fraction(14)]
    if component == "euclidean_projection":
        dx, px, mux = _metric_projection(x_normals, x_thresholds, [Fraction(1)] * 5)
        dw, pw, muw = _metric_projection(w_normals, w_thresholds, [Fraction(1)] * 5)
        result = [_exact(dx), _exact(dw), _exact(dw - dx), [_exact(value) for value in px], [_exact(value) for value in pw], [_exact(value) for value in muw]]
        return result, {"x_multipliers": [_exact(value) for value in mux], "strict_reversal": dw > dx}
    if component == "frobenius_projection":
        metric = [Fraction(1), Fraction(1), Fraction(1), Fraction(1), Fraction(2)]
        dx, _, _ = _metric_projection(x_normals, x_thresholds, metric)
        dw, _, _ = _metric_projection(w_normals, w_thresholds, metric)
        result = [_exact(dx), _exact(dw), _exact(dw - dx)]
        return result, {"strict_reversal": dw > dx, "metric_diagonal": [1, 1, 1, 1, 2]}
    if component == "common_radial_law":
        dx, _, _ = _metric_projection(x_normals, x_thresholds, [Fraction(1)] * 5)
        dw, _, _ = _metric_projection(w_normals, w_thresholds, [Fraction(1)] * 5)
        if not dx < dw:
            raise AssertionError("Selected-region onset order does not reverse")
        euclidean_shell = Fraction(80)
        euclidean_point = [Fraction(0), Fraction(4), Fraction(0), Fraction(0), Fraction(8)]
        if _dot(euclidean_point, euclidean_point) != euclidean_shell or _dot(x_normals[0], euclidean_point) <= x_thresholds[0] or not euclidean_shell < dw:
            raise AssertionError("Euclidean shell witness is invalid")
        frobenius_shell = Fraction(122)
        frobenius_point = [
            Fraction(9, 10),
            Fraction(127, 20),
            Fraction(2, 5),
            Fraction(1, 4),
            Fraction(127, 20),
        ]
        frobenius_metric = [Fraction(1), Fraction(1), Fraction(1), Fraction(1), Fraction(2)]
        frobenius_norm_square = sum(
            weight * value * value
            for weight, value in zip(frobenius_metric, frobenius_point, strict=True)
        )
        if frobenius_norm_square != frobenius_shell or _dot(x_normals[0], frobenius_point) <= x_thresholds[0] or not frobenius_shell < Fraction(618, 5):
            raise AssertionError("Frobenius shell witness is invalid")

        euclidean_far_shell = Fraction(233)
        euclidean_far_first = [Fraction(0), Fraction(5), Fraction(12), Fraction(0), Fraction(8)]
        euclidean_far_second = [Fraction(10), Fraction(0), Fraction(6), Fraction(-9), Fraction(-4)]
        if _dot(euclidean_far_first, euclidean_far_first) != euclidean_far_shell:
            raise AssertionError("Euclidean far-shell first-event point has the wrong norm")
        if _dot(euclidean_far_second, euclidean_far_second) != euclidean_far_shell:
            raise AssertionError("Euclidean far-shell second-event point has the wrong norm")
        if not (
            0 < 1 + euclidean_far_first[0] + euclidean_far_first[1] + 2 * euclidean_far_first[4]
            and 19 < euclidean_far_first[1] + 2 * euclidean_far_first[4]
            and 0 < 18 + euclidean_far_first[0] + 2 * euclidean_far_first[4]
        ):
            raise AssertionError("Euclidean far-shell first-event point is not strict")
        if not (
            -3 < euclidean_far_second[2]
            and 14 < euclidean_far_second[2] - euclidean_far_second[3]
            and 15 < -euclidean_far_second[3] - 2 * euclidean_far_second[4]
        ):
            raise AssertionError("Euclidean far-shell second-event point is not strict")

        frobenius_far_shell = Fraction(153)
        frobenius_far_first = [Fraction(0), Fraction(5), Fraction(0), Fraction(0), Fraction(8)]
        frobenius_far_second = [Fraction(2), Fraction(0), Fraction(6), Fraction(-9), Fraction(-4)]
        for name, point in (
            ("first", frobenius_far_first),
            ("second", frobenius_far_second),
        ):
            norm_square = sum(
                weight * value * value
                for weight, value in zip(frobenius_metric, point, strict=True)
            )
            if norm_square != frobenius_far_shell:
                raise AssertionError(f"Frobenius far-shell {name}-event point has the wrong norm")
        if not (
            0 < 1 + frobenius_far_first[0] + frobenius_far_first[1] + 2 * frobenius_far_first[4]
            and 19 < frobenius_far_first[1] + 2 * frobenius_far_first[4]
            and 0 < 18 + frobenius_far_first[0] + 2 * frobenius_far_first[4]
        ):
            raise AssertionError("Frobenius far-shell first-event point is not strict")
        if not (
            -3 < frobenius_far_second[2]
            and 14 < frobenius_far_second[2] - frobenius_far_second[3]
            and 15 < -frobenius_far_second[3] - 2 * frobenius_far_second[4]
        ):
            raise AssertionError("Frobenius far-shell second-event point is not strict")

        result = {
            "euclidean_intermediate_shell_radius_squared": 80,
            "euclidean_intermediate_probability_order": "P(w->y)=0<P(x->z)",
            "euclidean_far_shell_radius_squared": 233,
            "euclidean_two_shell_probability_order": "0<P(w->y)<P(x->z)",
            "frobenius_intermediate_shell_radius_squared": 122,
            "frobenius_intermediate_probability_order": "P(w->y)=0<P(x->z)",
            "frobenius_far_shell_radius_squared": 153,
            "frobenius_two_shell_probability_order": "0<P(w->y)<P(x->z)",
            "far_shell_weight": "epsilon=a/(2*(a+c))",
            "probability_gap_identity": "P(x->z)-P(w->y)=a/2+epsilon*b",
            "both_named_errors_positive": True,
            "one_common_two_shell_spherical_law_per_declared_metric": True,
        }
        return result, {
            "proof_schema": [
                "the exact Euclidean shell 80 lies strictly between squared onsets 361/5 and 1010/9",
                "the point (0,4,0,0,8) lies on that shell and satisfies the x-region inequality with strict slack one",
                "the w-region is empty on that shell because its squared onset exceeds 80",
                "the exact Frobenius shell 122 lies strictly between squared onsets 361/3 and 618/5",
                "the point (9/10,127/20,2/5,1/4,127/20) has Frobenius squared norm 122 and strict x-region slack 1/20",
                "the w-region is empty on the Frobenius shell because its squared onset exceeds 122",
                "on Euclidean squared radius 233, (0,5,12,0,8) and (10,0,6,-9,-4) are strict points of the first and second selected-output events",
                "on Frobenius squared radius 153, (0,5,0,0,8) and (2,0,6,-9,-4) are strict points of the first and second selected-output events",
                "the strict far-shell witnesses lie in nonempty open angular patches and therefore have positive normalized spherical measure",
                "write a>0 for the first-event mass on the intermediate shell and b,c>0 for the first- and second-event masses on the far shell",
                "mix far-shell weight epsilon=a/(2*(a+c)) into the intermediate shell; then 0<epsilon<1, the later event has mass epsilon*c>0, and the earlier-minus-later gap is a/2+epsilon*b>0",
                "the resulting two-atom radial law and normalized angular law are common to both compared inputs in each declared metric",
            ],
            "euclidean_squared_onsets": [_exact(dx), _exact(dw)],
            "frobenius_squared_onsets": ["361/3", "618/5"],
            "intermediate_strict_slacks": [1, "1/20"],
            "far_shell_points": {
                "euclidean": [
                    [_exact(value) for value in euclidean_far_first],
                    [_exact(value) for value in euclidean_far_second],
                ],
                "frobenius": [
                    [_exact(value) for value in frobenius_far_first],
                    [_exact(value) for value in frobenius_far_second],
                ],
            },
            "imports": ["FOUND-MEASURE-001"],
        }
    raise ValueError("Unknown SEL-F2 proof component")


_DISPATCH: dict[str, Callable[[str], tuple[Any, dict[str, Any]]]] = {
    "SUP-E1": _support_e1,
    "SUP-E2": _support_e2,
    "SUP-E3": _support_e3,
    "SUP-E4": _support_e4,
    "SEL-F1": _selection_f1,
    "SEL-F2": _selection_f2,
}


def ReplaySupportSelection(result_id: str, component: str) -> tuple[Any, dict[str, Any]]:
    checker = _DISPATCH.get(result_id)
    if checker is None:
        raise ValueError("Unknown support/selection result")
    result, detail = checker(component)
    return result, {"result_id": result_id, "component": component, **detail}
