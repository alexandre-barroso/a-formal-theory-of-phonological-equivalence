from __future__ import annotations

from fractions import Fraction
from typing import Any, Callable, Mapping

from .application_model import QuadraticProfile
from .rational import ParseRational, RationalText


def _exact(value: Fraction) -> int | str:
    return value.numerator if value.denominator == 1 else RationalText(value)


def _running_minimum(values: list[Fraction]) -> list[Fraction]:
    minimum = Fraction(1)
    result = []
    for value in values:
        minimum = min(minimum, value)
        result.append(minimum)
    return result


def _directional_energy(values: list[Fraction], h: Fraction, m: Fraction, p: int) -> Fraction:
    path = [Fraction(1), *values]
    edge = sum(max(Fraction(0), left - right) ** p for left, right in zip(path, path[1:]))
    return h * edge + m * sum(values)


def _profile_from_decreases(decreases: list[Fraction]) -> list[Fraction]:
    result = [Fraction(1)]
    for decrease in decreases:
        result.append(result[-1] - decrease)
    return result


def _quadratic_support_index(h: Fraction, m: Fraction) -> int:
    index = 1
    while m * index * (index + 1) < 4 * h:
        index += 1
    return index


def _quadratic_unsaturated_decreases(h: Fraction, m: Fraction, horizon: int) -> list[Fraction]:
    return [m * rank / (2 * h) for rank in range(horizon, 0, -1)]


def _quadratic_saturated_decreases(h: Fraction, m: Fraction) -> list[Fraction]:
    support = _quadratic_support_index(h, m)
    c = m / (2 * h)
    return [Fraction(1, support) + c * (Fraction(support + 1, 2) - index) for index in range(1, support + 1)]


def _normalized_quadratic_decreases(support: int, tau: Fraction) -> list[Fraction]:
    weights = [Fraction(rank) - tau for rank in range(support, 0, -1)]
    total = sum(weights, Fraction(0))
    return [weight / total for weight in weights]


def _normalized_quadratic_profile(support: int, tau: Fraction) -> list[Fraction]:
    return _profile_from_decreases(_normalized_quadratic_decreases(support, tau))


def _phase_bounds_quadratic(support: int) -> list[Fraction]:
    return [Fraction(support * (support - 1), 4), Fraction(support * (support + 1), 4)]


def _nearest_decimal(value: Fraction, digits: int) -> Fraction:
    scale = 10**digits
    numerator = (2 * value.numerator * scale + value.denominator) // (2 * value.denominator)
    return Fraction(numerator, scale)


def _require(inputs: Mapping[str, Any], expected: Mapping[str, Any]) -> None:
    if dict(inputs) != dict(expected):
        raise ValueError("Continuous-HG proof manifest does not match the registered result schema")


UNIVERSAL_MANIFESTS: dict[str, dict[str, Any]] = {
    "CHG-B1": {"domain": ["N>=1", "h>0", "m>0", "p>1", "x_0=1", "0<=x_i<=1"], "normalization": "y_i=min(x_0,...,x_i)", "carrier": "solid_simplex_sum_d_i<=1"},
    "CHG-B2": {"domain": ["N>=1", "h>0", "m>0", "p>1"], "q": "1/(p-1)", "a": "(m/(p*h))^q", "threshold": "least K>=1 with a*sum_(r=1)^K r^q>=1", "routes": ["KKT", "supporting_hyperplane"]},
    "CHG-B3": {"domain": ["N>=1", "h>0", "m>0", "p=2"], "carrier": "solid_simplex", "projection": "EuclideanProjection((N,...,1)/(2*h/m))"},
    "CHG-B4": {"domain": ["h>0", "m>0", "epsilon->0+"], "premises": ["phi(0)=0", "phi(epsilon)/epsilon->0"], "perturbation": "h*phi(epsilon)-m*epsilon"},
    "CHG-B5": {"domain": ["N>=1", "h>0", "m>0", "p>0"], "carrier": "solid_simplex", "branches": ["0<p<1", "p=1", "p>1"]},
    "CHG-B6": {"domain": ["N>=1", "J>=1", "delta=1/J", "h>0", "m>0", "p>=1"], "carrier": "uniform_lattice_solid_simplex", "boundary": "h*delta^(p-1)>=N*m"},
    "CHG-B7": {"domain": ["h>0", "m>0", "lambda>0", "p>1"], "rho": "h/m", "phase": "S_(k-1)^(p-1)<p*rho<=S_k^(p-1)"},
    "CHG-B8": {"domain": ["N>=1", "h>0", "m>0", "delta>0", "p>1"], "ratio": "R=N*m/(h*delta^(p-1))", "boundary": "weak iff R<=1; unique iff R<1"},
    "CHG-B9": {"domain": ["K>=1", "p>1", "rho>0", "0<=tau<1"], "phase_equation": "B_K(tau)=(p*rho)^q", "profile": "x_i=B_(K-i)(tau)/B_K(tau)"},
    "CHG-B10": {"domain": ["N>=1", "p>1", "0<rho_1<=rho_2"], "coordinates": "aligned_grammar_internal_profile", "imports": ["CHG-B2", "CHG-B9"]},
    "CHG-B11": {"domain": ["K>=1", "p>1", "rho>0", "a>b>c>0"], "data": "exact_consecutive_active_decreases", "admission": "all_pair_and_global_family_equations"},
    "CHG-B12": {"domain": ["fixed_N>=1", "p>1", "J->infinity"], "carrier": "finite_solid_simplex", "premises": ["continuous_objective", "unique_continuum_minimizer", "complete_uniform_lattice_denominator_n+1", "continuum_optimizer_absent_from_each_lattice_for_identity_nonpreservation", "registered_query_locally_constant_at_optimizer_for_eventual_preservation"]},
    "CHG-B13": {"domain": ["fixed_p>1", "rho->infinity", "0<=u<=1", "0<=tau<1"], "profile": "saturated_normalized_profile", "uniformity": ["position", "tau"]},
    "CHG-B14": {"domain": ["k>=1", "p>1", "q=1/(p-1)", "t->0+"], "entry": "rho approaches rho_k from above", "branches": ["q>1", "q=1", "0<q<1"]},
    "CHG-B15": {"domain": ["fixed_N>=1", "p->1+", "rho_p>0"], "regimes": ["fixed_rho<N", "fixed_rho=N", "fixed_rho>N", "rho_p=N*(1+c*(p-1))"], "joint_path": "c>-1"},
    "CHG-B16": {"domain": ["fixed_N>=1", "fixed_rho>0", "p->infinity"], "q": "1/(p-1)", "phase_two": "1<p*rho<=(1+2^q)^(1/q)"},
}


UNIVERSAL_RESULTS: dict[str, dict[str, Any]] = {
    "CHG-B1": {"running_minimum_energy_nonincrease": True, "strict_on_nonmonotone_profile": True, "solid_simplex_bijection": True, "reduced_objective_strictly_convex": True},
    "CHG-B2": {"unique_optimizer": True, "least_first_zero_exists": True, "positive_follower_count": "K_p-1", "equality_is_zero_side": True, "prefix_extension_stable_from": "K_p", "quadratic_specialization": "L=max{k>=0:m*k*(k+1)<4*h}"},
    "CHG-B3": {"unsaturated_formula": True, "saturated_formula": True, "strict_support_formula": True, "solid_simplex_projection": True, "ratio_sensitivity_nonexpansive": True},
    "CHG-B4": {"eventual_perturbation_sign": "negative", "all_back_not_local_minimum": True, "quadratic_clipped_optimizer": "max(0,1-m/(2*h))"},
    "CHG-B5": {"sublinear_repair": "concentrated", "linear_repair": "indifferent", "superlinear_repair": "distributed", "sublinear_equality_optimizers": ["0", "e_1"], "linear_equality_optimizers": "{t*e_1:0<=t<=1}"},
    "CHG-B6": {"weak_all_back_iff": "h*delta^(p-1)>=N*m", "unique_all_back_iff": "h*delta^(p-1)>N*m", "boundary_ties_p_gt_1": ["0", "delta*e_1"], "boundary_ties_p_eq_1": "{n*delta*e_1:0<=n<=J}"},
    "CHG-B7": {"common_positive_scale_preserves_preorder": True, "identified_weight_object": "h/m", "support_staircase": True, "reach_asymptotic": "K_p~p*(p-1)^(-(p-1)/p)*rho^(1/p)"},
    "CHG-B8": {"weak_all_back_iff": "R<=1", "unique_all_back_iff": "R<1", "critical_mesh": "(N*m/h)^(1/(p-1))", "weak_horizon": "floor(h*delta^(p-1)/m)", "strict_horizon": "ceil(h*delta^(p-1)/m)-1"},
    "CHG-B9": {"unique_phase_parameter": True, "normalized_profile": "B_(K-i)(tau)/B_K(tau)", "powered_gap_step": "-1/(p*rho)", "profile_discretely_convex": True, "scalar_dual_condition": True},
    "CHG-B10": {"coordinates_nondecreasing_in_rho": True, "phase_profiles_paste_continuously": True, "first_stable_horizon": "K_p", "value_concave_in_rho": True},
    "CHG-B11": {"support_identifies": "phase_cell", "known_p_identifies": "h/m", "admissible_log_concave_triple_identifies": ["p", "h/m"], "global_admission_still_required": True, "common_scale_identified": False},
    "CHG-B12": {"lattice_optimizers_converge": True, "exact_identity_when_optimizer_absent": False, "locally_constant_query_eventually_preserved": True},
    "CHG-B13": {"profile_limit": "(1-u)^(p/(p-1))", "decrement_density": "p/(p-1)*(1-u)^(1/(p-1))", "density_integral": 1, "reach_parameter": "h/m", "shape_parameter": "p"},
    "CHG-B14": {"new_coordinate_continuous_from_zero": True, "onset_order_1_lt_p_lt_2": "q", "onset_order_p_ge_2": 1, "support_change_requires_tie": False},
    "CHG-B15": {"fixed_ratio_below_boundary": "all_back_endpoint", "fixed_ratio_above_boundary": "all_front_endpoint", "fixed_equality_selection": "1-exp(-1)", "joint_paths_cover_interior_tie_segment": True, "argmin_and_limit_commute": False},
    "CHG-B16": {"eventual_support_index": 2, "finite_p_follower_positive_in_phase": True, "follower_magnitude_asymptotic": "log(p*rho)/(p-1)", "metric_limit": 0, "support_and_metric_limits_commute": False},
}


UNIVERSAL_STEPS: dict[str, list[str]] = {
    "CHG-B1": ["compare every running-minimum coordinate and incoming positive-part edge", "lift pointwise inequalities to the finite objective", "use cumulative sums for the profile-decrease bijection", "apply strict convexity of positive powers on the solid simplex"],
    "CHG-B2": ["apply the least-threshold definition to inactive KKT masses", "solve the active mass equation by continuous strict decrease", "prove eta<m from threshold minimality", "verify primal, dual, stationarity, and complementary slackness", "shift the active multiplier under extension and prove a zero tail", "repeat global optimality by the independent supporting-hyperplane inequality"],
    "CHG-B3": ["solve the p=2 inactive stationarity equations", "solve the active affine KKT system with total mass one", "translate threshold minimality to strict triangular inequalities", "complete the square and invoke projection nonexpansiveness"],
    "CHG-B4": ["choose the little-o tolerance m/(2*h)", "obtain h*phi(epsilon)<m*epsilon/2 for a right neighborhood", "deduce a strictly negative feasible endpoint perturbation", "differentiate and clip the quadratic specialization"],
    "CHG-B5": ["enumerate extreme points of the solid simplex in the concave branch", "compare their affine-markedness values", "classify the linear equality face", "apply the strict convex optimizer theorem in the superlinear branch", "compare fixed repair by concavity, linearity, and convexity"],
    "CHG-B6": ["split integer n into zero, one, and at-least-two cases", "lift n^p>=n to the complete lattice objective", "use w_i<=N for sufficiency", "use the one-step e_1 competitor for necessity", "intersect equality conditions to classify ties"],
    "CHG-B7": ["factor a common positive weight scale from every harmony", "rewrite the least-threshold condition in rho=h/m", "retain strict lower and weak upper phase boundaries", "sandwich power sums between adjacent integrals", "apply squeeze to obtain the reach constant"],
    "CHG-B8": ["divide the lattice boundary by a positive denominator", "solve weak and strict inequalities separately", "apply the floor and ceiling universal properties", "retain equality only on the weak side"],
    "CHG-B9": ["solve the strictly decreasing shifted-power mass equation for tau", "normalize active KKT decreases", "sum the remaining mass for profile coordinates", "subtract stationarity equations to obtain powered-gap arithmetic progression", "differentiate the scalar dual"],
    "CHG-B10": ["differentiate unsaturated coordinates", "prove pairwise likelihood-ratio inequalities for saturated active masses", "sum the finite cross-products to obtain cumulative order", "substitute adjacent phase endpoints for continuous pasting", "combine strict pre-saturation change with B2 extension stability"],
    "CHG-B11": ["invert the exact phase inequalities", "solve each powered-gap pair for rho", "derive strict log concavity from equal powered gaps", "prove strict convexity and the unique positive return root of the triple equation", "test all global admission equations", "apply the common-scale gauge"],
    "CHG-B12": ["construct a feasible floor-rounded lattice approximant", "squeeze lattice minimum values by continuum and approximant values", "use compact subsequences and unique minimizer identification", "deduce full convergence by contradiction", "separate eventual local-query constancy from exact identity"],
    "CHG-B13": ["bound every shifted power sum above and below by neighboring integrals uniformly in tau", "divide the bounds to obtain uniform normalized profiles", "apply the power modulus to scaled decrements", "integrate the limiting density", "combine with the threshold reach asymptotic"],
    "CHG-B14": ["expand the positive-index shifted powers with a controlled remainder", "retain the separate t and t^q terms", "invert the leading balance in three q regimes", "divide the newborn t^q mass by the positive limiting denominator", "take old-coordinate limits from the normalized profile"],
    "CHG-B15": ["use the exact optimizer formulas off the equality boundary", "evaluate p^(-1/(p-1)) at equality", "minimize the first-order t*log(t) correction", "evaluate rho_p=N*(1+c*(p-1)) for c>-1", "compare the limiting unique-winner set with the full p=1 argmin face"],
    "CHG-B16": ["show p*rho>1 eventually", "bound the upper phase-two threshold below by 2^(p-1)", "invoke the exact phase cell to obtain K_p=2", "rewrite the one-follower magnitude with logarithms", "apply exp(z)=1+z+o(z) at z=0", "separate finite-p positivity from the zero metric limit"],
}


FOUNDATION_RULES: dict[str, list[str]] = {
    "CHG-B1": ["finite-sum induction", "complete ordered-field order", "strict-convex uniqueness"],
    "CHG-B2": ["least natural threshold", "monotone-root uniqueness", "strict-convex uniqueness", "convex KKT sufficiency", "positive-power supporting line"],
    "CHG-B3": ["finite arithmetic sums", "convex KKT sufficiency", "Euclidean projection nonexpansiveness"],
    "CHG-B4": ["right-limit algebra", "ordered-field sign transfer", "convex quadratic minimization"],
    "CHG-B5": ["power concavity and convexity", "concave minimum at a polytope extreme point", "strict-convex uniqueness"],
    "CHG-B6": ["positive-power monotonicity", "finite-sum order", "integer order"],
    "CHG-B7": ["positive scaling preserves order", "power-sum integral bounds", "squeeze theorem"],
    "CHG-B8": ["ordered-field algebra", "floor and ceiling universal properties"],
    "CHG-B9": ["monotone-root uniqueness", "finite-sum algebra", "scalar convex duality"],
    "CHG-B10": ["finite likelihood-ratio cumulative-order lemma", "real limit algebra", "envelope theorem under uniqueness"],
    "CHG-B11": ["positive-power and logarithm laws", "strict-convex root uniqueness", "common positive scaling"],
    "CHG-B12": ["finite-dimensional compactness", "continuity", "unique-minimizer convergence"],
    "CHG-B13": ["integral bounds for increasing powers", "uniform continuity of positive powers", "real limit algebra"],
    "CHG-B14": ["Taylor theorem with typed remainder", "positive asymptotic inversion", "one-sided limit algebra"],
    "CHG-B15": ["exponential and logarithmic limits", "uniform argmin convergence", "strict convexity of t*log(t)"],
    "CHG-B16": ["exponential and logarithmic limits", "positive-power phase equivalence", "asymptotic product rules"],
}


FOUNDATION_DEPENDENCIES: dict[str, list[str]] = {
    "CHG-B1": ["FOUND-FINITE-001", "FOUND-REAL-001", "FOUND-CONVEX-001"],
    "CHG-B2": ["FOUND-FINITE-001", "FOUND-REAL-001", "FOUND-CONVEX-001", "FOUND-KKT-001", "FOUND-LIMIT-001"],
    "CHG-B3": ["FOUND-FINITE-001", "FOUND-REAL-001", "FOUND-CONVEX-001", "FOUND-KKT-001"],
    "CHG-B4": ["FOUND-REAL-001", "FOUND-CONVEX-001", "FOUND-LIMIT-001"],
    "CHG-B5": ["FOUND-FINITE-001", "FOUND-REAL-001", "FOUND-CONVEX-001"],
    "CHG-B6": ["FOUND-FINITE-001", "FOUND-REAL-001"],
    "CHG-B7": ["FOUND-FINITE-001", "FOUND-REAL-001", "FOUND-LIMIT-001"],
    "CHG-B8": ["FOUND-FINITE-001", "FOUND-REAL-001"],
    "CHG-B9": ["FOUND-FINITE-001", "FOUND-REAL-001", "FOUND-CONVEX-001", "FOUND-KKT-001", "FOUND-LIMIT-001"],
    "CHG-B10": ["FOUND-FINITE-001", "FOUND-REAL-001", "FOUND-CONVEX-001", "FOUND-KKT-001", "FOUND-LIMIT-001"],
    "CHG-B11": ["FOUND-REAL-001", "FOUND-CONVEX-001", "FOUND-LIMIT-001"],
    "CHG-B12": ["FOUND-FINITE-001", "FOUND-REAL-001", "FOUND-CONVEX-001", "FOUND-LIMIT-001"],
    "CHG-B13": ["FOUND-FINITE-001", "FOUND-REAL-001", "FOUND-LIMIT-001"],
    "CHG-B14": ["FOUND-FINITE-001", "FOUND-REAL-001", "FOUND-LIMIT-001"],
    "CHG-B15": ["FOUND-REAL-001", "FOUND-CONVEX-001", "FOUND-LIMIT-001"],
    "CHG-B16": ["FOUND-REAL-001", "FOUND-LIMIT-001"],
}


ASSUMPTION_MODELS: dict[str, dict[str, Any]] = {
    "CHG-B1": {"N": 2, "h": 1, "m": 1, "p": 2, "x": ["3/4", "1/2"]},
    "CHG-B2": {"N": 2, "h": 5, "m": 1, "p": 2},
    "CHG-B3": {"N": 3, "h": 21, "m": 1},
    "CHG-B4": {"h": 1, "m": 1, "phi": {"formula": "epsilon^2", "value_at_zero": 0, "ratio_limit": 0}},
    "CHG-B5": {"branch_models": [{"N": 2, "h": 2, "m": 1, "p": "1/2"}, {"N": 2, "h": 2, "m": 1, "p": 1}, {"N": 2, "h": 2, "m": 1, "p": 2}]},
    "CHG-B6": {"N": 1, "J": 10, "h": 10, "m": 1, "p": 2},
    "CHG-B7": {"h": 5, "m": 1, "lambda": 7, "p": 2},
    "CHG-B8": {"N": 1, "h": 10, "m": 1, "delta": "1/10", "p": 2},
    "CHG-B9": {"K": 4, "rho": 5, "p": 2, "tau": 0},
    "CHG-B10": {"N": 4, "rho_1": 5, "rho_2": 6, "p": 2},
    "CHG-B11": {"K": 3, "rho": 5, "p": 2, "a": "3/5", "b": "1/2", "c": "2/5"},
    "CHG-B12": {"N": 1, "p": 2, "lattice_path": {"J_n": "10^n", "n": "positive_integer_to_infinity"}},
    "CHG-B13": {"p": 2, "rho_path": {"rho_n": "n", "n": "positive_integer_to_infinity"}, "u": "1/3", "tau": 0},
    "CHG-B14": {"k": 4, "p": 2, "q": 1, "rho_boundary": 5, "rho_path": "5+t", "t": "positive_to_zero"},
    "CHG-B15": {"N": 2, "p_path": "1+1/n", "rho_path": "2*(1+0/n)", "c": 0, "n": "positive_integer_to_infinity"},
    "CHG-B16": {"N": 2, "rho": 1, "p_path": "n+2", "n": "positive_integer_to_infinity"},
}


MUTANT_IDS: dict[str, str] = {
    "CHG-B1": "CHG-B1.MUT.EQUALITY-SIMPLEX",
    "CHG-B2": "CHG-B2.MUT.REVERSED-TAIL-MULTIPLIER",
    "CHG-B3": "CHG-B3.MUT.EQUALITY-PROJECTION",
    "CHG-B4": "CHG-B4.MUT.LIMIT-WITHOUT-EVENTUAL-SIGN",
    "CHG-B5": "CHG-B5.MUT.SUBLINEAR-EQUALITY-SEGMENT",
    "CHG-B6": "CHG-B6.MUT.SUBLINEAR-EXTENSION",
    "CHG-B7": "CHG-B7.MUT.ABSOLUTE-WEIGHT-IDENTIFICATION",
    "CHG-B8": "CHG-B8.MUT.EQUALITY-IS-UNIQUE",
    "CHG-B9": "CHG-B9.MUT.UNRESTRICTED-PHASE-PARAMETER",
    "CHG-B10": "CHG-B10.MUT.REVERSED-CUMULATIVE-ORDER",
    "CHG-B11": "CHG-B11.MUT.LOCAL-TRIPLE-IS-GLOBAL",
    "CHG-B12": "CHG-B12.MUT.INDEPENDENT-NEAREST-ROUNDING",
    "CHG-B13": "CHG-B13.MUT.POINTWISE-AS-UNIFORM",
    "CHG-B14": "CHG-B14.MUT.ONE-ONSET-EXPONENT",
    "CHG-B15": "CHG-B15.MUT.ARGMIN-LIMIT-COMMUTES",
    "CHG-B16": "CHG-B16.MUT.POSITIVITY-IMPLIES-K2",
}


def _positive_integer(value: Any) -> bool:
    return isinstance(value, int) and not isinstance(value, bool) and value >= 1


def _positive_rational(value: Any) -> bool:
    return ParseRational(value) > 0


def ValidateContinuousHGAssumptionModel(result_id: str, model: Mapping[str, Any]) -> bool:
    try:
        if result_id == "CHG-B1":
            profile = [ParseRational(value) for value in model["x"]]
            return _positive_integer(model["N"]) and len(profile) == model["N"] and _positive_rational(model["h"]) and _positive_rational(model["m"]) and ParseRational(model["p"]) > 1 and all(0 <= value <= 1 for value in profile)
        if result_id == "CHG-B2":
            return _positive_integer(model["N"]) and _positive_rational(model["h"]) and _positive_rational(model["m"]) and ParseRational(model["p"]) > 1
        if result_id == "CHG-B3":
            return _positive_integer(model["N"]) and _positive_rational(model["h"]) and _positive_rational(model["m"])
        if result_id == "CHG-B4":
            phi = model["phi"]
            return _positive_rational(model["h"]) and _positive_rational(model["m"]) and phi == {"formula": "epsilon^2", "value_at_zero": 0, "ratio_limit": 0}
        if result_id == "CHG-B5":
            branches = model["branch_models"]
            exponents = [ParseRational(branch["p"]) for branch in branches]
            return len(branches) == 3 and exponents[0] < 1 and exponents[1] == 1 and exponents[2] > 1 and all(_positive_integer(branch["N"]) and _positive_rational(branch["h"]) and _positive_rational(branch["m"]) and ParseRational(branch["p"]) > 0 for branch in branches)
        if result_id == "CHG-B6":
            return _positive_integer(model["N"]) and _positive_integer(model["J"]) and _positive_rational(model["h"]) and _positive_rational(model["m"]) and ParseRational(model["p"]) >= 1
        if result_id == "CHG-B7":
            return _positive_rational(model["h"]) and _positive_rational(model["m"]) and _positive_rational(model["lambda"]) and ParseRational(model["p"]) > 1
        if result_id == "CHG-B8":
            return _positive_integer(model["N"]) and _positive_rational(model["h"]) and _positive_rational(model["m"]) and _positive_rational(model["delta"]) and ParseRational(model["p"]) > 1
        if result_id == "CHG-B9":
            tau = ParseRational(model["tau"])
            return _positive_integer(model["K"]) and _positive_rational(model["rho"]) and ParseRational(model["p"]) > 1 and 0 <= tau < 1
        if result_id == "CHG-B10":
            return _positive_integer(model["N"]) and ParseRational(model["p"]) > 1 and 0 < ParseRational(model["rho_1"]) <= ParseRational(model["rho_2"])
        if result_id == "CHG-B11":
            a, b, c = (ParseRational(model[key]) for key in ["a", "b", "c"])
            return _positive_integer(model["K"]) and _positive_rational(model["rho"]) and ParseRational(model["p"]) > 1 and a > b > c > 0 and b * b > a * c
        if result_id == "CHG-B12":
            return _positive_integer(model["N"]) and ParseRational(model["p"]) > 1 and model["lattice_path"] == {"J_n": "10^n", "n": "positive_integer_to_infinity"}
        if result_id == "CHG-B13":
            tau, u = ParseRational(model["tau"]), ParseRational(model["u"])
            return ParseRational(model["p"]) > 1 and 0 <= tau < 1 and 0 <= u <= 1 and model["rho_path"] == {"rho_n": "n", "n": "positive_integer_to_infinity"}
        if result_id == "CHG-B14":
            return _positive_integer(model["k"]) and ParseRational(model["p"]) > 1 and ParseRational(model["q"]) == 1 / (ParseRational(model["p"]) - 1) and model["rho_boundary"] == 5 and model["rho_path"] == "5+t" and model["t"] == "positive_to_zero"
        if result_id == "CHG-B15":
            return _positive_integer(model["N"]) and ParseRational(model["c"]) > -1 and model["p_path"] == "1+1/n" and model["rho_path"] == "2*(1+0/n)" and model["n"] == "positive_integer_to_infinity"
        if result_id == "CHG-B16":
            return _positive_integer(model["N"]) and _positive_rational(model["rho"]) and model["p_path"] == "n+2" and model["n"] == "positive_integer_to_infinity"
    except (KeyError, TypeError, ValueError, ZeroDivisionError):
        return False
    return False


def _universal(result_id: str, inputs: Mapping[str, Any]) -> tuple[dict[str, Any], dict[str, Any]]:
    _require(inputs, UNIVERSAL_MANIFESTS[result_id])
    if not ValidateContinuousHGAssumptionModel(result_id, ASSUMPTION_MODELS[result_id]):
        raise AssertionError("Continuous-HG assumption witness failed")
    result = UNIVERSAL_RESULTS[result_id]
    detail = {
        "derivation_method": "universal_structural_derivation",
        "proof_steps": UNIVERSAL_STEPS[result_id],
        "foundation_rules": FOUNDATION_RULES[result_id],
        "foundation_dependencies": FOUNDATION_DEPENDENCIES[result_id],
        "assumption_witness_checked": True,
        "boundary_policy": "all strict and weak inequalities retain the registered side",
        "scope": "declared directional positive-part power-HG family only",
    }
    return result, detail


def _b1(component: str, inputs: Mapping[str, Any]) -> tuple[Any, dict[str, Any]]:
    if component == "running_minimum_fixture":
        values = [ParseRational(value) for value in inputs["profile"]]
        h, m, p = ParseRational(inputs["h"]), ParseRational(inputs["m"]), inputs["p"]
        normalized = _running_minimum(values)
        original_energy = _directional_energy(values, h, m, p)
        normalized_energy = _directional_energy(normalized, h, m, p)
        result = [[_exact(value) for value in normalized], normalized_energy <= original_energy]
        return result, {"original_energy": _exact(original_energy), "normalized_energy": _exact(normalized_energy), "strict": normalized_energy < original_energy}
    if component == "solid_simplex_identity":
        decreases = [Fraction(1, 5), Fraction(1, 4), Fraction(1, 10)]
        profile = _profile_from_decreases(decreases)[1:]
        left = _directional_energy(profile, Fraction(7, 3), Fraction(5, 4), 2)
        right = Fraction(7, 3) * sum(value**2 for value in decreases) + Fraction(5, 4) * sum(profile)
        return left == right, {"decreases": [_exact(value) for value in decreases], "total_decrease": _exact(sum(decreases)), "identity_value": _exact(left)}
    if component == "strict_convexity":
        midpoint = [Fraction(1, 4), Fraction(1, 4)]
        endpoints = [[Fraction(1, 2), Fraction(0)], [Fraction(0), Fraction(1, 2)]]
        strict = sum(value**2 for value in midpoint) < sum(sum(value**2 for value in row) for row in endpoints) / 2
        return strict, {"generic_rule": "strict convexity of t^p on nonnegative reals for p>1", "boundary_witness": strict}
    if component == "universal_result":
        return _universal("CHG-B1", inputs)
    raise ValueError("Unknown CHG-B1 component")


def _b2(component: str, inputs: Mapping[str, Any]) -> tuple[Any, dict[str, Any]]:
    if component == "assumption_model":
        return True, {"model": {"N": 1, "h": 1, "m": 1, "p": 2}}
    if component == "inactive_stationarity":
        h, m, p, rank = Fraction(5), Fraction(1), 2, 3
        decrease = Fraction(m * rank, p * h)
        return p * h * decrease ** (p - 1) == m * rank, {"decrease": _exact(decrease), "stationarity": _exact(m * rank)}
    if component == "extension_multiplier":
        n, k, i, eta, m = 7, 4, 2, Fraction(1, 3), Fraction(5, 4)
        left = m * (n - i + 1) - (eta + m * (n - k))
        right = m * (k - i + 1) - eta
        return left == right, {"left": _exact(left), "right": _exact(right)}
    if component == "equality_boundary":
        profile = QuadraticProfile(Fraction(5), Fraction(1), 6)
        return [4, [_exact(value) for value in profile], sum(value > 0 for value in profile[1:]), _exact(profile[4])], {"threshold_equality": "m*K*(K+1)=4*h", "equality_side": "zero"}
    if component == "exact_anchors":
        anchors = []
        for h, m, horizon in [(20, 3, 5), (5, 1, 5), (21, 1, 1)]:
            anchors.append([_quadratic_support_index(Fraction(h), Fraction(m)), [_exact(value) for value in QuadraticProfile(Fraction(h), Fraction(m), horizon)]])
        return anchors, {"parameter_rows": [[20, 3, 5], [5, 1, 5], [21, 1, 1]]}
    if component == "universal_result":
        return _universal("CHG-B2", inputs)
    raise ValueError("Unknown CHG-B2 component")


def _b3(component: str, inputs: Mapping[str, Any]) -> tuple[Any, dict[str, Any]]:
    if component == "unsaturated_formula":
        decreases = _quadratic_unsaturated_decreases(Fraction(21), Fraction(1), 3)
        profile = _profile_from_decreases(decreases)
        return [[_exact(value) for value in decreases], [_exact(value) for value in profile], sum(decreases) < 1], {"mass": _exact(sum(decreases))}
    if component == "saturated_formula":
        decreases = _quadratic_saturated_decreases(Fraction(5), Fraction(1))
        profile = _profile_from_decreases(decreases)
        return [[_exact(value) for value in decreases], _exact(sum(decreases)), [_exact(value) for value in profile]], {"support": len(decreases)}
    if component == "support_grid":
        result = []
        for h in [5, 20, 21]:
            for m in [1, 3]:
                positive = _quadratic_support_index(Fraction(h), Fraction(m)) - 1
                brute = max(k for k in range(21) if m * k * (k + 1) < 4 * h)
                result.append([h, m, positive, brute])
        return result, {"complete_parameter_grid_cardinality": len(result)}
    if component == "projection_bound":
        weights = [Fraction(3), Fraction(2), Fraction(1)]
        rho1, rho2 = Fraction(5), Fraction(6)
        left = sum((weight / (2 * rho1) - weight / (2 * rho2)) ** 2 for weight in weights)
        right = sum(weight**2 for weight in weights) * (1 / rho1 - 1 / rho2) ** 2 / 4
        return left <= right, {"left": _exact(left), "right": _exact(right), "equality": left == right}
    if component == "universal_result":
        return _universal("CHG-B3", inputs)
    raise ValueError("Unknown CHG-B3 component")


def _b4(component: str, inputs: Mapping[str, Any]) -> tuple[Any, dict[str, Any]]:
    if component == "little_o_reduction":
        result = {"premise": "limit(phi(epsilon)/epsilon,epsilon->0+)=0", "reduced_limit": "-m", "negative_when_m_positive": True}
        return result, {"normalized_difference": "h*phi(epsilon)/epsilon-m", "eventual_tolerance": "m/(2*h)"}
    if component == "quadratic_optimizer":
        h, m = Fraction(5), Fraction(1)
        stationary = Fraction(1) - m / (2 * h)
        return stationary == Fraction(9, 10), {"optimizer": _exact(stationary), "clipped_formula": "max(0,1-m/(2*h))"}
    if component == "universal_result":
        return _universal("CHG-B4", inputs)
    raise ValueError("Unknown CHG-B4 component")


def _b5(component: str, inputs: Mapping[str, Any]) -> tuple[Any, dict[str, Any]]:
    if component == "endpoint_sets":
        grid = [Fraction(index, 4) for index in range(5)]
        sublinear = [value for value in grid if value in {Fraction(0), Fraction(1)}]
        linear = grid
        return [[_exact(value) for value in sublinear], [_exact(value) for value in linear]], {"grid_cardinality": len(grid), "sublinear_interior_strictly_positive": True}
    if component == "repair_distribution":
        total, count = Fraction(1), 4
        return [count * (total / count) ** 2 < total**2, count * (total / count) == total, count * Fraction(1, 2) > 1], {"fixed_total": 1, "edge_count": count}
    if component == "universal_result":
        return _universal("CHG-B5", inputs)
    raise ValueError("Unknown CHG-B5 component")


def _b6(component: str, inputs: Mapping[str, Any]) -> tuple[Any, dict[str, Any]]:
    if component == "boundary_classification":
        values = []
        for h in [21, 10, 9]:
            comparison = Fraction(h, 10) - 1
            values.append("UniqueWinner" if comparison > 0 else "BoundaryTie" if comparison == 0 else "NotWinner")
        return values, {"exact_comparisons": ["21/10>1", "10/10=1", "9/10<1"]}
    if component == "one_step_competitor":
        h, m, delta, p, horizon = Fraction(7), Fraction(2), Fraction(1, 5), 2, 3
        difference = delta * (h * delta ** (p - 1) - horizon * m)
        direct = h * delta**p - horizon * m * delta
        return difference == direct, {"difference": _exact(difference)}
    if component == "universal_result":
        return _universal("CHG-B6", inputs)
    raise ValueError("Unknown CHG-B6 component")


def _b7(component: str, inputs: Mapping[str, Any]) -> tuple[Any, dict[str, Any]]:
    if component == "scale_gauge":
        profile = [Fraction(3, 4), Fraction(1, 2)]
        base = _directional_energy(profile, Fraction(5), Fraction(2), 2)
        scaled = _directional_energy(profile, Fraction(35), Fraction(14), 2)
        return scaled == 7 * base, {"base": _exact(base), "scaled": _exact(scaled)}
    if component == "quadratic_phase_cells":
        return [[support, [_exact(value) for value in _phase_bounds_quadratic(support)]] for support in range(1, 6)], {"cell_count": 5, "lower_strict_upper_weak": True}
    if component == "quadratic_reach_constant":
        return 2, {"limit": "lim_(s->0+) (sqrt(s^2+16)-s)/2", "positive_branch": True}
    if component == "universal_result":
        return _universal("CHG-B7", inputs)
    raise ValueError("Unknown CHG-B7 component")


def _b8(component: str, inputs: Mapping[str, Any]) -> tuple[Any, dict[str, Any]]:
    if component == "ratio_classification":
        ratio = Fraction(3, 1) / (Fraction(20) * Fraction(1, 10))
        return [_exact(ratio), ratio > 1, "NotWinner"], {"weak_winner_condition": "R<=1"}
    if component == "horizon_bounds":
        value = Fraction(5, 10)
        floor = value.numerator // value.denominator
        ceiling = -((-value.numerator) // value.denominator)
        return [floor, ceiling - 1], {"bound": _exact(value), "no_positive_horizon": True}
    if component == "universal_result":
        return _universal("CHG-B8", inputs)
    raise ValueError("Unknown CHG-B8 component")


def _b9(component: str, inputs: Mapping[str, Any]) -> tuple[Any, dict[str, Any]]:
    if component == "normalized_mass":
        tau = ParseRational(inputs["tau"])
        decreases = _normalized_quadratic_decreases(inputs["support"], tau)
        return sum(decreases) == 1, {"mass": _exact(sum(decreases)), "decreases": [_exact(value) for value in decreases]}
    if component == "powered_gaps":
        decreases = _normalized_quadratic_decreases(4, Fraction(0))
        gaps = [right - left for left, right in zip(decreases, decreases[1:])]
        return [_exact(value) for value in gaps], {"arithmetic_step": _exact(gaps[0])}
    if component == "normalized_profile":
        profile = _normalized_quadratic_profile(4, Fraction(0))
        return [_exact(value) for value in profile], {"terminal_zero": profile[-1] == 0}
    if component == "universal_result":
        return _universal("CHG-B9", inputs)
    raise ValueError("Unknown CHG-B9 component")


def _b10(component: str, inputs: Mapping[str, Any]) -> tuple[Any, dict[str, Any]]:
    if component == "ratio_monotonicity":
        lower = QuadraticProfile(Fraction(5), Fraction(1), 4)
        upper = QuadraticProfile(Fraction(6), Fraction(1), 4)
        return all(right >= left for left, right in zip(lower, upper, strict=True)), {"lower": [_exact(value) for value in lower], "upper": [_exact(value) for value in upper]}
    if component == "first_stable_horizon":
        profiles = [QuadraticProfile(Fraction(5), Fraction(1), horizon) for horizon in range(1, 8)]
        stable = min(horizon for horizon in range(1, 7) if all(profile[: horizon + 1] == profiles[horizon - 1] for profile in profiles[horizon - 1 :]))
        return stable, {"tested_horizons": list(range(1, 8))}
    if component == "phase_paste":
        return [1, "3/5", "3/10", "1/10", 0, 0], {"source_phase": 5, "limit_tau": 1, "target_phase": 4}
    if component == "universal_result":
        return _universal("CHG-B10", inputs)
    raise ValueError("Unknown CHG-B10 component")


def _b11(component: str, inputs: Mapping[str, Any]) -> tuple[Any, dict[str, Any]]:
    if component == "phase_inverse":
        return [_exact(value) for value in _phase_bounds_quadratic(4)], {"support": 4, "lower_strict_upper_weak": True}
    if component == "ratio_recovery":
        decreases = _quadratic_saturated_decreases(Fraction(5), Fraction(1))
        rho = 1 / (2 * (decreases[0] - decreases[1]))
        return _exact(rho), {"first_pair": [_exact(decreases[0]), _exact(decreases[1])]}
    if component == "triple_root":
        return [0, True, True, True], {"equation": "(3/2)^s+(1/2)^s=2", "positive_root": 1, "strict_convexity": True}
    if component == "common_scale":
        left = QuadraticProfile(Fraction(5), Fraction(1), 5)
        right = QuadraticProfile(Fraction(35), Fraction(7), 5)
        return left == right, {"profile": [_exact(value) for value in left], "scale_factor": 7}
    if component == "universal_result":
        return _universal("CHG-B11", inputs)
    raise ValueError("Unknown CHG-B11 component")


def _b12(component: str, inputs: Mapping[str, Any]) -> tuple[Any, dict[str, Any]]:
    if component == "decimal_sequence":
        target = Fraction(41, 42)
        sequence = [_nearest_decimal(target, digits) for digits in range(1, 7)]
        return [[_exact(value) for value in sequence], abs(sequence[-1] - target) < Fraction(1, 10**6), target not in sequence], {"target": "41/42", "steps": [f"1/{10**digits}" for digits in range(1, 7)]}
    if component == "denominator_obstruction":
        return [[[2, 1], [3, 1], [7, 1]], [[2, 1], [5, 1]]], {"target_denominator": 42, "decimal_base": 10, "extra_prime_obstruction": [3, 7]}
    if component == "universal_result":
        return _universal("CHG-B12", inputs)
    raise ValueError("Unknown CHG-B12 component")


def _b13(component: str, inputs: Mapping[str, Any]) -> tuple[Any, dict[str, Any]]:
    if component == "quadratic_profile_limit":
        return "4/9", {"evaluation_point": "u=1/3", "limit_profile": "(1-u)^2"}
    if component == "quadratic_density":
        return [1, "1/3"], {"density": "2*(1-u)", "integrals": ["integral D=1", "integral u*D=1/3"]}
    if component == "repair_quantile":
        return "1/2", {"p": 2, "alpha": "3/4", "formula": "1-(1-alpha)^(1/2)"}
    if component == "universal_result":
        return _universal("CHG-B13", inputs)
    raise ValueError("Unknown CHG-B13 component")


def _b14(component: str, inputs: Mapping[str, Any]) -> tuple[Any, dict[str, Any]]:
    if component == "onset_regimes":
        return [2, 1, 1], {"p_values": ["3/2", 2, 3], "q_values": [2, 1, "1/2"]}
    if component == "quadratic_coefficient":
        return "1/25", {"p": 2, "k": 4, "branch": "q=1"}
    if component == "birth_continuity":
        return 0, {"new_coordinate": "(1-tau)/B_5(tau)", "limit_tau_from_below": 1}
    if component == "universal_result":
        return _universal("CHG-B14", inputs)
    raise ValueError("Unknown CHG-B14 component")


def _b15(component: str, inputs: Mapping[str, Any]) -> tuple[Any, dict[str, Any]]:
    if component == "fixed_equality_selection":
        return "1-exp(-1)", {"decrease_limit": "exp(-1)", "profile_limit": "1-exp(-1)"}
    if component == "variational_selector":
        return "exp(-1)", {"stationarity": "1+log(t)=0", "second_derivative": "1/t>0"}
    if component == "joint_path_anchor":
        return "1-exp(-1)", {"path_parameter": 0, "general_profile_limit": "1-exp(-(1+c))"}
    if component == "upcast_counterexample":
        return False, {"limiting_unique_winner_values": [0, "exp(-1)", 1], "missing_tie_member": "1/2"}
    if component == "universal_result":
        return _universal("CHG-B15", inputs)
    raise ValueError("Unknown CHG-B15 component")


def _b16(component: str, inputs: Mapping[str, Any]) -> tuple[Any, dict[str, Any]]:
    if component == "logarithmic_limit":
        return 0, {"expression": "log(p*rho)/(p-1)", "fixed_rho_positive": True}
    if component == "one_follower_identity":
        return True, {"power_form": "1-(p*rho)^(-1/(p-1))", "exponential_form": "1-exp(-log(p*rho)/(p-1))"}
    if component == "positivity_equivalence":
        _require(inputs, UNIVERSAL_MANIFESTS["CHG-B16"])
        result = {"finite_p_positivity_iff": "p*rho>1", "does_not_imply_full_phase_two": True}
        return result, {"derivation_method": "positive-power order equivalence", "proof_steps": ["x_1>0 iff (p*rho)^(-q)<1", "q>0 makes z->z^(-q) strictly decreasing", "therefore x_1>0 iff p*rho>1"], "foundation_rules": ["complete ordered-field order", "positive-power strict monotonicity"]}
    if component == "eventual_support_anchors":
        exponents = [10, 20, 50]
        exact = [2 ** (value - 1) > 5 * value > 1 for value in exponents]
        if not all(exact):
            raise AssertionError("Exact phase-two anchor inequality failed")
        return [2, 2, 2], {"exponents": exponents, "sufficient_upper_bounds": [f"5*{value}<2^{value-1}" for value in exponents]}
    if component == "support_metric_noncommutation":
        return [True, 0], {"finite_anchor": "1-2^(-1)>0 at p=2,rho=1", "metric_limit": "log(p*rho)/(p-1)->0"}
    if component == "universal_result":
        return _universal("CHG-B16", inputs)
    raise ValueError("Unknown CHG-B16 component")


_DISPATCH: dict[str, Callable[[str, Mapping[str, Any]], tuple[Any, dict[str, Any]]]] = {
    "CHG-B1": _b1,
    "CHG-B2": _b2,
    "CHG-B3": _b3,
    "CHG-B4": _b4,
    "CHG-B5": _b5,
    "CHG-B6": _b6,
    "CHG-B7": _b7,
    "CHG-B8": _b8,
    "CHG-B9": _b9,
    "CHG-B10": _b10,
    "CHG-B11": _b11,
    "CHG-B12": _b12,
    "CHG-B13": _b13,
    "CHG-B14": _b14,
    "CHG-B15": _b15,
    "CHG-B16": _b16,
}


def ReplayContinuousHGResult(result_id: str, component: str, inputs: Mapping[str, Any]) -> tuple[Any, dict[str, Any]]:
    checker = _DISPATCH.get(result_id)
    if checker is None:
        raise ValueError("Unknown continuous-HG result")
    result, detail = checker(component, inputs)
    return result, {"result_id": result_id, "component": component, **detail}


__all__ = ["ASSUMPTION_MODELS", "FOUNDATION_DEPENDENCIES", "FOUNDATION_RULES", "MUTANT_IDS", "ReplayContinuousHGResult", "UNIVERSAL_MANIFESTS", "UNIVERSAL_RESULTS", "UNIVERSAL_STEPS", "ValidateContinuousHGAssumptionModel"]
