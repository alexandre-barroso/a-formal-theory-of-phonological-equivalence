from __future__ import annotations

from fractions import Fraction
from typing import Any, Callable

from .rational import RationalText


def _exact(value: Fraction) -> int | str:
    return value.numerator if value.denominator == 1 else RationalText(value)


def _d1(component: str) -> tuple[Any, dict[str, Any]]:
    if component == "periodic_shift":
        result = {
            "F": "y+epsilon*delta/(2*Pi)*sin(2*Pi*y/delta)",
            "shift_identity": "F(y+delta)-F(y)=delta",
            "strictly_increasing_when": "abs(epsilon)<1",
        }
        return result, {
            "derivative": "1+epsilon*cos(2*Pi*y/delta)",
            "periodic_term": "P(y+delta)=P(y)",
        }
    if component == "integrated_potential":
        result = {
            "potential": "c*d^2/2+epsilon*delta^2/(4*Pi^2*c)*(1-cos(2*Pi*c*d/delta))",
            "derivative": "F(c*d)",
        }
        return result, {"normalization": "potential(0)=0", "parameters": ["c>0", "delta>0", "abs(epsilon)<1"]}
    if component == "candidate_order_reversal":
        result = {"difference": "1/100+(-9+Sqrt(5))/(32*Pi^2)", "sign": "negative"}
        return result, {"transcendental_bounds": ["314/100<Pi<22/7", "223/100<Sqrt(5)<224/100"]}
    if component == "fixed_load_equivalence":
        result = {
            "winner_equivalence_iff": "F(y+lambda)=F(y)+lambda on the complete reachable flux domain",
            "general_solution": "F(y)=y+P(y), P lambda-periodic",
            "obstacle_signs_preserved": True,
        }
        return result, {
            "proof_schema": [
                "old KKT residual sign is sign(y_i-y_(i+1)+lambda)",
                "new residual sign is sign(F(y_i)-F(y_(i+1))+lambda)",
                "strict monotonicity plus the shift identity preserves negative, zero, and positive residuals and obstacle multipliers",
                "complete two-edge probes realize every reachable pair (y,y+lambda), forcing the shift identity",
                "P=F-identity converts the shift identity into lambda-periodicity",
            ],
            "scope": "complete reachable probe language only",
        }
    raise ValueError("Unknown FLUX-D1 component")


def _d2(component: str) -> tuple[Any, dict[str, Any]]:
    if component == "commensurate_period":
        period = Fraction(1, 105)
        result = [_exact(Fraction(1, 5) / period), _exact(Fraction(1, 21) / period)]
        return result, {"common_period": "1/105", "integer_multiples": result}
    if component == "star_defect":
        result = {"epsilon": "1/2", "central_gradient_defect": "-1/(2*Pi)", "nonzero": True}
        return result, {"old_central_gradient": 0, "topology": "degree_three_star"}
    if component == "load_topology_rigidity":
        result = {
            "commensurate_loads": "nonidentity common-period gauge remains",
            "incommensurate_loads": "normalized continuous gauge is identity",
            "complete_degree_three_star": "normalized continuous gauge is identity",
        }
        return result, {
            "proof_schema": [
                "FLUX-D1 makes every registered load a period of P=F-identity",
                "commensurate loads possess a common nonzero period",
                "two incommensurate periods generate a dense additive subgroup",
                "continuity makes a function invariant under a dense period group constant; normalization makes the constant zero",
                "complete star probes impose additivity; continuous additive normalized F is identity",
            ],
            "dependency": "FLUX-D1",
        }
    raise ValueError("Unknown FLUX-D2 component")


def _d3(component: str) -> tuple[Any, dict[str, Any]]:
    raw = [Fraction(1, 3), Fraction(-2, 3), Fraction(1)]
    if component == "ledger_null_vector":
        matrix = [[Fraction(3, 2), Fraction(3, 4), Fraction(0)], [Fraction(1), Fraction(1), Fraction(1, 3)]]
        product = [sum(a * b for a, b in zip(row, raw, strict=True)) for row in matrix]
        result = [_exact(value) for value in product]
        return result, {"scaled_integral_matrix": [[_exact(value) for value in row] for row in matrix], "null_vector": [_exact(value) for value in raw]}
    if component == "monotonicity_bound":
        weighted_norm = sum(Fraction(index) * abs(value) for index, value in enumerate(raw, start=1))
        lower = Fraction(1) - Fraction(1, 10)
        result = _exact(lower)
        return result, {"weighted_l1_norm": _exact(weighted_norm), "derivative_perturbation_upper_bound": "1/10"}
    if component == "heldout_score":
        result = "1/(280*Pi^2)"
        return result, {"heldout_distance": "1/8", "registered_distances": ["1/3", "1/4"], "nonzero": True}
    if component == "finite_ledger_nonidentification":
        result = {
            "for_every_finite_ledger": "a distinct arbitrarily close analytic periodic gauge exists",
            "registered_path_winners_scores_ties_margins_fixed_support_maxent": "preserved exactly",
            "some_unregistered_score": "changed",
            "nullity_lower_bound": "K-J for K>J",
        }
        return result, {
            "proof_schema": [
                "J registered score constraints form a J by K linear integral matrix",
                "K>J gives a nonzero coefficient vector by rank-nullity",
                "distinct sine frequencies make the resulting analytic periodic perturbation nonzero",
                "scaling controls its derivative and preserves strict monotonicity",
                "the primitive vanishes at every registered distance, preserving exact score-derived consumers",
                "a nonzero analytic primitive is nonzero at some unregistered point",
            ],
            "dependency": "FLUX-D1",
            "scope": "one alternative per finite ledger",
        }
    raise ValueError("Unknown FLUX-D3 component")


def _d4(component: str) -> tuple[Any, dict[str, Any]]:
    if component == "flux_scales":
        result = {"drop_scale": "lambda_D=m/h", "response_scale": "lambda_R=m/(h*p)", "identity": "lambda_D=p*lambda_R"}
        return result, {"nonzero_denominators": ["h>0", "p>1"]}
    if component == "contact_coefficients":
        result = ["25/2", "8125*Pi^2/12"]
        return result, {
            "parameters": {"p": 2, "lambda_R": "1/10", "A": 4},
            "contacts": [{"nu": 1, "kappa": 1}, {"nu": 3, "kappa": "200*Pi^2/3"}],
        }
    if component == "lambert_normal_form":
        result = {
            "t": "(epsilon*W(Gamma*C/epsilon)/(Gamma*C))^(1/Gamma)",
            "identity": "C*t^Gamma/(-log(t))=epsilon",
            "log_slope_limit": "1/Gamma",
            "coefficient_limit": "C",
        }
        return result, {
            "defining_rule": "W(z)*exp(W(z))=z",
            "domain": ["epsilon>0", "Gamma>0", "C>0", "Gamma*C/epsilon>1"],
        }
    if component == "support_birth_response":
        result = {
            "Gamma": "nu*min(1,p-1)",
            "leading_balance": "t^Gamma/(-log(t))~epsilon/C",
            "solution": "t~(epsilon*W(Gamma*C/epsilon)/(Gamma*C))^(1/Gamma)",
            "realizable_contact_orders": "every positive odd nu=2*r+1",
        }
        return result, {
            "proof_schema": [
                "rescale the D1 flux from lambda_D to lambda_R=lambda_D/p",
                "the normalized raised-cosine derivative has contact order 2*r+1 and remains an increasing fixed-load gauge",
                "take the normalized little-o remainder as the prospectively registered interface premise",
                "exact limit algebra yields coefficient recovery, logarithmic slope, and the corrected quotient balance",
                "construct the unique positive Lambert witness and invert the quotient balance",
            ],
            "dependencies": ["FLUX-D1"],
            "withdrawal_conditions": ["positive gauge period", "finite odd contact", "positive C", "eventually positive t tending to zero", "normalized remainder tending to zero", "declared signed analytic extension"],
            "withdrawn_nonclaim": "No KKT/contact-germ derivation of the normalized remainder is asserted.",
        }
    raise ValueError("Unknown FLUX-D4 component")


def _d5(component: str) -> tuple[Any, dict[str, Any]]:
    if component == "finite_perturbation":
        result = {"primitive_at_0": 0, "primitive_at_1/2": 0, "marginal_jet_at_1/4": [0, 0, 0], "primitive_at_1/8_nonzero": True}
        return result, {
            "primitive": "sin(2*Pi*z)*(1-cos(2*Pi*z))^3*(1-cos(2*Pi*(z-1/4)))^2",
            "multiplicity_reason": "the last factor has order four at z=1/4, so its derivative has a zero of order three",
        }
    if component == "response_recurrence":
        result = "F(z_i(theta))=mu*(1+epsilon)*sum_(j=i)^N x_j(theta)^epsilon"
        return result, {"readout": "exact constitutive flux value on each admitted powered drop"}
    if component == "finite_vs_accumulating_tomography":
        result = {
            "declared_finite_audit_fibre": "nontrivial continuum",
            "accumulating_interior_exact_response_kernel": "diagonal",
            "accumulation_claim": "sufficient_not_necessary",
        }
        return result, {
            "proof_schema": [
                "each declared finite audit contributes finitely many linear vanishing conditions on a sufficiently rich raised-cosine analytic basis",
                "rank-nullity produces a nonzero perturbation and small scaling preserves admissibility",
                "the response recurrence evaluates F on each observed powered drop",
                "equal responses on an interior accumulation set give equal normalized analytic laws on the connected common domain by the analytic identity theorem",
            ],
            "dependency": "FLUX-D4",
            "scope": "explicit raised-cosine baselines and declared finite audit family",
        }
    raise ValueError("Unknown FLUX-D5 component")


_DISPATCH: dict[str, Callable[[str], tuple[Any, dict[str, Any]]]] = {
    "FLUX-D1": _d1,
    "FLUX-D2": _d2,
    "FLUX-D3": _d3,
    "FLUX-D4": _d4,
    "FLUX-D5": _d5,
}


def ReplayFluxResult(result_id: str, component: str) -> tuple[Any, dict[str, Any]]:
    checker = _DISPATCH.get(result_id)
    if checker is None:
        raise ValueError("Unknown flux result")
    result, detail = checker(component)
    return result, {"result_id": result_id, "component": component, **detail}
