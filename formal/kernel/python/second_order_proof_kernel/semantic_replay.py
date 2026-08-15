from __future__ import annotations

from typing import Any, Mapping

from .canonical import CanonicalHash
from .continuous_hg import ASSUMPTION_MODELS as CHG_ASSUMPTION_MODELS
from .continuous_hg import MUTANT_IDS as CHG_MUTANT_IDS
from .continuous_hg import ReplayContinuousHGResult
from .continuous_hg import ValidateContinuousHGAssumptionModel
from .contextual_model import ReplayContextualResult
from .flux import ReplayFluxResult
from .support_selection import ReplaySupportSelection


PROOF_METHOD = "SemanticDerivationProof"


ASSUMPTION_MODELS: dict[str, dict[str, Any]] = {
    **CHG_ASSUMPTION_MODELS,
    "CTX-C1": {"p": 2, "K": 2, "u": "1/2", "rho": "3/2", "endpoints": [1, 1]},
    "CTX-C2": {"p": 2, "K": 2, "rho": 3, "one_trigger": [1, 0], "opposite_triggers": [1, 1]},
    "FLUX-D1": {"load": 1, "epsilon": "1/2", "flux": "identity_plus_periodic_sine"},
    "FLUX-D2": {"loads": ["1/5", "1/21"], "common_period": "1/105", "continuous": True},
    "FLUX-D3": {"finite_ledger_rows": 2, "basis_dimension": 3, "epsilon": "1/100"},
    "FLUX-D4": {"p": 2, "epsilon": "1/100", "contact_order": 1, "contact_coefficient": 1},
    "FLUX-D5": {"baseline": "raised_cosine", "finite_audit": [0, "1/4", "1/2"], "connected_domain": True},
    "SUP-E1": {"edge": "quadratic", "site": "linear", "edge_weight": 5, "site_weight": 1},
    "SUP-E2": {"edge": "quadratic", "site": "linear", "edge_weight": 5, "site_weight": 1, "horizon": 5},
    "SUP-E3": {"p": 2, "h": 1, "m": 1, "lambda_isolated_by": ["lambda^2-3lambda+1", "0<lambda<1/2"]},
    "SUP-E4": {"p": 2, "h": 5, "m": 1, "lambda": "3/5", "terminal_coefficient": "3/2"},
    "SEL-F1": {"dimension": 3, "sphere_radius": 2, "target_normal": [1, 0, 0]},
    "SEL-F2": {"inputs": 2, "candidates": 4, "disruption_coordinates": 5, "shell_radius_squared": 80},
}


def SemanticMutantIds(result_id: str) -> list[str]:
    identifiers = [
        f"{result_id}.MUTANT.CONCLUSION",
        f"{result_id}.MUTANT.ASSUMPTION",
        f"{result_id}.MUTANT.COMPONENT",
    ]
    if result_id in CHG_MUTANT_IDS:
        identifiers.append(CHG_MUTANT_IDS[result_id])
    return identifiers


def _replay(claim: Mapping[str, Any]) -> tuple[Any, dict[str, Any]]:
    node = claim.get("node")
    if node == "analytic_proof_result" and claim.get("family") == "contextual_interaction":
        return ReplayContextualResult(claim["algorithm"], claim["inputs"])
    if node == "flux_result":
        return ReplayFluxResult(claim["result_id"], claim["component"])
    if node == "support_selection_result":
        return ReplaySupportSelection(claim["result_id"], claim["component"])
    if node == "continuous_hg_result":
        return ReplayContinuousHGResult(claim["result_id"], claim["component"], claim["inputs"])
    raise ValueError("Unknown semantic result claim")


def GenerateSemanticProof(specification: Mapping[str, Any], proof_goal: Mapping[str, Any]) -> dict[str, Any]:
    result_id = specification["result_id"]
    claim = proof_goal["claim"]
    observed, detail = _replay(claim)
    if observed != claim["expected"]:
        raise ValueError("Semantic result catalogue does not replay to its registered conclusion")
    assumptions = specification["assumptions"]
    assumption_model = ASSUMPTION_MODELS[result_id]
    assumption_model_result = ValidateContinuousHGAssumptionModel(result_id, assumption_model) if result_id in CHG_ASSUMPTION_MODELS else True
    if not assumption_model_result:
        raise ValueError("Semantic result assumption witness is unsatisfied")
    anti_vacuity = {
        "conclusion_is_not_assumption": specification["conclusion"]
        not in [{key: value for key, value in row.items() if key != "id"} for row in assumptions],
        "assumption_count": len(assumptions),
    }
    payload = {
        "semantic_kernel_version": "analytic-semantics-1.0.0",
        "claim": claim,
        "observed": observed,
        "derivation": detail,
        "assumption_manifest": {key: value for key, value in assumptions[0].items() if key != "id"},
        "assumption_model": assumption_model,
        "assumption_model_result": assumption_model_result,
        "anti_vacuity": anti_vacuity,
        "mutant_ids": SemanticMutantIds(result_id),
    }
    return {
        "schema_version": "1.1.0",
        "proof_id": f"{proof_goal['proof_goal_id']}.SEMANTIC.PROOF",
        "proof_method": PROOF_METHOD,
        "result_id": result_id,
        "proof_goal_id": proof_goal["proof_goal_id"],
        "formal_statement_sha256": specification["formal_statement_sha256"],
        "claim": claim,
        "claim_sha256": CanonicalHash(claim),
        "assumptions_used": [row["id"] for row in assumptions],
        "foundation_dependencies": specification["foundation_dependencies"],
        "result_dependencies": specification["result_dependencies"],
        "payload": payload,
    }


def CheckSemanticPayload(
    payload: Mapping[str, Any], specification: Mapping[str, Any], root: Any, claim: Any
) -> dict[str, Any]:
    del root
    required = {
        "semantic_kernel_version",
        "claim",
        "observed",
        "derivation",
        "assumption_manifest",
        "assumption_model",
        "assumption_model_result",
        "anti_vacuity",
        "mutant_ids",
    }
    if set(payload) != required or payload["semantic_kernel_version"] != "analytic-semantics-1.0.0":
        raise ValueError("Semantic derivation payload has an unknown grammar or kernel version")
    if payload["claim"] != claim:
        raise ValueError("Semantic derivation payload proves a different claim")
    matches = [row for row in specification["proof_goals"] if row["claim"] == claim]
    if len(matches) != 1 or matches[0]["proof_methods"] != [PROOF_METHOD]:
        raise ValueError("Semantic claim is absent, ambiguous, or assigned to another proof rule")
    assumptions = specification["assumptions"]
    if len(assumptions) != 1:
        raise ValueError("Semantic result must expose one exact assumption manifest")
    manifest = {key: value for key, value in assumptions[0].items() if key != "id"}
    if payload["assumption_manifest"] != manifest:
        raise ValueError("Semantic proof record silently changes the result assumptions")
    result_id = specification["result_id"]
    expected_model_result = ValidateContinuousHGAssumptionModel(result_id, payload["assumption_model"]) if result_id in CHG_ASSUMPTION_MODELS else True
    if payload["assumption_model"] != ASSUMPTION_MODELS.get(result_id) or payload["assumption_model_result"] is not True or not expected_model_result:
        raise ValueError("Semantic result lacks its exact satisfiable-model witness")
    expected_anti_vacuity = {
        "conclusion_is_not_assumption": specification["conclusion"]
        not in [{key: value for key, value in row.items() if key != "id"} for row in assumptions],
        "assumption_count": len(assumptions),
    }
    if payload["anti_vacuity"] != expected_anti_vacuity or not payload["anti_vacuity"]["conclusion_is_not_assumption"]:
        raise ValueError("Semantic result anti-vacuity check failed")
    if payload["mutant_ids"] != SemanticMutantIds(result_id):
        raise ValueError("Semantic result mutant manifest mismatch")
    observed, detail = _replay(claim)
    if observed != claim["expected"] or payload["observed"] != observed or payload["derivation"] != detail:
        raise ValueError("Semantic result derivation or exact result does not replay")
    return {
        "semantic_kernel_version": payload["semantic_kernel_version"],
        "result_sha256": CanonicalHash(observed),
        "derivation_sha256": CanonicalHash(detail),
        "assumption_model_sha256": CanonicalHash(payload["assumption_model"]),
        "mutant_count": len(payload["mutant_ids"]),
    }


__all__ = [
    "ASSUMPTION_MODELS",
    "PROOF_METHOD",
    "CheckSemanticPayload",
    "GenerateSemanticProof",
    "SemanticMutantIds",
]
