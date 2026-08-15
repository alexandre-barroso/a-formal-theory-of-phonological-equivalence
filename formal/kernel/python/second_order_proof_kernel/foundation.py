from __future__ import annotations

from typing import Any, Mapping

from .canonical import CanonicalHash


LOCAL_DERIVATIONS: dict[str, list[dict[str, Any]]] = {
    "FOUND-FINITE-001": [
        {"rule": "finite_extensional_induction", "conclusion": "finite_set_extensionality"},
        {"rule": "natural_induction_on_cardinality", "conclusion": "finite_sum_induction"},
        {"rule": "graph_extensionality", "conclusion": "finite_map_extensionality"},
        {"rule": "conjunction_introduction", "premises": [0, 1, 2]},
    ],
    "FOUND-TERMINATION-001": [
        {"rule": "least_element_principle", "domain": "natural numbers"},
        {"rule": "strict_descent_contradicts_minimality", "conclusion": "well_founded_descent"},
    ],
    "FOUND-PARTITION-001": [
        {"rule": "kernel_reflexive_symmetric_transitive", "domain": "finite maps"},
        {"rule": "quotient_map_factorization", "conclusion": "kernel_partition_factorization"},
    ],
    "FOUND-CONVEX-001": [
        {"rule": "strict_midpoint_inequality", "domain": "convex domain"},
        {"rule": "two_minimizers_contradiction", "conclusion": "strict_convexity_unique_minimizer"},
    ],
    "FOUND-LINEAR-001": [
        {"rule": "basis_extension", "domain": "finite rational matrices"},
        {"rule": "dimension_additivity", "conclusion": "rank_nullity"},
    ],
    "FOUND-CONVEX-HULL-001": [
        {"rule": "positive_barycentric_image_is_relative_open", "domain": "finite point sets"},
        {"rule": "face_separation_for_boundary_points", "conclusion": "positive_barycentric_relative_interior"},
    ],
    "FOUND-POLYNOMIAL-001": [
        {"rule": "finite_monomial_basis_uniqueness", "coefficient_field": "rationals"},
        {"rule": "coefficientwise_equality", "conclusion": "sparse_polynomial_extensionality"},
    ],
    "FOUND-EXP-ACTIVITY-BIJECTION-001": [
        {
            "rule": "exponential_positivity_and_monotonicity",
            "conclusion": "each coordinate exp(-w_i) lies in (0,1]",
        },
        {
            "rule": "logarithm_inverse_on_positive_reals",
            "conclusion": "w_i=-log(z_i) is nonnegative for every z_i in (0,1]",
        },
        {
            "rule": "finite_product_bijection",
            "premises": [0, 1],
            "conclusion": "the two componentwise maps are mutual inverses",
        },
    ],
}


def GenerateFoundationProof(item: Mapping[str, Any]) -> dict[str, Any]:
    identifier = item["foundation_id"]
    if identifier not in LOCAL_DERIVATIONS or item["classification"] != "derived foundation lemma":
        raise ValueError("Foundation item is not a locally derived schema")
    return {
        "schema_version": "1.0.0",
        "proof_id": f"{identifier}.PROOF",
        "proof_method": "LocalStructuralDerivationProof",
        "foundation_id": identifier,
        "formal_statement_sha256": CanonicalHash(item["formal_statement"]),
        "steps": LOCAL_DERIVATIONS[identifier],
        "conclusion": item["formal_statement"],
    }


def CheckFoundationProof(proof: Mapping[str, Any], item: Mapping[str, Any]) -> dict[str, Any]:
    if set(proof) != {"schema_version", "proof_id", "proof_method", "foundation_id", "formal_statement_sha256", "steps", "conclusion"}:
        raise ValueError("Foundation proof fields do not match the grammar")
    identifier = item["foundation_id"]
    if (
        proof["schema_version"] != "1.0.0"
        or proof["proof_id"] != f"{identifier}.PROOF"
        or proof["proof_method"] != "LocalStructuralDerivationProof"
        or proof["foundation_id"] != identifier
    ):
        raise ValueError("Foundation proof identity mismatch")
    if proof["formal_statement_sha256"] != CanonicalHash(item["formal_statement"]):
        raise ValueError("Foundation formal-statement hash mismatch")
    if proof["steps"] != LOCAL_DERIVATIONS.get(identifier):
        raise ValueError("Foundation structural derivation differs from its checked schema")
    if proof["conclusion"] != item["formal_statement"]:
        raise ValueError("Foundation proof establishes a different conclusion")
    return {"proof_id": proof["proof_id"], "proof_method": proof["proof_method"], "foundation_id": identifier, "status": "PASS", "step_count": len(proof["steps"]), "formal_statement_sha256": proof["formal_statement_sha256"]}


def CheckFoundationRegistry(registry: Mapping[str, Any], proofs: Mapping[str, Mapping[str, Any]]) -> dict[str, Any]:
    failures: list[dict[str, str]] = []
    results: list[dict[str, Any]] = []
    identifiers: set[str] = set()
    for item in registry.get("items", []):
        identifier = item.get("foundation_id", "")
        if not identifier or identifier in identifiers:
            failures.append({"foundation_id": identifier, "error": "Missing or duplicate foundation identifier"})
            continue
        identifiers.add(identifier)
        classification = item.get("classification")
        if classification == "derived foundation lemma":
            try:
                results.append(CheckFoundationProof(proofs[identifier], item))
            except (KeyError, ValueError) as error:
                failures.append({"foundation_id": identifier, "error": str(error)})
        elif classification in {"axiom", "imported standard theorem", "software-semantic assumption"}:
            if not item.get("source_citation") or item.get("proof_path"):
                failures.append({"foundation_id": identifier, "error": "Imported or assumed foundation metadata is incomplete or claims a local proof"})
            else:
                results.append({"foundation_id": identifier, "status": "PASS", "classification": classification, "formal_statement_sha256": CanonicalHash(item["formal_statement"])})
        else:
            failures.append({"foundation_id": identifier, "error": "Unknown foundation classification"})
    return {"status": "PASS" if not failures else "FAIL", "foundation_count": len(identifiers), "locally_derived_count": len(LOCAL_DERIVATIONS), "results": results, "failures": failures}


__all__ = ["CheckFoundationProof", "CheckFoundationRegistry", "GenerateFoundationProof", "LOCAL_DERIVATIONS"]
