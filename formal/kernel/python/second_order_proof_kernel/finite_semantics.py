from __future__ import annotations

import json
from fractions import Fraction
from itertools import chain, combinations, product
from typing import Any, Iterable, Mapping, Sequence

from .canonical import CanonicalHash


PROOF_METHOD = "FiniteSemanticProof"
LEAN_PROOF_METHOD = "LeanKernelProof"
FINITE_RESULT_IDS = frozenset({"CALC-F1", *(f"FIN-A{index}" for index in range(1, 8))})
FORMAL_STATEMENT_FIELDS = (
    "schema_version",
    "result_id",
    "kind",
    "group",
    "variables",
    "sorts",
    "domains",
    "definitions",
    "assumptions",
    "conclusion",
    "quantifier_prefix",
    "registered_query_type",
    "scope",
    "nonclaims",
    "foundation_dependencies",
    "result_dependencies",
    "source_transcription_dependencies",
    "expected_proof_methods",
    "withdrawal_condition",
)


def _variable(name: str) -> dict[str, Any]:
    return {"node": "variable", "name": name}


def _predicate(name: str, *arguments: Any) -> dict[str, Any]:
    return {"node": "predicate_application", "name": f"builtin:{name}", "arguments": list(arguments)}


def _function(name: str, *arguments: Any) -> dict[str, Any]:
    return {"node": "function_application", "name": f"builtin:{name}", "arguments": list(arguments)}


def _and(*arguments: Any) -> dict[str, Any]:
    return {"node": "and", "arguments": list(arguments)}


def _implies(antecedent: Any, consequent: Any) -> dict[str, Any]:
    return {"node": "implies", "antecedent": antecedent, "consequent": consequent}


def _equivalent(left: Any, right: Any) -> dict[str, Any]:
    return _and(_implies(left, right), _implies(right, left))


def _equal(left: Any, right: Any) -> dict[str, Any]:
    return {"node": "equal", "left": left, "right": right}


def _kernel(map_name: str, domain_name: str) -> dict[str, Any]:
    return {"node": "kernel", "map": _variable(map_name), "domain": _variable(domain_name)}


def _image(map_name: str, domain_name: str) -> dict[str, Any]:
    return {"node": "image", "map": _variable(map_name), "domain": _variable(domain_name)}


def _finite_domain(identifier: str, variable_name: str, predicate_name: str) -> dict[str, Any]:
    variable = _variable(variable_name)
    return {"id": identifier, "node": "domain", "variable": variable, "predicate": _predicate(predicate_name, variable)}


def _assumption(identifier: str, predicate_name: str, *arguments: Any) -> dict[str, Any]:
    return {"id": identifier, **_predicate(predicate_name, *arguments)}


def _clause(identifier: str, rule: str, formula: dict[str, Any]) -> dict[str, Any]:
    return {"id": identifier, "rule": rule, "formula": formula}


def _profiles() -> dict[str, dict[str, Any]]:
    contract = _variable("contract")
    rows = _variable("rows")
    source_answers = _variable("source_answers")
    target_answers = _variable("target_answers")
    transport = _variable("transport")
    row_order = _variable("row_order")
    subprocedures = _variable("subprocedures")
    calc_assumptions = [
        _assumption("CALC-F1.A1", "well_formed_finite_contract", contract, rows, source_answers, target_answers, transport),
        _assumption("CALC-F1.A2", "complete_matched_rows", contract, rows),
        _assumption("CALC-F1.A3", "exact_terminating_subprocedures", contract, subprocedures),
        _assumption("CALC-F1.A4", "strict_total_order", row_order, rows),
    ]
    mismatch = _function("complete_mismatch_set", rows, source_answers, target_answers, transport)
    admitted = _predicate("contract_admitted", contract)
    calc_clauses = [
        _clause("CALC-F1.C1", "admission_before_comparison", _predicate("admission_precedes_answer_comparison", contract)),
        _clause(
            "CALC-F1.C2",
            "finite_branch_partition",
            _predicate(
                "classifier_has_exactly_three_disjoint_branches",
                contract,
                ["NOT EVALUATED", "Q-CONSERVATIVE", "Q-NONCONSERVATIVE"],
            ),
        ),
        _clause(
            "CALC-F1.C3",
            "mismatch_extensionality",
            _implies(
                admitted,
                _equivalent(
                    _predicate("mismatch_set_empty", mismatch),
                    _predicate("transported_answers_equal_on_all_rows", rows, source_answers, target_answers, transport),
                ),
            ),
        ),
        _clause(
            "CALC-F1.C4",
            "finite_least_witness",
            _implies(
                _and(admitted, _predicate("mismatch_set_nonempty", mismatch)),
                _predicate("returns_complete_set_and_least_mismatch", mismatch, row_order),
            ),
        ),
        _clause(
            "CALC-F1.C5",
            "finite_structural_termination",
            _predicate("terminates_by_finite_structural_measure", contract, rows, subprocedures),
        ),
    ]

    source_orbits = _variable("source_orbits")
    target_orbits = _variable("target_orbits")
    orbit_map = _variable("orbit_map")
    fin_a1_assumptions = [
        _assumption("FIN-A1.A1", "duplicate_free_finite_set", source_orbits),
        _assumption("FIN-A1.A2", "duplicate_free_finite_set", target_orbits),
        _assumption("FIN-A1.A3", "total_induced_orbit_map", orbit_map, source_orbits, target_orbits),
        _assumption("FIN-A1.A4", "equivariance_witnesses_orbit_well_definedness", orbit_map),
    ]
    orbit_collisions = {"node": "collision_pairs", "domain": source_orbits, "map": orbit_map}
    orbit_injective = _predicate("injective_on", orbit_map, source_orbits)
    inverse_exists = _predicate("two_sided_inverse_on_image_exists", orbit_map, source_orbits)
    fin_a1_clauses = [
        _clause("FIN-A1.C1", "equivariance_descent", _predicate("induced_orbit_map_is_well_defined", orbit_map, source_orbits, target_orbits)),
        _clause("FIN-A1.C2", "collision_injectivity", _equivalent(_predicate("finite_relation_empty", orbit_collisions), orbit_injective)),
        _clause("FIN-A1.C3", "inverse_on_image_construction", _equivalent(orbit_injective, inverse_exists)),
        _clause("FIN-A1.C4", "inverse_uniqueness", _implies(inverse_exists, _predicate("inverse_on_image_is_unique", orbit_map, source_orbits))),
        _clause("FIN-A1.C5", "empty_source_vacuity", _implies(_predicate("finite_set_empty", source_orbits), _predicate("recovery_status_is_vacuous", orbit_map))),
    ]

    raw_source = _variable("raw_source")
    raw_target = _variable("raw_target")
    weakening = _variable("weakening")
    source_policy = _variable("source_policy")
    target_policy = _variable("target_policy")
    action_lift = _variable("action_lift")
    fin_a2_assumptions = [
        _assumption("FIN-A2.A1", "duplicate_free_finite_set", raw_source),
        _assumption("FIN-A2.A2", "duplicate_free_finite_set", raw_target),
        _assumption("FIN-A2.A3", "total_map", weakening, raw_source, raw_target),
        _assumption("FIN-A2.A4", "complete_action_policies", source_policy, target_policy, raw_source, raw_target),
    ]
    recovery = _predicate("representative_recovery_exists", weakening, source_policy, target_policy, action_lift)
    recovery_conditions = _and(
        _predicate("injective_on", weakening, raw_source),
        _predicate("image_stable_before_restriction", _image("weakening", "raw_source"), target_policy),
        _predicate("coherent_action_lift", weakening, source_policy, target_policy, action_lift),
    )
    fin_a2_clauses = [
        _clause("FIN-A2.C1", "representative_recovery_necessity", _implies(recovery, recovery_conditions)),
        _clause("FIN-A2.C2", "representative_recovery_construction", _implies(recovery_conditions, recovery)),
        _clause("FIN-A2.C3", "pre_restriction_stability", _predicate("target_stability_checked_on_complete_policy", weakening, target_policy, raw_target)),
        _clause("FIN-A2.C4", "action_lift_functoriality", _predicate("action_lift_preserves_identity_composition_and_square", action_lift, source_policy, target_policy, weakening)),
    ]

    state_graph = _variable("state_graph")
    stop_policy = _variable("stop_policy")
    coefficient_domain = _variable("coefficient_domain")
    readout = _variable("readout")
    cast_registry = _variable("cast_registry")
    fin_a3_assumptions = [
        _assumption("FIN-A3.A1", "finite_state_action_graph", state_graph),
        _assumption("FIN-A3.A2", "exact_stop_policy", stop_policy, state_graph),
        _assumption("FIN-A3.A3", "exact_coefficient_domain", coefficient_domain),
        _assumption("FIN-A3.A4", "exact_readout_and_equality", readout),
        _assumption("FIN-A3.A5", "prospective_cast_registry", cast_registry),
    ]
    serial_tags = ["StoppedSet", "StoppedProbability", "WeightedSeries", "AllPrefixes"]
    fin_a3_clauses = [
        _clause("FIN-A3.C1", "tagged_sum_disjointness", _predicate("answer_tags_pairwise_disjoint", serial_tags)),
        _clause("FIN-A3.C2", "typed_equality_guard", _predicate("cross_tag_comparison_requires_registered_cast", serial_tags, cast_registry)),
        _clause("FIN-A3.C3", "probability_mass_retention", _predicate("stopped_probability_retains_nontermination_mass", state_graph, stop_policy)),
        _clause("FIN-A3.C4", "generic_series_typing", _predicate("weighted_series_has_no_probability_semantics_without_normalization", coefficient_domain)),
        _clause("FIN-A3.C5", "prefix_stopped_separation", _predicate("prefix_and_stopped_answers_require_registered_projection", readout, cast_registry)),
    ]

    reachable = _variable("reachable")
    strong_query = _variable("strong_query")
    weak_query = _variable("weak_query")
    factor = _variable("factor")
    reduction = _variable("reduction")
    consumer_family = _variable("consumer_family")
    added_consumer = _variable("added_consumer")
    fin_a4_assumptions = [
        _assumption("FIN-A4.A1", "duplicate_free_finite_set", reachable),
        _assumption("FIN-A4.A2", "total_maps_on", [strong_query, weak_query, reduction], reachable),
        _assumption("FIN-A4.A3", "weak_query_factors_through_strong", weak_query, factor, strong_query, reachable),
        _assumption("FIN-A4.A4", "prospectively_fixed_consumer_family", consumer_family, added_consumer),
    ]
    strong_kernel = _kernel("strong_query", "reachable")
    weak_kernel = _kernel("weak_query", "reachable")
    reduction_kernel = _kernel("reduction", "reachable")
    fin_a4_clauses = [
        _clause("FIN-A4.C1", "factor_map_kernel_inclusion", _predicate("relation_subset", strong_kernel, weak_kernel)),
        _clause(
            "FIN-A4.C2",
            "kernel_inclusion_transitivity",
            _implies(_predicate("relation_subset", reduction_kernel, strong_kernel), _predicate("relation_subset", reduction_kernel, weak_kernel)),
        ),
        _clause(
            "FIN-A4.C3",
            "tuple_kernel_intersection",
            _equal(
                _function("product_query_kernel", reachable, consumer_family, added_consumer),
                {"node": "intersection", "arguments": [_function("consumer_family_kernel", reachable, consumer_family), _kernel("added_consumer", "reachable")]},
            ),
        ),
        _clause("FIN-A4.C4", "reachable_domain_guard", _predicate("all_kernel_claims_restricted_to", reachable)),
    ]

    carrier = _variable("carrier")
    queries = _variable("queries")
    product_query = _variable("product_query")
    added_query = _variable("added_query")
    chain_maps = _variable("chain_maps")
    deterministic_suffix = _variable("deterministic_suffix")
    markov_suffix = _variable("markov_suffix")
    fin_a5_assumptions = [
        _assumption("FIN-A5.A1", "duplicate_free_finite_set", carrier),
        _assumption("FIN-A5.A2", "finite_total_query_family", queries, carrier),
        _assumption("FIN-A5.A3", "product_query_of_family", product_query, queries, carrier),
        _assumption("FIN-A5.A4", "total_map", reduction, carrier, _image("reduction", "carrier")),
        _assumption("FIN-A5.A5", "total_map", added_query, carrier, _image("added_query", "carrier")),
        _assumption("FIN-A5.A6", "finite_composable_map_chain", chain_maps, carrier),
        _assumption("FIN-A5.A7", "suffixes_see_only_reduced_value", deterministic_suffix, markov_suffix, reduction),
    ]
    product_kernel = _kernel("product_query", "carrier")
    reduction_kernel_a5 = _kernel("reduction", "carrier")
    fin_a5_clauses = [
        _clause("FIN-A5.C1", "finite_product_kernel", _equal(product_kernel, _function("intersection_of_query_kernels", carrier, queries))),
        _clause("FIN-A5.C2", "finite_factorization_equivalence", _equivalent(_predicate("relation_subset", reduction_kernel_a5, product_kernel), _predicate("query_family_factors_through", queries, reduction, carrier))),
        _clause("FIN-A5.C3", "minimum_direct_carrier", _predicate("product_query_is_minimum_exact_direct_carrier", product_query, queries, carrier)),
        _clause("FIN-A5.C4", "blockwise_added_price", _equal(_function("added_consumer_price", carrier, queries, added_query), _function("sum_block_image_cardinality_minus_one", carrier, queries, added_query))),
        _clause("FIN-A5.C5", "zero_price_redundancy", _equivalent(_equal(_function("added_consumer_price", carrier, queries, added_query), {"node": "natural", "value": 0}), _predicate("consumer_constant_on_every_old_block", added_query, carrier, queries))),
        _clause("FIN-A5.C6", "finite_least_loss", _predicate("earliest_kernel_loss_exists_when_any_loss_exists", chain_maps, product_kernel, carrier)),
        _clause("FIN-A5.C7", "postcomposition_nonrecovery", _predicate("collapsed_pair_remains_equal_under_value_only_suffixes", reduction, deterministic_suffix, markov_suffix, carrier)),
        _clause("FIN-A5.C8", "binary_separator", _equivalent(_predicate("injective_on", reduction, carrier), _predicate("all_binary_consumers_factor_through", reduction, carrier))),
        _clause("FIN-A5.C9", "collision_chain_partition", _predicate("chain_collisions_are_disjoint_union_of_first_introductions", chain_maps, carrier)),
    ]

    consumer_universe = _variable("consumer_universe")
    redundancy_closure = _variable("redundancy_closure")
    signature = _variable("signature")
    contextual_relations = _variable("contextual_relations")
    direct_kernel = _variable("direct_kernel")
    fin_a6_assumptions = [
        _assumption("FIN-A6.A1", "finite_consumer_universe_on_carrier", consumer_universe, carrier),
        _assumption("FIN-A6.A2", "kernel_induced_redundancy_closure", redundancy_closure, consumer_universe, carrier),
        _assumption("FIN-A6.A3", "fixed_complete_partial_signature", signature, carrier),
        _assumption("FIN-A6.A4", "nonempty_family_of_strong_congruences", contextual_relations, signature, carrier),
        _assumption("FIN-A6.A5", "direct_consumer_kernel", direct_kernel, consumer_universe, carrier),
    ]
    fin_a6_clauses = [
        _clause("FIN-A6.C1", "closure_operator_laws", _predicate("extensive_monotone_idempotent", redundancy_closure, consumer_universe)),
        _clause("FIN-A6.C2", "closure_fixed_point_lattice", _predicate("closure_fixed_points_form_lattice_with_intersection_and_closed_union", redundancy_closure, consumer_universe)),
        _clause("FIN-A6.C3", "strong_congruence_nonempty_intersection", _predicate("nonempty_intersection_is_strong_congruence", contextual_relations, signature, carrier)),
        _clause("FIN-A6.C4", "greatest_contextual_refinement", _predicate("finite_refinement_yields_greatest_strong_congruence_below", direct_kernel, signature, carrier)),
        _clause("FIN-A6.C5", "partial_definedness_strongness_obstruction", _predicate("nonuniform_partial_definedness_refutes_proposed_relation_strongness", signature, carrier)),
    ]

    external_response = _variable("external_response")
    reachable_codes = _variable("reachable_codes")
    code_map = _variable("code_map")
    interpretation = _variable("interpretation")
    semantic_equality = _variable("semantic_equality")
    reader = _variable("reader")
    descent = _variable("descent")
    source_section = _variable("source_section")
    fin_a7_assumptions = [
        _assumption("FIN-A7.A1", "finite_reachable_code_image", reachable_codes),
        _assumption("FIN-A7.A2", "exact_code_map_and_interpretation", external_response, code_map, interpretation, reachable_codes),
        _assumption("FIN-A7.A3", "exact_semantic_equality", semantic_equality, interpretation),
        _assumption("FIN-A7.A4", "reader_faithful_on_reachable_codes", reader, interpretation, reachable_codes),
        _assumption("FIN-A7.A5", "descended_transformation_on_reachable_codes", descent, reachable_codes),
        _assumption("FIN-A7.A6", "semantic_and_query_squares_commute", code_map, interpretation, reader, descent, external_response),
    ]
    fin_a7_clauses = [
        _clause("FIN-A7.C1", "finite_code_factorization", _predicate("carrier_answers_decidable_from_reachable_codes", reachable_codes, reader, descent, semantic_equality)),
        _clause("FIN-A7.C2", "section_nonoccurrence", _predicate("carrier_verdict_independent_of_source_section", reachable_codes, reader, descent)),
        _clause("FIN-A7.C3", "single_preimage_lift", _implies(_predicate("proved_preimage_for_one_mismatch", source_section, code_map), _predicate("one_source_witness_lifts", source_section, code_map))),
        _clause("FIN-A7.C4", "current_mismatch_section_lift", _implies(_predicate("section_on_current_mismatch_codes", source_section, code_map), _predicate("all_current_mismatch_witnesses_lift", source_section, code_map))),
        _clause("FIN-A7.C5", "global_section_lift", _implies(_predicate("global_section_on_reachable_codes", source_section, code_map), _predicate("all_reachable_code_witnesses_lift", source_section, code_map))),
        _clause("FIN-A7.C6", "injective_section_uniqueness", _implies(_predicate("injective_code_map", code_map), _predicate("unique_set_theoretic_section_on_image", code_map))),
        _clause("FIN-A7.C7", "finite_least_preimage_section", _implies(_predicate("explicit_finite_ordered_source", external_response), _predicate("effective_least_preimage_section_exists", code_map, external_response))),
    ]

    return {
        "CALC-F1": {
            "variables": [("contract", "finite proof code"), ("rows", "finite sequence"), ("source_answers", "finite map"), ("target_answers", "finite map"), ("transport", "finite map"), ("row_order", "relation"), ("subprocedures", "finite sequence")],
            "domains": [_finite_domain("CALC-F1.DOMAIN", "contract", "finite_contract_code")],
            "assumptions": calc_assumptions,
            "clauses": calc_clauses,
            "registered_query_type": "exact finite contract-relative preservation classification",
        },
        "FIN-A1": {
            "variables": [("source_orbits", "finite set"), ("target_orbits", "finite set"), ("orbit_map", "finite map")],
            "domains": [_finite_domain("FIN-A1.DOMAIN", "source_orbits", "finite_orbit_set")],
            "assumptions": fin_a1_assumptions,
            "clauses": fin_a1_clauses,
            "registered_query_type": "semantic orbit recovery on a finite induced map",
        },
        "FIN-A2": {
            "variables": [("raw_source", "finite set"), ("raw_target", "finite set"), ("weakening", "finite map"), ("source_policy", "finite proof code"), ("target_policy", "finite proof code"), ("action_lift", "finite proof code")],
            "domains": [_finite_domain("FIN-A2.DOMAIN", "raw_source", "finite_representative_source")],
            "assumptions": fin_a2_assumptions,
            "clauses": fin_a2_clauses,
            "registered_query_type": "raw representative recovery under a complete action policy",
        },
        "FIN-A3": {
            "variables": [("state_graph", "finite directed graph"), ("stop_policy", "finite proof code"), ("coefficient_domain", "finite proof code"), ("readout", "finite proof code"), ("cast_registry", "finite proof code")],
            "domains": [_finite_domain("FIN-A3.DOMAIN", "state_graph", "finite_serial_graph")],
            "assumptions": fin_a3_assumptions,
            "clauses": fin_a3_clauses,
            "registered_query_type": "syntax-relative equality of disjoint tagged serial-answer sorts",
        },
        "FIN-A4": {
            "variables": [("reachable", "finite set"), ("strong_query", "finite map"), ("weak_query", "finite map"), ("factor", "finite map"), ("reduction", "finite map"), ("consumer_family", "finite sequence"), ("added_consumer", "finite map")],
            "domains": [_finite_domain("FIN-A4.DOMAIN", "reachable", "prospectively_fixed_reachable_set")],
            "assumptions": fin_a4_assumptions,
            "clauses": fin_a4_clauses,
            "registered_query_type": "finite query factorization and direct-consumer refinement",
        },
        "FIN-A5": {
            "variables": [("carrier", "finite set"), ("queries", "finite sequence"), ("product_query", "finite map"), ("reduction", "finite map"), ("added_query", "finite map"), ("chain_maps", "finite sequence"), ("deterministic_suffix", "finite map"), ("markov_suffix", "finite map")],
            "domains": [_finite_domain("FIN-A5.DOMAIN", "carrier", "finite_direct_answer_carrier")],
            "assumptions": fin_a5_assumptions,
            "clauses": fin_a5_clauses,
            "registered_query_type": "finite direct-carrier factorization, price, and irreversible loss",
        },
        "FIN-A6": {
            "variables": [("carrier", "finite set"), ("consumer_universe", "finite sequence"), ("redundancy_closure", "finite map"), ("signature", "finite proof code"), ("contextual_relations", "finite sequence"), ("direct_kernel", "relation")],
            "domains": [_finite_domain("FIN-A6.DOMAIN", "carrier", "finite_information_carrier")],
            "assumptions": fin_a6_assumptions,
            "clauses": fin_a6_clauses,
            "registered_query_type": "direct closure lattice and fixed-signature contextual meet structure",
        },
        "FIN-A7": {
            "variables": [("external_response", "finite proof code"), ("reachable_codes", "finite set"), ("code_map", "finite proof code"), ("interpretation", "finite map"), ("semantic_equality", "finite proof code"), ("reader", "finite map"), ("descent", "finite map"), ("source_section", "partial map")],
            "domains": [_finite_domain("FIN-A7.DOMAIN", "reachable_codes", "finite_reachable_code_image")],
            "assumptions": fin_a7_assumptions,
            "clauses": fin_a7_clauses,
            "registered_query_type": "finite carrier decision with separately typed source-witness lifting",
        },
    }


PROFILES = _profiles()


def _foundation_dependencies(identifier: str) -> list[str]:
    dependencies = ["FOUND-LOGIC-001", "FOUND-FINITE-001", "FOUND-PARTITION-001"]
    if identifier in {"FIN-A3", "FIN-A5"}:
        dependencies.append("FOUND-MARKOV-001")
    if identifier in {"CALC-F1", "FIN-A5", "FIN-A6"}:
        dependencies.append("FOUND-TERMINATION-001")
    return dependencies


def _powerset(values: Sequence[Any]) -> list[tuple[Any, ...]]:
    return [subset for size in range(len(values) + 1) for subset in combinations(values, size)]


def _canonical(value: Any) -> str:
    if isinstance(value, Fraction):
        value = {"fraction": [value.numerator, value.denominator]}
    return json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":"), default=str)


def _unique(values: Iterable[Any]) -> list[Any]:
    result: dict[str, Any] = {}
    for value in values:
        result[_canonical(value)] = value
    return [result[key] for key in sorted(result)]


def _partition(domain: Sequence[Any], maps: Sequence[Mapping[Any, Any]]) -> list[list[Any]]:
    blocks: dict[str, list[Any]] = {}
    for value in domain:
        signature = tuple(mapping.get(value, ("undefined",)) for mapping in maps)
        blocks.setdefault(_canonical(signature), []).append(value)
    return sorted((sorted(block, key=_canonical) for block in blocks.values()), key=_canonical)


def _map_kernel(domain: Sequence[Any], mapping: Mapping[Any, Any]) -> set[tuple[Any, Any]]:
    return {(left, right) for left in domain for right in domain if mapping[left] == mapping[right]}


def _collisions(domain: Sequence[Any], mapping: Mapping[Any, Any]) -> list[list[Any]]:
    return [[left, right] for index, left in enumerate(domain) for right in domain[index + 1 :] if mapping[left] == mapping[right]]


def _factors(domain: Sequence[Any], reduction: Mapping[Any, Any], query: Mapping[Any, Any]) -> bool:
    return all(reduction[left] != reduction[right] or query[left] == query[right] for left in domain for right in domain)


def _compose(first: Mapping[Any, Any], second: Mapping[Any, Any], domain: Sequence[Any]) -> dict[Any, Any]:
    return {value: second[first[value]] for value in domain}


def _strict_total_order(values: Sequence[Any], relation: Sequence[Sequence[Any]]) -> bool:
    pairs = {(row[0], row[1]) for row in relation}
    return all((left, right) in pairs for left in values for right in values if left != right and values.index(left) < values.index(right)) and all((value, value) not in pairs for value in values)


def _finite_classifier(contract: Mapping[str, Any]) -> dict[str, Any]:
    required = {"domain", "source_answers", "target_answers", "matched_rows", "transport", "query_type", "evaluator", "layer", "presentation_action"}
    malformed = not required.issubset(contract)
    rows = contract.get("matched_rows", [])
    domain = contract.get("domain", [])
    source = contract.get("source_answers", {})
    target = contract.get("target_answers", {})
    transport = contract.get("transport", {})
    malformed = malformed or not rows or {row[0] for row in rows} != set(domain)
    malformed = malformed or contract.get("query_type") not in {"Winner"} or contract.get("evaluator") not in {"StrictOT"}
    malformed = malformed or contract.get("layer") not in {"Grammar"} or not contract.get("presentation_action")
    malformed = malformed or any(left not in source or right not in target for left, right in rows)
    malformed = malformed or any(target[right] not in transport for _, right in rows)
    malformed = malformed or any(type(source[left]) is not type(transport[target[right]]) for left, right in rows if target[right] in transport and left in source)
    if malformed:
        return {"class": "NOT EVALUATED", "witness": "MalformedContract", "mismatches": []}
    mismatches = [[left, right] for left, right in rows if source[left] != transport[target[right]]]
    return {"class": "Q-CONSERVATIVE" if not mismatches else "Q-NONCONSERVATIVE", "witness": "", "mismatches": mismatches}


def _base_contract() -> dict[str, Any]:
    return {
        "domain": ["s1", "s2"],
        "source_answers": {"s1": "A", "s2": "B"},
        "target_answers": {"t1": "A", "t2": "B"},
        "matched_rows": [["s1", "t1"], ["s2", "t2"]],
        "transport": {"A": "A", "B": "B"},
        "query_type": "Winner",
        "evaluator": "StrictOT",
        "layer": "Grammar",
        "presentation_action": {"Identity": "Identity"},
    }


def _induced_orbit_map(source_orbits: Sequence[Sequence[Any]], target_orbits: Sequence[Sequence[Any]], mapping: Mapping[Any, Any]) -> dict[tuple[Any, ...], tuple[Any, ...]]:
    target_by_value = {value: tuple(orbit) for orbit in target_orbits for value in orbit}
    result: dict[tuple[Any, ...], tuple[Any, ...]] = {}
    for orbit in source_orbits:
        images = {target_by_value[mapping[value]] for value in orbit}
        if len(images) != 1:
            raise ValueError("Map does not induce a well-defined orbit map")
        result[tuple(orbit)] = next(iter(images))
    return result


def _added_price(domain: Sequence[Any], old_queries: Sequence[Mapping[Any, Any]], added_query: Mapping[Any, Any]) -> int:
    return sum(len({added_query[value] for value in block}) - 1 for block in _partition(domain, old_queries))


def _first_loss(domain: Sequence[Any], chain_maps: Sequence[Mapping[Any, Any]], query: Mapping[Any, Any]) -> int | None:
    current = {value: value for value in domain}
    for index, mapping in enumerate(chain_maps, start=1):
        current = _compose(current, mapping, domain)
        if not _factors(domain, current, query):
            return index
    return None


def _relation(partition: Sequence[Sequence[Any]]) -> set[tuple[Any, Any]]:
    return set(chain.from_iterable(product(block, repeat=2) for block in partition))


def _strong_congruence(domain: Sequence[Any], table: Mapping[tuple[Any, ...], Any], partition: Sequence[Sequence[Any]]) -> bool:
    relation = _relation(partition)
    arity = len(next(iter(table), ()))
    tuples = list(product(domain, repeat=arity))
    for left in tuples:
        for right in tuples:
            related = all((a, b) in relation for a, b in zip(left, right, strict=True))
            left_defined = left in table
            right_defined = right in table
            if related and (left_defined != right_defined or left_defined and (table[left], table[right]) not in relation):
                return False
    return True


def _closure(domain: Sequence[Any], universe: Sequence[Mapping[Any, Any]], subset: Sequence[int]) -> list[int]:
    selected = [universe[index - 1] for index in subset]
    relation = _relation(_partition(domain, selected))
    return [index for index, query in enumerate(universe, start=1) if all((query[left] == query[right]) for left, right in relation)]


def _parse_expected(value: str) -> Any:
    try:
        return json.loads(value)
    except json.JSONDecodeError:
        return value


def _regression_result(identifier: str) -> Any:
    if identifier.startswith("CALC-F1."):
        base = _base_contract()
        if identifier == "CALC-F1.ADMISSION.01":
            return _finite_classifier(base)["class"] == "Q-CONSERVATIVE"
        if identifier == "CALC-F1.PROGRESS.02":
            changed = {**base, "target_answers": {"t1": "A", "t2": "C"}, "transport": {"A": "A", "B": "B", "C": "C"}}
            refused = {**base, "matched_rows": []}
            return [_finite_classifier(value)["class"] for value in [base, changed, refused]]
        if identifier == "CALC-F1.WITNESS.03":
            changed = {**base, "target_answers": {"t1": "A", "t2": "C"}, "transport": {"A": "A", "B": "B", "C": "C"}}
            result = _finite_classifier(changed)
            row = result["mismatches"][0]
            return [result["class"], row, base["source_answers"][row[0]] == changed["transport"][changed["target_answers"][row[1]]]]
        if identifier == "CALC-F1.TERMINATION.04":
            return {"DomainSize": len(base["domain"]), "MatchedRowCount": len(base["matched_rows"]), "SourceTableSize": len(base["source_answers"]), "TargetTableSize": len(base["target_answers"])}
        if identifier == "CALC-F1.REFUSALS.05":
            malformed = []
            for field, value in [("source_answers", {}), ("transport", {}), ("query_type", "UnregisteredNonsense"), ("presentation_action", {}), ("layer", "UnregisteredLayer"), ("matched_rows", [["s1", "t1"]]), ("transport", {"A": 1, "B": 2})]:
                malformed.append({**base, field: value})
            results = [_finite_classifier(value) for value in malformed]
            return [[value["class"] for value in results], [value["witness"] for value in results]]
    if identifier == "FIN-A1.INVERSE.01":
        source = [("a",), ("b", "c")]
        target = [(1,), (2,), (3,)]
        induced = _induced_orbit_map(source, target, {"a": 1, "b": 2, "c": 2})
        inverse = {value: key for key, value in induced.items()}
        return [len(set(induced.values())) == len(source), _collisions(source, induced) == [], all(inverse[induced[value]] == value for value in source), len(set(induced.values())) == len(source)]
    if identifier == "FIN-A1.EMPTY.02":
        return "EMPTY LICENSED SOURCE IMAGE: SEMANTIC INVERSE VACUOUS"
    if identifier == "FIN-A1.EQUIVARIANCE.03":
        domain = ["a", "b", "c"]
        target = [1, 2, 3]
        mapping = {"a": 1, "b": 2, "c": 2}
        source_action = {"a": "a", "b": "c", "c": "b"}
        target_action = {1: 1, 2: 2, 3: 3}
        induced = _induced_orbit_map([("a",), ("b", "c")], [(1,), (2,), (3,)], mapping)
        return [set(source_action) == set(domain) and set(source_action.values()) <= set(domain), set(target_action) == set(target) and set(target_action.values()) <= set(target), all(mapping[source_action[value]] == target_action[mapping[value]] for value in domain), all(value is not None for value in induced.values())]
    if identifier == "FIN-A1.NEGATIVE.04":
        source = [("a",), ("b", "c")]
        induced = _induced_orbit_map(source, [(1,), (2,)], {"a": 1, "b": 1, "c": 1})
        collisions = _collisions(source, induced)
        return [len(set(induced.values())) == len(source), [[list(value) for value in row] for row in collisions], bool(collisions)]
    if identifier == "FIN-A2.PROOF.01":
        source = ["a", "b"]
        mapping = {"a": "c", "b": "d"}
        inverse = {value: key for key, value in mapping.items()}
        arrows = [["idc", "c", "c"], ["idd", "d", "d"]]
        outbound = [row for row in arrows if row[1] in mapping.values() and row[2] not in mapping.values()]
        return [len(set(mapping.values())) == len(source), outbound, {value: inverse[mapping[value]] for value in source}]
    if identifier == "FIN-A2.OUTBOUND.02":
        return [row for row in [["swap", "c", "d"], ["swapInverse", "d", "c"]] if row[1] in {"c"} and row[2] not in {"c"}]
    if identifier == "FIN-A2.COHERENCE.03":
        source = ["a", "b"]
        target = ["c", "d"]
        mapping = {"a": "c", "b": "d"}
        source_identity = {value: value for value in source}
        source_swap = {"a": "b", "b": "a"}
        target_identity = {value: value for value in target}
        target_swap = {"c": "d", "d": "c"}
        return [all(mapping[source_identity[value]] == target_identity[mapping[value]] for value in source), all(mapping[source_swap[value]] == target_swap[mapping[value]] for value in source), _compose(source_swap, source_swap, source) == source_identity, _compose(target_swap, target_swap, target) == target_identity, sorted(mapping.values()) == sorted(target)]
    if identifier == "FIN-A3.MARGINALS.01":
        first = {(0, 0): Fraction(1, 2), (1, 1): Fraction(1, 2)}
        second = {(0, 1): Fraction(1, 2), (1, 0): Fraction(1, 2)}
        def marginal(law: Mapping[tuple[int, int], Fraction], coordinate: int) -> dict[int, Fraction]:
            result: dict[int, Fraction] = {}
            for outcome, mass in law.items():
                result[outcome[coordinate]] = result.get(outcome[coordinate], Fraction()) + mass
            return result
        return [marginal(first, 0) == marginal(second, 0), marginal(first, 1) == marginal(second, 1), first == second]
    if identifier == "FIN-A3.NONTERMINATION.02":
        first = [Fraction(1)]
        second = [Fraction(1, 2)]
        normalize = lambda values: [value / sum(values) for value in values]
        return [[int(value) for value in normalize(first)], [int(value) for value in normalize(second)], {"Stopped": {"w": Fraction(1)}, "Infinity": Fraction(0)} == {"Stopped": {"w": Fraction(1, 2)}, "Infinity": Fraction(1, 2)}]
    if identifier == "FIN-A3.EDGECASES.03":
        return {"DeadlockState": "dead", "EmptyWordMass": "1/4", "ProbabilityInfinityMass": 0, "StructuralCycle": True, "SummedWordMass": 1}
    if identifier == "FIN-A3.TYPES.04":
        tags = ["StoppedSet", "StoppedProbability", "WeightedSeries", "AllPrefixes"]
        return [tags, len(set(tags)) == len(tags), Fraction(3, 4) + Fraction(1, 4), 5]
    if identifier == "FIN-A4.KERNEL.01":
        domain = ["a", "b", "c"]
        strong = {"a": 1, "b": 2, "c": 3}
        weak = {"a": 0, "b": 0, "c": 1}
        reduction = {value: value for value in domain}
        return [_factors(domain, reduction, strong), _factors(domain, reduction, weak), _map_kernel(domain, strong) <= _map_kernel(domain, weak)]
    if identifier == "FIN-A4.CONVERSES.02":
        domain = ["a", "b"]
        reduction = {"a": 0, "b": 0}
        strong = {"a": 0, "b": 1}
        weak = {"a": 0, "b": 0}
        return [_factors(domain, reduction, weak), _factors(domain, reduction, strong), len(_partition(domain, [weak, strong])) > len(_partition(domain, [weak]))]
    if identifier == "FIN-A4.REACHABLE.03":
        domain = ["a", "b", "c"]
        reachable = ["a", "b"]
        reduction = {"a": "x", "b": "y", "c": "x"}
        query = {"a": "A", "b": "B", "c": "C"}
        return [_factors(domain, reduction, query), _factors(reachable, reduction, query), [value for value in domain if value not in reachable]]
    if identifier == "FIN-A5.CARRIER.01":
        domain = [1, 2, 3, 4]
        first = {1: 0, 2: 0, 3: 1, 4: 1}
        second = {1: 0, 2: 1, 3: 0, 4: 1}
        tuples = {(first[value], second[value]) for value in domain}
        return [len(_partition(domain, [first, second])), len(tuples), max(len(set(first.values())), len(set(second.values()))), len(set(first.values())) * len(set(second.values()))]
    if identifier == "FIN-A5.PRICE.02":
        domain = [1, 2, 3, 4]
        return _added_price(domain, [{1: 0, 2: 0, 3: 1, 4: 1}], {1: 0, 2: 1, 3: 0, 4: 1})
    if identifier == "FIN-A5.LOSS.03":
        domain = [1, 2, 3]
        query = {1: "A", 2: "B", 3: "C"}
        first = {1: "x", 2: "y", 3: "z"}
        second = {"x": "u", "y": "u", "z": "v"}
        return [_first_loss(domain, [first, second], query), first[1] != first[2], second[first[1]] == second[first[2]], query[1] != query[2]]
    if identifier == "FIN-A5.FACTORIZATION.04":
        domain = [1, 2, 3, 4]
        reduction = {1: "x", 2: "x", 3: "y", 4: "y"}
        query = {1: "A", 2: "A", 3: "B", 4: "B"}
        reader = {"x": "A", "y": "B"}
        return [_factors(domain, reduction, query), _map_kernel(domain, reduction) <= _map_kernel(domain, query), all(reader[reduction[value]] == query[value] for value in domain), len(set(reduction.values())) == len(set(query.values()))]
    if identifier == "FIN-A5.REDUNDANCY.05":
        domain = [1, 2, 3, 4]
        old = {1: 0, 2: 0, 3: 1, 4: 1}
        redundant = {1: "a", 2: "a", 3: "b", 4: "b"}
        splitting = {1: "a", 2: "b", 3: "a", 4: "b"}
        return [_added_price(domain, [old], redundant), sum(len({redundant[value] for value in block}) - 1 for block in _partition(domain, [old])), _added_price(domain, [old], splitting), sum(len({splitting[value] for value in block}) - 1 for block in _partition(domain, [old]))]
    if identifier == "FIN-A5.POSTPROCESS.06":
        reduction = {"a": "x", "b": "x", "c": "y"}
        deterministic = {"x": "u", "y": "v"}
        markov = {"x": {"u": Fraction(1, 3), "v": Fraction(2, 3)}, "y": {"u": Fraction(3, 4), "v": Fraction(1, 4)}}
        return [deterministic[reduction["a"]] == deterministic[reduction["b"]], markov[reduction["a"]] == markov[reduction["b"]], markov[reduction["a"]] != markov[reduction["c"]]]
    if identifier == "FIN-A5.UNIVERSAL.07":
        domain = [1, 2, 3]
        injective = {1: "a", 2: "b", 3: "c"}
        collapsed = {1: "a", 2: "a", 3: "c"}
        queries = [{value: bit for value, bit in zip(domain, bits, strict=True)} for bits in product([0, 1], repeat=3)]
        separator = next(query for query in queries if not _factors(domain, collapsed, query))
        encoded = {"WolframAssociationEntries": [{"KeyInputForm": f"HoldComplete[{key}]", "Value": value} for key, value in separator.items()]}
        return [all(_factors(domain, injective, query) for query in queries), all(_factors(domain, collapsed, query) for query in queries), encoded]
    if identifier == "FIN-A5.COLLISIONS.08":
        domain = [1, 2, 3, 4]
        first = {1: "a", 2: "a", 3: "b", 4: "c"}
        second = {"a": "x", "b": "x", "c": "y"}
        composite = _compose(first, second, domain)
        old = _collisions(domain, first)
        total = _collisions(domain, composite)
        new = [row for row in total if row not in old]
        return [old, new, sorted(old + new) == total]
    if identifier == "FIN-A6.LATTICE.01":
        domain = list(product([0, 1], repeat=2))
        first = {value: value[0] for value in domain}
        second = {value: value[1] for value in domain}
        left = _partition(domain, [first])
        right = _partition(domain, [second])
        joint = _partition(domain, [first, second])
        return [len(left), len(right), len(joint), left != right]
    if identifier in {"FIN-A6.CLOSURE.02", "FIN-A6.LATTICEOPS.04"}:
        domain = list(product([0, 1], repeat=2))
        universe = [{value: value[0] for value in domain}, {value: value[1] for value in domain}, {value: 1 - value[0] for value in domain}, {value: sum(value) % 2 for value in domain}]
        subsets = [list(value) for value in _powerset([1, 2, 3, 4])]
        closed = [subset for subset in subsets if _closure(domain, universe, subset) == subset]
        if identifier == "FIN-A6.CLOSURE.02":
            extensive = all(set(subset) <= set(_closure(domain, universe, subset)) for subset in subsets)
            monotone = all(not set(left) <= set(right) or set(_closure(domain, universe, left)) <= set(_closure(domain, universe, right)) for left in subsets for right in subsets)
            idempotent = all(_closure(domain, universe, _closure(domain, universe, subset)) == _closure(domain, universe, subset) for subset in subsets)
            return [extensive, monotone, idempotent, _closure(domain, universe, [1]), _closure(domain, universe, [1, 2])]
        return [len(closed), all(sorted(set(left) & set(right)) in closed for left in closed for right in closed), all(_closure(domain, universe, sorted(set(left) | set(right))) in closed for left in closed for right in closed)]
    if identifier == "FIN-A6.DEFINEDNESS.03":
        domain = ["a", "b"]
        table = {("a",): "a"}
        return [_strong_congruence(domain, table, [domain]), 0 < len(table) < len(domain)]
    if identifier == "FIN-A6.CONTEXT.05":
        domain = ["a", "b", "c", "d"]
        table = {(value,): value for value in domain}
        first = {"a": 0, "b": 0, "c": 1, "d": 1}
        second = {"a": 0, "b": 1, "c": 0, "d": 1}
        p1 = _partition(domain, [first])
        p2 = _partition(domain, [second])
        joint = _partition(domain, [first, second])
        return [_strong_congruence(domain, table, p1), _strong_congruence(domain, table, p2), _strong_congruence(domain, table, joint), _relation(p1) & _relation(p2) == _relation(joint)]
    if identifier == "FIN-A7.DIAGRAM.01":
        domain = [1, 2, 3]
        code = {1: "odd", 2: "even", 3: "odd"}
        transform = {1: 3, 2: 2, 3: 1}
        descended = {"odd": "odd", "even": "even"}
        response = {1: 1, 2: 0, 3: 1}
        interpretation = {"odd": 1, "even": 0}
        return all(descended[code[value]] == code[transform[value]] and interpretation[code[value]] == response[value] for value in domain)
    if identifier == "FIN-A7.SECTION.02":
        codes = ["odd", "even"]
        descent = {"odd": "merged", "even": "merged"}
        source = {"odd": 1, "even": 0}
        target = {"merged": 0}
        mismatches = [code for code in codes if source[code] != target[descent[code]]]
        unique = len([code for code in codes if descent[code] == "merged"]) == 1
        return {"CarrierClass": "Q-CONSERVATIVE" if not mismatches else "Q-NONCONSERVATIVE", "CarrierMismatchCodes": mismatches, "SourceWitnessStatus": "AVAILABLE" if unique else "NOT EVALUATED", "UniqueSourceSectionAvailable": unique}
    if identifier == "FIN-A7.CODE.03":
        required = {"Sort", "Parameters", "CodeCarrier", "Interpretation", "SemanticEquality", "ReachableImage", "Reader", "Descent"}
        response = {"Sort": "DirectionalHGResponse", "Parameters": {"h": 5, "m": 1, "p": 2}, "CodeCarrier": ["K4", "K5"], "Interpretation": {"K4": [1, Fraction(3, 5), Fraction(3, 10), Fraction(1, 10), 0], "K5": [1, Fraction(13, 20), Fraction(3, 8), Fraction(7, 40), Fraction(1, 20), 0]}, "SemanticEquality": "ExactEquality", "ReachableImage": ["K4", "K5"], "Reader": {"K4": 3, "K5": 4}, "Descent": {"K4": "K4", "K5": "K5"}}
        return [required <= set(response), len(set(response["CodeCarrier"])) == len(response["CodeCarrier"]), sorted(response["ReachableImage"]) == sorted(response["CodeCarrier"]), response["Interpretation"]["K4"] == [1, Fraction(3, 5), Fraction(3, 10), Fraction(1, 10), 0], response["Interpretation"]["K4"] != response["Interpretation"]["K5"]]
    if identifier == "FIN-A7.POSITIVESECTION.04":
        source = [1, 2, 3]
        code = {1: "odd", 2: "even", 3: "primeOdd"}
        section = {value: key for key, value in code.items()}
        carrier_values = list(code.values())
        return [len(set(carrier_values)) == len(source), sorted(section) == sorted(carrier_values), all(section[code[value]] == value for value in source)]
    if identifier == "FIN-A7.REFUSALS.05":
        dependencies = ["CodeCarrier", "Interpretation", "SemanticEquality", "ReachableImage", "Reader", "Descent", "SourceSection"]
        return [{"CarrierDecision": "AVAILABLE" if dependency == "SourceSection" else "NOT EVALUATED", "Missing": dependency, "SourceWitness": "NOT EVALUATED"} for dependency in dependencies]
    raise ValueError(f"No exact finite replay algorithm is registered for {identifier}")


def _json_value(value: Any) -> Any:
    if isinstance(value, Fraction):
        return value.numerator if value.denominator == 1 else f"{value.numerator}/{value.denominator}"
    if isinstance(value, tuple):
        return [_json_value(child) for child in value]
    if isinstance(value, list):
        return [_json_value(child) for child in value]
    if isinstance(value, dict):
        return {str(key): _json_value(child) for key, child in value.items()}
    return value


def _satisfiability_model(identifier: str) -> dict[str, Any]:
    models = {
        "CALC-F1": {"contract": _base_contract(), "rows": [["s1", "t1"], ["s2", "t2"]], "source_answers": {"s1": "A", "s2": "B"}, "target_answers": {"t1": "A", "t2": "B"}, "transport": {"A": "A", "B": "B"}, "row_order": [["s1/t1", "s2/t2"]], "subprocedures": ["source", "target", "transport"]},
        "FIN-A1": {"source_orbits": [["a"]], "target_orbits": [[1]], "orbit_map": [{"key": ["a"], "value": [1]}]},
        "FIN-A2": {"raw_source": ["a"], "raw_target": ["c"], "weakening": {"a": "c"}, "source_policy": {"id": {"a": "a"}}, "target_policy": {"id": {"c": "c"}}, "action_lift": {"id": "id"}},
        "FIN-A3": {"state_graph": {"states": ["s", "z"], "edges": [["s", "a", "z"]]}, "stop_policy": {"stops": ["z"]}, "coefficient_domain": "rational", "readout": "exact", "cast_registry": []},
        "FIN-A4": {"reachable": ["a"], "strong_query": {"a": 1}, "weak_query": {"a": 0}, "factor": {"1": 0}, "reduction": {"a": "x"}, "consumer_family": [{"a": 1}], "added_consumer": {"a": 0}},
        "FIN-A5": {"carrier": ["a"], "queries": [{"a": 0}], "product_query": {"a": [0]}, "reduction": {"a": "x"}, "added_query": {"a": 0}, "chain_maps": [{"a": "x"}], "deterministic_suffix": {"x": "y"}, "markov_suffix": {"x": {"y": "1"}}},
        "FIN-A6": {"carrier": ["a"], "consumer_universe": [{"a": 0}], "redundancy_closure": {"empty": [1], "one": [1]}, "signature": {"identity": {"a": "a"}}, "contextual_relations": [[["a", "a"]]], "direct_kernel": [["a", "a"]]},
        "FIN-A7": {"external_response": {"ordered_source": ["s"]}, "reachable_codes": ["c"], "code_map": {"s": "c"}, "interpretation": {"c": "answer"}, "semantic_equality": "exact", "reader": {"c": "answer"}, "descent": {"c": "c"}, "source_section": {"c": "s"}},
    }
    return models[identifier]


def _model_is_satisfiable(identifier: str, model: Mapping[str, Any]) -> bool:
    if model != _satisfiability_model(identifier):
        return False
    if identifier == "CALC-F1":
        return _finite_classifier(model["contract"])["class"] == "Q-CONSERVATIVE" and _strict_total_order(["s1/t1", "s2/t2"], model["row_order"])
    if identifier == "FIN-A1":
        return len(model["source_orbits"]) == len(model["orbit_map"])
    if identifier == "FIN-A2":
        return len(set(model["weakening"].values())) == len(model["raw_source"])
    if identifier == "FIN-A3":
        return model["stop_policy"]["stops"] == ["z"] and not model["cast_registry"]
    if identifier == "FIN-A4":
        return _factors(model["reachable"], model["strong_query"], model["weak_query"])
    if identifier == "FIN-A5":
        return _factors(model["carrier"], model["reduction"], model["queries"][0])
    if identifier == "FIN-A6":
        return _strong_congruence(model["carrier"], {("a",): "a"}, [["a"]])
    if identifier == "FIN-A7":
        return model["reader"]["c"] == model["interpretation"]["c"] and model["source_section"][model["code_map"]["s"]] == "s"
    return False


def _proof_steps(identifier: str, specification: Mapping[str, Any]) -> list[dict[str, Any]]:
    profile = PROFILES[identifier]
    assumptions = [value["id"] for value in profile["assumptions"]]
    steps = []
    for clause in profile["clauses"]:
        steps.append({"step_id": clause["id"], "rule": clause["rule"], "premises": assumptions, "claim": clause["formula"], "claim_sha256": CanonicalHash(clause["formula"])})
    conclusion = {"node": "and", "arguments": [clause["formula"] for clause in profile["clauses"]]}
    steps.append({"step_id": f"{identifier}.CONCLUDE", "rule": "conjunction_introduction", "premises": [clause["id"] for clause in profile["clauses"]], "claim": conclusion, "claim_sha256": CanonicalHash(conclusion)})
    if conclusion != specification["conclusion"]:
        raise ValueError("Finite semantic specification conclusion does not match its proof schema")
    return steps


def _mutant_ids(identifier: str) -> list[str]:
    return {
        "CALC-F1": ["answer_comparison_before_admission", "omit_complete_mismatch_set", "remove_termination_premise"],
        "FIN-A1": ["replace_injectivity_by_surjectivity", "allow_orbit_collision_with_inverse"],
        "FIN-A2": ["omit_pre_restriction_stability", "omit_coherent_lift"],
        "FIN-A3": ["erase_answer_tags", "allow_unregistered_cross_tag_cast"],
        "FIN-A4": ["reverse_kernel_inclusion", "replace_kernel_intersection_by_union"],
        "FIN-A5": ["reverse_factorization_kernel_inclusion", "allow_suffix_side_channel", "replace_price_image_count_by_block_size"],
        "FIN-A6": ["assert_contextual_join_lattice", "allow_empty_strong_congruence_intersection", "change_partial_signature"],
        "FIN-A7": ["require_section_for_carrier_verdict", "omit_reader_faithfulness", "infer_effective_inverse_from_injectivity_alone"],
    }[identifier]


def BuildFiniteSemanticSpecification(result: Mapping[str, str], registered_proof_goals: Sequence[Mapping[str, str]], dependencies: Sequence[str]) -> dict[str, Any]:
    identifier = result["result_id"]
    if identifier not in FINITE_RESULT_IDS:
        raise ValueError(f"{identifier} is not one of the bounded finite semantic results")
    profile = PROFILES[identifier]
    proof_goal_ids = [row["proof_goal_id"] for row in registered_proof_goals]
    metaproof_id = f"{identifier}.METAPROOF"
    if proof_goal_ids.count(metaproof_id) != 1:
        raise ValueError(f"{identifier} must have exactly one universal METAPROOF proof goal")
    clauses = [value["formula"] for value in profile["clauses"]]
    conclusion = {"node": "and", "arguments": clauses}
    constructed_proof_goals = []
    for row in registered_proof_goals:
        proof_goal_id = row["proof_goal_id"]
        if proof_goal_id == metaproof_id:
            claim = conclusion
        else:
            expected = _parse_expected(row["expected_exact_result"])
            claim = _equal(_function("finite_regression_observed", proof_goal_id), {"node": "typed_answer", "answer_type": "registered_exact_result", "value": expected})
        method = LEAN_PROOF_METHOD if row["machine_status"] == "LeanKernelProofPass" else PROOF_METHOD
        constructed_proof_goals.append({"proof_goal_id": proof_goal_id, "mandatory": True, "claim": claim, "proof_methods": [method]})
    variables = [{"name": name, "sort": sort} for name, sort in profile["variables"]]
    statement_link = {
        "id": f"{identifier}.STATEMENT",
        "node": "statement_correspondence",
        "english_statement_sha256": CanonicalHash({"locale": "en", "statement": result["statement_en"]}),
        "portuguese_statement_sha256": CanonicalHash({"locale": "pt_BR", "statement": result["statement_pt_BR"]}),
    }
    specification = {
        "schema_version": "1.0.0",
        "result_id": identifier,
        "title_en": result["title_en"],
        "title_pt_BR": result["title_pt_BR"],
        "kind": result["kind"],
        "group": result["group"],
        "variables": variables,
        "sorts": sorted({"Boolean", *(value["sort"] for value in variables)}),
        "domains": profile["domains"],
        "definitions": [statement_link, *[{"id": clause["id"], **clause["formula"]} for clause in profile["clauses"]]],
        "assumptions": profile["assumptions"],
        "conclusion": conclusion,
        "proof_goals": constructed_proof_goals,
        "quantifier_prefix": [{"quantifier": "forall", "variables": [value["name"] for value in variables]}],
        "registered_query_type": profile["registered_query_type"],
        "scope": result["scope"],
        "nonclaims": result["nonclaims"],
        "foundation_dependencies": _foundation_dependencies(identifier),
        "result_dependencies": list(dependencies),
        "source_transcription_dependencies": [],
        "expected_proof_methods": sorted({value["proof_methods"][0] for value in constructed_proof_goals}),
        "english_statement_sha256": CanonicalHash({"locale": "en", "statement": result["statement_en"]}),
        "portuguese_statement_sha256": CanonicalHash({"locale": "pt_BR", "statement": result["statement_pt_BR"]}),
        "withdrawal_condition": result["withdrawal_condition"],
    }
    specification["formal_statement_sha256"] = FiniteFormalStatementHash(specification)
    return specification


def FiniteFormalStatementHash(specification: Mapping[str, Any]) -> str:
    return CanonicalHash({field: specification[field] for field in FORMAL_STATEMENT_FIELDS})


def GenerateFiniteSemanticProofs(specification: Mapping[str, Any]) -> list[dict[str, Any]]:
    identifier = specification["result_id"]
    ValidateFiniteSemanticSpecification(specification)
    proofs = []
    for proof_goal in specification["proof_goals"]:
        if proof_goal["proof_methods"] == [LEAN_PROOF_METHOD]:
            continue
        proof_goal_id = proof_goal["proof_goal_id"]
        structural = proof_goal_id == f"{identifier}.METAPROOF"
        payload = {
            "semantic_kernel_version": "finite-semantics-1.0.0",
            "result_schema_id": f"{identifier}.FINITE-SCHEMA.1",
            "derivation_method": "universal_structural_derivation" if structural else "exact_finite_replay",
            "derivation": _proof_steps(identifier, specification) if structural else [],
            "regression_algorithm": None if structural else proof_goal_id,
            "regression_expected": None if structural else proof_goal["claim"]["right"]["value"],
            "assumption_model": _satisfiability_model(identifier),
            "assumption_model_result": True,
            "anti_vacuity": {"conclusion_is_not_assumption": specification["conclusion"] not in [{key: value for key, value in assumption.items() if key != "id"} for assumption in specification["assumptions"]], "assumption_count": len(specification["assumptions"])},
            "mutant_ids": _mutant_ids(identifier),
        }
        proof = {
            "schema_version": "1.1.0",
            "proof_id": f"{proof_goal_id}.FINITE-SEMANTIC.PROOF",
            "proof_method": PROOF_METHOD,
            "result_id": identifier,
            "proof_goal_id": proof_goal_id,
            "formal_statement_sha256": specification["formal_statement_sha256"],
            "claim": proof_goal["claim"],
            "claim_sha256": CanonicalHash(proof_goal["claim"]),
            "assumptions_used": [value["id"] for value in specification["assumptions"]],
            "foundation_dependencies": specification["foundation_dependencies"],
            "result_dependencies": specification["result_dependencies"],
            "payload": payload,
        }
        CheckFiniteSemanticProof(proof, specification)
        proofs.append(proof)
    return proofs


def ValidateFiniteSemanticSpecification(specification: Mapping[str, Any]) -> None:
    identifier = specification.get("result_id")
    if identifier not in FINITE_RESULT_IDS:
        raise ValueError("Unknown finite semantic result")
    profile = PROFILES[identifier]
    expected_variables = [{"name": name, "sort": sort} for name, sort in profile["variables"]]
    expected_sorts = sorted({"Boolean", *(value["sort"] for value in expected_variables)})
    expected_conclusion = {"node": "and", "arguments": [value["formula"] for value in profile["clauses"]]}
    statement_link = {
        "id": f"{identifier}.STATEMENT",
        "node": "statement_correspondence",
        "english_statement_sha256": specification.get("english_statement_sha256"),
        "portuguese_statement_sha256": specification.get("portuguese_statement_sha256"),
    }
    expected_definitions = [statement_link, *[{"id": clause["id"], **clause["formula"]} for clause in profile["clauses"]]]
    if (
        specification.get("variables") != expected_variables
        or specification.get("sorts") != expected_sorts
        or specification.get("domains") != profile["domains"]
        or specification.get("definitions") != expected_definitions
        or specification.get("assumptions") != profile["assumptions"]
        or specification.get("conclusion") != expected_conclusion
        or specification.get("registered_query_type") != profile["registered_query_type"]
        or specification.get("foundation_dependencies") != _foundation_dependencies(identifier)
        or specification.get("source_transcription_dependencies") != []
        or specification.get("expected_proof_methods") != sorted({PROOF_METHOD, LEAN_PROOF_METHOD})
    ):
        raise ValueError("Finite semantic result differs from its exact typed schema")
    if specification.get("quantifier_prefix") != [{"quantifier": "forall", "variables": [value["name"] for value in expected_variables]}]:
        raise ValueError("Finite semantic result has a weakened or malformed quantifier prefix")
    if "proof_goals" not in specification:
        raise ValueError("Finite semantic result lacks registered proof goals")
    proof_goals = specification["proof_goals"]
    proof_goal_fields = {"proof_goal_id", "mandatory", "claim", "proof_methods"}
    if not isinstance(proof_goals, list) or any(
        not isinstance(value, Mapping) or set(value) != proof_goal_fields
        for value in proof_goals
    ):
        raise ValueError("Finite semantic proof-goal records have an unknown grammar")
    metaproofs = [value for value in proof_goals if value["proof_goal_id"] == f"{identifier}.METAPROOF"]
    if len(metaproofs) != 1 or metaproofs[0]["claim"] != expected_conclusion or metaproofs[0]["proof_methods"] != [LEAN_PROOF_METHOD]:
        raise ValueError("Finite semantic universal proof goal is absent, duplicated, or weakened")
    proof_goal_ids = [value["proof_goal_id"] for value in proof_goals]
    if len(proof_goal_ids) != len(set(proof_goal_ids)):
        raise ValueError("Finite semantic proof-goal identifiers are duplicated")
    if any(value["mandatory"] is not True or value["proof_methods"] != ([LEAN_PROOF_METHOD] if value["proof_goal_id"] == f"{identifier}.METAPROOF" else [PROOF_METHOD]) for value in proof_goals):
        raise ValueError("Finite result uses a nonsemantic or unchecked proof route")
    for proof_goal in proof_goals:
        proof_goal_id = proof_goal["proof_goal_id"]
        if proof_goal_id == f"{identifier}.METAPROOF":
            continue
        expected_value = _json_value(_regression_result(proof_goal_id))
        expected_claim = _equal(
            _function("finite_regression_observed", proof_goal_id),
            {"node": "typed_answer", "answer_type": "registered_exact_result", "value": expected_value},
        )
        if proof_goal["claim"] != expected_claim:
            raise ValueError(f"Finite replay proof goal {proof_goal_id} differs from its trusted exact algorithm")
    if specification.get("formal_statement_sha256") != FiniteFormalStatementHash(specification):
        raise ValueError("Finite semantic result hash is stale")


def _require_proof_fields(proof: Mapping[str, Any]) -> None:
    required = {"schema_version", "proof_id", "proof_method", "result_id", "proof_goal_id", "formal_statement_sha256", "claim", "claim_sha256", "assumptions_used", "foundation_dependencies", "result_dependencies", "payload"}
    if set(proof) != required:
        raise ValueError("Finite semantic proof-record fields do not match the grammar")
    payload_required = {"semantic_kernel_version", "result_schema_id", "derivation_method", "derivation", "regression_algorithm", "regression_expected", "assumption_model", "assumption_model_result", "anti_vacuity", "mutant_ids"}
    if not isinstance(proof["payload"], dict) or set(proof["payload"]) != payload_required:
        raise ValueError("Finite semantic payload fields do not match the grammar")


def _reject_floats(value: Any) -> None:
    if isinstance(value, float):
        raise ValueError("Floating-point values are forbidden in finite semantic proof records")
    if isinstance(value, dict):
        for child in value.values():
            _reject_floats(child)
    elif isinstance(value, list):
        for child in value:
            _reject_floats(child)


def _replay_derivation(identifier: str, derivation: Sequence[Mapping[str, Any]], specification: Mapping[str, Any]) -> None:
    expected = _proof_steps(identifier, specification)
    if list(derivation) != expected:
        raise ValueError("Finite semantic derivation differs from the trusted structural proof schema")
    available = {value["id"] for value in specification["assumptions"]}
    claims: dict[str, Any] = {}
    allowed_rules = {value["rule"] for value in PROFILES[identifier]["clauses"]} | {"conjunction_introduction"}
    for step in derivation:
        if step["rule"] not in allowed_rules or any(premise not in available for premise in step["premises"]):
            raise ValueError("Finite semantic derivation has an unknown rule or unavailable premise")
        if step["claim_sha256"] != CanonicalHash(step["claim"]):
            raise ValueError("Finite semantic derivation step hash is stale")
        if step["rule"] == "conjunction_introduction":
            expected_claim = {"node": "and", "arguments": [claims[premise] for premise in step["premises"]]}
            if step["claim"] != expected_claim:
                raise ValueError("Conjunction introduction does not compose the cited claims")
        available.add(step["step_id"])
        claims[step["step_id"]] = step["claim"]
    if not derivation or derivation[-1]["claim"] != specification["conclusion"]:
        raise ValueError("Finite semantic derivation does not end at the registered result conclusion")


def CheckFiniteSemanticProof(proof: Mapping[str, Any], specification: Mapping[str, Any]) -> dict[str, Any]:
    _require_proof_fields(proof)
    _reject_floats(proof)
    ValidateFiniteSemanticSpecification(specification)
    identifier = specification["result_id"]
    if proof["schema_version"] != "1.1.0" or proof["proof_method"] != PROOF_METHOD or proof["result_id"] != identifier:
        raise ValueError("Unknown finite semantic proof-record schema, proof method, or result")
    if proof["proof_id"] != f"{proof['proof_goal_id']}.FINITE-SEMANTIC.PROOF":
        raise ValueError("Finite semantic proof-record identifier is not canonical")
    if proof["formal_statement_sha256"] != specification["formal_statement_sha256"] or proof["formal_statement_sha256"] != FiniteFormalStatementHash(specification):
        raise ValueError("Finite semantic proof-record result hash mismatch")
    proof_goals = [value for value in specification["proof_goals"] if value["proof_goal_id"] == proof["proof_goal_id"]]
    if (
        len(proof_goals) != 1
        or proof_goals[0].get("proof_methods") != [PROOF_METHOD]
        or proof["claim"] != proof_goals[0]["claim"]
        or proof["claim_sha256"] != CanonicalHash(proof["claim"])
    ):
        raise ValueError("Finite semantic proof record proves a different or absent proof goal")
    expected_assumptions = [value["id"] for value in specification["assumptions"]]
    if proof["assumptions_used"] != expected_assumptions:
        raise ValueError("Finite semantic proof record omits, duplicates, or adds assumptions")
    if proof["foundation_dependencies"] != specification["foundation_dependencies"] or proof["result_dependencies"] != specification["result_dependencies"]:
        raise ValueError("Finite semantic proof-record dependency set mismatch")
    payload = proof["payload"]
    if payload["semantic_kernel_version"] != "finite-semantics-1.0.0" or payload["result_schema_id"] != f"{identifier}.FINITE-SCHEMA.1":
        raise ValueError("Finite semantic kernel or result-schema version mismatch")
    if payload["assumption_model_result"] is not True or not _model_is_satisfiable(identifier, payload["assumption_model"]):
        raise ValueError("Finite semantic assumption model is not an exact satisfiability witness")
    expected_anti_vacuity = {"conclusion_is_not_assumption": specification["conclusion"] not in [{key: value for key, value in assumption.items() if key != "id"} for assumption in specification["assumptions"]], "assumption_count": len(specification["assumptions"])}
    if payload["anti_vacuity"] != expected_anti_vacuity or payload["anti_vacuity"]["conclusion_is_not_assumption"] is not True:
        raise ValueError("Finite semantic anti-vacuity proof failed")
    if payload["mutant_ids"] != _mutant_ids(identifier):
        raise ValueError("Finite semantic result-specific mutant manifest mismatch")
    structural = proof["proof_goal_id"] == f"{identifier}.METAPROOF"
    if structural:
        if payload["derivation_method"] != "universal_structural_derivation" or payload["regression_algorithm"] is not None or payload["regression_expected"] is not None:
            raise ValueError("Universal finite result uses a fixture or malformed proof kind")
        _replay_derivation(identifier, payload["derivation"], specification)
        detail = {"derivation_method": payload["derivation_method"], "step_count": len(payload["derivation"]), "conclusion_sha256": CanonicalHash(specification["conclusion"])}
    else:
        if payload["derivation_method"] != "exact_finite_replay" or payload["derivation"] != [] or payload["regression_algorithm"] != proof["proof_goal_id"]:
            raise ValueError("Finite regression proof record has a malformed replay payload")
        observed = _json_value(_regression_result(payload["regression_algorithm"]))
        if observed != payload["regression_expected"] or observed != proof["claim"]["right"]["value"]:
            raise ValueError("Exact finite replay differs from the registered result")
        detail = {"derivation_method": payload["derivation_method"], "algorithm": payload["regression_algorithm"], "result_sha256": CanonicalHash(observed)}
    return {"proof_id": proof["proof_id"], "result_id": identifier, "proof_goal_id": proof["proof_goal_id"], "proof_method": PROOF_METHOD, "status": "PASS", "formal_statement_sha256": specification["formal_statement_sha256"], "assumptions_used": proof["assumptions_used"], "detail": detail}


def CheckFiniteSemanticPayload(payload: Mapping[str, Any], specification: Mapping[str, Any], root: Any, claim: Any) -> dict[str, Any]:
    del root
    ValidateFiniteSemanticSpecification(specification)
    matches = [value for value in specification["proof_goals"] if value["claim"] == claim]
    if len(matches) != 1:
        raise ValueError("Finite semantic payload claim is absent or ambiguous")
    proof_goal = matches[0]
    proof = {
        "schema_version": "1.1.0",
        "proof_id": f"{proof_goal['proof_goal_id']}.FINITE-SEMANTIC.PROOF",
        "proof_method": PROOF_METHOD,
        "result_id": specification["result_id"],
        "proof_goal_id": proof_goal["proof_goal_id"],
        "formal_statement_sha256": specification["formal_statement_sha256"],
        "claim": claim,
        "claim_sha256": CanonicalHash(claim),
        "assumptions_used": [value["id"] for value in specification["assumptions"]],
        "foundation_dependencies": specification["foundation_dependencies"],
        "result_dependencies": specification["result_dependencies"],
        "payload": dict(payload),
    }
    return CheckFiniteSemanticProof(proof, specification)["detail"]


def MutateFiniteSpecification(specification: Mapping[str, Any], mutant_id: str) -> dict[str, Any]:
    copied = json.loads(json.dumps(specification, ensure_ascii=False))
    identifier = copied["result_id"]
    if mutant_id not in _mutant_ids(identifier):
        raise ValueError("Unknown result-specific finite mutant")

    clause_mutants = {
        "answer_comparison_before_admission": (0, "answer_comparison_precedes_admission"),
        "omit_complete_mismatch_set": (2, "partial_mismatch_sample_suffices"),
        "replace_injectivity_by_surjectivity": (1, "surjectivity_replaces_collision_freedom"),
        "allow_orbit_collision_with_inverse": (2, "orbit_collision_compatible_with_inverse"),
        "omit_pre_restriction_stability": (1, "representative_recovery_without_image_stability"),
        "omit_coherent_lift": (3, "representative_recovery_without_coherent_lift"),
        "erase_answer_tags": (0, "serial_answer_tags_erased"),
        "allow_unregistered_cross_tag_cast": (1, "unregistered_cross_tag_cast_allowed"),
        "reverse_kernel_inclusion": (0, "weak_kernel_is_subset_of_strong_kernel"),
        "replace_kernel_intersection_by_union": (2, "product_query_kernel_is_kernel_union"),
        "reverse_factorization_kernel_inclusion": (1, "factorization_uses_reversed_kernel_inclusion"),
        "allow_suffix_side_channel": (6, "collapsed_pair_recovered_by_unregistered_side_channel"),
        "replace_price_image_count_by_block_size": (3, "added_consumer_price_uses_raw_block_size"),
        "assert_contextual_join_lattice": (4, "strong_congruences_form_contextual_join_lattice"),
        "require_section_for_carrier_verdict": (1, "carrier_verdict_requires_source_section"),
        "infer_effective_inverse_from_injectivity_alone": (5, "injectivity_alone_supplies_effective_inverse"),
    }
    assumption_mutants = {
        "remove_termination_premise": "CALC-F1.A3",
        "allow_empty_strong_congruence_intersection": "FIN-A6.A4",
        "change_partial_signature": "FIN-A6.A3",
        "omit_reader_faithfulness": "FIN-A7.A4",
    }
    if mutant_id in clause_mutants:
        index, predicate_name = clause_mutants[mutant_id]
        original = copied["conclusion"]["arguments"][index]
        replacement = _predicate(predicate_name, original)
        copied["conclusion"]["arguments"][index] = replacement
        copied["definitions"][index] = {"id": copied["definitions"][index]["id"], **replacement}
    else:
        assumption_id = assumption_mutants[mutant_id]
        copied["assumptions"] = [value for value in copied["assumptions"] if value["id"] != assumption_id]
    copied["proof_goals"] = [
        {**value, "claim": copied["conclusion"] if value["proof_goal_id"] == f"{identifier}.METAPROOF" else value["claim"]}
        for value in copied["proof_goals"]
    ]
    copied["formal_statement_sha256"] = FiniteFormalStatementHash(copied)
    return copied


__all__ = [
    "BuildFiniteSemanticSpecification",
    "PROOF_METHOD",
    "CheckFiniteSemanticProof",
    "CheckFiniteSemanticPayload",
    "FINITE_RESULT_IDS",
    "FiniteFormalStatementHash",
    "GenerateFiniteSemanticProofs",
    "MutateFiniteSpecification",
    "ValidateFiniteSemanticSpecification",
]
