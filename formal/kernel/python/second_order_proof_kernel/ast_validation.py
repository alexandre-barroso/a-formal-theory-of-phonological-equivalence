from __future__ import annotations

from typing import Any


SUPPORTED_SORTS = {
    "Boolean", "natural number", "integer", "rational", "real", "nonnegative real", "positive real", "finite index set", "finite sequence", "finite set", "finite multiset", "finite map", "partial map", "relation", "partition", "finite directed graph", "polynomial", "Laurent polynomial", "finite exponential sum", "vector", "matrix", "probability mass function", "typed answer object", "analytic germ with declared remainder condition", "finite proof code"
}

OPAQUE_NODES = {"declared_assumption_bundle", "declared_domain", "proof_goal", "registered_mathematical_statement"}

FORMAL_NODES = {
    "add", "analytic_proof_result", "and", "asymptotic_equivalent", "bell_number", "boolean", "cardinality", "collision_pairs", "compose", "conditional", "conjunction", "contextual_assumptions", "continuous_hg_assumptions", "continuous_hg_result", "convex", "derivative", "difference", "divide", "domain", "equal", "exact_application_result", "exact_data_replay", "exists", "exponential_polynomial_identity", "fibre", "finite_decision", "finite_enumeration_result", "finite_map", "finite_product", "finite_recursion", "finite_set", "finite_sum", "flux_assumptions", "flux_result", "forall", "frontier", "function_application", "geometric_stopped_law", "graph_has_reachable_cycle", "greater", "greater_equal", "image", "implies", "in", "integer", "intersection", "inverse_image", "kernel", "kernel_partition", "kkt_conditions", "laurent_polynomial_identity", "less", "less_equal", "limit", "list", "lookup", "many_sorted_valid", "map", "map_image", "map_kernel", "map_set", "matrix", "max", "membership", "min", "multiset", "multiply", "natural", "negate", "nonnegative", "not", "not_equal", "or", "outbound_edges", "partition", "polynomial", "polynomial_identity", "positive", "positive_part", "power", "predicate_application", "probability_mass_function", "pushforward_sum", "quotient", "rational", "real_constant", "relation", "select", "semantic_domain", "sequence", "set", "set_difference", "statement_correspondence", "subtract", "support_selection_assumptions", "support_selection_result", "termination_measure", "typed_answer", "union", "unique", "values", "variable", "vector"
}


def ValidateSpecification(specification: dict[str, Any]) -> list[str]:
    failures: list[str] = []
    variables = specification.get("variables", [])
    names = [value.get("name") for value in variables if isinstance(value, dict)]
    if len(names) != len(variables) or any(not isinstance(value, str) or not value for value in names) or len(names) != len(set(names)):
        failures.append("variables are not uniquely and explicitly declared")
    for value in variables:
        if value.get("sort") not in SUPPORTED_SORTS:
            failures.append(f"unsupported variable sort: {value.get('sort')}")
    sorts = specification.get("sorts", [])
    if any(value not in SUPPORTED_SORTS for value in sorts):
        failures.append("the specification declares an unsupported sort")
    definition_names = {value.get("id") for value in specification.get("definitions", []) if isinstance(value, dict)}
    if None in definition_names or len(definition_names) != len(specification.get("definitions", [])):
        failures.append("definitions are not uniquely identified")
    used: set[str] = set()
    for field in ["domains", "definitions", "assumptions", "conclusion"]:
        failures.extend(ValidateNode(specification.get(field), set(names), definition_names, used, field))
    if used != set(names):
        failures.append("formal variables are undeclared or unused")
    if any(value.get("quantifier") not in {"forall", "exists"} for value in specification.get("quantifier_prefix", [])):
        failures.append("quantifier prefix contains a nonformal declaration")
    return sorted(set(failures))


def ValidateNode(value: Any, variables: set[str], definitions: set[str], used: set[str], location: str) -> list[str]:
    failures: list[str] = []
    if isinstance(value, list):
        for index, child in enumerate(value):
            failures.extend(ValidateNode(child, variables, definitions, used, f"{location}[{index}]"))
        return failures
    if not isinstance(value, dict):
        return failures
    node = value.get("node")
    if node in OPAQUE_NODES:
        failures.append(f"{location}: opaque node {node}")
    elif node is not None and node not in FORMAL_NODES:
        failures.append(f"{location}: unknown formal node {node}")
    if node == "variable":
        name = value.get("name")
        if name not in variables:
            failures.append(f"{location}: undeclared variable {name}")
        else:
            used.add(name)
    if node in {"function_application", "predicate_application"}:
        name = value.get("name")
        if name not in definitions and not str(name).startswith("builtin:"):
            failures.append(f"{location}: undefined symbol {name}")
    if "text" in value or "text_en" in value or "text_pt_BR" in value:
        failures.append(f"{location}: prose is not a formal definition")
    if node == "select":
        failures.extend(ValidateNode(value.get("domain"), variables, definitions, used, f"{location}.domain"))
        bound_name = value.get("variable")
        if not isinstance(bound_name, str) or not bound_name:
            failures.append(f"{location}: select binder is malformed")
        else:
            bound_used: set[str] = set()
            failures.extend(ValidateNode(value.get("predicate"), variables | {bound_name}, definitions, bound_used, f"{location}.predicate"))
            if bound_name not in bound_used:
                failures.append(f"{location}: select binder is unused")
            used.update(bound_used - {bound_name})
        return failures
    for key, child in value.items():
        if key not in {"node", "name", "id", "sort", "returns", "operator", "value", "quantifier"}:
            failures.extend(ValidateNode(child, variables, definitions, used, f"{location}.{key}"))
    return failures
