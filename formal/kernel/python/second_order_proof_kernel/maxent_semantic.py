from __future__ import annotations

import csv
import json
from collections import Counter
from pathlib import Path
from typing import Any, Mapping

from .canonical import CanonicalHash, FileHash, LoadJson
from .maxent_semantic_g1_g5 import (
    BuildETRINVResidual,
    CheckMaxEntG1G5SemanticPayload,
    ClearLaurentPolynomial,
    CompileIntegerPolynomial,
    ExactConeAlternative,
    GenerateMaxEntG1G5CatalogAdapters,
    SEMANTIC_PROOF_GOAL_IDS as G1_G5_CLOSURE_PROOF_GOALS,
    StrictifierParameters,
)
from .maxent_semantic_g6_g9 import (
    CheckMaxEntG6G9SemanticPayload,
    SEMANTIC_PROOF_SCHEMAS as G6_G9_CLOSURE_SCHEMAS,
    GenerateMaxEntG6G9SemanticProofs,
)


RESULT_IDS = tuple(f"MAX-G{index}" for index in range(1, 10))
SCHEMA_VERSION = "2.0.0"
SEMANTIC_KERNEL_VERSION = "maxent-semantics-1.0.0"
SHARED_DEFINITION_FILE_SHA256 = "8df017476a6fe6df6c37a15606af0a7db7c09f2e1b7256e8cbaa68b94ce4dafb"
SEMANTIC_INVENTORY_FILE_SHA256 = "7834bf6e60e280e0d034f159230f246aa30f5d6dbb117bfb90a46ae94bc7a0f7"
FOUNDATION_SCHEMA_FILE_SHA256 = "26d00f724f1ae7538a27bd3df354989e06b20cd429381eccba2c322cb5fa1456"
G1_G5_CLOSURE_CHECKER = (
    "formal/kernel/python/second_order_proof_kernel/maxent_semantic_g1_g5.py"
)
G6_G9_CLOSURE_CHECKER = (
    "formal/kernel/python/second_order_proof_kernel/maxent_semantic_g6_g9.py"
)
SEMANTIC_CLOSURE_PROOF_GOALS = frozenset(
    set(G1_G5_CLOSURE_PROOF_GOALS) | set(G6_G9_CLOSURE_SCHEMAS)
)
SEMANTIC_CLOSURE_CHECKERS = {
    proof_goal_id: G1_G5_CLOSURE_CHECKER
    for proof_goal_id in G1_G5_CLOSURE_PROOF_GOALS
} | {
    proof_goal_id: G6_G9_CLOSURE_CHECKER
    for proof_goal_id in G6_G9_CLOSURE_SCHEMAS
}
G1_G5_WOLFRAM_REPLAY = (
    "formal/proofs/maxent/semantic/closures/MAX-G1-G5.wolfram-replay.json"
)
BANNED_NODES = {
    "declared_assumption_bundle",
    "declared_domain",
    "proof_goal",
    "registered_mathematical_statement",
}
ALLOWED_NODES = {
    "add",
    "and",
    "cartesian_power",
    "closed_interval",
    "constant_definition",
    "divide",
    "equal",
    "exclusive_or",
    "exists",
    "exp",
    "finite_product",
    "finite_sequence",
    "finite_set",
    "finite_sum",
    "forall",
    "function_application",
    "function_definition",
    "greater",
    "greater_equal",
    "iff",
    "implies",
    "integer",
    "left_open_interval",
    "less",
    "less_equal",
    "map",
    "multiply",
    "negate",
    "not",
    "power",
    "predicate_application",
    "rational",
    "record_type",
    "subtract",
    "sum_type",
    "tensor",
    "variable",
    "vector",
}
SPECIFICATION_FIELDS = {
    "assumptions",
    "conclusion",
    "definition_dependencies",
    "definitions",
    "domains",
    "formal_statement_sha256",
    "expected_proof_methods",
    "foundation_dependencies",
    "group",
    "kind",
    "nonclaims",
    "proof_goals",
    "quantifier_prefix",
    "registered_query_type",
    "schema_version",
    "scope",
    "sorts",
    "source_transcription_dependencies",
    "result_dependencies",
    "result_id",
    "title_en",
    "title_pt_BR",
    "variables",
    "withdrawal_condition",
}

CURRENT_SEMANTIC_REVIEW_STATUS = "MACHINE_CLOSED_RELATIVE_TO_FOUNDATION"


def _deliverables_root(root: Path | str | None) -> Path:
    if root is None:
        return Path(__file__).resolve().parents[4]
    path = Path(root).resolve()
    if (path / "formal").is_dir() and (path / "proofs").is_dir():
        return path
    if (path / "deliverables" / "formal").is_dir():
        return path / "deliverables"
    raise ValueError("MAX semantic root does not resolve to the deliverables directory")


def _semantic_root(root: Path | str | None) -> Path:
    return _deliverables_root(root) / "formal" / "proofs" / "maxent" / "semantic"


def _walk(value: Any):
    yield value
    if isinstance(value, dict):
        for child in value.values():
            yield from _walk(child)
    elif isinstance(value, list):
        for child in value:
            yield from _walk(child)


def _free_variables(value: Any, bound: frozenset[str] = frozenset()) -> set[str]:
    if isinstance(value, list):
        result: set[str] = set()
        for child in value:
            result |= _free_variables(child, bound)
        return result
    if not isinstance(value, dict):
        return set()
    node = value.get("node")
    if node == "variable":
        return set() if value["name"] in bound else {value["name"]}
    if node in {"forall", "exists"}:
        names = {binding["variable"] for binding in value["bindings"]}
        return _free_variables(value["body"], bound | names)
    if node in {"finite_sum", "finite_product", "map"}:
        name = value["binding"]["variable"]
        return _free_variables(value["domain"], bound) | _free_variables(value["body"], bound | {name})
    if node == "function_definition":
        names = {parameter["name"] for parameter in value["parameters"]}
        return _free_variables(value["body"], bound | names)
    result: set[str] = set()
    for child in value.values():
        result |= _free_variables(child, bound)
    return result


def _formal_hash(specification: Mapping[str, Any]) -> str:
    return CanonicalHash(
        {
            key: value
            for key, value in specification.items()
            if key not in {"title_en", "title_pt_BR", "formal_statement_sha256"}
        }
    )


def _read_result_field(text: str, label: str) -> str:
    prefix = f"\\ResultField{{{label}}}{{"
    start = text.find(prefix)
    if start < 0:
        raise ValueError(f"Missing bilingual proof field: {label}")
    cursor = start + len(prefix)
    depth = 1
    while cursor < len(text) and depth:
        if text[cursor] == "{" and (cursor == 0 or text[cursor - 1] != "\\"):
            depth += 1
        elif text[cursor] == "}" and (cursor == 0 or text[cursor - 1] != "\\"):
            depth -= 1
        cursor += 1
    if depth:
        raise ValueError(f"Unbalanced bilingual proof field: {label}")
    return text[start + len(prefix) : cursor - 1]


def _written_statement(result_id: str, locale: str, root: Path | str | None) -> dict[str, Any]:
    deliverables = _deliverables_root(root)
    language = "en" if locale == "en" else "pt_BR"
    label = "Exact statement." if locale == "en" else "Enunciado exato."
    path = deliverables / "proofs" / language / "results" / f"{result_id}.tex"
    text = path.read_text(encoding="utf-8")
    if f"\\ResultID{{{result_id}}}" not in text or f"formal/specs/{result_id}.json" not in text:
        raise ValueError("Bilingual proof lacks its result identifier or canonical-spec marker")
    canonical = LoadJson(deliverables / "formal" / "specs" / f"{result_id}.json")
    definitions = canonical.get("definitions", [])
    if len(definitions) != 1:
        raise ValueError("Canonical bilingual bridge has no unique registered statement")
    key = "text_en" if locale == "en" else "text_pt_BR"
    expected = definitions[0].get(key)
    observed = _read_result_field(text, label)
    normalized = observed.replace("\\(", "").replace("\\)", "")
    for latex_token, plain_token in (
        ("\\{", "{"),
        ("\\}", "}"),
        ("\\ldots", "..."),
    ):
        normalized = normalized.replace(latex_token, plain_token)
    observed_statement_sha256 = CanonicalHash({"locale": locale, "statement": normalized})
    hash_key = "english_statement_sha256" if locale == "en" else "portuguese_statement_sha256"
    expected_hash = definitions[0].get(hash_key)
    if expected is not None:
        if normalized != expected:
            raise ValueError("Bilingual exact statement differs from the current registered statement")
    elif expected_hash != observed_statement_sha256:
        raise ValueError("Bilingual exact statement hash differs from the current registered statement")
    return {
        "path": str(path.relative_to(deliverables)),
        "sha256": FileHash(path),
        "registered_statement_sha256": observed_statement_sha256,
        "lexical_match": True,
    }


def _validate_specification(specification: Mapping[str, Any], root: Path | str | None) -> None:
    if set(specification) != SPECIFICATION_FIELDS:
        raise ValueError("MAX semantic specification fields differ from the declared grammar")
    result_id = specification.get("result_id")
    if result_id not in RESULT_IDS or specification.get("schema_version") != SCHEMA_VERSION:
        raise ValueError("Unknown MAX result or semantic schema version")
    if specification.get("group") != "MAX" or specification.get("kind") != "theorem":
        raise ValueError("MAX semantic result has the wrong group or kind")
    if _formal_hash(specification) != specification.get("formal_statement_sha256"):
        raise ValueError("MAX semantic formal-statement hash mismatch")
    variable_names = [row.get("name") for row in specification["variables"]]
    if len(variable_names) != len(set(variable_names)) or any(not isinstance(name, str) for name in variable_names):
        raise ValueError("MAX semantic variables are malformed or duplicated")
    top_variables = set(variable_names)
    for section in ["definitions", "domains", "assumptions", "conclusion", "proof_goals"]:
        unbound = _free_variables(specification[section]) - top_variables
        if unbound:
            raise ValueError(f"MAX semantic specification has unbound variables in {section}: {sorted(unbound)}")
    proof_goals = specification["proof_goals"]
    proof_goal_ids = [row.get("proof_goal_id") for row in proof_goals]
    if len(proof_goal_ids) != len(set(proof_goal_ids)) or any(not isinstance(value, str) for value in proof_goal_ids):
        raise ValueError("MAX semantic proof-goal identifiers are malformed or duplicated")
    if any(row.get("mandatory") is not True for row in proof_goals):
        raise ValueError("MAX semantic specification contains a nonmandatory registered proof goal")
    claims = [row.get("claim") for row in proof_goals]
    if specification["conclusion"] != {"node": "and", "arguments": claims}:
        raise ValueError("MAX semantic conclusion is not the ordered conjunction of its proof goals")
    expected_methods = sorted(
        {
            proof_method
            for row in proof_goals
            for proof_method in row.get("proof_methods", [])
        }
    )
    if specification["expected_proof_methods"] != expected_methods:
        raise ValueError("MAX semantic proof-method union mismatch")
    nodes = {
        value["node"]
        for value in _walk(specification)
        if isinstance(value, dict) and isinstance(value.get("node"), str)
    }
    if nodes & BANNED_NODES or nodes - ALLOWED_NODES:
        raise ValueError("MAX semantic AST contains an opaque or unknown node")
    semantic = _semantic_root(root)
    shared_path = semantic / "shared_maxent_definitions.json"
    inventory_path = semantic / "semantic_spec_inventory.json"
    foundation_path = semantic / "required_foundation_schemas.json"
    if (
        FileHash(shared_path) != SHARED_DEFINITION_FILE_SHA256
        or FileHash(inventory_path) != SEMANTIC_INVENTORY_FILE_SHA256
        or FileHash(foundation_path) != FOUNDATION_SCHEMA_FILE_SHA256
    ):
        raise ValueError("MAX semantic shared definition, inventory, or foundation hash mismatch")
    shared = LoadJson(shared_path)
    if specification["definition_dependencies"] != [shared.get("definition_set_id")]:
        raise ValueError("MAX semantic shared-definition dependency mismatch")
    if "Private`" in json.dumps(specification, ensure_ascii=False) or "Private`" in json.dumps(shared, ensure_ascii=False):
        raise ValueError("MAX semantic specification exposes a Wolfram private context")
    inventory = LoadJson(inventory_path)
    rows = [row for row in inventory["specifications"] if row["result_id"] == result_id]
    if len(rows) != 1 or rows[0]["proof_goals"] != proof_goal_ids or rows[0]["formal_statement_sha256"] != specification["formal_statement_sha256"]:
        raise ValueError("MAX semantic inventory disagrees with the specification")
    required_foundation_registry = LoadJson(foundation_path)
    required_foundation_rows = required_foundation_registry.get("items", [])
    required_foundation_fields = {
        "classification",
        "formal_statement",
        "foundation_id",
        "justification",
        "proof_path",
        "source_citation",
        "withdrawal_effect",
    }
    if required_foundation_registry.get("schema_version") != SCHEMA_VERSION:
        raise ValueError("MAX required-foundation registry version changed")
    required_foundations = {row.get("foundation_id") for row in required_foundation_rows}
    if len(required_foundations) != len(required_foundation_rows) or None in required_foundations:
        raise ValueError("MAX required-foundation identifiers are absent or duplicated")
    deliverables = _deliverables_root(root)
    for row in required_foundation_rows:
        if set(row) != required_foundation_fields:
            raise ValueError("MAX required-foundation metadata is incomplete")
        if row["classification"] not in {
            "axiom",
            "derived foundation lemma",
            "imported standard theorem",
            "software-semantic assumption",
        }:
            raise ValueError("MAX required-foundation classification is unknown")
        if not row["source_citation"] or not row["justification"] or not row["withdrawal_effect"]:
            raise ValueError("MAX required-foundation provenance or scope metadata is empty")
        proof_path = row["proof_path"]
        if row["classification"] == "derived foundation lemma":
            proof_path = (deliverables / proof_path).resolve()
            if not proof_path or deliverables.resolve() not in proof_path.parents or not proof_path.is_file():
                raise ValueError("MAX derived foundation lacks its local proof")
            proof = LoadJson(proof_path)
            if set(proof) != {
                "conclusion",
                "formal_statement_sha256",
                "foundation_id",
                "proof_id",
                "proof_method",
                "schema_version",
                "steps",
            }:
                raise ValueError("MAX derived-foundation proof has an unknown grammar")
            if (
                proof["schema_version"] != "1.0.0"
                or proof["proof_id"] != f"{row['foundation_id']}.PROOF"
                or proof["proof_method"] != "LocalStructuralDerivationProof"
                or proof["foundation_id"] != row["foundation_id"]
                or proof["formal_statement_sha256"] != CanonicalHash(row["formal_statement"])
                or proof["conclusion"] != row["formal_statement"]
                or not proof["steps"]
            ):
                raise ValueError("MAX derived-foundation proof is false or stale")
        elif proof_path:
            raise ValueError("MAX imported or assumed foundation falsely names a local proof")
    integrated_foundation_rows = LoadJson(
        deliverables / "formal" / "foundation" / "trusted_foundation.json"
    )["items"]
    integrated_by_id = {row["foundation_id"]: row for row in integrated_foundation_rows}
    integrated_foundations = set(integrated_by_id)
    for row in required_foundation_rows:
        integrated = integrated_by_id.get(row["foundation_id"])
        if integrated is not None and (
            integrated["classification"] != row["classification"]
            or integrated["formal_statement"] != row["formal_statement"]
            or integrated["proof_path"] != row["proof_path"]
        ):
            raise ValueError("MAX required foundation conflicts with an integrated foundation of the same ID")
    if set(specification["foundation_dependencies"]) - required_foundations - integrated_foundations:
        raise ValueError("MAX semantic specification names an unknown foundation dependency")
    for dependency in specification["source_transcription_dependencies"]:
        path = (deliverables / dependency).resolve()
        if deliverables.resolve() not in path.parents or not path.is_file():
            raise ValueError("MAX semantic source-transcription dependency is absent or escapes the package")
    for dependency in specification["result_dependencies"]:
        if dependency not in RESULT_IDS or not (deliverables / "formal" / "specs" / f"{dependency}.json").is_file():
            raise ValueError("MAX semantic result dependency is absent or unknown")
    canonical = LoadJson(deliverables / "formal" / "specs" / f"{result_id}.json")
    if specification["title_en"] != canonical.get("title_en") or specification["title_pt_BR"] != canonical.get("title_pt_BR"):
        raise ValueError("MAX semantic title differs from the current bilingual canonical title")
    _written_statement(result_id, "en", root)
    _written_statement(result_id, "pt_BR", root)


def BuildMaxEntSemanticSpecification(result_id: str, root: Path | str | None = None) -> dict[str, Any]:
    if result_id not in RESULT_IDS:
        raise ValueError("Unknown finite-MaxEnt result identifier")
    specification = LoadJson(_semantic_root(root) / "specs" / f"{result_id}.json")
    _validate_specification(specification, root)
    return specification


def _lean_kernel_proof_goal_ids(
    root: Path | str | None,
) -> frozenset[str]:
    path = _deliverables_root(root) / "registry" / "proof_goal_registry.tsv"
    with path.open(encoding="utf-8", newline="") as handle:
        rows = list(csv.DictReader(handle, delimiter="\t"))
    identifiers = {
        row["proof_goal_id"]
        for row in rows
        if row["result_id"] in RESULT_IDS
        and (
            row.get("proof_goal_type") == "LeanKernelProof"
            or row.get("machine_status") == "LeanKernelProofPass"
        )
    }
    if len(identifiers) != 8:
        raise ValueError("MAX Lean-kernel proof-goal registry must contain exactly eight goals")
    return frozenset(identifiers)


def CheckMaxEntG1G5WolframReplay(
    root: Path | str | None = None,
) -> dict[str, Any]:
    deliverables = _deliverables_root(root)
    replay = LoadJson(deliverables / G1_G5_WOLFRAM_REPLAY)
    required = {
        "schema_version",
        "kernel",
        "wolfram_source",
        "wolfram_source_sha256",
        "residual_constructors",
        "contraction_strictifier",
        "one_hot_tag_lift",
        "laurent_and_integer_compiler",
        "g4_and_g5",
    }
    if (
        set(replay) != required
        or replay["schema_version"] != "1.0.0"
        or replay["kernel"] != "MaxEntG1G5SemanticClosure`"
    ):
        raise ValueError("MAX G1--G5 Wolfram replay has an unknown grammar or identity")
    source_path = "formal/kernel/wolfram/MaxEntG1G5SemanticClosure.wl"
    if (
        replay["wolfram_source"] != source_path
        or replay["wolfram_source_sha256"] != FileHash(deliverables / source_path)
    ):
        raise ValueError("MAX G1--G5 Wolfram replay source is absent or stale")
    constructors = [
        {"kind": "one", "variable_index": 0},
        {"kind": "add", "left_index": 0, "right_index": 1, "result_index": 2},
        {"kind": "inverse", "left_index": 0, "right_index": 1},
    ]
    residuals = [
        BuildETRINVResidual({"variable_count": 3, "equations": [constructor]})
        for constructor in constructors
    ]
    expected_residual = {
        "coefficient_l1_norms": [row["coefficient_l1_norm"] for row in residuals],
        "total_degrees": [row["total_degree"] for row in residuals],
    }
    if replay["residual_constructors"] != expected_residual:
        raise ValueError("Wolfram ETR-INV residual anchors differ from the exact compiler")
    parameters = StrictifierParameters(
        {
            "variable_count": 2,
            "equations": [{"kind": "one", "variable_index": 0}],
        }
    )
    expected_strictifier = {
        "exact_recurrence_orders_0_through_10": True,
        "local_error_identity_exact": True,
        "completed_square_identity_exact": True,
        "strict_scale_bounds_1_through_128": True,
        "sample_gap_exponent": parameters["dyadic_gap_exponent"],
        "sample_chain_length": parameters["chain_length"],
        "sample_strict_negative_power_exponent": -8189,
        "sample_strict_negative_exact": True,
    }
    if replay["contraction_strictifier"] != expected_strictifier:
        raise ValueError("Wolfram contraction-strictifier anchors changed")
    expected_tag = {
        "positive_copy_dominates_common_factor": True,
        "negative_copy_is_bounded_by_common_factor": True,
        "all_one_tag_slice_exact": True,
    }
    if replay["one_hot_tag_lift"] != expected_tag:
        raise ValueError("Wolfram one-hot-tag domination anchors failed")
    laurent = ClearLaurentPolynomial(
        {
            "dimension": 2,
            "terms": [
                {"exponents": [-2, 1], "coefficient": "1/2"},
                {"exponents": [0, -1], "coefficient": "-3/4"},
            ],
        }
    )
    compiled = CompileIntegerPolynomial(
        {
            "dimension": 1,
            "terms": [
                {"exponents": [1], "coefficient": "-1"},
                {"exponents": [2], "coefficient": "2"},
            ],
        }
    )
    expected_laurent = {
        "minimal_shift": laurent["shift"],
        "positive_denominator_lcm": laurent["positive_denominator_lcm"],
        "cleared_coefficient_rows": [[[2, 0], -3], [[0, 2], 2]],
        "cleared_polynomial_exact": True,
        "integer_compiler_coefficient_l1": compiled["coefficient_l1_norm"],
    }
    if replay["laurent_and_integer_compiler"] != expected_laurent:
        raise ValueError("Wolfram Laurent or integer-compiler anchors changed")
    expected_g4_g5 = {
        "g4_cross_factorization_exact": True,
        "g4_probability_table": [
            {
                "activity": "3/4",
                "left_probability": "32/59",
                "right_probability": "16/25",
            },
            {
                "activity": "1/2",
                "left_probability": "4/5",
                "right_probability": "4/5",
            },
            {
                "activity": "1/4",
                "left_probability": "32/33",
                "right_probability": "16/17",
            },
        ],
        "g4_unique_physical_interior_root": "1/2",
        "g5_kernel_branch_exact": ExactConeAlternative([[1, -1]])["branch"]
        == "normalized_nonnegative_kernel",
        "g5_row_space_branch_exact": ExactConeAlternative([[1, 0], [0, 1]])[
            "branch"
        ]
        == "strictly_positive_row_space",
    }
    if replay["g4_and_g5"] != expected_g4_g5:
        raise ValueError("Wolfram G4 or G5 exact anchors changed")
    return {
        "status": "PASS",
        "wolfram_source_sha256": replay["wolfram_source_sha256"],
        "replay_sha256": CanonicalHash(replay),
        "cross_engine_anchor_count": 5,
    }


def GenerateMaxEntSemanticProofs(root: Path | str | None = None) -> list[dict[str, Any]]:
    lean_kernel_proof_goal_ids = _lean_kernel_proof_goal_ids(root)
    g1_g5_rows = GenerateMaxEntG1G5CatalogAdapters(root)
    if any(row["proof_goal_id"] in lean_kernel_proof_goal_ids for row in g1_g5_rows):
        raise ValueError("MAX G1--G5 semantic adapters overlap Lean-kernel proof goals")
    g1_g5_closures = {row["proof_goal_id"]: row for row in g1_g5_rows}
    g6_g9_closures: dict[str, dict[str, Any]] = {}
    for proof in GenerateMaxEntG6G9SemanticProofs(root):
        proof_goal_id = proof["proof_goal_id"]
        if proof_goal_id in lean_kernel_proof_goal_ids:
            raise ValueError("MAX G6--G9 semantic proofs overlap Lean-kernel proof goals")
        checker_path = _deliverables_root(root) / G6_G9_CLOSURE_CHECKER
        g6_g9_closures[proof_goal_id] = {
            "result_id": proof["result_id"],
            "proof_goal_id": proof_goal_id,
            "closure_proof": proof,
            "checker_module": G6_G9_CLOSURE_CHECKER,
            "checker_module_sha256": FileHash(checker_path),
            "replayed_universal": proof_goal_id
            not in {
                "MAX-G6.ENUM.01",
                "MAX-G6.PROVENANCE.03",
                "MAX-G9.LAWTOENV.01",
                "MAX-G9.ENVTOLAW.02",
            },
            "supports_whole_result_closure": True,
        }
    semantic_closures = g1_g5_closures | g6_g9_closures
    if (
        len(semantic_closures) != 22
        or set(semantic_closures) != set(SEMANTIC_CLOSURE_PROOF_GOALS)
    ):
        raise ValueError("MAX semantic closure adapters must cover all 22 non-Lean proof goals")
    records: list[dict[str, Any]] = []
    seen: set[str] = set()
    for result_id in RESULT_IDS:
        specification = BuildMaxEntSemanticSpecification(result_id, root)
        bilingual = {
            "english": _written_statement(result_id, "en", root),
            "portuguese": _written_statement(result_id, "pt_BR", root),
            "semantic_review_status": CURRENT_SEMANTIC_REVIEW_STATUS,
            "semantic_review_reason": (
                "The semantic companion is machine-closed relative to its declared "
                "trusted foundation."
            ),
        }
        for proof_goal in specification["proof_goals"]:
            proof_goal_id = proof_goal["proof_goal_id"]
            if proof_goal_id in lean_kernel_proof_goal_ids:
                continue
            if proof_goal_id not in semantic_closures or proof_goal_id in seen:
                raise ValueError("MAX semantic closure coverage is incomplete or duplicated")
            seen.add(proof_goal_id)
            adapter = semantic_closures[proof_goal_id]
            closure = adapter["closure_proof"]
            payload = {
                "semantic_kernel_version": SEMANTIC_KERNEL_VERSION,
                "closure_status": CURRENT_SEMANTIC_REVIEW_STATUS,
                "proof_goal_id": proof_goal_id,
                "claim_sha256": CanonicalHash(proof_goal["claim"]),
                "proof_method": closure["proof_method"],
                "closure_proof": closure,
                "checker_module": adapter["checker_module"],
                "checker_module_sha256": adapter["checker_module_sha256"],
                "replayed_universal": adapter["replayed_universal"],
                "supports_whole_result_closure": adapter[
                    "supports_whole_result_closure"
                ],
            }
            record = {
                "schema_version": "1.0.0",
                "record_id": f"{proof_goal_id}.MAXENT-SEMANTIC",
                "record_class": "MaxEntSemanticClosureRecord",
                "result_id": result_id,
                "proof_goal_id": proof_goal_id,
                "formal_statement_sha256": specification["formal_statement_sha256"],
                "claim": proof_goal["claim"],
                "claim_sha256": CanonicalHash(proof_goal["claim"]),
                "declared_proof_methods": proof_goal["proof_methods"],
                "foundation_dependencies": specification["foundation_dependencies"],
                "result_dependencies": specification["result_dependencies"],
                "bilingual_statement_audit": bilingual,
                "payload": payload,
            }
            result = CheckMaxEntSemanticPayload(record["payload"], specification, root, record["claim"])
            if result["status"] != "PASS":
                raise ValueError("MAX semantic proof did not pass its independent checker")
            records.append(record)
    if len(records) != 22 or set(semantic_closures) != seen:
        raise ValueError("MAX semantic proof catalogue does not cover all 22 non-Lean proof goals exactly once")
    return records


def BuildMaxEntSemanticCatalog(
    root: Path | str | None = None,
) -> dict[str, Any]:
    records = GenerateMaxEntSemanticProofs(root)
    lean_kernel_proof_goal_ids = _lean_kernel_proof_goal_ids(root)
    status_counts = Counter(row["payload"]["closure_status"] for row in records)
    universal = [
        row["proof_goal_id"]
        for row in records
        if row["payload"]["replayed_universal"]
    ]
    registered = [
        row["proof_goal_id"]
        for row in records
        if not row["payload"]["replayed_universal"]
    ]
    semantic_closed_results = {
        result_id
        for result_id in RESULT_IDS
        if all(
            row["payload"]["supports_whole_result_closure"]
            for row in records
            if row["result_id"] == result_id
        )
    }
    if status_counts != {CURRENT_SEMANTIC_REVIEW_STATUS: 22}:
        raise ValueError("MAX semantic catalogue is not closed on all 22 non-Lean proof goals")
    if semantic_closed_results != set(RESULT_IDS):
        raise ValueError("MAX semantic catalogue does not cover all nine results")
    return {
        "schema_version": "1.0.0",
        "catalog_id": "MAXENT-SEMANTIC-CLOSURE-AUDIT-1",
        "scope": "MAX-G1 through MAX-G9: 22 semantic-replay proof goals and 8 Lean-kernel proof goals",
        "record_count": len(records),
        "semantic_replay_proof_goal_count": len(records),
        "lean_kernel_proof_goal_count": len(lean_kernel_proof_goal_ids),
        "total_registered_proof_goal_count": len(records) + len(lean_kernel_proof_goal_ids),
        "lean_kernel_proof_goal_ids": sorted(lean_kernel_proof_goal_ids),
        "closure_status_counts": dict(sorted(status_counts.items())),
        "replay_kind_counts": {
            "registered_exact_nonuniversal": len(registered),
            "universal_proof_schema_relative_to_foundation": len(universal),
        },
        "replayed_universal_proof_goals": universal,
        "semantic_replay_covered_result_count": len(semantic_closed_results),
        "semantic_replay_covered_result_ids": sorted(semantic_closed_results),
        "records": records,
    }


def BuildMaxEntBilingualStatementAudit(
    root: Path | str | None = None,
) -> dict[str, Any]:
    records = GenerateMaxEntSemanticProofs(root)
    audits: list[dict[str, Any]] = []
    for result_id in RESULT_IDS:
        matches = [
            row["bilingual_statement_audit"]
            for row in records
            if row["result_id"] == result_id
        ]
        if not matches or any(row != matches[0] for row in matches[1:]):
            raise ValueError("MAX bilingual audit differs within one result")
        audits.append({"result_id": result_id, **matches[0]})
    if any(
        audit["semantic_review_status"] != CURRENT_SEMANTIC_REVIEW_STATUS
        or not audit["english"]["lexical_match"]
        or not audit["portuguese"]["lexical_match"]
        for audit in audits
    ):
        raise ValueError("MAX bilingual audit is not current and matched")
    return {
        "schema_version": "1.0.0",
        "status": "PASS_BILINGUAL_STATEMENT_MATCH",
        "lexically_matched_result_count": len(audits),
        "audited_result_count": len(audits),
        "semantic_replay_proof_goal_count": len(records),
        "lean_kernel_proof_goal_count": len(_lean_kernel_proof_goal_ids(root)),
        "total_registered_proof_goal_count": len(records) + len(_lean_kernel_proof_goal_ids(root)),
        "audits": audits,
    }


def CheckMaxEntSemanticPayload(
    payload: Mapping[str, Any],
    specification: Mapping[str, Any],
    root: Path | str | None = None,
    claim: Any = None,
) -> dict[str, Any]:
    _validate_specification(specification, root)
    proof_goal_id = payload.get("proof_goal_id")
    matches = [row for row in specification["proof_goals"] if row["proof_goal_id"] == proof_goal_id]
    if len(matches) != 1:
        raise ValueError("MAX semantic payload names an absent or ambiguous proof goal")
    proof_goal = matches[0]
    if claim is None:
        claim = proof_goal["claim"]
    if claim != proof_goal["claim"] or payload.get("claim_sha256") != CanonicalHash(claim):
        raise ValueError("MAX semantic payload proves a different or stale claim")
    status = payload.get("closure_status")
    if proof_goal_id in SEMANTIC_CLOSURE_PROOF_GOALS:
        required = {
            "semantic_kernel_version",
            "closure_status",
            "proof_goal_id",
            "claim_sha256",
            "proof_method",
            "closure_proof",
            "checker_module",
            "checker_module_sha256",
            "replayed_universal",
            "supports_whole_result_closure",
        }
        if set(payload) != required or status != "MACHINE_CLOSED_RELATIVE_TO_FOUNDATION":
            raise ValueError("Machine-closed MAX semantic payload has an unknown grammar or status")
        if payload["semantic_kernel_version"] != SEMANTIC_KERNEL_VERSION:
            raise ValueError("MAX semantic kernel version mismatch")
        expected_checker = SEMANTIC_CLOSURE_CHECKERS[proof_goal_id]
        if payload["checker_module"] != expected_checker:
            raise ValueError("MAX semantic closure points to an unrelated checker")
        checker_path = _deliverables_root(root) / expected_checker
        if payload["checker_module_sha256"] != FileHash(checker_path):
            raise ValueError("MAX semantic closure checker digest is stale")
        closure = payload["closure_proof"]
        if (
            closure.get("proof_goal_id") != proof_goal_id
            or closure.get("result_id") != specification["result_id"]
            or closure.get("claim") != claim
            or closure.get("claim_sha256") != payload["claim_sha256"]
            or closure.get("proof_method") != payload["proof_method"]
        ):
            raise ValueError("MAX semantic closure proof is unrelated or stale")
        if proof_goal_id in G1_G5_CLOSURE_PROOF_GOALS:
            detail = CheckMaxEntG1G5SemanticPayload(
                closure["payload"], specification, root, claim
            )
            expected_universal = proof_goal_id != "MAX-G4.TIE.02"
        else:
            detail = CheckMaxEntG6G9SemanticPayload(
                closure["payload"], specification, root, claim
            )
            expected_universal = proof_goal_id not in {
                "MAX-G6.ENUM.01",
                "MAX-G6.PROVENANCE.03",
                "MAX-G9.LAWTOENV.01",
                "MAX-G9.ENVTOLAW.02",
            }
        if payload["replayed_universal"] is not expected_universal or payload["supports_whole_result_closure"] is not True:
            raise ValueError("MAX semantic closure misstates its quantifier or whole-result support")
        return {
            "status": "PASS",
            "closure_status": status,
            "proof_goal_id": proof_goal_id,
            "claim_sha256": payload["claim_sha256"],
            "checker_module_sha256": payload["checker_module_sha256"],
            "detail": detail,
        }
    raise ValueError("MAX semantic payload names a proof goal outside the closed semantic layer")


__all__ = [
    "BuildMaxEntBilingualStatementAudit",
    "BuildMaxEntSemanticSpecification",
    "BuildMaxEntSemanticCatalog",
    "CheckMaxEntG1G5WolframReplay",
    "CheckMaxEntSemanticPayload",
    "GenerateMaxEntSemanticProofs",
    "SEMANTIC_KERNEL_VERSION",
    "RESULT_IDS",
]
