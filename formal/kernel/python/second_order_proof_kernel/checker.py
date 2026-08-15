from __future__ import annotations

import csv
import json
from collections import Counter
from fractions import Fraction
from pathlib import Path
from typing import Any, Callable

from .ast_validation import ValidateSpecification
from .application_model import ReplayApplication
from .canonical import CanonicalHash, FileHash, LoadJson
from .expressions import EvaluateExpression, FreeVariables, RequireBoolean, Substitute
from .finite_model import EvaluateFiniteModel
from .finite_semantics import CheckFiniteSemanticPayload
from .foundation import CheckFoundationRegistry
from .linear import Determinant, Multiply as MatrixMultiply, ParseMatrix, PositiveSemidefinite, Rank
from .maxent_semantic import CheckMaxEntSemanticPayload
from .polynomial import Add, Multiply, ParsePolynomial
from .rational import ParseDecimalRational, ParseRational, RationalText
from .semantic_replay import CheckSemanticPayload


ALLOWED_PROOF_METHODS = {
    "FirstOrderProof", "BooleanTautologyProof", "FiniteEnumerationProof", "InductionProof",
    "RewriteChainProof", "PolynomialIdentityProof", "LaurentClearingProof", "IdealMembershipProof",
    "SumOfSquaresProof", "SemialgebraicUnsatProof", "ExactLinearAlgebraProof", "ConvexityProof",
    "KKTGlobalOptimalityProof", "LimitProof", "AsymptoticProof", "OpenPatchMeasureProof",
    "ConvexHullProof", "ComplexityReductionProof", "CounterexampleProof", "ExactDataReplayProof",
    "TerminationMeasureProof", "ExactFiniteComputationProof", "FiniteSemanticProof", "SemanticDerivationProof", "MaxEntSemanticClosureProof", "GeometricSeriesProof", "ExactApplicationProof", "LeanKernelProof"
}

MAXENT_SEMANTIC_PROOF_METHOD = "MaxEntSemanticClosureProof"
MAXENT_CANONICAL_SPECIFICATION_FIELDS = {
    "assumptions",
    "conclusion",
    "definitions",
    "domains",
    "english_statement_sha256",
    "expected_proof_methods",
    "formal_statement_sha256",
    "foundation_dependencies",
    "group",
    "kind",
    "nonclaims",
    "portuguese_statement_sha256",
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

_ACTIVE_PROOFS: set[str] = set()


def RejectFloatingPoint(value: Any) -> None:
    if isinstance(value, float):
        raise ValueError("Floating-point values are forbidden in proof records")
    if isinstance(value, dict):
        for key, child in value.items():
            if not isinstance(key, str):
                raise ValueError("Proof-record object keys must be strings")
            RejectFloatingPoint(child)
    if isinstance(value, list):
        for child in value:
            RejectFloatingPoint(child)


def RequireFields(value: dict[str, Any], required: set[str], optional: set[str] = set()) -> None:
    if set(value) - required - optional or not required.issubset(value):
        raise ValueError("Proof-record payload fields do not match the declared grammar")


def CheckProof(proof: dict[str, Any], specification: dict[str, Any], root: Path) -> dict[str, Any]:
    RejectFloatingPoint(proof)
    required = {"schema_version", "proof_id", "proof_method", "result_id", "proof_goal_id", "formal_statement_sha256", "claim", "claim_sha256", "assumptions_used", "foundation_dependencies", "result_dependencies", "payload"}
    if set(proof) != required:
        raise ValueError("Proof-record fields do not match the declared grammar")
    if proof["schema_version"] != "1.1.0" or proof["proof_method"] not in ALLOWED_PROOF_METHODS:
        raise ValueError("Unknown proof-record schema or proof rule")
    if proof["result_id"] != specification["result_id"]:
        raise ValueError("Proof-record result identifier mismatch")
    expected_hash = FormalStatementHash(specification)
    if proof["formal_statement_sha256"] != expected_hash or specification["formal_statement_sha256"] != expected_hash:
        raise ValueError("Canonical result hash mismatch")
    expected_claim = ExpectedClaim(specification, proof["proof_goal_id"])
    if proof["claim"] != expected_claim or proof["claim_sha256"] != CanonicalHash(expected_claim):
        raise ValueError("Proof record proves a different proof-goal claim")
    proof_goal_rows = [
        proof_goal
        for proof_goal in specification["proof_goals"]
        if proof_goal.get("proof_goal_id") == proof["proof_goal_id"]
    ]
    if (
        len(proof_goal_rows) != 1
        or proof["proof_method"] not in proof_goal_rows[0]["proof_methods"]
        or proof["proof_method"] not in specification["expected_proof_methods"]
    ):
        raise ValueError("Proof method is not declared for this registered proof goal")
    assumption_ids = {value["id"] for value in specification["assumptions"]}
    used = proof["assumptions_used"]
    if len(used) != len(set(used)) or not set(used).issubset(assumption_ids):
        raise ValueError("Proof record uses undeclared or duplicate assumptions")
    if sorted(proof["foundation_dependencies"]) != sorted(set(proof["foundation_dependencies"])):
        raise ValueError("Duplicate foundation dependency")
    if not set(proof["foundation_dependencies"]).issubset(set(specification["foundation_dependencies"])):
        raise ValueError("Proof record silently adds a foundation dependency")
    if not set(proof["result_dependencies"]).issubset(set(specification["result_dependencies"])):
        raise ValueError("Proof record silently adds a result dependency")
    if proof["proof_method"] in {
        "FiniteSemanticProof",
        "SemanticDerivationProof",
        MAXENT_SEMANTIC_PROOF_METHOD,
        "LeanKernelProof",
    }:
        if used != [value["id"] for value in specification["assumptions"]]:
            raise ValueError("Semantic proof record omits, duplicates, reorders, or adds assumptions")
        if proof["foundation_dependencies"] != specification["foundation_dependencies"]:
            raise ValueError("Semantic proof-record foundation dependency set mismatch")
        if proof["result_dependencies"] != specification["result_dependencies"]:
            raise ValueError("Semantic proof-record result dependency set mismatch")
    proof_id = proof["proof_id"]
    if proof_id in _ACTIVE_PROOFS:
        raise ValueError("Circular proof-record dependency")
    checker = ProofCheckers().get(proof["proof_method"])
    if checker is None:
        raise ValueError("Unknown proof rule")
    _ACTIVE_PROOFS.add(proof_id)
    try:
        detail = checker(proof["payload"], specification, root, expected_claim)
    finally:
        _ACTIVE_PROOFS.remove(proof_id)
    return {"proof_id": proof_id, "result_id": proof["result_id"], "proof_goal_id": proof["proof_goal_id"], "proof_method": proof["proof_method"], "status": "PASS", "formal_statement_sha256": expected_hash, "assumptions_used": used, "detail": detail}


def CheckStatementCheck(
    check: dict[str, Any], specification: dict[str, Any], root: Path
) -> dict[str, Any]:
    RejectFloatingPoint(check)
    required = {
        "schema_version",
        "check_id",
        "check_type",
        "result_id",
        "formal_statement_sha256",
        "payload",
    }
    if set(check) != required:
        raise ValueError("Statement-check fields do not match the declared grammar")
    result_id = specification["result_id"]
    expected_hash = FormalStatementHash(specification)
    if (
        check["schema_version"] != "1.0.0"
        or check["check_id"] != f"{result_id}.STATEMENT-CORRESPONDENCE.CHECK"
        or check["check_type"] != "StatementCorrespondenceCheck"
        or check["result_id"] != result_id
        or check["formal_statement_sha256"] != expected_hash
        or specification["formal_statement_sha256"] != expected_hash
    ):
        raise ValueError("Statement-check identity or formal-statement hash mismatch")
    detail = CheckStatementCorrespondencePayload(
        check["payload"], specification, root
    )
    return {
        "check_id": check["check_id"],
        "check_type": check["check_type"],
        "result_id": result_id,
        "status": "PASS",
        "formal_statement_sha256": expected_hash,
        "detail": detail,
    }


def FormalStatementHash(specification: dict[str, Any]) -> str:
    fields = ["schema_version", "result_id", "kind", "group", "variables", "sorts", "domains", "definitions", "assumptions", "conclusion", "quantifier_prefix", "registered_query_type", "scope", "nonclaims", "foundation_dependencies", "result_dependencies", "source_transcription_dependencies", "expected_proof_methods", "withdrawal_condition"]
    return CanonicalHash({field: specification[field] for field in fields})


def ValidateMaxEntCanonicalSpecification(
    specification: dict[str, Any], root: Path
) -> list[str]:
    failures: list[str] = []
    if set(specification) != MAXENT_CANONICAL_SPECIFICATION_FIELDS:
        failures.append("MAX canonical specification fields differ from the declared grammar")
        return failures
    result_id = specification.get("result_id")
    if (
        not isinstance(result_id, str)
        or not result_id.startswith("MAX-G")
        or specification.get("schema_version") != "1.0.0"
        or specification.get("group") != "MAX"
        or specification.get("kind") != "theorem"
    ):
        failures.append("MAX canonical specification identity or schema is invalid")
        return failures
    companion_relative = (
        f"formal/proofs/maxent/semantic/specs/{result_id}.json"
    )
    companion_path = root / companion_relative
    if not companion_path.is_file():
        failures.append("MAX semantic companion specification is absent")
        return failures
    companion = LoadJson(companion_path)
    companion_hash = CanonicalHash(
        {
            key: value
            for key, value in companion.items()
            if key
            not in {
                "title_en",
                "title_pt_BR",
                "formal_statement_sha256",
            }
        }
    )
    if (
        companion.get("schema_version") != "2.0.0"
        or companion.get("result_id") != result_id
        or companion.get("group") != "MAX"
        or companion.get("kind") != "theorem"
        or companion.get("formal_statement_sha256") != companion_hash
    ):
        failures.append("MAX semantic companion identity or formal hash is stale")
    if "proof_goals" not in companion:
        failures.append("MAX semantic companion lacks registered proof goals")
        return failures
    expected_link = {
        "id": f"{result_id}.STATEMENT",
        "node": "statement_correspondence",
        "english_statement_sha256": specification["english_statement_sha256"],
        "portuguese_statement_sha256": specification[
            "portuguese_statement_sha256"
        ],
        "semantic_definition_dependencies": companion.get(
            "definition_dependencies"
        ),
        "semantic_definitions": companion.get("definitions"),
        "semantic_scope": companion.get("scope"),
        "semantic_nonclaims": companion.get("nonclaims"),
        "semantic_withdrawal_condition": companion.get("withdrawal_condition"),
        "semantic_specification_path": companion_relative,
        "semantic_specification_sha256": FileHash(companion_path),
        "semantic_formal_statement_sha256": companion.get(
            "formal_statement_sha256"
        ),
    }
    if specification["definitions"] != [expected_link]:
        failures.append("MAX canonical bilingual link or semantic definition bridge changed")
    copied_fields = [
        "variables",
        "sorts",
        "domains",
        "assumptions",
        "conclusion",
        "quantifier_prefix",
        "registered_query_type",
        "foundation_dependencies",
        "result_dependencies",
        "source_transcription_dependencies",
    ]
    for field in copied_fields:
        if specification[field] != companion.get(field):
            failures.append(f"MAX canonical field differs from semantic companion: {field}")
    registry_path = root / "registry" / "result_registry.tsv"
    dependency_path = root / "registry" / "result_dependency_edges.tsv"
    proof_goal_path = root / "registry" / "proof_goal_registry.tsv"
    try:
        with registry_path.open(encoding="utf-8", newline="") as handle:
            rows = [
                row
                for row in csv.DictReader(handle, delimiter="\t")
                if row["result_id"] == result_id
            ]
        if len(rows) != 1:
            failures.append("MAX result is absent or duplicated in the canonical registry")
        else:
            registry = rows[0]
            for field in [
                "title_en",
                "title_pt_BR",
                "scope",
                "nonclaims",
                "withdrawal_condition",
            ]:
                if specification[field] != registry[field]:
                    failures.append(
                        f"MAX canonical field differs from result registry: {field}"
                    )
            if specification["english_statement_sha256"] != CanonicalHash(
                {"locale": "en", "statement": registry["statement_en"]}
            ):
                failures.append("MAX English statement hash differs from result registry")
            if specification["portuguese_statement_sha256"] != CanonicalHash(
                {"locale": "pt_BR", "statement": registry["statement_pt_BR"]}
            ):
                failures.append("MAX Portuguese statement hash differs from result registry")
        with dependency_path.open(encoding="utf-8", newline="") as handle:
            registry_dependencies = sorted(
                row["source_result_id"]
                for row in csv.DictReader(handle, delimiter="\t")
                if row["target_result_id"] == result_id
            )
        if specification["result_dependencies"] != registry_dependencies:
            failures.append("MAX result dependencies differ from dependency registry")
        with proof_goal_path.open(encoding="utf-8", newline="") as handle:
            maxent_proof_goal_rows = [
                row
                for row in csv.DictReader(handle, delimiter="\t")
                if row["result_id"].startswith("MAX-G")
            ]
        maxent_proof_goal_ids = [
            row["proof_goal_id"] for row in maxent_proof_goal_rows
        ]
        if len(maxent_proof_goal_ids) != 30 or len(set(maxent_proof_goal_ids)) != 30:
            failures.append(
                "MAX proof-goal registry does not contain exactly 30 unique proof goals"
            )
        registry_proof_goal_ids = [
            row["proof_goal_id"]
            for row in maxent_proof_goal_rows
            if row["result_id"] == result_id
        ]
        canonical_proof_goal_ids = [
            row["proof_goal_id"] for row in specification["proof_goals"]
        ]
        if canonical_proof_goal_ids != registry_proof_goal_ids:
            failures.append(
                "MAX canonical proof-goal identifiers or order differ from the proof-goal registry"
            )
    except (KeyError, OSError) as error:
        failures.append(f"MAX canonical registry cannot be audited: {error}")
    registered_method_by_proof_goal = {
        row["proof_goal_id"]: (
            "LeanKernelProof"
            if row.get("proof_goal_type") == "LeanKernelProof"
            or row.get("machine_status") == "LeanKernelProofPass"
            else MAXENT_SEMANTIC_PROOF_METHOD
        )
        for row in maxent_proof_goal_rows
    }
    expected_proof_goals = [
        {
            "proof_goal_id": row["proof_goal_id"],
            "mandatory": True,
            "claim": row["claim"],
            "proof_methods": [
                registered_method_by_proof_goal[row["proof_goal_id"]]
            ],
        }
        for row in companion["proof_goals"]
    ]
    if specification["proof_goals"] != expected_proof_goals:
        failures.append("MAX canonical proof-goal claims or proof method changed")
    if specification["expected_proof_methods"] != sorted(
        {
            registered_method_by_proof_goal[row["proof_goal_id"]]
            for row in maxent_proof_goal_rows
            if row["result_id"] == result_id
        }
    ):
        failures.append("MAX canonical expected proof methods changed")
    if specification["formal_statement_sha256"] != FormalStatementHash(
        specification
    ):
        failures.append("MAX canonical formal statement hash is stale")
    try:
        RejectFloatingPoint(specification)
    except ValueError as error:
        failures.append(str(error))
    return sorted(set(failures))


def ExpectedClaim(specification: dict[str, Any], proof_goal_id: str) -> Any:
    if "proof_goals" not in specification:
        raise ValueError("Result specification lacks registered proof goals")
    proof_goals = specification["proof_goals"]
    if not isinstance(proof_goals, list):
        raise ValueError("Result specification proof goals must be a list")
    matches = [value for value in proof_goals if value.get("proof_goal_id") == proof_goal_id]
    if len(matches) != 1:
        raise ValueError("Proof goal is absent or duplicated in the result specification")
    if "claim" not in matches[0]:
        raise ValueError("Proof goal lacks its registered claim")
    return matches[0]["claim"]


def CheckMaxEntCanonicalPayload(
    payload: dict[str, Any],
    specification: dict[str, Any],
    root: Path,
    claim: Any,
) -> dict[str, Any]:
    findings = ValidateMaxEntCanonicalSpecification(specification, root)
    if findings:
        raise ValueError(
            "MAX canonical semantic bridge is invalid: " + "; ".join(findings)
        )
    companion = LoadJson(
        root
        / "formal"
        / "proofs"
        / "maxent"
        / "semantic"
        / "specs"
        / f"{specification['result_id']}.json"
    )
    detail = CheckMaxEntSemanticPayload(payload, companion, root, claim)
    return {
        "status": "PASS",
        "closure_status": detail["closure_status"],
        "proof_goal_id": detail["proof_goal_id"],
        "claim_sha256": detail["claim_sha256"],
        "canonical_formal_statement_sha256": specification[
            "formal_statement_sha256"
        ],
        "semantic_formal_statement_sha256": companion[
            "formal_statement_sha256"
        ],
        "detail": detail,
    }


def RequirePolynomialVariables(variables: list[str], polynomials: list[dict[tuple[int, ...], Fraction]]) -> None:
    if len(variables) != len(set(variables)):
        raise ValueError("Duplicate polynomial variable")
    used = {variables[index] for polynomial in polynomials for monomial in polynomial for index, power in enumerate(monomial) if power > 0}
    if used != set(variables):
        raise ValueError("Polynomial variables are undeclared or unused")


def CheckProofFile(proof_path: Path, specification_path: Path, root: Path) -> dict[str, Any]:
    return CheckProof(LoadJson(proof_path), LoadJson(specification_path), root)


def ResultDependencyClosure(
    dependencies: dict[str, list[str]], own_result_complete: set[str]
) -> dict[str, Any]:
    result_ids = set(dependencies)
    unknown = {
        result_id: sorted(set(required) - result_ids)
        for result_id, required in dependencies.items()
        if set(required) - result_ids
    }

    colour: dict[str, int] = {result_id: 0 for result_id in result_ids}
    stack: list[str] = []
    cycles: set[tuple[str, ...]] = set()

    def canonical_cycle(values: list[str]) -> tuple[str, ...]:
        body = values[:-1]
        rotations = [tuple(body[index:] + body[:index]) for index in range(len(body))]
        return min(rotations)

    def visit(result_id: str) -> None:
        colour[result_id] = 1
        stack.append(result_id)
        for dependency in dependencies[result_id]:
            if dependency not in result_ids:
                continue
            if colour[dependency] == 0:
                visit(dependency)
            elif colour[dependency] == 1:
                start = stack.index(dependency)
                cycles.add(canonical_cycle(stack[start:] + [dependency]))
        stack.pop()
        colour[result_id] = 2

    for result_id in sorted(result_ids):
        if colour[result_id] == 0:
            visit(result_id)

    closed: set[str] = set()
    changed = True
    while changed:
        changed = False
        for result_id in sorted(own_result_complete - closed):
            required = set(dependencies[result_id])
            if required.issubset(closed):
                closed.add(result_id)
                changed = True

    rows = []
    for result_id in sorted(result_ids):
        required = sorted(set(dependencies[result_id]))
        rows.append(
            {
                "result_id": result_id,
                "own_result_complete": result_id in own_result_complete,
                "dependencies": required,
                "closed_dependencies": [value for value in required if value in closed],
                "blocked_dependencies": [value for value in required if value not in closed],
                "dependency_closed": result_id in closed,
            }
        )
    return {
        "closed_result_ids": sorted(closed),
        "unknown_dependencies": unknown,
        "cycles": [list(value) for value in sorted(cycles)],
        "rows": rows,
    }


def CheckDirectory(root: Path, strict: bool = True) -> dict[str, Any]:
    foundation_registry = LoadJson(root / "formal" / "foundation" / "trusted_foundation.json")
    foundation_proofs = {
        path.stem: LoadJson(path)
        for path in (root / "formal" / "proofs" / "foundation").glob("*.json")
    }
    foundation_report = CheckFoundationRegistry(foundation_registry, foundation_proofs)
    foundation_ids = {value["foundation_id"] for value in foundation_registry["items"]}
    specifications = {path.stem: path for path in (root / "formal" / "specs").glob("*.json")}
    specification_values = {result_id: LoadJson(path) for result_id, path in specifications.items()}
    proofs: list[dict[str, Any]] = []
    statement_checks: list[dict[str, Any]] = []
    failures: list[dict[str, str]] = []
    specification_failures: dict[str, list[str]] = {}
    if strict and foundation_report["status"] != "PASS":
        failures.append({"proof": "trusted_foundation", "error": "Trusted foundation replay failed"})
    for result_id, specification in specification_values.items():
        if specification.get("group") == "MAX":
            findings = ValidateMaxEntCanonicalSpecification(specification, root)
        else:
            findings = ValidateSpecification(specification)
        unknown_foundations = sorted(set(specification.get("foundation_dependencies", [])) - foundation_ids)
        if unknown_foundations:
            findings.append("unknown foundation dependencies: " + ", ".join(unknown_foundations))
        if findings:
            specification_failures[result_id] = findings
            if strict:
                failures.append({"proof": result_id, "error": "Canonical formal statement is nonsemantic: " + "; ".join(findings)})
    for path in sorted((root / "formal" / "proofs").glob("*.json")):
        try:
            proof = LoadJson(path)
            result_id = proof.get("result_id", "")
            if result_id not in specifications:
                raise ValueError("Proof record has no canonical result specification")
            proofs.append(CheckProof(proof, specification_values[result_id], root))
        except Exception as error:
            failures.append({"proof": path.name, "error": f"{type(error).__name__}: {error}"})
    for path in sorted((root / "formal" / "statement_checks").glob("*.json")):
        try:
            check = LoadJson(path)
            result_id = check.get("result_id", "")
            if result_id not in specifications:
                raise ValueError("Statement check has no canonical result specification")
            statement_checks.append(
                CheckStatementCheck(check, specification_values[result_id], root)
            )
        except Exception as error:
            failures.append(
                {
                    "statement_check": path.name,
                    "error": f"{type(error).__name__}: {error}",
                }
            )
    result_counts = Counter(proof["result_id"] for proof in proofs)
    proof_id_counts = Counter(proof["proof_id"] for proof in proofs)
    proof_goal_counts = Counter(
        (proof["result_id"], proof["proof_goal_id"]) for proof in proofs
    )
    accepted_proof_goals = {
        (proof["result_id"], proof["proof_goal_id"]) for proof in proofs
    }
    missing = sorted(set(specifications) - set(result_counts))
    missing_proof_goals = []
    for result_id, specification in specification_values.items():
        proof_goals = specification["proof_goals"]
        required_proof_goals = [argument["proof_goal_id"] for argument in proof_goals if argument["mandatory"]]
        for proof_goal_id in required_proof_goals:
            if (result_id, proof_goal_id) not in accepted_proof_goals:
                missing_proof_goals.append(proof_goal_id)
    if strict and missing:
        failures.extend({"proof": result_id, "error": "No accepted proof"} for result_id in missing)
    if strict and missing_proof_goals:
        failures.extend({"proof": proof_goal_id, "error": "No accepted proof for registered proof goal"} for proof_goal_id in missing_proof_goals)
    if strict:
        failures.extend(
            {
                "proof": proof_id,
                "error": f"Proof identifier occurs {count} times",
            }
            for proof_id, count in sorted(proof_id_counts.items())
            if count != 1
        )
        failures.extend(
            {
                "proof": proof_goal_id,
                "error": f"Registered proof goal has {count} accepted proofs; exactly one is required",
            }
            for (_, proof_goal_id), count in sorted(proof_goal_counts.items())
            if count != 1
        )
    own_proof_complete: set[str] = set()
    for result_id, specification in specification_values.items():
        proof_goals = specification["proof_goals"]
        required = {
            argument["proof_goal_id"]
            for argument in proof_goals
            if argument["mandatory"]
        }
        if result_id not in specification_failures and all(
            proof_goal_counts[(result_id, proof_goal_id)] == 1
            for proof_goal_id in required
        ):
            own_proof_complete.add(result_id)

    statement_check_id_counts = Counter(
        check["check_id"] for check in statement_checks
    )
    statement_check_result_counts = Counter(
        check["result_id"] for check in statement_checks
    )
    accepted_statement_check_results = {
        result_id
        for result_id, count in statement_check_result_counts.items()
        if count == 1
    }
    missing_statement_check_ids = sorted(
        f"{result_id}.STATEMENT-CORRESPONDENCE.CHECK"
        for result_id in set(specifications) - accepted_statement_check_results
    )
    if strict and missing_statement_check_ids:
        failures.extend(
            {
                "statement_check": check_id,
                "error": "No accepted bilingual statement check",
            }
            for check_id in missing_statement_check_ids
        )
    if strict:
        failures.extend(
            {
                "statement_check": check_id,
                "error": f"Statement-check identifier occurs {count} times",
            }
            for check_id, count in sorted(statement_check_id_counts.items())
            if count != 1
        )
        failures.extend(
            {
                "statement_check": f"{result_id}.STATEMENT-CORRESPONDENCE.CHECK",
                "error": f"Result has {count} accepted statement checks; exactly one is required",
            }
            for result_id, count in sorted(statement_check_result_counts.items())
            if count != 1
        )
    own_result_complete = own_proof_complete & accepted_statement_check_results

    dependency_report = ResultDependencyClosure(
        {
            result_id: specification["result_dependencies"]
            for result_id, specification in specification_values.items()
        },
        own_result_complete,
    )
    closed_results = dependency_report["closed_result_ids"]
    mandatory_proof_goals = {
        (result_id, argument["proof_goal_id"])
        for result_id, specification in specification_values.items()
        for argument in specification["proof_goals"]
        if argument["mandatory"]
    }
    accepted_mandatory_proof_goals = mandatory_proof_goals & accepted_proof_goals
    proof_goal_results = [
        proof
        for proof in proofs
        if (proof["result_id"], proof["proof_goal_id"])
        in mandatory_proof_goals
    ]
    if strict:
        failures.extend(
            {
                "proof": result_id,
                "error": "Unknown result dependencies: " + ", ".join(values),
            }
            for result_id, values in dependency_report["unknown_dependencies"].items()
        )
        failures.extend(
            {
                "proof": " -> ".join(cycle + [cycle[0]]),
                "error": "Circular result dependency",
            }
            for cycle in dependency_report["cycles"]
        )
        for row in dependency_report["rows"]:
            if row["own_result_complete"] and not row["dependency_closed"]:
                failures.append(
                    {
                        "proof": row["result_id"],
                        "error": "Local proof and statement check pass but result dependencies remain open: "
                        + ", ".join(row["blocked_dependencies"]),
                    }
                )
    result_records = [
        {
            **row,
            "status": "PASS" if row["dependency_closed"] else "FAIL",
        }
        for row in dependency_report["rows"]
    ]
    return {
        "status": "PASS" if not failures else "FAIL",
        "foundation_replay": foundation_report,
        "specification_count": len(specifications),
        "semantic_specification_count": len(specifications) - len(specification_failures),
        "semantic_specification_failures": specification_failures,
        "proof_count": len(proofs),
        "proof_goal_count": len(mandatory_proof_goals),
        "accepted_mandatory_proof_goal_count": len(accepted_mandatory_proof_goals),
        "statement_check_count": len(statement_checks),
        "accepted_statement_check_count": sum(
            check["status"] == "PASS" for check in statement_checks
        ),
        "result_count_with_proof": len(result_counts),
        "own_proof_complete_result_count": len(own_proof_complete),
        "own_proof_complete_result_ids": sorted(own_proof_complete),
        "own_result_complete_count": len(own_result_complete),
        "own_result_complete_ids": sorted(own_result_complete),
        "machine_closed_result_count": len(closed_results),
        "machine_closed_result_ids": closed_results,
        "result_dependency_closure": dependency_report,
        "missing_result_ids": missing,
        "missing_proof_goal_ids": sorted(missing_proof_goals),
        "missing_statement_check_ids": missing_statement_check_ids,
        "proofs": proofs,
        "proof_goal_results": proof_goal_results,
        "statement_checks": statement_checks,
        "result_records": result_records,
        "failures": failures,
    }


def ProofCheckers() -> dict[str, Callable[[dict[str, Any], dict[str, Any], Path, Any], Any]]:
    return {
        "BooleanTautologyProof": CheckBooleanTautology,
        "FiniteEnumerationProof": CheckFiniteEnumeration,
        "PolynomialIdentityProof": CheckPolynomialIdentity,
        "LaurentClearingProof": CheckPolynomialIdentity,
        "IdealMembershipProof": CheckIdealMembership,
        "SumOfSquaresProof": CheckSumOfSquares,
        "SemialgebraicUnsatProof": CheckSemialgebraicUnsat,
        "ExactLinearAlgebraProof": CheckLinearAlgebra,
        "CounterexampleProof": CheckCounterexample,
        "ExactDataReplayProof": CheckDataReplay,
        "ExactFiniteComputationProof": CheckFiniteComputation,
        "FiniteSemanticProof": CheckFiniteSemanticPayload,
        "SemanticDerivationProof": CheckSemanticPayload,
        MAXENT_SEMANTIC_PROOF_METHOD: CheckMaxEntCanonicalPayload,
        "GeometricSeriesProof": CheckGeometricSeries,
        "ExactApplicationProof": CheckApplication,
        "LeanKernelProof": CheckLeanKernelProof,
        "TerminationMeasureProof": CheckTermination,
        "RewriteChainProof": CheckRewriteChain,
        "FirstOrderProof": CheckFirstOrderProof,
        "InductionProof": CheckInduction,
        "ConvexityProof": CheckFoundationInstantiation,
        "KKTGlobalOptimalityProof": CheckFoundationInstantiation,
        "LimitProof": CheckFoundationInstantiation,
        "AsymptoticProof": CheckFoundationInstantiation,
        "OpenPatchMeasureProof": CheckFoundationInstantiation,
        "ConvexHullProof": CheckFoundationInstantiation,
        "ComplexityReductionProof": CheckFoundationInstantiation,
    }


def CheckFiniteComputation(payload: dict[str, Any], specification: dict[str, Any], root: Path, claim: Any) -> dict[str, Any]:
    RequireFields(payload, {"expression", "expected"})
    if claim != {"node": "equal", "left": payload["expression"], "right": payload["expected"]}:
        raise ValueError("Finite computation proof does not match its claim")
    observed = EvaluateFiniteModel(payload["expression"])
    expected = EvaluateFiniteModel(payload["expected"])
    if observed != expected:
        raise ValueError("Exact finite computation result mismatch")
    return {"expression_sha256": CanonicalHash(payload["expression"]), "result_sha256": CanonicalHash(payload["expected"])}


def CheckApplication(payload: dict[str, Any], specification: dict[str, Any], root: Path, claim: Any) -> dict[str, Any]:
    RequireFields(payload, {"source", "algorithm", "inputs", "expected"})
    source = payload["source"]
    RequireFields(source, {"path", "sha256", "transcription_id"})
    path = (root / source["path"]).resolve()
    if root.resolve() not in path.parents or not path.is_file() or path.suffix != ".json" or FileHash(path) != source["sha256"]:
        raise ValueError("Application source transcription path or hash mismatch")
    transcription = LoadJson(path)
    if transcription.get("transcription_id") != source["transcription_id"]:
        raise ValueError("Application source transcription identifier mismatch")
    observed, detail = ReplayApplication(payload["algorithm"], payload["inputs"], transcription)
    if observed != payload["expected"]:
        raise ValueError("Exact application replay result mismatch")
    expected_claim = {"node": "exact_application_result", "source": source, "algorithm": payload["algorithm"], "inputs": payload["inputs"], "expected": payload["expected"]}
    if claim != expected_claim:
        raise ValueError("Application proof does not match its claim")
    return {"algorithm": payload["algorithm"], "source_transcription_sha256": source["sha256"], "result_sha256": CanonicalHash(observed), "derivation": detail}


def CheckGeometricSeries(payload: dict[str, Any], specification: dict[str, Any], root: Path, claim: Any) -> dict[str, Any]:
    RequireFields(payload, {"variable", "range_assumption", "state_count", "coefficients", "base_left", "base_right", "step_left", "step_right", "total_mass", "infinity_mass"})
    variable = payload["variable"]
    if variable != "p" or payload["state_count"] != 2 or payload["total_mass"] != "1" or payload["infinity_mass"] != "0":
        raise ValueError("Geometric stopped-law proof has the wrong typed endpoints")
    expected_assumption = {"node": "and", "arguments": [{"node": "greater", "left": {"node": "variable", "name": variable}, "right": {"node": "rational", "value": "0"}}, {"node": "less", "left": {"node": "variable", "name": variable}, "right": {"node": "rational", "value": "1"}}]}
    declared_assumptions = [{key: value for key, value in assumption.items() if key != "id"} for assumption in specification["assumptions"]]
    if payload["range_assumption"] != expected_assumption or expected_assumption not in declared_assumptions or "FOUND-LIMIT-001" not in specification["foundation_dependencies"]:
        raise ValueError("Geometric stopped-law range assumption mismatch")
    expected_coefficients = [{"node": "multiply", "arguments": [{"node": "subtract", "left": {"node": "rational", "value": "1"}, "right": {"node": "variable", "name": variable}}, {"node": "power", "base": {"node": "variable", "name": variable}, "exponent": {"node": "natural", "value": index}}]} for index in range(4)]
    if payload["coefficients"] != expected_coefficients:
        raise ValueError("Geometric stopped-law coefficient formula mismatch")
    base_left = ParsePolynomial(payload["base_left"], ["p"])
    base_right = ParsePolynomial(payload["base_right"], ["p"])
    step_left = ParsePolynomial(payload["step_left"], ["p", "y"])
    step_right = ParsePolynomial(payload["step_right"], ["p", "y"])
    if base_left != base_right or step_left != step_right:
        raise ValueError("Geometric stopped-law induction identity fails")
    expected_claim = {"node": "geometric_stopped_law", "variable": variable, "range_assumption": expected_assumption, "state_count": 2, "coefficients": expected_coefficients, "total_mass": {"node": "rational", "value": "1"}, "infinity_mass": {"node": "rational", "value": "0"}}
    if claim != expected_claim:
        raise ValueError("Geometric stopped-law proof proves a different claim")
    return {"state_count": 2, "coefficient_count": 4, "induction_base_terms": len(base_left), "induction_step_terms": len(step_left), "limit_foundation": "FOUND-LIMIT-001"}


def CheckBooleanTautology(payload: dict[str, Any], specification: dict[str, Any], root: Path, claim: Any) -> dict[str, Any]:
    RequireFields(payload, {"variables", "formula", "domain_cardinality"})
    variables = payload["variables"]
    if len(variables) != len(set(variables)):
        raise ValueError("Duplicate tautology variable")
    if FreeVariables(payload["formula"]) != set(variables):
        raise ValueError("Tautology variables are undeclared or unused")
    if claim != payload["formula"]:
        raise ValueError("Boolean proof formula does not match its claim")
    rows = []
    for mask in range(1 << len(variables)):
        environment = {name: bool(mask & (1 << index)) for index, name in enumerate(variables)}
        if not RequireBoolean(EvaluateExpression(payload["formula"], environment)):
            raise ValueError("Boolean formula is not a tautology")
        rows.append(environment)
    if payload["domain_cardinality"] != len(rows):
        raise ValueError("Boolean enumeration cardinality mismatch")
    return {"enumerated": len(rows)}


def CheckFiniteEnumeration(payload: dict[str, Any], specification: dict[str, Any], root: Path, claim: Any) -> dict[str, Any]:
    RequireFields(payload, {"variable", "domain", "domain_cardinality", "predicate", "expected_results"})
    domain = payload["domain"]
    if len(domain) != payload["domain_cardinality"] or len({json.dumps(value, sort_keys=True, separators=(",", ":")) for value in domain}) != len(domain):
        raise ValueError("Finite enumeration domain is incomplete or duplicated")
    if FreeVariables(payload["predicate"]) != {payload["variable"]}:
        raise ValueError("Finite enumeration variable is undeclared or unused")
    observed = [EvaluateExpression(payload["predicate"], {payload["variable"]: value}) for value in domain]
    if observed != payload["expected_results"]:
        raise ValueError("Finite enumeration result mismatch")
    expected_claim = {"node": "finite_enumeration_result", "variable": payload["variable"], "domain": domain, "predicate": payload["predicate"], "results": observed}
    if claim != expected_claim:
        raise ValueError("Finite enumeration proof does not match its claim")
    return {"enumerated": len(domain), "results_sha256": CanonicalHash(observed)}


def CheckPolynomialIdentity(payload: dict[str, Any], specification: dict[str, Any], root: Path, claim: Any) -> dict[str, Any]:
    RequireFields(payload, {"variables", "left", "right"})
    variables = payload["variables"]
    left = ParsePolynomial(payload["left"], variables)
    right = ParsePolynomial(payload["right"], variables)
    RequirePolynomialVariables(variables, [left, right])
    if left != right:
        raise ValueError("False polynomial identity")
    if claim != {"node": "polynomial_identity", "variables": variables, "left": payload["left"], "right": payload["right"]}:
        raise ValueError("Polynomial proof does not match its claim")
    return {"variables": len(variables), "terms": len(left)}


def CheckIdealMembership(payload: dict[str, Any], specification: dict[str, Any], root: Path, claim: Any) -> dict[str, Any]:
    RequireFields(payload, {"variables", "generators", "multipliers", "target"})
    variables = payload["variables"]
    generators = [ParsePolynomial(value, variables) for value in payload["generators"]]
    multipliers = [ParsePolynomial(value, variables) for value in payload["multipliers"]]
    target = ParsePolynomial(payload["target"], variables)
    RequirePolynomialVariables(variables, generators + multipliers + [target])
    if len(generators) != len(multipliers):
        raise ValueError("Ideal-membership proof length mismatch")
    combined = {}
    for generator, multiplier in zip(generators, multipliers, strict=True):
        combined = Add(combined, Multiply(generator, multiplier))
    if combined != target:
        raise ValueError("Invalid ideal membership identity")
    if claim != {"node": "ideal_membership", "variables": variables, "generators": payload["generators"], "target": payload["target"]}:
        raise ValueError("Ideal-membership proof does not match its claim")
    return {"generator_count": len(generators), "target_terms": len(target)}


def CheckSumOfSquares(payload: dict[str, Any], specification: dict[str, Any], root: Path, claim: Any) -> dict[str, Any]:
    RequireFields(payload, {"variables", "target", "squares", "weights"})
    variables = payload["variables"]
    target = ParsePolynomial(payload["target"], variables)
    squares = [ParsePolynomial(value, variables) for value in payload["squares"]]
    weights = [ParseRational(value) for value in payload["weights"]]
    RequirePolynomialVariables(variables, [target] + squares)
    if len(squares) != len(weights) or any(weight < 0 for weight in weights):
        raise ValueError("Invalid sum-of-squares weights")
    combined = {}
    for square, weight in zip(squares, weights, strict=True):
        scaled = {monomial: weight * coefficient for monomial, coefficient in Multiply(square, square).items()}
        combined = Add(combined, scaled)
    if combined != target:
        raise ValueError("Invalid sum-of-squares identity")
    if claim != {"node": "polynomial_nonnegative", "variables": variables, "polynomial": payload["target"]}:
        raise ValueError("Sum-of-squares proof does not match its claim")
    return {"square_count": len(squares)}


def CheckSemialgebraicUnsat(payload: dict[str, Any], specification: dict[str, Any], root: Path, claim: Any) -> dict[str, Any]:
    RequireFields(payload, {"variables", "equalities", "inequalities", "equality_multipliers", "preordering_terms"})
    variables = payload["variables"]
    equalities = [ParsePolynomial(value, variables) for value in payload["equalities"]]
    inequalities = [ParsePolynomial(value, variables) for value in payload["inequalities"]]
    multipliers = [ParsePolynomial(value, variables) for value in payload["equality_multipliers"]]
    if len(equalities) != len(multipliers):
        raise ValueError("Semialgebraic equality multiplier count mismatch")
    dimension = len(variables)
    left = {(0,) * dimension: Fraction(1)}
    proof_polynomials = equalities + inequalities + multipliers
    for term in payload["preordering_terms"]:
        matrix = ParseMatrix(term["gram_matrix"])
        if not PositiveSemidefinite(matrix):
            raise ValueError("Semialgebraic Gram matrix is not positive semidefinite")
        monomials = [tuple(value) for value in term["monomials"]]
        if len(matrix) != len(monomials) or any(len(row) != len(monomials) for row in matrix):
            raise ValueError("Semialgebraic Gram dimensions do not match monomial basis")
        if any(len(value) != dimension or any(not isinstance(power, int) or isinstance(power, bool) or power < 0 for power in value) for value in monomials):
            raise ValueError("Malformed semialgebraic monomial basis")
        sos = {}
        for row, left_monomial in enumerate(monomials):
            for column, right_monomial in enumerate(monomials):
                coefficient = matrix[row][column]
                monomial = tuple(a + b for a, b in zip(left_monomial, right_monomial, strict=True))
                sos[monomial] = sos.get(monomial, Fraction(0)) + coefficient
        factor = sos
        indices = term["inequality_indices"]
        if len(indices) != len(set(indices)) or any(not isinstance(index, int) or isinstance(index, bool) or index < 0 or index >= len(inequalities) for index in indices):
            raise ValueError("Invalid semialgebraic inequality index")
        for index in indices:
            factor = Multiply(factor, inequalities[index])
        left = Add(left, factor)
        proof_polynomials.append(sos)
    right = {}
    for equality, multiplier in zip(equalities, multipliers, strict=True):
        right = Add(right, Multiply(multiplier, equality))
    if left != right:
        raise ValueError("Invalid real Positivstellensatz identity")
    RequirePolynomialVariables(variables, proof_polynomials)
    expected_claim = {"node": "semialgebraic_unsatisfiable", "variables": variables, "equalities": payload["equalities"], "nonnegative_inequalities": payload["inequalities"]}
    if claim != expected_claim:
        raise ValueError("Semialgebraic proof does not match its claim")
    return {"equality_count": len(equalities), "inequality_count": len(inequalities), "preordering_term_count": len(payload["preordering_terms"])}


def CheckLinearAlgebra(payload: dict[str, Any], specification: dict[str, Any], root: Path, claim: Any) -> dict[str, Any]:
    RequireFields(payload, {"matrix", "rank"}, {"determinant", "right_matrix", "product"})
    if ("right_matrix" in payload) != ("product" in payload):
        raise ValueError("Linear-algebra product fields must occur together")
    matrix = ParseMatrix(payload["matrix"])
    observed_rank = Rank(matrix)
    if observed_rank != payload["rank"]:
        raise ValueError("Rank proof mismatch")
    if "determinant" in payload and RationalText(Determinant(matrix)) != payload["determinant"]:
        raise ValueError("Determinant proof mismatch")
    if "right_matrix" in payload:
        right = ParseMatrix(payload["right_matrix"])
        expected = ParseMatrix(payload["product"])
        if MatrixMultiply(matrix, right) != expected:
            raise ValueError("Exact matrix product mismatch")
    expected_claim = {"node": "exact_linear_algebra", "matrix": payload["matrix"], "rank": payload["rank"]}
    if "determinant" in payload:
        expected_claim["determinant"] = payload["determinant"]
    if "right_matrix" in payload:
        expected_claim["right_matrix"] = payload["right_matrix"]
        expected_claim["product"] = payload["product"]
    if claim != expected_claim:
        raise ValueError("Linear-algebra proof does not match its claim")
    return {"rank": observed_rank, "rows": len(matrix), "columns": len(matrix[0]) if matrix else 0}


def CheckCounterexample(payload: dict[str, Any], specification: dict[str, Any], root: Path, claim: Any) -> dict[str, Any]:
    RequireFields(payload, {"assignment", "assumptions", "conclusion"})
    environment = {name: ParseRational(value) if isinstance(value, (int, str)) and not isinstance(value, bool) else value for name, value in payload["assignment"].items()}
    assumptions = [RequireBoolean(EvaluateExpression(value, environment)) for value in payload["assumptions"]]
    if not assumptions or not all(assumptions):
        raise ValueError("Counterexample does not satisfy every assumption")
    if RequireBoolean(EvaluateExpression(payload["conclusion"], environment)):
        raise ValueError("Counterexample conclusion did not fail")
    if claim != {"node": "counterexample", "assumptions": payload["assumptions"], "conclusion": payload["conclusion"], "assignment": payload["assignment"]}:
        raise ValueError("Counterexample proof does not match its claim")
    return {"assumption_count": len(assumptions), "assignment_sha256": CanonicalHash(payload["assignment"])}


def CheckDataReplay(payload: dict[str, Any], specification: dict[str, Any], root: Path, claim: Any) -> dict[str, Any]:
    RequireFields(payload, {"sources", "algorithm", "expected"})
    tables: dict[str, list[dict[str, str]]] = {}
    normalized_sources = []
    for source in payload["sources"]:
        RequireFields(source, {"role", "path", "sha256", "row_count", "key_fields", "required_fields"})
        path = (root / source["path"]).resolve()
        if root.resolve() not in path.parents or not path.is_file() or path.suffix != ".tsv" or FileHash(path) != source["sha256"]:
            raise ValueError("Data-replay proof source path or hash mismatch")
        with path.open(encoding="utf-8", newline="") as handle:
            rows = list(csv.DictReader(handle, delimiter="\t"))
        if len(rows) != source["row_count"] or not rows or set(source["required_fields"]) - set(rows[0]):
            raise ValueError("Data-replay proof row count or schema mismatch")
        keys = [tuple(row[field] for field in source["key_fields"]) for row in rows]
        if len(keys) != len(set(keys)):
            raise ValueError("Data-replay proof natural keys are not unique")
        tables[source["role"]] = rows
        normalized_sources.append(source)
    observed = ReplayDataAlgorithm(payload["algorithm"], tables)
    if observed != payload["expected"]:
        raise ValueError("Data proof replay result mismatch")
    expected_claim = {"node": "exact_data_replay", "sources": normalized_sources, "algorithm": payload["algorithm"], "expected": payload["expected"]}
    if claim != expected_claim:
        raise ValueError("Data-replay proof does not match its claim")
    return {"algorithm": payload["algorithm"], "source_count": len(tables), "row_count": sum(len(value) for value in tables.values()), "result_sha256": CanonicalHash(observed)}


def ReplayDataAlgorithm(algorithm: str, tables: dict[str, list[dict[str, str]]]) -> Any:
    if algorithm == "portuguese_query_hierarchy_v1":
        rows = tables["portuguese_cells"]
        variants = ["full", "leave_flatness_out", "leave_high_low_out", "leave_zcr_out"]
        key = lambda row: (row["window_id"], row["band_lower_hz"])
        full = {key(row): row["development_gate_pass"] for row in rows if row["score_variant"] == "full"}
        weak = sum(ParseDecimalRational(row["median_delta"]) > 0 for row in rows)
        changed_union: set[tuple[str, str]] = set()
        changed_directions: Counter[tuple[str, str]] = Counter()
        summaries = []
        for variant in variants:
            selected = [row for row in rows if row["score_variant"] == variant]
            changed = {key(row) for row in selected if row["development_gate_pass"] != full[key(row)]}
            if variant != "full":
                changed_union.update(changed)
                changed_directions.update((full[key(row)], row["development_gate_pass"]) for row in selected if row["development_gate_pass"] != full[key(row)])
            summaries.append({"reader": variant, "weak_positive_cells": weak, "strong_pass_cells": sum(row["development_gate_pass"] == "YES" for row in selected), "strong_total_cells": len(selected), "changed_decisions_from_full": len(changed)})
        return {"reader_summaries": summaries, "total_changed_reduction_decisions": sum(changed_directions.values()), "changed_yes_to_no": changed_directions[("YES", "NO")], "changed_no_to_yes": changed_directions[("NO", "YES")], "unique_changed_cells": len(changed_union)}
    if algorithm == "english_pooled_order_v1":
        aggregate = tables["english_aggregate"]
        margins = tables["english_speaker_scenarios"]
        scenario_keys = {(row["tracker_id"], row["start_offset_ms"], row["end_offset_ms"]) for row in aggregate}
        splits = {row["speaker_split"] for row in aggregate}
        median_fields = [field for field in aggregate[0] if field.endswith("_median_hz")]
        positive = sum(ParseDecimalRational(row[field]) > 0 for row in aggregate for field in median_fields)
        anchors = [(row, field) for row in aggregate for field in row if field.endswith("_positive_speakers") and row[field] == "29" and int(row["paired_speaker_support"]) - int(row[field]) == 13]
        if not anchors or any(row["q_order_result"] != "DEFINED_ALL_14_POSITIVE" for row in aggregate):
            raise ValueError("English registered order or support anchor is absent")
        boundary = int(anchors[0][0]["paired_speaker_support"]) // 2
        return {"scenarios": len(scenario_keys), "splits": len(splits), "aggregate_rows": len(aggregate), "positive_median_cells": positive, "speaker_scenario_rows": len(margins), "illustrative_support": "29_vs_13", "raw_surplus": 16, "above_strict_majority": 29 - boundary}
    if algorithm == "mandarin_construction_scope_v1":
        rows = tables["mandarin_rows"]
        original = Counter(row["original_decision"] for row in rows)
        corrected = Counter(row["corrected_decision"] for row in rows)
        retyped = sum(row["construction_scope_class"].startswith("CLEAR_COMPLEX") and row["original_decision"] != "MATCH" and row["corrected_decision"] == "MATCH" for row in rows)
        return [{"stage": "coarse_substring", "matches": original["MATCH"], "counterexamples": original["COUNTEREXAMPLE"], "refusals": original["NO_CONCLUSION_SCOPE"], "clear_complex_final_retyped_as_match": 0}, {"stage": "construction_sensitive", "matches": corrected["MATCH"], "counterexamples": corrected["COUNTEREXAMPLE"], "refusals": corrected["NO_CONCLUSION_SCOPE"], "clear_complex_final_retyped_as_match": retyped}]
    raise ValueError("Unknown exact data replay algorithm")


def CheckTermination(payload: dict[str, Any], specification: dict[str, Any], root: Path, claim: Any) -> dict[str, Any]:
    RequireFields(payload, {"measure_values"})
    values = [ParseRational(value) for value in payload["measure_values"]]
    if not values or any(value < 0 for value in values) or any(later >= earlier for earlier, later in zip(values, values[1:])):
        raise ValueError("Termination measure is not strictly descending in the nonnegative order")
    if claim != {"node": "termination_measure", "measure_values": payload["measure_values"]}:
        raise ValueError("Termination proof does not match its claim")
    return {"steps": len(values) - 1, "terminal_measure": RationalText(values[-1])}


def CheckStatementCorrespondencePayload(
    payload: dict[str, Any], specification: dict[str, Any], root: Path
) -> dict[str, Any]:
    RequireFields(payload, {"en_statement_path", "en_statement_file_sha256", "en_statement_sha256", "en_statement_marker", "pt_BR_statement_path", "pt_BR_statement_file_sha256", "pt_BR_statement_sha256", "pt_BR_statement_marker"})
    for locale, field in [("en", "english_statement_sha256"), ("pt_BR", "portuguese_statement_sha256")]:
        path = root / payload[f"{locale}_statement_path"]
        if not path.is_file() or FileHash(path) != payload[f"{locale}_statement_file_sha256"]:
            raise ValueError("Written statement source hash mismatch")
        if payload[f"{locale}_statement_sha256"] != specification[field]:
            raise ValueError("Localized statement hash mismatch")
        source = path.read_text(encoding="utf-8")
        if payload[f"{locale}_statement_marker"] not in source:
            raise ValueError("Localized statement source lacks its canonical marker")
    return {"formal_statement_sha256": FormalStatementHash(specification)}


def CheckLeanKernelProof(
    payload: dict[str, Any],
    specification: dict[str, Any],
    root: Path,
    claim: Any,
) -> dict[str, Any]:
    required_paths = {
        "proof_goal_coverage_path": "lean/reports/proof_goal_coverage.tsv",
        "lean_toolchain_path": "lean/lean-toolchain",
        "lake_manifest_path": "lean/lake-manifest.json",
        "build_log_path": "lean/logs/build.txt",
        "axiom_audit_log_path": "lean/logs/axiom_audit.txt",
        "axiom_policy_log_path": "lean/logs/axiom_policy.txt",
        "forbidden_token_log_path": "lean/logs/forbidden_tokens.txt",
        "leanchecker_fresh_log_path": "lean/logs/leanchecker.txt",
    }
    required_hashes = {
        path_field.replace("_path", "_sha256") for path_field in required_paths
    }
    RequireFields(
        payload,
        set(required_paths)
        | required_hashes
        | {"proof_goal_id", "lean_declarations"},
    )
    for path_field, expected_relative in required_paths.items():
        if payload[path_field] != expected_relative:
            raise ValueError(f"Lean proof uses an unexpected evidence path: {path_field}")
        evidence_path = root / expected_relative
        hash_field = path_field.replace("_path", "_sha256")
        if not evidence_path.is_file() or FileHash(evidence_path) != payload[hash_field]:
            raise ValueError(f"Lean proof evidence hash mismatch: {path_field}")

    proof_goal_id = payload["proof_goal_id"]
    matching_goals = [
        proof_goal
        for proof_goal in specification["proof_goals"]
        if proof_goal["proof_goal_id"] == proof_goal_id
        and proof_goal["claim"] == claim
    ]
    if len(matching_goals) != 1:
        raise ValueError("Lean proof goal identity or claim differs from the specification")
    coverage_path = root / required_paths["proof_goal_coverage_path"]
    with coverage_path.open(encoding="utf-8", newline="") as handle:
        matches = [
            row
            for row in csv.DictReader(handle, delimiter="\t")
            if row.get("proof_goal_id") == proof_goal_id
            and row.get("result_id") == specification["result_id"]
        ]
    if len(matches) != 1 or matches[0].get("formalization_status") != "lean_closed":
        raise ValueError("Lean proof goal lacks one exact lean_closed declaration mapping")
    declarations = matches[0].get("lean_declaration", "").split(";")
    if not declarations or any(not declaration for declaration in declarations):
        raise ValueError("Lean proof goal has no concrete declaration mapping")
    if payload["lean_declarations"] != declarations:
        raise ValueError("Lean proof declarations differ from the registered mapping")

    build_text = (root / required_paths["build_log_path"]).read_text(encoding="utf-8")
    axiom_text = (root / required_paths["axiom_audit_log_path"]).read_text(encoding="utf-8")
    axiom_policy_text = (root / required_paths["axiom_policy_log_path"]).read_text(encoding="utf-8")
    forbidden_text = (root / required_paths["forbidden_token_log_path"]).read_text(encoding="utf-8")
    leanchecker_text = (root / required_paths["leanchecker_fresh_log_path"]).read_text(encoding="utf-8")
    if "All targets up-to-date" not in build_text:
        raise ValueError("Pinned Lean build did not finish successfully")
    if not axiom_text.strip():
        raise ValueError("Lean axiom audit is empty")
    if "PASS: all " not in axiom_policy_text or "explicit standard whitelist" not in axiom_policy_text:
        raise ValueError("Lean axiom audit did not satisfy the public policy")
    if "PASS: no sorry, admit, native_decide, unsafe, or project axiom declarations found." not in forbidden_text:
        raise ValueError("Lean forbidden-token audit did not pass")
    if leanchecker_text.splitlines() != [
        "$ lake env leanchecker --fresh PhonologicalCalculus.All",
        "Independent kernel check completed successfully.",
    ]:
        raise ValueError("Fresh Lean kernel check is absent or ambiguous")
    return {
        "proof_goal_id": proof_goal_id,
        "lean_declarations": declarations,
        "declaration_count": len(declarations),
        "pinned_toolchain_sha256": payload["lean_toolchain_sha256"],
        "pinned_lake_manifest_sha256": payload["lake_manifest_sha256"],
        "fresh_kernel_check": True,
    }


def CheckRewriteChain(payload: dict[str, Any], specification: dict[str, Any], root: Path, claim: Any) -> dict[str, Any]:
    RequireFields(payload, {"start", "end", "rules", "steps", "rules_used"})
    current = payload["start"]
    declared = {rule["id"]: rule for rule in payload["rules"]}
    used: list[str] = []
    for step in payload["steps"]:
        if step["rule"] not in declared:
            raise ValueError("Rewrite step cites an unknown rule")
        rule = declared[step["rule"]]
        if current != step["before"] or step["before"] != rule["left"] or step["after"] != rule["right"]:
            raise ValueError("Rewrite chain step is not justified")
        current = step["after"]
        used.append(step["rule"])
    if current != payload["end"] or sorted(set(used)) != sorted(payload["rules_used"]):
        raise ValueError("Rewrite chain endpoint or dependency mismatch")
    if claim != {"node": "equal", "left": payload["start"], "right": payload["end"]}:
        raise ValueError("Rewrite proof does not match its claim")
    return {"step_count": len(payload["steps"]), "rules_used": sorted(set(used))}


def CheckFirstOrderProof(payload: dict[str, Any], specification: dict[str, Any], root: Path, claim: Any) -> dict[str, Any]:
    RequireFields(payload, {"variables", "premises", "steps", "conclusion_step", "conclusion"})
    variables = payload["variables"]
    if len(variables) != len(set(variables)):
        raise ValueError("Duplicate first-order proof variable")
    premise_ids = [row["id"] for row in payload["premises"]]
    if len(premise_ids) != len(set(premise_ids)):
        raise ValueError("Duplicate first-order premise identifier")
    known: dict[str, Any] = {row["id"]: row["formula"] for row in payload["premises"]}
    step_ids: set[str] = set()
    for step in payload["steps"]:
        if step["id"] in known or step["id"] in step_ids:
            raise ValueError("Duplicate first-order proof step identifier")
        rule = step["rule"]
        if rule == "modus_ponens":
            implication = known[step["implication"]]
            antecedent = known[step["antecedent"]]
            if implication.get("node") != "implies" or implication["antecedent"] != antecedent or implication["consequent"] != step["formula"]:
                raise ValueError("Invalid modus ponens step")
        elif rule == "conjunction_introduction":
            formulas = [known[value] for value in step["premise_ids"]]
            if step["formula"] != {"node": "and", "arguments": formulas}:
                raise ValueError("Invalid conjunction introduction")
        elif rule == "conjunction_elimination":
            source = known[step["premise_id"]]
            if source.get("node") != "and" or step["formula"] not in source["arguments"]:
                raise ValueError("Invalid conjunction elimination")
        elif rule == "disjunction_introduction":
            source = known[step["premise_id"]]
            if step["formula"].get("node") != "or" or source not in step["formula"]["arguments"]:
                raise ValueError("Invalid disjunction introduction")
        elif rule == "universal_elimination":
            source = known[step["premise_id"]]
            if source.get("node") != "forall" or len(source["bindings"]) != 1:
                raise ValueError("Universal elimination requires one quantified binding")
            binding = source["bindings"][0]
            if step["formula"] != Substitute(source["body"], binding["variable"], step["term"]):
                raise ValueError("Invalid universal elimination")
        elif rule == "existential_introduction":
            target = step["formula"]
            if target.get("node") != "exists" or len(target["bindings"]) != 1:
                raise ValueError("Existential introduction requires one quantified binding")
            binding = target["bindings"][0]
            if known[step["premise_id"]] != Substitute(target["body"], binding["variable"], step["witness"]):
                raise ValueError("Invalid existential introduction")
        elif rule == "equality_reflexivity":
            if step["formula"] != {"node": "equal", "left": step["term"], "right": step["term"]}:
                raise ValueError("Invalid equality reflexivity")
        elif rule == "equality_symmetry":
            source = known[step["premise_id"]]
            if source.get("node") != "equal" or step["formula"] != {"node": "equal", "left": source["right"], "right": source["left"]}:
                raise ValueError("Invalid equality symmetry")
        elif rule == "equality_transitivity":
            left = known[step["left_id"]]
            right = known[step["right_id"]]
            if left.get("node") != "equal" or right.get("node") != "equal" or left["right"] != right["left"] or step["formula"] != {"node": "equal", "left": left["left"], "right": right["right"]}:
                raise ValueError("Invalid equality transitivity")
        elif rule == "iff_elimination":
            equivalence = known[step["equivalence_id"]]
            premise = known[step["premise_id"]]
            if equivalence.get("node") != "iff":
                raise ValueError("Iff elimination requires an equivalence")
            forward = equivalence["left"] == premise and equivalence["right"] == step["formula"]
            backward = equivalence["right"] == premise and equivalence["left"] == step["formula"]
            if not forward and not backward:
                raise ValueError("Invalid iff elimination")
        else:
            raise ValueError("Unknown first-order proof rule")
        known[step["id"]] = step["formula"]
        step_ids.add(step["id"])
    if known[payload["conclusion_step"]] != payload["conclusion"]:
        raise ValueError("First-order proof conclusion mismatch")
    if claim != payload["conclusion"]:
        raise ValueError("First-order proof does not match its claim")
    used_variables = set().union(*(FreeVariables(value) for value in known.values())) if known else set()
    if used_variables != set(variables):
        raise ValueError("First-order proof variables are undeclared or unused")
    return {"proof_length": len(payload["steps"]), "premise_count": len(payload["premises"]), "variables": variables}


def CheckInduction(payload: dict[str, Any], specification: dict[str, Any], root: Path, claim: Any) -> dict[str, Any]:
    RequireFields(payload, {"variables", "base_left", "base_right", "step_left", "step_right", "measure_variable", "conclusion"})
    variables = payload["variables"]
    base_left = ParsePolynomial(payload["base_left"], variables)
    base_right = ParsePolynomial(payload["base_right"], variables)
    step_left = ParsePolynomial(payload["step_left"], variables)
    step_right = ParsePolynomial(payload["step_right"], variables)
    if base_left != base_right or step_left != step_right:
        raise ValueError("Invalid algebraic-induction proof")
    if payload["measure_variable"] not in variables:
        raise ValueError("Induction measure variable is undeclared")
    if claim != payload["conclusion"]:
        raise ValueError("Induction proof does not match its claim")
    return {"variables": variables, "base_terms": len(base_left), "step_terms": len(step_left)}


def CheckFoundationInstantiation(payload: dict[str, Any], specification: dict[str, Any], root: Path, claim: Any) -> dict[str, Any]:
    RequireFields(payload, {"foundation_id", "foundation_statement_sha256", "premise_proofs", "instantiated_conclusion"})
    foundation_id = payload["foundation_id"]
    if foundation_id not in specification["foundation_dependencies"]:
        raise ValueError("Foundation instantiation is undeclared")
    foundation = LoadJson(root / "formal" / "foundation" / "trusted_foundation.json")
    items = {value["foundation_id"]: value for value in foundation["items"]}
    if foundation_id not in items or payload["foundation_statement_sha256"] != CanonicalHash(items[foundation_id]["formal_statement"]):
        raise ValueError("Foundation statement identity mismatch")
    premises = payload["premise_proofs"]
    if not premises:
        raise ValueError("Foundation instantiation has no checked premise")
    replayed = []
    for premise in premises:
        if set(premise) != {"path", "sha256", "proof_id"}:
            raise ValueError("Foundation premise reference is malformed")
        path = (root / premise["path"]).resolve()
        if root.resolve() not in path.parents or not path.is_file() or FileHash(path) != premise["sha256"]:
            raise ValueError("Foundation-premise proof path or hash mismatch")
        proof = LoadJson(path)
        if proof["proof_id"] != premise["proof_id"]:
            raise ValueError("Foundation-premise proof identifier mismatch")
        result_id = proof["result_id"]
        specification_path = root / "formal" / "specs" / f"{result_id}.json"
        if not specification_path.is_file():
            raise ValueError("Foundation premise lacks a result specification")
        replayed.append(CheckProof(proof, LoadJson(specification_path), root)["proof_id"])
    if payload["instantiated_conclusion"] != claim:
        raise ValueError("Foundation instantiation proves a different conclusion")
    return {"foundation_id": foundation_id, "premise_count": len(premises), "replayed_premise_ids": replayed}
