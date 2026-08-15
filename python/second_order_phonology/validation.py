from __future__ import annotations

import json
import os
import subprocess
import sys
import zipfile
from collections import Counter
from pathlib import Path
from typing import Any, Callable

from .asset_validation import ValidateBilingualAssets
from .audit import RemoveExecutionJunk, ScanPublicTree
from .common import AuditOutputDirectory, IgnoredDirectoryNames, ROOT, ReadJson, ReadTsv, Sha256File, WriteJson
from .machine_closure import ValidateMachineClosure
from .release import BuildManifest, ValidateArchive, ValidateExtractedArchive
from .style import ValidatePythonStyle


def Check(name: str, passed: bool, observed: Any, expected: Any) -> dict[str, Any]:
    return {"check": name, "status": "PASS" if passed else "FAIL", "observed": observed, "expected": expected}


def RequiredPaths() -> list[str]:
    return [
        "README.md", "README.pt-BR.md", "CITATION.cff", "LICENSES.md", "CHANGELOG.md", "Makefile", "pyproject.toml", "uv.lock", ".gitignore", ".gitattributes", "release/release_notes.md", "release/release_notes.pt-BR.md",
        "environment/README.md", "environment/python-version.txt", "environment/wolfram-version.txt", "environment/tex-version.txt", "environment/system-requirements.md", "environment/open-source-build.Dockerfile", "environment/environment_report.json",
        "locales/terminology.tsv", "locales/labels_en.json", "locales/labels_pt_BR.json",
        "registry/result_registry.tsv", "registry/proof_goal_registry.tsv", "registry/result_status.tsv", "registry/claim_budget.tsv", "registry/source_claim_crosswalk.tsv", "registry/result_dependency_edges.tsv", "registry/result_asset_crosswalk.tsv", "registry/chapter_asset_map.tsv", "registry/figure_manifest.tsv", "registry/table_manifest.tsv", "registry/release_metadata_required.tsv",
        "proofs/compiled/proof_compendium_en.pdf", "proofs/compiled/proof_compendium_pt_BR.pdf",
        "verification/wolfram/SecondOrderPhonologyVerification.wl", "verification/reports/machine_verification.json", "verification/reports/proof_coverage.tsv", "verification/reports/cross_engine_agreement.tsv", "verification/reports/release_verification.json",
        "verification/reports/cross_engine_results.tsv", "verification/reports/cross_engine_proof_goals.tsv", "verification/reports/cross_engine_proofs.json", "verification/reports/cross_engine_disagreements.tsv",
        "formal/foundation/trusted_foundation.json", "formal/schemas/result_spec.schema.json", "formal/schemas/proof.schema.json", "formal/schemas/statement_check.schema.json", "formal/kernel/wolfram/SecondOrderMachineClosure.wl", "formal/kernel/wolfram/SecondOrderProofCLI.wl",
        "formal/reports/formal_closure.json", "formal/reports/formal_closure.md", "formal/reports/formal_closure.pt-BR.md", "formal/reports/proof_inventory.tsv", "formal/reports/statement_check_inventory.tsv", "formal/reports/trusted_foundation_usage.tsv", "formal/reports/result_dependency_closure.tsv", "formal/reports/statement_correspondence.tsv", "formal/reports/assumption_satisfiability.tsv", "formal/reports/assumption_usage.tsv", "formal/reports/assumption_minimality.tsv", "formal/reports/mutation_report.tsv", "formal/reports/mutation_report.json", "formal/reports/kernel_test_report.json", "formal/reports/kernel_test_report.md", "formal/reports/kernel_coverage.json", "formal/reports/release_attestation.json", "formal/reports/source_conflicts.tsv",
        "data/dataset_manifest.tsv", "bibliography/references.bib", "bibliography/references_provenance.bib", "bibliography/reference_manifest.tsv", "bibliography/source_relevance.tsv", "bibliography/bibliography_validation.json", "bibliography/redistribution_audit.tsv",
        "figures/captions/captions_en.tsv", "figures/captions/captions_pt_BR.tsv", "figures/alt_text/alt_text_en.tsv", "figures/alt_text/alt_text_pt_BR.tsv", "figures/latex/figures_en.tex", "figures/latex/figures_pt_BR.tex",
        "tables/latex/tables_en.tex", "tables/latex/tables_pt_BR.tex",
        "lean/README.md", "lean/README.pt-BR.md", "lean/FOUNDATION.md", "lean/FOUNDATION.pt-BR.md", "lean/lean-toolchain", "lean/lakefile.toml", "lean/lake-manifest.json",
        "lean/PhonologicalCalculus.lean", "lean/PhonologicalCalculus/All.lean", "lean/PhonologicalCalculus/AxiomAudit.lean", "lean/PhonologicalCalculus/EquationAudit.lean", "lean/PhonologicalCalculus/MappingAudit.lean", "lean/PhonologicalCalculus/Registry.lean", "lean/PhonologicalCalculus/Registry/Data.lean",
        "lean/reports/coverage_overrides.tsv", "lean/reports/result_coverage.tsv", "lean/reports/proof_goal_coverage.tsv", "lean/reports/equation_coverage.tsv", "lean/reports/SOURCE_MANIFEST.sha256", "lean/reports/ARTIFACT_MANIFEST.sha256",
        "lean/logs/versions.txt", "lean/logs/dependency_resolution.txt", "lean/logs/forbidden_tokens.txt", "lean/logs/coverage_consistency.txt", "lean/logs/axiom_audit_coverage.txt", "lean/logs/axiom_audit_script_tests.txt", "lean/logs/equation_coverage.txt", "lean/logs/build.txt", "lean/logs/axiom_audit.txt", "lean/logs/equation_audit.txt", "lean/logs/mapping_audit.txt", "lean/logs/axiom_policy.txt", "lean/logs/leanchecker.txt", "lean/logs/coverage_summary.txt", "lean/logs/source_manifest_check.txt", "lean/logs/public_hygiene.txt",
    ]


def StructureChecks() -> list[dict[str, Any]]:
    missing = [path for path in RequiredPaths() if not (ROOT / path).exists()]
    scan = ScanPublicTree()
    ignored_directories = IgnoredDirectoryNames()
    manifest_rows = ReadTsv(ROOT / "ARTIFACT_MANIFEST.tsv") if (ROOT / "ARTIFACT_MANIFEST.tsv").is_file() else []
    return [
        Check("required_paths", not missing, missing, []),
        Check("public_tree_clean", scan["status"] == "PASS", scan["finding_count"], 0),
        Check("audit_output_ignored", len(ignored_directories - {"build", "__pycache__"}) == 1, sorted(ignored_directories), "one ignored audit-output directory"),
        Check("ignored_directories_unmanifested", not any(Path(row.get("path", "")).parts and Path(row.get("path", "")).parts[0] in ignored_directories for row in manifest_rows), sorted(ignored_directories), "no ignored directory in manifest"),
    ]


def RegistryChecks() -> list[dict[str, Any]]:
    results = ReadTsv(ROOT / "registry" / "result_registry.tsv")
    proof_goals = ReadTsv(ROOT / "registry" / "proof_goal_registry.tsv")
    statuses = ReadTsv(ROOT / "registry" / "result_status.tsv")
    conflicts = ReadTsv(ROOT / "formal" / "reports" / "source_conflicts.tsv")
    crosswalk = ReadTsv(ROOT / "registry" / "result_asset_crosswalk.tsv")
    flagship = {"CALC-F1", "CHG-B2", "MAX-G3", "MAX-G8", "SEL-F2"}
    flagship_rows = [row for row in results if row["result_id"] in flagship]
    required_fields = ["statement_sha256", "chapter", "nonclaims", "withdrawal_condition"]
    result_missing = [row["result_id"] for row in results if any(not str(row.get(field, "")).strip() for field in ["title_en", "title_pt_BR", "statement_en", "statement_pt_BR", "assumptions", "scope", "nonclaims", "ownership_class", "withdrawal_condition", "normative_source_file", "normative_source_anchor", "statement_sha256", "chapter", "review_priority"])]
    claims = ReadTsv(ROOT / "registry" / "claim_budget.tsv")
    claim_missing = [row["claim_id"] for row in claims if any(not str(row.get(field, "")).strip() for field in ["one_sentence_claim_en", "one_sentence_claim_pt_BR", "status", "chapter", "allowed_strength", "prohibited_upcast", "primary_evidence"])]
    allowed_claim_statuses = {"flagship_methodological", "flagship_mathematical", "supporting_mathematical_result", "published_analysis_consequence", "data_demonstration", "limitation_or_refusal", "appendix_only"}
    invalid_claim_statuses = [row["claim_id"] for row in claims if row["status"] not in allowed_claim_statuses]
    written_statuses = {
        "CompleteCounterexampleProof",
        "CompleteOriginalWrittenProof",
        "CompleteReductionProof",
        "CompleteSpecializationProof",
        "ComputationalResultOnly",
    }
    return [
        Check("result_count", len(results) == 68, len(results), 68),
        Check("result_ids_unique", len({row["result_id"] for row in results}) == 68, len({row["result_id"] for row in results}), 68),
        Check("proof_goal_count", len(proof_goals) == 218, len(proof_goals), 218),
        Check("proof_goal_ids_unique", len({row["proof_goal_id"] for row in proof_goals}) == 218, len({row["proof_goal_id"] for row in proof_goals}), 218),
        Check("result_status_count", len(statuses) == 68, len(statuses), 68),
        Check("written_proof_status_vocabulary", all(row["dissertation_proof_status"] in written_statuses for row in statuses), sorted({row["dissertation_proof_status"] for row in statuses}), sorted(written_statuses)),
        Check("source_conflicts_resolved", all(row["status"] == "resolved" for row in conflicts), Counter(row["status"] for row in conflicts), {"resolved": len(conflicts)}),
        Check("flagship_fields", len(flagship_rows) == len(flagship) and all(all(row[field] for field in required_fields) for row in flagship_rows), len(flagship_rows), len(flagship)),
        Check("flagship_crosswalk", all(any(asset["result_id"] == row["result_id"] and asset["written_proof_files"] and asset["python_checks"] and asset["chapter"] for asset in crosswalk) for row in flagship_rows), len(flagship_rows), len(flagship)),
        Check("result_required_fields", not result_missing, result_missing, []),
        Check("claim_count", len(claims) == 58, len(claims), 58),
        Check("claim_required_fields", not claim_missing, claim_missing, []),
        Check("claim_status_vocabulary", not invalid_claim_statuses, invalid_claim_statuses, []),
    ]


def ProofChecks() -> list[dict[str, Any]]:
    results = {row["result_id"]: row for row in ReadTsv(ROOT / "registry" / "result_registry.tsv")}
    statuses = ReadTsv(ROOT / "registry" / "result_status.tsv")
    missing: list[str] = []
    mismatches: list[str] = []
    label_mismatches: list[str] = []
    for row in statuses:
        identifier = row["result_id"]
        for field in ["written_proof_en", "written_proof_pt_BR"]:
            if not (ROOT / row[field]).is_file():
                missing.append(f"{identifier}:{field}")
        if row["statement_sha256"] != results[identifier]["statement_sha256"]:
            mismatches.append(identifier)
        for locale in ["en", "pt_BR"]:
            proof_path = ROOT / "proofs" / locale / "results" / f"{identifier}.tex"
            if proof_path.is_file():
                source = proof_path.read_text(encoding="utf-8")
                if f"\\stablelabel{{{identifier}}}" not in source or "\\begin{recordproof}" not in source:
                    label_mismatches.append(f"{locale}:{identifier}")
    english = sorted(path.stem for path in (ROOT / "proofs" / "en" / "results").glob("*.tex")) if (ROOT / "proofs" / "en" / "results").is_dir() else []
    portuguese = sorted(path.stem for path in (ROOT / "proofs" / "pt_BR" / "results").glob("*.tex")) if (ROOT / "proofs" / "pt_BR" / "results").is_dir() else []
    nonclosed_mandatory = [row["result_id"] for row in statuses if row["machine_status"] != "MachineClosed"]
    equation_rows = ReadTsv(ROOT / "proofs" / "shared" / "equation_sources.sha256.tsv")
    equation_mismatches = [row["path"] for row in equation_rows if not (ROOT / "proofs" / row["path"]).is_file() or Sha256File(ROOT / "proofs" / row["path"]) != row["sha256"]]
    return [
        Check("proof_files_present", not missing, missing, []),
        Check("proof_statement_hashes", not mismatches, mismatches, []),
        Check("proof_labels_and_environments", not label_mismatches, label_mismatches, []),
        Check("bilingual_result_ids", english == portuguese == sorted(results), {"en": len(english), "pt_BR": len(portuguese)}, {"en": 68, "pt_BR": 68}),
        Check("compiled_compendia", all((ROOT / path).is_file() for path in ["proofs/compiled/proof_compendium_en.pdf", "proofs/compiled/proof_compendium_pt_BR.pdf"]), "present", "present"),
        Check("all_mandatory_results_machine_closed", not nonclosed_mandatory and len(statuses) == 68, nonclosed_mandatory, []),
        Check("shared_equation_hashes", not equation_mismatches, equation_mismatches, []),
    ]


def MachineChecks() -> list[dict[str, Any]]:
    report = ReadJson(ROOT / "verification" / "reports" / "machine_verification.json")
    registry = {row["result_id"]: row for row in ReadTsv(ROOT / "registry" / "result_registry.tsv")}
    mismatches = [result["ResultID"] for result in report["Results"] if result.get("StatementSHA256") != registry[result["ResultID"]]["statement_sha256"]]
    agreement = ReadTsv(ROOT / "verification" / "reports" / "cross_engine_agreement.tsv")
    result_agreement = ReadTsv(ROOT / "verification" / "reports" / "cross_engine_results.tsv")
    proof_goal_agreement = ReadTsv(ROOT / "verification" / "reports" / "cross_engine_proof_goals.tsv")
    cross_proofs = ReadJson(ROOT / "verification" / "reports" / "cross_engine_proofs.json")
    disagreements = ReadTsv(ROOT / "verification" / "reports" / "cross_engine_disagreements.tsv")
    result_statuses = Counter(result.get("Status", "") for result in report["Results"])
    proof_goal_statuses = Counter(proof_goal.get("Status", "") for result in report["Results"] for proof_goal in result["ProofGoalResults"])
    finite_report = ReadJson(ROOT / "verification" / "reports" / "python_finite_calculus.json")
    finite_closure = next((check for check in finite_report.get("checks", []) if check.get("check") == "registered_proof_goal_closure"), {})
    return [
        Check("machine_result_count", report["ResultCount"] == 68, report["ResultCount"], 68),
        Check("machine_result_statuses_exact", result_statuses == Counter({"MachineClosed": 68}), dict(result_statuses), {"MachineClosed": 68}),
        Check("machine_proof_goal_statuses_exact", proof_goal_statuses == Counter({"MachineClosed": 218}), dict(proof_goal_statuses), {"MachineClosed": 218}),
        Check("finite_calculus_observes_machine_closed_status", finite_closure.get("status") == "PASS" and finite_closure.get("observed") == {"MachineClosed": 218}, finite_closure, {"status": "PASS", "observed": {"MachineClosed": 218}}),
        Check("machine_statement_hashes", not mismatches, mismatches, []),
        Check("cross_engine_agreement", len(agreement) >= 8 and all(row["agreement"] == "true" for row in agreement), sum(row["agreement"] == "true" for row in agreement), len(agreement)),
        Check("complete_cross_engine_results", len(result_agreement) == 68 and all(row["agreement"] == "true" for row in result_agreement), len(result_agreement), 68),
        Check("complete_cross_engine_proof_goals", len(proof_goal_agreement) == 218 and all(row["agreement"] == "true" for row in proof_goal_agreement), len(proof_goal_agreement), 218),
        Check("complete_cross_engine_proof_report", cross_proofs.get("status") == "PASS" and not disagreements, {"status": cross_proofs.get("status"), "disagreements": len(disagreements)}, {"status": "PASS", "disagreements": 0}),
    ]


def DataChecks() -> list[dict[str, Any]]:
    manifest = ReadTsv(ROOT / "data" / "dataset_manifest.tsv")
    missing: list[str] = []
    hash_mismatches: list[str] = []
    row_mismatches: list[str] = []
    schema_mismatches: list[str] = []
    duplicate_rows: list[str] = []
    for row in manifest:
        data_path = ROOT / row["dataset"]
        schema_path = ROOT / row["schema"]
        if not data_path.is_file() or not schema_path.is_file():
            missing.append(row["dataset"])
            continue
        if Sha256File(data_path) != row["sha256"]:
            hash_mismatches.append(row["dataset"])
        if data_path.suffix == ".tsv" and len(ReadTsv(data_path)) != int(row["row_count"]):
            row_mismatches.append(row["dataset"])
        schema = json.loads(schema_path.read_text(encoding="utf-8"))
        if data_path.suffix == ".tsv":
            rows = ReadTsv(data_path)
            item_schema = schema.get("items", {})
            required = item_schema.get("required", [])
            properties = item_schema.get("properties", {})
            if rows and (set(rows[0]) != set(properties) or any(any(field not in row for field in required) for row in rows)):
                schema_mismatches.append(row["dataset"])
            signatures = [tuple(record.get(field, "") for field in rows[0]) for record in rows] if rows else []
            if len(signatures) != len(set(signatures)):
                duplicate_rows.append(row["dataset"])
        elif data_path.suffix == ".json":
            content = ReadJson(data_path)
            if schema.get("type") == "object" and not isinstance(content, dict):
                schema_mismatches.append(row["dataset"])
            if schema.get("type") == "array" and not isinstance(content, list):
                schema_mismatches.append(row["dataset"])
    demonstrations = ReadJson(ROOT / "verification" / "reports" / "python_demonstrations.json")
    return [
        Check("canonical_dataset_count", len(manifest) == 36, len(manifest), 36),
        Check("canonical_data_files", not missing, missing, []),
        Check("canonical_data_hashes", not hash_mismatches, hash_mismatches, []),
        Check("canonical_row_counts", not row_mismatches, row_mismatches, []),
        Check("canonical_schema_shapes", not schema_mismatches, schema_mismatches, []),
        Check("canonical_duplicate_rows", not duplicate_rows, duplicate_rows, []),
        Check("headline_demonstrations", demonstrations["status"] == "PASS", demonstrations["status"], "PASS"),
    ]


def AssetChecks() -> list[dict[str, Any]]:
    validation = ValidateBilingualAssets()
    figures = ReadTsv(ROOT / "registry" / "figure_manifest.tsv")
    tables = ReadTsv(ROOT / "registry" / "table_manifest.tsv")
    figure_files = [ROOT / row[field] for row in figures for field in ["svg", "pdf", "png"]]
    table_files = [ROOT / row[field] for row in tables for field in ["latex", "tsv", "markdown"]]
    figure_pairs = Counter(row["figure_id"] for row in figures)
    table_pairs = Counter(row["table_id"] for row in tables)
    source_pairing = all(len({row["source_sha256"] for row in figures if row["figure_id"] == identifier}) == 1 for identifier in figure_pairs)
    return [
        Check("figure_manifest_rows", len(figures) == 76, len(figures), 76),
        Check("figure_language_pairs", len(figure_pairs) == 38 and all(value == 2 for value in figure_pairs.values()), dict(figure_pairs), "38 pairs"),
        Check("figure_render_count", all(path.is_file() for path in figure_files), sum(path.is_file() for path in figure_files), 228),
        Check("figure_source_pairing", source_pairing, source_pairing, True),
        Check("table_manifest_rows", len(tables) == 28, len(tables), 28),
        Check("table_language_pairs", len(table_pairs) == 14 and all(value == 2 for value in table_pairs.values()), dict(table_pairs), "14 pairs"),
        Check("table_artifact_count", all(path.is_file() for path in table_files), sum(path.is_file() for path in table_files), 84),
        Check("bilingual_asset_validation", validation["status"] == "PASS", validation["findings"], []),
    ]


def BibliographyChecks() -> list[dict[str, Any]]:
    validation = ReadJson(ROOT / "bibliography" / "bibliography_validation.json")
    manifest = ReadTsv(ROOT / "bibliography" / "reference_manifest.tsv")
    biber = validation["biber"]
    errors = int(biber["compile_errors"]) + int(biber["provenance_errors"])
    warnings = int(biber["compile_warnings"]) + int(biber["provenance_warnings"])
    counts = validation["counts"]
    bijection = validation["bijection"]
    return [
        Check("bibliography_key_count", len(manifest) == 173, len(manifest), 173),
        Check("biber_errors", errors == 0, errors, 0),
        Check("biber_warnings", warnings == 0, warnings, 0),
        Check("bibliography_status", validation.get("result") == "PASS", validation.get("result"), "PASS"),
        Check("reference_bijection", all(bool(value) for key, value in bijection.items() if key.startswith("keys_equal")), bijection, "all key sets equal"),
        Check("current_status_rechecks", int(counts["current_status_rechecks"]) == 18, counts["current_status_rechecks"], 18),
    ]


def PythonQualityChecks() -> list[dict[str, Any]]:
    environment = dict(os.environ)
    environment["PYTHONDONTWRITEBYTECODE"] = "1"
    completed = subprocess.run([sys.executable, "-m", "unittest", "discover", "-s", "verification/python/tests", "-p", "test_*.py"], cwd=ROOT, env=environment, capture_output=True, text=True, encoding="utf-8", check=False, timeout=3600)
    RemoveExecutionJunk()
    excluded = {".lake", "build", "release", *IgnoredDirectoryNames()}
    source_text = "\n".join(path.read_text(encoding="utf-8") for path in sorted(ROOT.rglob("*.py")) if not any(part in excluded for part in path.parts))
    candidates = ["requests." + "get(", "url" + "open(", "socket." + "create_connection(", "http." + "client."]
    network_tokens = [token for token in candidates if token in source_text]
    return [
        Check("python_tests", completed.returncode == 0, (completed.stdout + completed.stderr)[-2000:], "all tests pass"),
        Check("normal_build_has_no_network_calls", not network_tokens, network_tokens, []),
    ]


def LeanChecks() -> list[dict[str, Any]]:
    result_path = ROOT / "lean" / "reports" / "result_coverage.tsv"
    proof_goal_path = ROOT / "lean" / "reports" / "proof_goal_coverage.tsv"
    result_rows = ReadTsv(result_path) if result_path.is_file() else []
    proof_goal_rows = ReadTsv(proof_goal_path) if proof_goal_path.is_file() else []
    registered_results = ReadTsv(ROOT / "registry" / "result_registry.tsv")
    registered_proof_goals = ReadTsv(ROOT / "registry" / "proof_goal_registry.tsv")
    logs = ROOT / "lean" / "logs"
    forbidden_text = (logs / "forbidden_tokens.txt").read_text(encoding="utf-8") if (logs / "forbidden_tokens.txt").is_file() else ""
    coverage_consistency_text = (logs / "coverage_consistency.txt").read_text(encoding="utf-8") if (logs / "coverage_consistency.txt").is_file() else ""
    axiom_coverage_text = (logs / "axiom_audit_coverage.txt").read_text(encoding="utf-8") if (logs / "axiom_audit_coverage.txt").is_file() else ""
    axiom_script_tests_text = (logs / "axiom_audit_script_tests.txt").read_text(encoding="utf-8") if (logs / "axiom_audit_script_tests.txt").is_file() else ""
    equation_coverage_text = (logs / "equation_coverage.txt").read_text(encoding="utf-8") if (logs / "equation_coverage.txt").is_file() else ""
    build_text = (logs / "build.txt").read_text(encoding="utf-8") if (logs / "build.txt").is_file() else ""
    axiom_text = (logs / "axiom_audit.txt").read_text(encoding="utf-8") if (logs / "axiom_audit.txt").is_file() else ""
    equation_audit_text = (logs / "equation_audit.txt").read_text(encoding="utf-8") if (logs / "equation_audit.txt").is_file() else ""
    mapping_audit_text = (logs / "mapping_audit.txt").read_text(encoding="utf-8") if (logs / "mapping_audit.txt").is_file() else ""
    axiom_policy_text = (logs / "axiom_policy.txt").read_text(encoding="utf-8") if (logs / "axiom_policy.txt").is_file() else ""
    checker_text = (logs / "leanchecker.txt").read_text(encoding="utf-8") if (logs / "leanchecker.txt").is_file() else ""
    source_manifest_text = (logs / "source_manifest_check.txt").read_text(encoding="utf-8") if (logs / "source_manifest_check.txt").is_file() else ""
    public_hygiene_text = (logs / "public_hygiene.txt").read_text(encoding="utf-8") if (logs / "public_hygiene.txt").is_file() else ""
    forbidden_axioms = [token for token in ["sorryAx", "Lean.trustCompiler", "ofReduceBool"] if token in axiom_text]
    source_manifest_path = ROOT / "lean" / "reports" / "SOURCE_MANIFEST.sha256"
    source_manifest_rows = [line.split("  ", 1) for line in source_manifest_path.read_text(encoding="utf-8").splitlines() if "  " in line] if source_manifest_path.is_file() else []
    source_manifest_mismatches = [relative for digest, relative in source_manifest_rows if not (ROOT / "lean" / relative).is_file() or Sha256File(ROOT / "lean" / relative) != digest]
    artifact_manifest_path = ROOT / "lean" / "reports" / "ARTIFACT_MANIFEST.sha256"
    artifact_manifest_rows = [line.split("  ", 1) for line in artifact_manifest_path.read_text(encoding="utf-8").splitlines() if "  " in line] if artifact_manifest_path.is_file() else []
    artifact_manifest_mismatches = [relative for digest, relative in artifact_manifest_rows if not (ROOT / "lean" / relative).is_file() or Sha256File(ROOT / "lean" / relative) != digest]
    return [
        Check("lean_result_inventory", len(result_rows) == 68, len(result_rows), 68),
        Check("lean_proof_goal_inventory", len(proof_goal_rows) == 218, len(proof_goal_rows), 218),
        Check("lean_result_registry_identity", {row.get("result_id", "") for row in result_rows} == {row["result_id"] for row in registered_results}, len({row.get("result_id", "") for row in result_rows}), 68),
        Check("lean_proof_goal_registry_identity", {row.get("proof_goal_id", "") for row in proof_goal_rows} == {row["proof_goal_id"] for row in registered_proof_goals}, len({row.get("proof_goal_id", "") for row in proof_goal_rows}), 218),
        Check("lean_result_closure_exact", Counter(row.get("formalization_status", "") for row in result_rows) == Counter({"lean_closed": 68}), Counter(row.get("formalization_status", "") for row in result_rows), {"lean_closed": 68}),
        Check("lean_proof_goal_closure_exact", Counter(row.get("formalization_status", "") for row in proof_goal_rows) == Counter({"lean_closed": 218}), Counter(row.get("formalization_status", "") for row in proof_goal_rows), {"lean_closed": 218}),
        Check("lean_closed_declarations_present", all(row.get("lean_declaration", "").strip() for row in result_rows + proof_goal_rows), True, True),
        Check("lean_forbidden_token_audit", "PASS: no sorry, admit, native_decide, unsafe, or project axiom declarations found." in forbidden_text, "PASS" if "PASS:" in forbidden_text else "missing", "PASS"),
        Check("lean_coverage_consistency", "PASS: Lean registry lists, row-level coverage, and 68/218 totals agree." in coverage_consistency_text, "PASS" if "PASS:" in coverage_consistency_text else "FAIL", "PASS"),
        Check("lean_axiom_audit_coverage", "exported theorem and lemma declarations have one axiom-audit target." in axiom_coverage_text and "PASS:" in axiom_coverage_text, "PASS" if "PASS:" in axiom_coverage_text else "FAIL", "PASS"),
        Check("lean_axiom_audit_checker_tests", "PASS: axiom-audit checker rejects error-only, incomplete, and unexpected-axiom logs" in axiom_script_tests_text, "PASS" if "PASS:" in axiom_script_tests_text else "FAIL", "PASS"),
        Check("lean_equation_coverage", "PASS: 63 unique public equation labels have nonempty scoped Lean mappings." in equation_coverage_text, "PASS" if "PASS:" in equation_coverage_text else "FAIL", "PASS"),
        Check("lean_build", "$ lake --no-build build" in build_text and "error:" not in build_text.lower(), "PASS" if "$ lake --no-build build" in build_text and "error:" not in build_text.lower() else "FAIL", "PASS"),
        Check("lean_axiom_audit", bool(axiom_text) and not forbidden_axioms, forbidden_axioms if axiom_text else ["missing log"], []),
        Check("lean_equation_audit", "$ lake env lean PhonologicalCalculus/EquationAudit.lean" in equation_audit_text and "error:" not in equation_audit_text.lower(), "PASS" if equation_audit_text and "error:" not in equation_audit_text.lower() else "FAIL", "PASS"),
        Check("lean_registry_mapping_audit", "$ lake env lean PhonologicalCalculus/MappingAudit.lean" in mapping_audit_text and "error:" not in mapping_audit_text.lower(), "PASS" if mapping_audit_text and "error:" not in mapping_audit_text.lower() else "FAIL", "PASS"),
        Check("lean_axiom_policy", "reported axiom dependencies are in the explicit standard whitelist." in axiom_policy_text and "PASS:" in axiom_policy_text, "PASS" if "PASS:" in axiom_policy_text else "FAIL", "PASS"),
        Check("lean_independent_kernel_replay", "$ lake env leanchecker --fresh PhonologicalCalculus.All" in checker_text and "Independent kernel check completed successfully." in checker_text, "PASS" if "$ lake env leanchecker --fresh PhonologicalCalculus.All" in checker_text and "Independent kernel check completed successfully." in checker_text else "FAIL", "PASS"),
        Check("lean_source_manifest", "$ shasum -a 256 -c reports/SOURCE_MANIFEST.sha256" in source_manifest_text and "FAILED" not in source_manifest_text, "PASS" if "$ shasum -a 256 -c reports/SOURCE_MANIFEST.sha256" in source_manifest_text and "FAILED" not in source_manifest_text else "FAIL", "PASS"),
        Check("lean_source_manifest_current", bool(source_manifest_rows) and not source_manifest_mismatches, source_manifest_mismatches if source_manifest_rows else ["missing manifest"], []),
        Check("lean_artifact_manifest_current", bool(artifact_manifest_rows) and not artifact_manifest_mismatches, artifact_manifest_mismatches if artifact_manifest_rows else ["missing manifest"], []),
        Check("lean_public_hygiene", "PASS: no workstation-specific paths, log control characters, or leanchecker failure diagnostics found." in public_hygiene_text, "PASS" if "PASS:" in public_hygiene_text else "FAIL", "PASS"),
    ]


def ManifestChecks() -> list[dict[str, Any]]:
    BuildManifest()
    rows = ReadTsv(ROOT / "ARTIFACT_MANIFEST.tsv")
    missing = [row["path"] for row in rows if not (ROOT / row["path"]).is_file()]
    mismatches = [row["path"] for row in rows if (ROOT / row["path"]).is_file() and Sha256File(ROOT / row["path"]) != row["sha256"]]
    return [Check("manifest_files", not missing, missing, []), Check("manifest_hashes", not mismatches, mismatches, [])]


def ReleaseChecks(require_release: bool) -> list[dict[str, Any]]:
    archive = ROOT / "release" / "second_order_phonology_artifact.zip"
    if not require_release:
        return [Check("release_deferred", True, "working_tree_validation", "working_tree_validation")]
    if not archive.is_file():
        return [Check("release_archive", False, "missing", "present")]
    validation = ValidateArchive(archive)
    extracted_validation = ValidateExtractedArchive(archive)
    checksum_path = ROOT / "release" / "second_order_phonology_artifact.zip.sha256"
    expected = checksum_path.read_text(encoding="utf-8").split()[0] if checksum_path.is_file() else ""
    return [
        Check("release_archive_clean", validation["status"] == "PASS", validation["findings"], []),
        Check("release_archive_extracted_validation", extracted_validation["status"] == "PASS", extracted_validation["findings"], []),
        Check("release_archive_sha256", expected == Sha256File(archive), Sha256File(archive), expected),
    ]


def ValidatePackage(strict: bool, require_release: bool, machine_closed: bool = False) -> dict[str, Any]:
    RemoveExecutionJunk()
    style = ValidatePythonStyle()
    sections: list[tuple[str, Callable[[], list[dict[str, Any]]]]] = [
        ("structure", StructureChecks),
        ("scientific_registry", RegistryChecks),
        ("proof_closure", ProofChecks),
        ("machine_verification", MachineChecks),
        ("data", DataChecks),
        ("figures_and_tables", AssetChecks),
        ("bibliography", BibliographyChecks),
        ("lean_formalization", LeanChecks),
        ("python_execution", PythonQualityChecks),
        ("manifest", ManifestChecks),
    ]
    results: dict[str, list[dict[str, Any]]] = {}
    for name, function in sections:
        results[name] = function()
    results["python_quality"] = [Check("python_style", style["status"] == "PASS", style["finding_count"], 0)]
    if machine_closed:
        machine_closure = ValidateMachineClosure()
        results["machine_closure"] = [Check("machine_closed_requires_strict_validation", strict, strict, True), *machine_closure["checks"]]
    results["release"] = ReleaseChecks(require_release)
    failures = [f"{section}:{check['check']}" for section, checks in results.items() for check in checks if check["status"] == "FAIL"]
    report = {"status": "PASS" if not failures else "FAIL", "strict": strict, "machine_closed": machine_closed, "release_required": require_release, "failure_count": len(failures), "failures": failures, "sections": results}
    WriteJson(AuditOutputDirectory() / "package_validation.json", report)
    WriteValidationMarkdown(report)
    return report


def WriteValidationMarkdown(report: dict[str, Any]) -> None:
    lines = ["# Package validation", "", f"Status: **{report['status']}**", "", f"Failures: {report['failure_count']}", ""]
    for section, checks in report["sections"].items():
        lines.extend([f"## {section.replace('_', ' ').title()}", "", "| Check | Status |", "|---|---|"])
        for check in checks:
            lines.append(f"| {check['check']} | {check['status']} |")
        lines.append("")
    (AuditOutputDirectory() / "package_validation.md").write_text("\n".join(lines), encoding="utf-8", newline="\n")
