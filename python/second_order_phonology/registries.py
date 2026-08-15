from __future__ import annotations

import json
from pathlib import Path
from typing import Any, Mapping, Sequence

from .common import CatalogSortKey, ROOT, ReadJson, ReadTsv, Sha256File, Sha256Text, StripHoldComplete, WriteJson, WriteTsv


RESULT_FIELDS = [
    "result_id",
    "group",
    "kind",
    "title_en",
    "title_pt_BR",
    "statement_en",
    "statement_pt_BR",
    "assumptions",
    "scope",
    "nonclaims",
    "ownership_class",
    "novelty_claim",
    "withdrawal_condition",
    "normative_source_file",
    "normative_source_anchor",
    "statement_sha256",
    "main_or_appendix",
    "chapter",
    "mandatory_for_dissertation",
    "citation_keys",
    "review_priority",
]
PROOF_GOAL_FIELDS = [
    "proof_goal_id",
    "result_id",
    "title",
    "proof_goal_type",
    "mandatory",
    "machine_method",
    "expected_exact_result",
    "machine_status",
    "written_proof_anchor",
    "source_dependencies",
    "failure_effect",
    "notes",
]


def LoadCatalog() -> list[dict[str, Any]]:
    report = ReadJson(ROOT / "verification" / "reports" / "machine_verification.json")
    results = report["Results"]
    identifiers = [str(result["ResultID"]) for result in results]
    if len(results) != 68 or len(set(identifiers)) != 68:
        raise ValueError(f"Expected 68 unique catalog results, found {len(results)} rows and {len(set(identifiers))} identifiers")
    return sorted(results, key=lambda result: CatalogSortKey(str(result["ResultID"])))


def LoadMetadata() -> dict[str, Any]:
    return ReadJson(Path(__file__).with_name("registry_metadata.json"))


def ProofStatusFor(result: Mapping[str, Any]) -> str:
    identifier = str(result["ResultID"])
    classification = str(result["Classification"]).lower()
    if identifier.startswith("DATA-"):
        return "ComputationalResultOnly"
    if identifier in {"MAX-G3", "MAX-G4"}:
        return "CompleteReductionProof"
    if identifier in {"SEL-F2", "MAX-G9"}:
        return "CompleteCounterexampleProof"
    if "specialization" in classification or "inherited" in classification:
        return "CompleteSpecializationProof"
    return "CompleteOriginalWrittenProof"


def FigureIdsFor(group: str, identifier: str) -> str:
    mapping = {
        "CALC": "FIG-01;FIG-02;FIG-03;FIG-04;FIG-05;FIG-06;FIG-07",
        "FIN": "FIG-06;FIG-08",
        "CHG": "FIG-15;FIG-16;FIG-17;FIG-18;FIG-19;FIG-20;FIG-21;FIG-22;FIG-23",
        "CTX": "FIG-22",
        "FLUX": "FIG-24;FIG-25",
        "SUP": "FIG-26",
        "SEL": "FIG-28",
        "MAX": "FIG-09;FIG-10;FIG-11;FIG-12;FIG-13;FIG-14",
        "APP": "FIG-27;FIG-28;FIG-29;FIG-30;FIG-31",
        "DATA": "FIG-32;FIG-A01;FIG-A02",
    }
    if identifier == "CALC-F1":
        return "FIG-01;FIG-03;FIG-07"
    return mapping[group]


def TableIdsFor(group: str) -> str:
    return {
        "CALC": "TAB-02;TAB-03;TAB-04;TAB-A02",
        "FIN": "TAB-01;TAB-04;TAB-A02",
        "CHG": "TAB-06;TAB-A02",
        "CTX": "TAB-06;TAB-A02",
        "FLUX": "TAB-06;TAB-A02",
        "SUP": "TAB-06;TAB-A02",
        "SEL": "TAB-08;TAB-A02",
        "MAX": "TAB-07;TAB-A02",
        "APP": "TAB-08;TAB-A02",
        "DATA": "TAB-09;TAB-A02",
    }[group]


def PythonChecksFor(group: str) -> str:
    return {
        "CALC": "scripts/verify_finite_calculus.py",
        "FIN": "scripts/verify_finite_calculus.py",
        "CHG": "scripts/verify_continuous_hg.py",
        "CTX": "scripts/verify_continuous_hg.py",
        "FLUX": "scripts/verify_continuous_hg.py",
        "SUP": "scripts/verify_continuous_hg.py",
        "SEL": "scripts/verify_applications.py",
        "MAX": "scripts/verify_maxent.py",
        "APP": "scripts/verify_applications.py",
        "DATA": "scripts/verify_demonstrations.py",
    }[group]


def DataFilesFor(group: str) -> str:
    return {
        "CALC": "data/canonical/finite_calculus/regressions.tsv;data/canonical/finite_calculus/contracts.json",
        "FIN": "data/canonical/finite_calculus/query_sort_registry.tsv;data/canonical/finite_calculus/witnesses.tsv",
        "CHG": "data/canonical/continuous_hg/exact_profiles.tsv;data/canonical/continuous_hg/support_phase_boundaries.tsv",
        "CTX": "data/canonical/continuous_hg/support_bifurcations.tsv",
        "FLUX": "data/canonical/continuous_hg/contact_response.tsv;data/canonical/continuous_hg/identifiability_examples.tsv",
        "SUP": "data/canonical/continuous_hg/continuation_comparisons.tsv",
        "SEL": "data/canonical/applications/goldrick_daland_counterexample.tsv",
        "MAX": "data/canonical/maxent/response_capacity.tsv;data/canonical/maxent/law_envelope_incomparability.tsv",
        "APP": "data/canonical/applications",
        "DATA": "data/canonical/demonstrations",
    }[group]


def ApplicationIdsFor(identifier: str) -> str:
    if identifier in {"APP-MCC-GRID", "APP-MCC-LENGTH", "APP-MCC-COMP", "APP-BASIC"}:
        return identifier
    if identifier in {"CHG-B2", "CHG-B3", "CHG-B6", "CHG-B7", "CHG-B8"}:
        return "APP-MCC-GRID;APP-MCC-LENGTH;APP-MCC-COMP"
    if identifier in {"MAX-G5", "MAX-G6"}:
        return "APP-BASIC"
    if identifier == "SEL-F2":
        return "SEL-F2"
    if identifier in {"MAX-G7", "MAX-G9"}:
        return "APP-PATER;APP-CABRERA"
    if identifier == "FIN-A7":
        return "APP-WALKER"
    return "not_applicable"


def PortugueseClaim(claim: Mapping[str, Any], translations: Mapping[str, Any]) -> str:
    direct = str(claim.get("exact_final_proposition_pt_BR", "")).strip()
    if direct:
        return direct
    identifiers = [value.strip() for value in str(claim["result_ids"]).split(";") if value.strip()]
    statements = []
    for identifier in identifiers:
        translated = translations.get(identifier)
        if isinstance(translated, dict):
            statement = StripHoldComplete(str(translated.get("statement_pt_BR", "")))
            if statement:
                statements.append(statement)
    if statements:
        return " ".join(statements)
    raise ValueError(f"Missing Brazilian Portuguese claim text for {claim['claim_id']}")


def BuildResultRegistry() -> list[dict[str, Any]]:
    translations = ReadJson(ROOT / "locales" / "result_text_pt_BR.json")
    metadata = {row["id"]: row for row in LoadMetadata()["results"]}
    rows: list[dict[str, Any]] = []
    for catalog_result in LoadCatalog():
        identifier = str(catalog_result["ResultID"])
        translated = translations.get(identifier)
        details = metadata.get(identifier)
        if not isinstance(translated, dict) or not isinstance(details, dict):
            raise ValueError(f"Missing result metadata or Portuguese text for {identifier}")
        statement = StripHoldComplete(str(catalog_result["Statement"]))
        statement_pt = StripHoldComplete(str(translated["statement_pt_BR"]))
        rows.append(
            {
                "result_id": identifier,
                "group": catalog_result["Group"],
                "kind": details["kind"],
                "title_en": catalog_result["Title"],
                "title_pt_BR": translated["title_pt_BR"],
                "statement_en": statement,
                "statement_pt_BR": statement_pt,
                "assumptions": StripHoldComplete(str(catalog_result["Assumptions"])),
                "scope": catalog_result["Scope"],
                "nonclaims": catalog_result["NonClaims"],
                "ownership_class": details["ownership_class"],
                "novelty_claim": details["novelty_claim"],
                "withdrawal_condition": details["withdrawal_condition"],
                "normative_source_file": f"proofs/en/results/{identifier}.tex",
                "normative_source_anchor": f"res:{identifier}",
                "statement_sha256": Sha256Text(statement),
                "main_or_appendix": details["main_or_appendix"],
                "chapter": details["chapter"],
                "mandatory_for_dissertation": details["mandatory_for_dissertation"],
                "citation_keys": details["citation_keys"],
                "review_priority": details["review_priority"],
            }
        )
    WriteTsv(ROOT / "registry" / "result_registry.tsv", rows, RESULT_FIELDS)
    return rows


def BuildProofGoalRegistry() -> list[dict[str, Any]]:
    registry_path = ROOT / "registry" / "proof_goal_registry.tsv"
    existing_rows = {
        row["proof_goal_id"]: row
        for row in ReadTsv(registry_path)
    } if registry_path.is_file() else {}
    coverage_rows = {
        row["id"]: row
        for row in ReadTsv(ROOT / "lean" / "reports" / "coverage_overrides.tsv")
        if row["scope"] == "proof_goal"
    }
    raw_pass_types = {
        "ExactSymbolicPass",
        "ExactConstructivePass",
        "ExhaustiveFinitePass",
        "ReductionProofPass",
    }
    rows: list[dict[str, Any]] = []
    for catalog_result in LoadCatalog():
        identifier = str(catalog_result["ResultID"])
        for proof_goal in catalog_result["ProofGoalResults"]:
            proof_goal_id = str(proof_goal["ProofGoalID"])
            source_type = str(proof_goal["Classification"])
            source_title = str(proof_goal["Title"])
            if source_type in {"LeanKernelProofReferenceCheck", "LeanKernelProof"}:
                coverage = coverage_rows.get(proof_goal_id)
                if coverage is None or coverage["formalization_status"] != "lean_closed":
                    raise ValueError(f"Missing Lean closure metadata for {proof_goal_id}")
                title = "Kernel-checked integrated theorem" if "written-proof" in source_title.lower() or "written proof" in source_title.lower() else source_title
                proof_goal_type = "LeanKernelProof"
                machine_method = f"Lean 4 kernel proof via {coverage['lean_declaration']}"
                closure_status = "LeanKernelProofPass"
                notes = coverage["note_en"]
            elif source_type in raw_pass_types:
                title = source_title
                proof_goal_type = source_type
                machine_method = str(proof_goal["ProofMethod"])
                closure_status = source_type
                notes = "Exact Wolfram source-catalog result, independently linked to the registered Lean declarations and proof replay. " + str(proof_goal.get("Note", ""))
            elif source_type == "LeanKernelProofAndExactProofReplay" and proof_goal_id in existing_rows:
                existing = existing_rows[proof_goal_id]
                title = existing["title"]
                proof_goal_type = existing["proof_goal_type"]
                machine_method = existing["machine_method"]
                closure_status = existing["machine_status"]
                notes = existing["notes"]
            else:
                raise ValueError(f"No machine-closure metadata rule for {proof_goal_id}: {source_type}")
            rows.append(
                {
                    "proof_goal_id": proof_goal_id,
                    "result_id": identifier,
                    "title": title,
                    "proof_goal_type": proof_goal_type,
                    "mandatory": True,
                    "machine_method": machine_method,
                    "expected_exact_result": proof_goal["Expected"],
                    "machine_status": closure_status,
                    "written_proof_anchor": f"proofs/en/results/{identifier}.tex#proof:{identifier}",
                    "source_dependencies": catalog_result["SourceReference"],
                    "failure_effect": "A failed mandatory proof record blocks the registered result and the canonical release; a written proof cannot substitute for a failed or absent machine-checkable proof.",
                    "notes": notes,
                }
            )
    if len(rows) != 218 or len({row["proof_goal_id"] for row in rows}) != 218:
        raise ValueError("The public proof-goal registry must preserve 218 unique proof goals")
    WriteTsv(ROOT / "registry" / "proof_goal_registry.tsv", rows, PROOF_GOAL_FIELDS)
    return rows


def BuildResultStatus(results: Sequence[Mapping[str, Any]]) -> list[dict[str, Any]]:
    catalog_results = {str(catalog_result["ResultID"]): catalog_result for catalog_result in LoadCatalog()}
    rows: list[dict[str, Any]] = []
    for result in results:
        identifier = str(result["result_id"])
        catalog_result = catalog_results[identifier]
        rows.append(
            {
                "result_id": identifier,
                "machine_status": "MachineClosed",
                "dissertation_proof_status": ProofStatusFor(catalog_result),
                "machine_report": "verification/reports/machine_verification.json",
                "written_proof_en": f"proofs/en/results/{identifier}.tex",
                "written_proof_pt_BR": f"proofs/pt_BR/results/{identifier}.tex",
                "statement_sha256": result["statement_sha256"],
                "status_explanation": "MachineClosed means that every registered proof goal is discharged by an accepted proof of its declared method under the canonical formal statement, exact assumptions, source transcriptions, and explicit trusted-foundation dependencies. Lean-backed goals additionally require the pinned build, exact declaration map, axiom-policy audit, forbidden-token audit, and fresh kernel check; Wolfram performs a reference check rather than claiming an independent proof for those goals. The bilingual written proof remains explanatory rather than substitutive evidence.",
            }
        )
    fields = ["result_id", "machine_status", "dissertation_proof_status", "machine_report", "written_proof_en", "written_proof_pt_BR", "statement_sha256", "status_explanation"]
    WriteTsv(ROOT / "registry" / "result_status.tsv", rows, fields)
    return rows


def BuildClaimBudget() -> list[dict[str, Any]]:
    metadata = LoadMetadata()
    translations = ReadJson(ROOT / "locales" / "claim_text_pt_BR.json")
    rows: list[dict[str, Any]] = []
    for claim in metadata["claims"]:
        identifiers = [value.strip() for value in str(claim["result_ids"]).split(";") if value.strip() and value.strip() != "not_applicable"]
        result_rows = {str(row["id"]): row for row in metadata["results"]}
        citations = sorted({key for identifier in identifiers for key in str(result_rows.get(identifier, {}).get("citation_keys", "")).split(";") if key})
        figures = sorted({value for identifier in identifiers for value in FigureIdsFor(identifier.split("-", 1)[0], identifier).split(";")})
        tables = sorted({value for identifier in identifiers for value in TableIdsFor(identifier.split("-", 1)[0]).split(";")})
        rows.append(
            {
                "claim_id": claim["claim_id"],
                "result_ids": claim["result_ids"],
                "one_sentence_claim_en": claim["exact_final_proposition"],
                "one_sentence_claim_pt_BR": str(translations[claim["claim_id"]]),
                "status": claim["status"],
                "chapter": claim["chapter"],
                "allowed_strength": claim["allowed_strength"],
                "prohibited_upcast": claim["prohibited_upcast"],
                "primary_evidence": claim["primary_evidence"],
                "figures": ";".join(figures) or "not_applicable",
                "tables": ";".join(tables) or "not_applicable",
                "citations": ";".join(citations) or "not_applicable",
            }
        )
    fields = ["claim_id", "result_ids", "one_sentence_claim_en", "one_sentence_claim_pt_BR", "status", "chapter", "allowed_strength", "prohibited_upcast", "primary_evidence", "figures", "tables", "citations"]
    WriteTsv(ROOT / "registry" / "claim_budget.tsv", rows, fields)
    return rows


def BuildSourceClaimCrosswalk() -> list[dict[str, Any]]:
    metadata = LoadMetadata()
    rows: list[dict[str, Any]] = []
    for claim in metadata["claims"]:
        rows.append(
            {
                "record_id": claim["claim_id"],
                "record_type": "claim",
                "result_ids": claim["result_ids"],
                "citation_keys": "not_applicable",
                "exact_result_or_role": claim["exact_final_proposition"],
                "evidence_route": claim["primary_evidence"],
                "scope_ceiling": claim["prohibited_upcast"],
                "reproducibility_level": "R0_written_or_exact_machine_record",
            }
        )
    for application in metadata["applications"]:
        rows.append(
            {
                "record_id": application["stable_public_id"],
                "record_type": "source_facing_application",
                "result_ids": application["dependency_result_ids"],
                "citation_keys": application["citation_keys"],
                "exact_result_or_role": application["exact_source_facing_result"],
                "evidence_route": application["proof_or_audit_route"],
                "scope_ceiling": application["nonclaim_or_ceiling"],
                "reproducibility_level": "R0_source_facing_formal_replay",
            }
        )
    fields = ["record_id", "record_type", "result_ids", "citation_keys", "exact_result_or_role", "evidence_route", "scope_ceiling", "reproducibility_level"]
    WriteTsv(ROOT / "registry" / "source_claim_crosswalk.tsv", rows, fields)
    return rows


def BuildDependencyEdges() -> list[dict[str, Any]]:
    rows = [
        {
            "source_result_id": edge["prerequisite_id"],
            "target_result_id": edge["dependent_id"],
            "dependency_type": edge["relation_type"],
            "authoritative_basis": edge["authoritative_basis"],
            "notes": edge["notes"],
        }
        for edge in LoadMetadata()["dependency_edges"]
    ]
    WriteTsv(ROOT / "registry" / "result_dependency_edges.tsv", rows, ["source_result_id", "target_result_id", "dependency_type", "authoritative_basis", "notes"])
    return rows


def BuildAssetCrosswalk(results: Sequence[Mapping[str, Any]]) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    for result in results:
        identifier = str(result["result_id"])
        group = str(result["group"])
        rows.append(
            {
                "result_id": identifier,
                "written_proof_files": f"proofs/en/results/{identifier}.tex;proofs/pt_BR/results/{identifier}.tex",
                "wolfram_catalog_id": identifier,
                "python_checks": PythonChecksFor(group),
                "canonical_data_files": DataFilesFor(group),
                "figure_ids": FigureIdsFor(group, identifier),
                "table_ids": TableIdsFor(group),
                "application_ids": ApplicationIdsFor(identifier),
                "chapter": result["chapter"],
                "review_notes": "The mapping preserves stable identity and keeps machine verification distinct from written proof closure.",
            }
        )
    fields = ["result_id", "written_proof_files", "wolfram_catalog_id", "python_checks", "canonical_data_files", "figure_ids", "table_ids", "application_ids", "chapter", "review_notes"]
    WriteTsv(ROOT / "registry" / "result_asset_crosswalk.tsv", rows, fields)
    return rows


def FileHashOrPending(relative_path: str) -> str:
    path = ROOT / relative_path
    return Sha256File(path) if path.is_file() else "generated_during_build"


def BuildFigureManifest() -> list[dict[str, Any]]:
    requirements = ReadTsv(ROOT / "registry" / "figure_build_spec.tsv")
    rows: list[dict[str, Any]] = []
    for requirement in requirements:
        figure_id = requirement["figure_id"]
        short_name = requirement["short_name"]
        width_field = "full_width_mm" if requirement["assigned_width"] == "full" else "single_column_mm"
        for locale in ["en", "pt_BR"]:
            title = requirement["title_en"] if locale == "en" else requirement["title_pt_BR"]
            rows.append(
                {
                    "figure_id": figure_id,
                    "locale": locale,
                    "title": title,
                    "placement": "appendix" if figure_id.startswith("FIG-A") else "main",
                    "intended_width_mm": requirement[width_field],
                    "source_data": requirement["canonical_inputs"],
                    "source_spec": requirement["figure_source_spec"],
                    "source_sha256": FileHashOrPending(requirement["figure_source_spec"]),
                    "svg": f"figures/{locale}/{'appendix' if figure_id.startswith('FIG-A') else 'main'}/{figure_id}_{short_name}_{locale}.svg",
                    "pdf": f"figures/{locale}/{'appendix' if figure_id.startswith('FIG-A') else 'main'}/{figure_id}_{short_name}_{locale}.pdf",
                    "png": f"figures/{locale}/{'appendix' if figure_id.startswith('FIG-A') else 'main'}/{figure_id}_{short_name}_{locale}.png",
                    "caption_file": f"figures/captions/captions_{locale}.tsv",
                    "alt_text_file": f"figures/alt_text/alt_text_{locale}.tsv",
                    "cross_engine_required": requirement["cross_engine_required"],
                    "result_ids": requirement["primary_ids"],
                }
            )
    fields = ["figure_id", "locale", "title", "placement", "intended_width_mm", "source_data", "source_spec", "source_sha256", "svg", "pdf", "png", "caption_file", "alt_text_file", "cross_engine_required", "result_ids"]
    WriteTsv(ROOT / "registry" / "figure_manifest.tsv", rows, fields)
    return rows


def BuildTableManifest() -> list[dict[str, Any]]:
    requirements = ReadTsv(ROOT / "registry" / "table_requirements_source.tsv")
    rows: list[dict[str, Any]] = []
    for requirement in requirements:
        table_id = requirement["table_id"]
        short_name = table_id.lower().replace("-", "_")
        for locale in ["en", "pt_BR"]:
            rows.append(
                {
                    "table_id": table_id,
                    "locale": locale,
                    "title": requirement["title_en"] if locale == "en" else requirement["title_pt_BR"],
                    "canonical_sources": requirement["canonical_sources"],
                    "latex": f"tables/{locale}/{table_id}_{short_name}_{locale}.tex",
                    "tsv": f"tables/{locale}/{table_id}_{short_name}_{locale}.tsv",
                    "markdown": f"tables/{locale}/{table_id}_{short_name}_{locale}.md",
                    "scope_note": requirement["scope_or_validation_note"],
                }
            )
    fields = ["table_id", "locale", "title", "canonical_sources", "latex", "tsv", "markdown", "scope_note"]
    WriteTsv(ROOT / "registry" / "table_manifest.tsv", rows, fields)
    return rows


def BuildChapterAssetMap(results: Sequence[Mapping[str, Any]], claims: Sequence[Mapping[str, Any]]) -> list[dict[str, Any]]:
    rows: list[dict[str, Any]] = []
    chapters = sorted({str(row["chapter"]) for row in results} | {str(row["chapter"]) for row in claims})
    for chapter in chapters:
        result_ids = [str(row["result_id"]) for row in results if str(row["chapter"]) == chapter]
        claim_ids = [str(row["claim_id"]) for row in claims if str(row["chapter"]) == chapter]
        figures = sorted({value for row in results if str(row["chapter"]) == chapter for value in FigureIdsFor(str(row["group"]), str(row["result_id"])).split(";")})
        tables = sorted({value for row in results if str(row["chapter"]) == chapter for value in TableIdsFor(str(row["group"])).split(";")})
        rows.append(
            {
                "chapter": chapter,
                "result_ids": ";".join(result_ids) or "not_applicable",
                "claim_ids": ";".join(claim_ids) or "not_applicable",
                "figure_ids": ";".join(figures) or "not_applicable",
                "table_ids": ";".join(tables) or "not_applicable",
                "scope_note_en": "Assets support only the registered result and claim strength for this chapter.",
                "scope_note_pt_BR": "Os materiais sustentam somente a força registrada dos resultados e das afirmações deste capítulo.",
            }
        )
    fields = ["chapter", "result_ids", "claim_ids", "figure_ids", "table_ids", "scope_note_en", "scope_note_pt_BR"]
    WriteTsv(ROOT / "registry" / "chapter_asset_map.tsv", rows, fields)
    return rows


def BuildReleaseMetadata() -> list[dict[str, Any]]:
    rows = [
        {"field": "author_orcid", "value": "", "required_before_archival_release": "false", "authority": "author", "reason": "No ORCID was inferable from the repository; omission does not block local artifact validation."},
        {"field": "archival_doi", "value": "", "required_before_archival_release": "false", "authority": "archive", "reason": "A DOI has not been minted and is not claimed."},
        {"field": "project_license_choice", "value": "all_rights_reserved_pending_author_choice", "required_before_archival_release": "true", "authority": "author", "reason": "The repository does not establish a public software or documentation license."},
        {"field": "release_version", "value": "0.1.0-pre-dissertation", "required_before_archival_release": "false", "authority": "artifact", "reason": "Descriptive package version; not a DOI or publication claim."},
    ]
    WriteTsv(ROOT / "registry" / "release_metadata_required.tsv", rows, ["field", "value", "required_before_archival_release", "authority", "reason"])
    return rows


def BuildSourceConflicts() -> list[dict[str, Any]]:
    resolutions = {
        "C01": "The executable package and reports use their declared public paths and are covered by package manifests.",
        "C02": "The registry hashes the canonical English catalog statement; the Wolfram report is synchronized to those hashes during the full build.",
        "C03": "APP-PATER, APP-WALKER, and APP-CABRERA were assigned as application identifiers without changing the 68 registered result IDs.",
        "C04": "result_status.tsv preserves independent machine and explanatory written-proof axes while requiring machine-proof closure for every released result.",
        "C05": "One bilingual proof file per stable result ID is generated and compiled.",
        "C06": "MAX-G3 remains one ID for the exact executable compiler and its foundation-relative semantic and object-size requirements; no universal-real classification is registered.",
        "C07": "MAX-G4 records the exact duplicate-free binary selector bridge and local charge bounds; conventional coNP-completeness is conditional on ExecutableCNFConventionalBoundary.",
        "C08": "CHG-B7 retains one stable ID while its proof separates inherited scale gauge from new family-specific phase laws.",
        "C09": "Inherited results use complete self-contained specialization proofs unless an exact imported locator is verified.",
        "C10": "The concise catalog statement is the cross-engine registry statement; its full quantified statement or application record remains in the written proof.",
        "C11": "Expected is serialized losslessly into expected_exact_result.",
        "C12": "The immutable baseline records the former 44 result-level and 45 proof-goal-level gaps; final reports require closure of 68 registered results and discharge of 218 proof goals.",
        "C13": "English summaries distinguish the raw surplus of 16 from eight above the strict-majority threshold.",
        "C14": "Mandarin files document the separate 616-row scope ledger and 639-row corrected table; final counts are 622, 13, and 4.",
        "C15": "Applications and data demonstrations remain separate kinds and are not counted as new theorem ownership.",
        "C16": "Placement is recorded independently from evidential and mandatory status.",
        "C17": "Regression withdrawal conditions are stated directly in the public registry and remain subordinate to the normative finite specification.",
        "C18": "Public TeX proofs carry the current result status; earlier filenames have no evidential role in the package.",
        "C19": "The Wolfram interface replays the exact source catalogue and provides a separate fail-closed semantic proof mode.",
        "C20": "Application and data crosswalks state R0/R1 scope and external dependencies without end-to-end upcast.",
        "C21": "The canonical support-birth balance and both readable proofs use the quotient form, consistent with the registered Lambert identity and coefficient limit.",
    }
    topics = {
        "C01": ("Executable artifact location", "Earlier records named superseded output locations.", "The public package requires one stable executable and report location."),
        "C02": ("Statement-hash correspondence", "The original catalog exposed statements without per-result hashes.", "The public registry requires a per-result statement digest and stale-correspondence check."),
        "C03": ("Application identity", "Three source-facing applications were promoted after the 68-result namespace was fixed.", "Applications require stable identities without expanding or renumbering the result namespace."),
        "C04": ("Independent proof-status axes", "The baseline had forty-four nonmechanized catalog results.", "The final release requires machine-checkable proofs while retaining written proofs as a separate explanatory axis."),
        "C05": ("One proof file per stable result", "The mathematics was distributed across larger source dossiers.", "The public package requires bilingual result-addressable proof files."),
        "C06": ("MAX-G3 proof structure", "Earlier wording joined the compiler to an unproved standard complexity classification.", "The executable catalog preserves one stable MAX-G3 identifier for exact compiler semantics and foundation-relative object-size bounds."),
        "C07": ("MAX-G4 restricted complexity result", "Earlier wording stated an unconditional class result and imported a separate universal-real cell.", "The duplicate-free binary selector bridge and local charges belong to MAX-G4; conventional coNP-completeness is a conditional boundary theorem."),
        "C08": ("CHG-B7 mixed ancestry", "Common positive scale invariance is inherited.", "Family-specific phase laws under the same stable ID are project results."),
        "C09": ("Imported-result proof form", "Several results have generic mathematical ancestry rather than an exact imported theorem locator.", "A self-contained specialization proof is required unless an exact citation is verified."),
        "C10": ("Catalog versus full result statement", "Executable catalog statements are concise summaries.", "Written proofs contain the full quantified statement or application record and delimitations."),
        "C11": ("Expected-result field naming", "The executable report uses the field `Expected`.", "The public proof-goal registry requires the lossless field `expected_exact_result`."),
        "C12": ("Result and proof-goal denominators", "The baseline contained forty-four nonmechanized results and forty-five nonmechanized proof goals.", "The final denominator remains sixty-eight registered results and 218 registered proof goals, all of which must close."),
        "C13": ("English majority arithmetic", "The raw difference between 29 and 13 speakers is 16.", "The count 29 is eight above the strict-majority threshold."),
        "C14": ("Mandarin ledger denominators", "The construction-scope ledger contains 616 coarse rows.", "The corrected 639-row table yields 622 matches, 13 counterexamples, and four refusals."),
        "C15": ("Applications versus theorem ownership", "Application and data rows are mandatory catalog results.", "Their mandatory status does not convert them into original theorem ownership."),
        "C16": ("Placement versus authority", "Many complete secondary results are placed in appendices.", "Appendix placement does not reduce a result's registered evidential status."),
        "C17": ("Regression withdrawal conditions", "The finite specification defines fifteen mandatory regression results.", "The ownership matrix does not provide a separate withdrawal row for each regression."),
        "C18": ("Current public proof identity", "Some development sources used provisional filenames.", "Stable public result IDs and proof files control current correspondence."),
        "C19": ("Verification exit modes", "The Wolfram source catalogue separates exact calculations from semantic proof checks.", "Machine-closed execution requires the semantic proof layer and exits nonzero on any missing proof."),
        "C20": ("Reproducibility levels", "Source-facing applications replay formal source objects.", "Corpus demonstrations replay reduced ledgers with separately stated external dependencies."),
        "C21": ("FLUX-D4 support-birth balance", "The earlier readable derivation and one canonical response component multiplied by -log(t).", "The registered Lambert normal-form identity and normalized coefficient limit require division by -log(t)."),
    }
    rows: list[dict[str, Any]] = []
    for identifier in sorted(topics):
        topic, evidence_a, evidence_b = topics[identifier]
        required_resolution = "Apply the normative hierarchy and preserve stable result identity, exact scope, and independent evidence statuses."
        no_invention_rule = "Do not invent a result, proof status, application identity, or empirical conclusion to remove the discrepancy."
        if identifier == "C21":
            required_resolution = "Replace the false product balance by the quotient balance in the canonical replay and both readable proofs, then regenerate every dependent hash, proof record, mutant, and report."
            no_invention_rule = "Do not alter Gamma, C, the Lambert-W solution, or the normalized remainder premise to preserve the false product wording."
        rows.append({"conflict_id": identifier, "severity": "material", "topic": topic, "evidence_a": evidence_a, "evidence_b": evidence_b, "required_resolution": required_resolution, "no_invention_rule": no_invention_rule, "resolution": resolutions[identifier], "status": "resolved"})
    fields = ["conflict_id", "severity", "topic", "evidence_a", "evidence_b", "required_resolution", "no_invention_rule", "resolution", "status"]
    WriteTsv(ROOT / "formal" / "reports" / "source_conflicts.tsv", rows, fields)
    return rows


def BuildRegistries() -> dict[str, int]:
    results = BuildResultRegistry()
    proof_goals = BuildProofGoalRegistry()
    statuses = BuildResultStatus(results)
    claims = BuildClaimBudget()
    source_rows = BuildSourceClaimCrosswalk()
    assets = BuildAssetCrosswalk(results)
    edges = BuildDependencyEdges()
    figures = BuildFigureManifest()
    tables = BuildTableManifest()
    chapters = BuildChapterAssetMap(results, claims)
    release_metadata = BuildReleaseMetadata()
    conflicts = BuildSourceConflicts()
    counts = {
        "results": len(results),
        "proof_goals": len(proof_goals),
        "result_status_rows": len(statuses),
        "claims": len(claims),
        "source_claim_rows": len(source_rows),
        "asset_crosswalk_rows": len(assets),
        "dependency_edges": len(edges),
        "figure_manifest_rows": len(figures),
        "table_manifest_rows": len(tables),
        "chapter_rows": len(chapters),
        "release_metadata_rows": len(release_metadata),
        "source_conflicts": len(conflicts),
    }
    WriteJson(ROOT / "registry" / "registry_build_counts.json", counts)
    return counts
