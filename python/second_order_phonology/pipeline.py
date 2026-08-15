from __future__ import annotations

import json
import subprocess
import sys
import time
from collections import Counter
from pathlib import Path
from typing import Any, Callable

from .asset_validation import ValidateBilingualAssets
from .audit import AuditSources
from .bibliography import RunBiberValidation
from .checks import CompareEngines, VerifyApplications, VerifyContinuousHg, VerifyDemonstrations, VerifyFiniteCalculus, VerifyMaxEnt
from .common import AuditOutputDirectory, ROOT, ReadJson, ReadTsv, Sha256File, WriteJson
from .data_build import BuildCanonicalData
from .latex_build import CompileProofCompendia
from .machine_closure import CleanMachineClosureReports, ValidateMachineClosure
from .registries import BuildFigureManifest, BuildRegistries
from .release import BuildRelease, CleanGenerated, WriteReleaseNotes
from .reports import EnrichMachineReport, PromoteMachineClosureReport
from .style import ValidatePythonStyle
from .validation import ValidatePackage
from .wolfram import RunWolfram


MAX_STAGE_SECONDS = 3600


def ProcessOutput(value: str | bytes | None) -> str:
    if value is None:
        return ""
    if isinstance(value, bytes):
        return value.decode("utf-8", errors="replace")
    return value


def RunCallable(name: str, function: Callable[[], Any], stages: list[dict[str, Any]]) -> Any:
    started = time.perf_counter()
    result = function()
    status = result.get("status", "PASS") if isinstance(result, dict) else "PASS"
    stages.append({"stage": name, "status": status, "elapsed_seconds": round(time.perf_counter() - started, 6), "command": "internal deterministic library call"})
    if status == "FAIL":
        raise RuntimeError(f"Stage failed: {name}")
    return result


def RunCommand(name: str, arguments: list[str], stages: list[dict[str, Any]]) -> None:
    started = time.perf_counter()
    command = [sys.executable, *arguments]
    display = "python3 " + " ".join(arguments)
    try:
        completed = subprocess.run(command, cwd=ROOT, capture_output=True, text=True, encoding="utf-8", check=False, timeout=MAX_STAGE_SECONDS)
    except subprocess.TimeoutExpired as error:
        output = ProcessOutput(error.stdout) + ProcessOutput(error.stderr)
        stages.append({"stage": name, "status": "FAIL", "elapsed_seconds": round(time.perf_counter() - started, 6), "command": display, "output": output[-2000:]})
        raise RuntimeError(f"Stage exceeded {MAX_STAGE_SECONDS} seconds: {name}: {output[-1000:]}") from error
    stages.append({"stage": name, "status": "PASS" if completed.returncode == 0 else "FAIL", "elapsed_seconds": round(time.perf_counter() - started, 6), "command": display, "output": (completed.stdout + completed.stderr)[-2000:]})
    if completed.returncode != 0:
        raise RuntimeError(f"Stage failed: {name}: {(completed.stdout + completed.stderr)[-1000:]}")


def RunExternalCommand(
    name: str,
    arguments: list[str],
    stages: list[dict[str, Any]],
    working_directory: Path,
) -> None:
    started = time.perf_counter()
    display = " ".join(arguments)
    try:
        completed = subprocess.run(
            arguments,
            cwd=working_directory,
            capture_output=True,
            text=True,
            encoding="utf-8",
            check=False,
            timeout=MAX_STAGE_SECONDS,
        )
    except subprocess.TimeoutExpired as error:
        output = ProcessOutput(error.stdout) + ProcessOutput(error.stderr)
        stages.append(
            {
                "stage": name,
                "status": "FAIL",
                "elapsed_seconds": round(time.perf_counter() - started, 6),
                "command": display,
                "output": output[-2000:],
            }
        )
        raise RuntimeError(f"Stage exceeded {MAX_STAGE_SECONDS} seconds: {name}: {output[-1000:]}") from error
    stages.append(
        {
            "stage": name,
            "status": "PASS" if completed.returncode == 0 else "FAIL",
            "elapsed_seconds": round(time.perf_counter() - started, 6),
            "command": display,
            "output": (completed.stdout + completed.stderr)[-2000:],
        }
    )
    if completed.returncode != 0:
        raise RuntimeError(
            f"Stage failed: {name}: {(completed.stdout + completed.stderr)[-1000:]}"
        )


def BuildSummary(stages: list[dict[str, Any]], command: str, wolfram_rerun: bool, machine_closed: bool) -> dict[str, Any]:
    results = ReadTsv(ROOT / "registry" / "result_registry.tsv")
    statuses = ReadTsv(ROOT / "registry" / "result_status.tsv")
    datasets = ReadTsv(ROOT / "data" / "dataset_manifest.tsv")
    figures = ReadTsv(ROOT / "registry" / "figure_manifest.tsv")
    tables = ReadTsv(ROOT / "registry" / "table_manifest.tsv")
    bibliography = ReadJson(ROOT / "bibliography" / "bibliography_validation.json")
    machine = ReadJson(ROOT / "verification" / "reports" / "machine_verification.json")
    agreement = ReadTsv(ROOT / "verification" / "reports" / "cross_engine_agreement.tsv")
    complete_agreement = ReadJson(ROOT / "verification" / "reports" / "cross_engine_proofs.json") if (ROOT / "verification" / "reports" / "cross_engine_proofs.json").is_file() else None
    release_checksum = ROOT / "release" / "second_order_phonology_artifact.zip.sha256"
    machine_counts = Counter(row["machine_status"] for row in statuses)
    proof_counts = Counter(row["dissertation_proof_status"] for row in statuses)
    written_proof_present = [row["result_id"] for row in statuses if row["dissertation_proof_status"].strip()]
    all_machine_closed = machine_counts == Counter({"MachineClosed": 68})
    machine_closure = ValidateMachineClosure() if machine_closed else {"status": "NOT_REQUESTED", "result_count": 0, "proof_goal_count": 0, "failure_count": 0, "failures": []}
    report = {
        "status": "PASS" if all(row["status"] == "PASS" for row in stages) and all_machine_closed and len(written_proof_present) == 68 else "FAIL",
        "command": command,
        "wolfram_rerun": wolfram_rerun,
        "machine_closed_requested": machine_closed,
        "machine_closure_status": machine_closure["status"],
        "machine_closure_failures": machine_closure["failures"],
        "result_count": len(results),
        "flagship_result_count": sum(row["review_priority"] == "flagship" for row in results),
        "machine_complete_result_count": machine["CompleteResultCount"],
        "machine_status_counts": dict(sorted(machine_counts.items())),
        "written_proof_status_counts": dict(sorted(proof_counts.items())),
        "written_proof_result_count": len(written_proof_present),
        "imported_result_count": proof_counts.get("ImportedTheoremWithExactCitation", 0) + proof_counts.get("CompleteSpecializationProof", 0),
        "proof_goal_status_counts": machine["ProofGoalStatusCounts"],
        "cross_engine_comparisons": complete_agreement["agreement_count"] if machine_closed and complete_agreement is not None else len(agreement),
        "cross_engine_disagreements": complete_agreement["disagreement_count"] if machine_closed and complete_agreement is not None else sum(row["agreement"] != "true" for row in agreement),
        "reference_count": bibliography["counts"]["compile_entries"],
        "biber_warning_count": int(bibliography["biber"]["compile_warnings"]) + int(bibliography["biber"]["provenance_warnings"]),
        "figure_counts": {locale: {extension: sum(row["locale"] == locale and (ROOT / row[extension]).is_file() for row in figures) for extension in ["svg", "pdf", "png"]} for locale in ["en", "pt_BR"]},
        "table_counts": {locale: {extension: sum(row["locale"] == locale and (ROOT / row[extension]).is_file() for row in tables) for extension in ["latex", "tsv", "markdown"]} for locale in ["en", "pt_BR"]},
        "canonical_dataset_count": len(datasets),
        "canonical_data_row_total": sum(int(row["row_count"]) for row in datasets),
        "release_sha256": release_checksum.read_text(encoding="utf-8").split()[0] if release_checksum.is_file() else "not_built",
        "stages": stages,
        "remaining_limitations": (["Machine closure is relative to the explicitly registered trusted foundation and exact source transcriptions."] if machine_closed else ["The working build does not assert canonical machine-closed release status."]) + ["The package is a result-specific proof-carrying artifact, not a general-purpose proof assistant.", "Third-party source PDFs and corpus media are not redistributed.", "ORCID, DOI, and a public reuse license remain under human authority."],
    }
    if machine_closed and machine_closure["status"] != "PASS":
        report["status"] = "FAIL"
    WriteJson(AuditOutputDirectory() / "build_report.json", report)
    WriteBuildMarkdown(report)
    return report


def WriteBuildMarkdown(report: dict[str, Any]) -> None:
    lines = [
        "# Build report",
        "",
        f"Status: **{report['status']}**",
        "",
        f"- Registered results: {report['result_count']}",
        f"- Flagship results: {report['flagship_result_count']}",
        f"- Machine-complete results: {report['machine_complete_result_count']}",
        f"- Machine-closed release requested: {report['machine_closed_requested']}",
        f"- Machine-closure gate: {report['machine_closure_status']}",
        f"- Results with registered written proofs: {report['written_proof_result_count']}",
        f"- Cross-engine comparisons: {report['cross_engine_comparisons']}",
        f"- Cross-engine disagreements: {report['cross_engine_disagreements']}",
        f"- Bibliography entries: {report['reference_count']}",
        f"- Biber warnings: {report['biber_warning_count']}",
        f"- Canonical datasets: {report['canonical_dataset_count']}",
        f"- Canonical rows: {report['canonical_data_row_total']}",
        f"- Release SHA-256: {report['release_sha256']}",
        "",
        "## Executed stages",
        "",
        "| Stage | Status | Seconds | Command |",
        "|---|---|---:|---|",
    ]
    for stage in report["stages"]:
        lines.append(f"| {stage['stage']} | {stage['status']} | {stage['elapsed_seconds']} | {stage['command']} |")
    lines.extend(["", "## Remaining limitations", ""])
    lines.extend(f"- {value}" for value in report["remaining_limitations"])
    (AuditOutputDirectory() / "build_report.md").write_text("\n".join(lines) + "\n", encoding="utf-8", newline="\n")


def BuildAll(clean: bool, with_wolfram: bool, figures_only: bool, tables_only: bool, strict: bool, command: str, machine_closed: bool = False) -> dict[str, Any]:
    stages: list[dict[str, Any]] = []
    if machine_closed and (not clean or not with_wolfram or not strict or figures_only or tables_only):
        raise ValueError("machine-closed mode requires a clean, Wolfram-enabled, strict, complete build")
    if clean:
        RunCallable("clean", CleanGenerated, stages)
    if machine_closed:
        RunCallable("clean_machine_closure_reports", CleanMachineClosureReports, stages)
        result = RunCallable(
            "wolfram_source_catalog_rebuild",
            lambda: RunWolfram("dissertation-release", True),
            stages,
        )
        if not result["accepted_exit"]:
            raise RuntimeError("Wolfram source-catalog rebuild returned an unaccepted exit code")
    if figures_only:
        RunCommand("generate_figures", ["scripts/generate_figures.py"], stages)
        RunCallable("refresh_figure_manifest", BuildFigureManifest, stages)
        RunCallable("validate_bilingual_assets", ValidateBilingualAssets, stages)
        return {"status": "PASS", "stages": stages}
    if tables_only:
        RunCommand("generate_tables", ["scripts/generate_tables.py"], stages)
        RunCallable("validate_bilingual_assets", ValidateBilingualAssets, stages)
        return {"status": "PASS", "stages": stages}
    RunCallable("build_registries", BuildRegistries, stages)
    RunCallable("canonical_data", BuildCanonicalData, stages)
    if not machine_closed:
        RunCallable("finite_calculus", VerifyFiniteCalculus, stages)
    RunCallable("continuous_hg", VerifyContinuousHg, stages)
    RunCallable("finite_maxent", VerifyMaxEnt, stages)
    RunCallable("applications", VerifyApplications, stages)
    RunCallable("demonstrations", VerifyDemonstrations, stages)
    RunCallable("bibliography", RunBiberValidation, stages)
    RunCallable("proof_compilation", CompileProofCompendia, stages)
    if not machine_closed:
        RunCallable("report_correspondence", EnrichMachineReport, stages)
    if with_wolfram:
        if not machine_closed:
            result = RunCallable("wolfram_dissertation_release", lambda: RunWolfram("dissertation-release", True), stages)
            if not result["accepted_exit"]:
                raise RuntimeError("Wolfram dissertation-release mode returned an unaccepted exit code")
        RunCallable("report_correspondence_after_wolfram", EnrichMachineReport, stages)
    if machine_closed:
        RunCommand("build_formal_specs", ["scripts/build_formal_specs.py"], stages)
        RunCommand("synchronize_proof_metadata", ["scripts/synchronize_proof_metadata.py"], stages)
        RunCallable("proof_compilation_after_metadata", CompileProofCompendia, stages)
        RunCommand("build_foundation_proofs", ["scripts/build_foundation_proofs.py"], stages)
        RunExternalCommand(
            "lean_verification",
            ["sh", "scripts/verify.sh"],
            stages,
            ROOT / "lean",
        )
        RunCommand("generate_proofs", ["scripts/generate_proofs.py", "--with-wolfram"], stages)
        RunCommand("check_proofs", ["scripts/check_proofs.py", "--all", "--strict", "--machine-closed"], stages)
        RunCommand("assumption_reports", ["scripts/build_assumption_reports.py"], stages)
        RunCommand("mutation_suite", ["scripts/run_mutation_suite.py", "--all", "--strict"], stages)
        RunCommand("statement_correspondence", ["scripts/validate_statement_correspondence.py", "--strict"], stages)
        RunCallable("promote_machine_closure_report", PromoteMachineClosureReport, stages)
        RunCallable("finite_calculus_after_machine_closure", VerifyFiniteCalculus, stages)
    RunCallable("cross_engine_agreement", CompareEngines, stages)
    if machine_closed:
        RunCommand("complete_cross_engine_reports", ["scripts/build_cross_engine_reports.py"], stages)
    RunCommand("generate_tables", ["scripts/generate_tables.py"], stages)
    RunCommand("generate_figures", ["scripts/generate_figures.py"], stages)
    RunCallable("refresh_figure_manifest", BuildFigureManifest, stages)
    RunCallable("validate_bilingual_assets", ValidateBilingualAssets, stages)
    RunCallable("python_style", ValidatePythonStyle, stages)
    RunCallable("source_audit", AuditSources, stages)
    if strict:
        if machine_closed:
            RunCommand("kernel_tests", ["scripts/run_kernel_tests.py", "--strict"], stages)
            RunCommand("formal_closure_reports", ["scripts/build_formal_closure_reports.py"], stages)
            RunCallable("machine_closure_gate_before_release", ValidateMachineClosure, stages)
        else:
            RunCommand("tests", ["-m", "unittest", "discover", "-s", "verification/python/tests", "-p", "test_*.py"], stages)
        RunCallable("release_notes", lambda: (WriteReleaseNotes() or {"status": "PASS"}), stages)
        RunCallable("pre_release_validation", lambda: ValidatePackage(True, False, machine_closed), stages)
        RunCallable("release", BuildRelease, stages)
        RunCallable("strict_validation", lambda: ValidatePackage(True, True, machine_closed), stages)
    return BuildSummary(stages, command, with_wolfram, machine_closed)
