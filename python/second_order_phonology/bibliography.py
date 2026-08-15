from __future__ import annotations

import re
import shutil
import subprocess
from pathlib import Path
from typing import Any

from .common import ROOT, ReadTsv, WriteJson


def BibKeys(path: Path) -> list[str]:
    text = path.read_text(encoding="utf-8")
    return re.findall(r"(?m)^@[A-Za-z]+\{([^,]+),", text)


def RunBiberValidation() -> dict[str, Any]:
    executable = shutil.which("biber") or "/usr/local/texlive/2026/bin/universal-darwin/biber"
    build_directory = ROOT / "build" / "biber"
    build_directory.mkdir(parents=True, exist_ok=True)
    compile_path = ROOT / "bibliography" / "references.bib"
    provenance_path = ROOT / "bibliography" / "references_provenance.bib"
    compile_result = ValidateBib(executable, build_directory, compile_path, "compile")
    provenance_result = ValidateBib(executable, build_directory, provenance_path, "provenance")
    compile_keys = BibKeys(compile_path)
    provenance_keys = BibKeys(provenance_path)
    manifest = ReadTsv(ROOT / "bibliography" / "reference_manifest.tsv")
    relevance = ReadTsv(ROOT / "bibliography" / "source_relevance.tsv")
    redistribution = ReadTsv(ROOT / "bibliography" / "redistribution_audit.tsv")
    manifest_keys = [row["bibkey"] for row in manifest]
    relevance_keys = [row["bibkey"] for row in relevance]
    redistribution_keys = [row["bibkey"] for row in redistribution]
    current_status_rechecks = sum("2026-08-09" in row["notes"] for row in manifest)
    biber = {
        "version": BiberVersion(executable),
        "compile_exit_code": compile_result["exit_code"],
        "compile_warnings": compile_result["warnings"],
        "compile_errors": compile_result["errors"],
        "provenance_exit_code": provenance_result["exit_code"],
        "provenance_warnings": provenance_result["warnings"],
        "provenance_errors": provenance_result["errors"],
    }
    counts = {
        "compile_entries": len(compile_keys),
        "provenance_entries": len(provenance_keys),
        "manifest_rows": len(manifest),
        "source_relevance_rows": len(relevance),
        "redistribution_rows": len(redistribution),
        "current_status_rechecks": current_status_rechecks,
    }
    compile_set = set(compile_keys)
    bijection = {
        "keys_equal_compile_provenance": compile_set == set(provenance_keys),
        "keys_equal_compile_manifest": compile_set == set(manifest_keys),
        "keys_equal_compile_relevance": compile_set == set(relevance_keys),
        "keys_equal_compile_redistribution": compile_set == set(redistribution_keys),
    }
    errors = biber["compile_errors"] + biber["provenance_errors"]
    warnings = biber["compile_warnings"] + biber["provenance_warnings"]
    passed = all(value == 173 for key, value in counts.items() if key != "current_status_rechecks") and current_status_rechecks == 18 and len(compile_keys) == len(compile_set) and all(bijection.values()) and errors == warnings == 0 and biber["compile_exit_code"] == biber["provenance_exit_code"] == 0
    report = {
        "result": "PASS" if passed else "FAIL",
        "status": "PASS" if passed else "FAIL",
        "biber": biber,
        "counts": counts,
        "bijection": bijection,
        "biber_version": biber["version"],
        "exit_code": max(biber["compile_exit_code"], biber["provenance_exit_code"]),
        "warnings": warnings,
        "errors": errors,
        "bibliography_keys": len(compile_keys),
        "unique_bibliography_keys": len(compile_set),
        "reference_manifest_rows": len(manifest),
        "command": "biber --tool --validate-datamodel bibliography/references.bib",
    }
    WriteJson(ROOT / "bibliography" / "bibliography_validation.json", report)
    WriteBibliographyMarkdown(report)
    return report


def ValidateBib(executable: str, build_directory: Path, source: Path, stem: str) -> dict[str, int]:
    build_input = build_directory / f"{stem}.bib"
    output = build_directory / f"{stem}_validated.bib"
    shutil.copyfile(source, build_input)
    command = [executable, "--tool", "--validate-datamodel", "--output-file", output.name, build_input.name]
    completed = subprocess.run(command, cwd=build_directory, capture_output=True, text=True, encoding="utf-8", check=False, timeout=600)
    combined = completed.stdout + "\n" + completed.stderr
    log_path = build_directory / f"{stem}.bib.blg"
    if log_path.is_file():
        combined += "\n" + log_path.read_text(encoding="utf-8", errors="replace")
    return {
        "exit_code": completed.returncode,
        "warnings": len(re.findall(r"(?m)^WARN", combined)),
        "errors": len(re.findall(r"(?m)^(?:ERROR|FATAL)", combined)),
    }


def BiberVersion(executable: str) -> str:
    completed = subprocess.run([executable, "--version"], capture_output=True, text=True, encoding="utf-8", check=False, timeout=60)
    return (completed.stdout or completed.stderr).strip().splitlines()[0]


def WriteBibliographyMarkdown(report: dict[str, Any]) -> None:
    text = "\n".join([
        "# Bibliography validation",
        "",
        f"Status: **{report['status']}**",
        "",
        f"- Compile-bibliography keys: {report['counts']['compile_entries']}",
        f"- Provenance-bibliography keys: {report['counts']['provenance_entries']}",
        f"- Unique compile keys: {report['unique_bibliography_keys']}",
        f"- Reference-manifest rows: {report['counts']['manifest_rows']}",
        f"- Current-status rechecks: {report['counts']['current_status_rechecks']}",
        f"- Biber warnings across both bibliographies: {report['warnings']}",
        f"- Biber errors across both bibliographies: {report['errors']}",
        f"- Validator: {report['biber_version']}",
        "",
        "The compile bibliography contains only fields admitted by the BibLaTeX data model. Provenance and redistribution notes are kept in separate public audit files.",
        "",
    ])
    (ROOT / "bibliography" / "bibliography_validation.md").write_text(text, encoding="utf-8", newline="\n")
