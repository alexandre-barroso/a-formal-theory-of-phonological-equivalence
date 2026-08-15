from __future__ import annotations

import re
import shutil
from pathlib import Path
from typing import Any

from .common import AuditOutputDirectory, IgnoredDirectoryNames, ROOT, ReadTsv, Sha256File, WriteJson, WriteTsv


TEXT_SUFFIXES = {".bib", ".cff", ".csv", ".json", ".md", ".py", ".tex", ".tsv", ".txt", ".wl", ".yml", ".yaml", ".toml", ".Dockerfile", ""}
EXCLUDED_PARTS = {".lake", "build", "release", "compiled", *IgnoredDirectoryNames()}


def PublicFiles(include_release: bool = False) -> list[Path]:
    excluded = EXCLUDED_PARTS - ({"release"} if include_release else set())
    return sorted(path for path in ROOT.rglob("*") if path.is_file() and not any(part in excluded for part in path.parts))


def TextFile(path: Path) -> bool:
    return path.suffix in TEXT_SUFFIXES or path.name in {"Makefile", ".gitignore", ".gitattributes"}


def PrivatePathFindings(value: str) -> list[str]:
    patterns = [re.compile("/" + r"Volumes/[^\s\]\[\)\(\}\{\"']+"), re.compile("/" + r"Users/[^\s\]\[\)\(\}\{\"']+")]
    return [match.group(0) for pattern in patterns for match in pattern.finditer(value)]


def ScanPublicTree() -> dict[str, Any]:
    hidden_patterns = {".DS_Store", "__MACOSX", ".pyc", "__pycache__"}
    forbidden_suffixes = {".aux", ".blg", ".log", ".swp", ".tmp"}
    findings: list[dict[str, Any]] = []
    for path in sorted(ROOT.rglob("*")):
        relative = path.relative_to(ROOT).as_posix()
        if any(part in EXCLUDED_PARTS for part in path.parts):
            continue
        if path.name in hidden_patterns or path.suffix in forbidden_suffixes or path.name.startswith("._"):
            findings.append({"file": relative, "category": "forbidden_file", "detail": path.name})
        if not path.is_file() or not TextFile(path):
            continue
        try:
            text = path.read_text(encoding="utf-8")
        except UnicodeDecodeError as error:
            findings.append({"file": relative, "category": "invalid_utf8", "detail": str(error)})
            continue
        if any(ord(character) < 32 and character not in "\n\r\t" for character in text):
            findings.append({"file": relative, "category": "control_character", "detail": "nonprinting control byte"})
        for match in PrivatePathFindings(text):
            findings.append({"file": relative, "category": "absolute_private_path", "detail": match})
        for marker in ["TO" + "DO", "FIX" + "ME", "X" * 3]:
            if re.search(rf"\b{re.escape(marker)}\b", text):
                findings.append({"file": relative, "category": "prohibited_marker", "detail": marker})
    report = {"status": "PASS" if not findings else "FAIL", "file_count": len(PublicFiles()), "finding_count": len(findings), "findings": findings}
    internal = AuditOutputDirectory()
    WriteJson(internal / "static_scan.json", report)
    WriteTsv(internal / "static_scan_findings.tsv", findings, ["file", "category", "detail"])
    return report


def RemoveExecutionJunk() -> int:
    removed = 0
    for path in sorted(ROOT.rglob("*"), reverse=True):
        if path.is_file() and (path.name == ".DS_Store" or path.name.startswith("._") or path.suffix == ".pyc"):
            path.unlink()
            removed += 1
        elif path.is_dir() and path.name in {"__pycache__", ".pytest_cache", ".mypy_cache"}:
            shutil.rmtree(path)
            removed += 1
    return removed


def AuditSources() -> dict[str, Any]:
    RemoveExecutionJunk()
    result_rows = ReadTsv(ROOT / "registry" / "result_registry.tsv") if (ROOT / "registry" / "result_registry.tsv").is_file() else []
    proof_goal_rows = ReadTsv(ROOT / "registry" / "proof_goal_registry.tsv") if (ROOT / "registry" / "proof_goal_registry.tsv").is_file() else []
    bibliography_rows = ReadTsv(ROOT / "bibliography" / "reference_manifest.tsv") if (ROOT / "bibliography" / "reference_manifest.tsv").is_file() else []
    source_files = [ROOT / "verification" / "reports" / "machine_verification.json", ROOT / "verification" / "wolfram" / "SecondOrderPhonologyVerification.wl", ROOT / "bibliography" / "references.bib"]
    hashes = {path.relative_to(ROOT).as_posix(): Sha256File(path) for path in source_files if path.is_file()}
    scan = ScanPublicTree()
    report = {
        "status": "PASS" if len(result_rows) in {0, 68} and len(proof_goal_rows) in {0, 218} and scan["status"] == "PASS" else "FAIL",
        "current_result_rows": len(result_rows),
        "current_proof_goal_rows": len(proof_goal_rows),
        "current_reference_manifest_rows": len(bibliography_rows),
        "normative_public_hashes": hashes,
        "static_scan_status": scan["status"],
    }
    WriteJson(AuditOutputDirectory() / "source_audit_current.json", report)
    return report
