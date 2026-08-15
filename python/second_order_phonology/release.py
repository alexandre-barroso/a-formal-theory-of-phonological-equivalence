from __future__ import annotations

import csv
import hashlib
import json
import os
import stat
import shutil
import subprocess
import sys
import tempfile
import zipfile
from collections import Counter
from pathlib import Path, PurePosixPath
from typing import Any

from .common import AuditOutputDirectory, IgnoredDirectoryNames, ROOT, Sha256File, WriteJson, WriteTsv


EXCLUDED_PARTS = {".lake", "build", "__pycache__", ".pytest_cache", ".mypy_cache", *IgnoredDirectoryNames()}
EXCLUDED_SUFFIXES = {".aux", ".blg", ".log", ".pyc", ".swp", ".tmp"}
CLEAN_DIRECTORY_NAMES = {"build", "__pycache__", ".pytest_cache", ".mypy_cache"}
GENERATED_RELEASE_FILES = {
    "ARTIFACT_MANIFEST.tsv",
    "MANIFEST.sha256",
    "release/second_order_phonology_artifact.zip",
    "release/second_order_phonology_artifact.zip.sha256",
}
CANONICAL_ARCHIVE_TIMESTAMP = (1980, 1, 1, 0, 0, 0)
CANONICAL_ARCHIVE_MODE = 0o100644


def SourceTreeSymlinks() -> list[str]:
    findings: list[str] = []
    for path in ROOT.rglob("*"):
        relative = path.relative_to(ROOT)
        if any(part in EXCLUDED_PARTS for part in relative.parts):
            continue
        if relative.parts and relative.parts[0] == "release" and relative.as_posix() not in {"release/release_notes.md", "release/release_notes.pt-BR.md"}:
            continue
        if path.is_symlink():
            findings.append(relative.as_posix())
    return sorted(findings)


def ManifestFiles() -> list[Path]:
    symlinks = SourceTreeSymlinks()
    if symlinks:
        raise ValueError("symbolic links are forbidden in the public source tree: " + ", ".join(symlinks))
    files: list[Path] = []
    for path in ROOT.rglob("*"):
        if not path.is_file():
            continue
        relative = path.relative_to(ROOT)
        if any(part in EXCLUDED_PARTS for part in relative.parts):
            continue
        if relative.parts and relative.parts[0] == "release" and relative.as_posix() not in {"release/release_notes.md", "release/release_notes.pt-BR.md"}:
            continue
        if path.name in {"MANIFEST.sha256", "ARTIFACT_MANIFEST.tsv"}:
            continue
        if path.suffix in EXCLUDED_SUFFIXES or path.name in {".DS_Store"} or path.name.startswith("._"):
            continue
        files.append(path)
    return sorted(files, key=lambda value: value.relative_to(ROOT).as_posix())


def BuildManifest() -> dict[str, Any]:
    rows: list[dict[str, Any]] = []
    checksum_lines: list[str] = []
    for path in ManifestFiles():
        relative = path.relative_to(ROOT).as_posix()
        digest = Sha256File(path)
        rows.append({"path": relative, "sha256": digest, "bytes": path.stat().st_size, "role": ArtifactRole(relative), "included_in_release": "true"})
        checksum_lines.append(f"{digest}  {relative}")
    WriteTsv(ROOT / "ARTIFACT_MANIFEST.tsv", rows, ["path", "sha256", "bytes", "role", "included_in_release"])
    (ROOT / "MANIFEST.sha256").write_text("\n".join(checksum_lines) + "\n", encoding="utf-8", newline="\n")
    return {"file_count": len(rows), "total_bytes": sum(int(row["bytes"]) for row in rows)}


def ArtifactRole(relative: str) -> str:
    first = relative.split("/", 1)[0]
    return {
        "bibliography": "bibliographic_metadata",
        "data": "canonical_data_or_schema",
        "environment": "reproducibility_environment",
        "figures": "bilingual_figure",
        "formal": "formal_specification_proof_or_report",
        "lean": "lean_formalization_source_or_report",
        "locales": "controlled_localization",
        "proofs": "written_proof",
        "registry": "scientific_registry",
        "scripts": "build_or_validation_script",
        "tables": "bilingual_table",
        "verification": "machine_verification",
    }.get(first, "package_metadata")


def CleanGenerated() -> dict[str, int]:
    removed = 0
    for relative in sorted(GENERATED_RELEASE_FILES):
        path = ROOT / relative
        if path.is_file() or path.is_symlink():
            path.unlink()
            removed += 1
    for path in sorted(ROOT.rglob("*"), reverse=True):
        relative = path.relative_to(ROOT)
        if ".lake" in relative.parts:
            continue
        if path.is_file() and (path.suffix in EXCLUDED_SUFFIXES or path.name in {".DS_Store"} or path.name.startswith("._")):
            path.unlink()
            removed += 1
        if path.is_dir() and path.name in CLEAN_DIRECTORY_NAMES:
            shutil.rmtree(path)
            removed += 1
    return {"removed_entries": removed}


def DeterministicZip() -> tuple[Path, str]:
    release_directory = ROOT / "release"
    release_directory.mkdir(parents=True, exist_ok=True)
    archive = release_directory / "second_order_phonology_artifact.zip"
    WriteReleaseNotes()
    BuildManifest()
    paths = [ROOT / "MANIFEST.sha256", ROOT / "ARTIFACT_MANIFEST.tsv", *ManifestFiles()]
    unique = sorted(set(paths), key=lambda value: value.relative_to(ROOT).as_posix())
    with tempfile.TemporaryDirectory(prefix="second-order-phonology-release-") as temporary:
        staging = Path(temporary) / "artifact"
        for path in unique:
            relative = path.relative_to(ROOT)
            destination = staging / relative
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(path, destination)
        staged = sorted((path for path in staging.rglob("*") if path.is_file()), key=lambda value: value.relative_to(staging).as_posix())
        with zipfile.ZipFile(archive, "w", compression=zipfile.ZIP_DEFLATED, compresslevel=9) as handle:
            for path in staged:
                relative = path.relative_to(staging).as_posix()
                information = zipfile.ZipInfo(relative, date_time=CANONICAL_ARCHIVE_TIMESTAMP)
                information.compress_type = zipfile.ZIP_DEFLATED
                information.external_attr = (CANONICAL_ARCHIVE_MODE & 0xFFFF) << 16
                handle.writestr(information, path.read_bytes(), compress_type=zipfile.ZIP_DEFLATED, compresslevel=9)
    digest = Sha256File(archive)
    (release_directory / "second_order_phonology_artifact.zip.sha256").write_text(f"{digest}  {archive.name}\n", encoding="utf-8", newline="\n")
    return archive, digest


def ValidateArchive(archive: Path) -> dict[str, Any]:
    prohibited_names = {".DS_Store", "__MACOSX", ".lake", "__pycache__", *IgnoredDirectoryNames()}
    findings: list[dict[str, str]] = []
    with zipfile.ZipFile(archive) as handle:
        names = handle.namelist()
        if len(names) != len(set(names)):
            findings.append({"category": "duplicate_entry", "detail": "archive contains duplicate member names"})
        unsafe_names = [name for name in names if not SafeArchiveName(name)]
        findings.extend({"category": "unsafe_entry", "detail": name} for name in unsafe_names)
        symlinks = [information.filename for information in handle.infolist() if stat.S_ISLNK(information.external_attr >> 16)]
        findings.extend({"category": "symbolic_link", "detail": name} for name in symlinks)
        for information in handle.infolist():
            if information.date_time != CANONICAL_ARCHIVE_TIMESTAMP:
                findings.append({"category": "noncanonical_timestamp", "detail": information.filename})
            mode = information.external_attr >> 16
            if not stat.S_ISREG(mode) or stat.S_IMODE(mode) != stat.S_IMODE(CANONICAL_ARCHIVE_MODE):
                findings.append({"category": "noncanonical_mode", "detail": information.filename})
        try:
            manifest_rows = ReadManifestRows(handle)
        except (KeyError, UnicodeDecodeError, csv.Error):
            manifest_rows = []
            findings.append({"category": "manifest_parse", "detail": "ARTIFACT_MANIFEST.tsv is missing or malformed"})
        manifest_paths = [row.get("path", "") for row in manifest_rows]
        if len(manifest_paths) != len(set(manifest_paths)):
            findings.append({"category": "manifest_duplicate", "detail": "ARTIFACT_MANIFEST.tsv contains duplicate paths"})
        if any(not SafeArchiveName(path) for path in manifest_paths):
            findings.append({"category": "manifest_path", "detail": "ARTIFACT_MANIFEST.tsv contains an unsafe path"})
        if any(row.get("included_in_release") != "true" for row in manifest_rows):
            findings.append({"category": "manifest_release_flag", "detail": "every manifest row must be included in the release"})
        expected_names = sorted(["ARTIFACT_MANIFEST.tsv", "MANIFEST.sha256", *[row["path"] for row in manifest_rows]])
        if names != sorted(names):
            findings.append({"category": "ordering", "detail": "archive entries are not sorted"})
        if names != expected_names:
            findings.append({"category": "manifest_membership", "detail": "archive membership differs from ARTIFACT_MANIFEST.tsv"})
        for required_note in ["release/release_notes.md", "release/release_notes.pt-BR.md"]:
            if required_note not in names:
                findings.append({"category": "required_entry", "detail": required_note})
        for name in names:
            if name in unsafe_names or name in symlinks:
                continue
            parts = Path(name).parts
            if any(part in prohibited_names for part in parts) or name.endswith(tuple(EXCLUDED_SUFFIXES)):
                findings.append({"category": "forbidden_entry", "detail": name})
            if name.lower().endswith(".pdf") and name.startswith("bibliography/"):
                findings.append({"category": "third_party_pdf", "detail": name})
            data = handle.read(name)
            if b"/" + b"Volumes/" in data or b"/" + b"Users/" in data:
                findings.append({"category": "private_path", "detail": name})
        for row in manifest_rows:
            path = row.get("path", "")
            if path in names:
                data = handle.read(path)
                if hashlib.sha256(data).hexdigest() != row.get("sha256"):
                    findings.append({"category": "manifest_hash", "detail": path})
                if str(len(data)) != row.get("bytes"):
                    findings.append({"category": "manifest_size", "detail": path})
        expected_checksums = "".join(f"{row.get('sha256', '')}  {row.get('path', '')}\n" for row in manifest_rows).encode("utf-8")
        try:
            recorded_checksums = handle.read("MANIFEST.sha256")
        except KeyError:
            recorded_checksums = b""
        if recorded_checksums != expected_checksums:
            findings.append({"category": "checksum_manifest", "detail": "MANIFEST.sha256 does not exactly encode ARTIFACT_MANIFEST.tsv"})
    return {"status": "PASS" if not findings else "FAIL", "entry_count": len(names), "findings": findings, "sha256": Sha256File(archive)}


def ReadManifestRows(handle: zipfile.ZipFile) -> list[dict[str, str]]:
    content = handle.read("ARTIFACT_MANIFEST.tsv").decode("utf-8").splitlines()
    reader = csv.DictReader(content, delimiter="\t")
    expected = ["path", "sha256", "bytes", "role", "included_in_release"]
    if reader.fieldnames != expected:
        raise csv.Error("unexpected artifact-manifest header")
    rows = list(reader)
    if any(None in row or any(row.get(field) is None for field in expected) for row in rows):
        raise csv.Error("malformed artifact-manifest row")
    return rows


def SafeArchiveName(name: str) -> bool:
    path = PurePosixPath(name)
    return bool(name) and "\\" not in name and not path.is_absolute() and ".." not in path.parts and path.as_posix() == name


def ValidateExtractedArchive(archive: Path) -> dict[str, Any]:
    archive_validation = ValidateArchive(archive)
    if archive_validation["status"] != "PASS":
        return {"status": "FAIL", "returncode": None, "findings": [{"category": "archive_precheck", "detail": "in-memory validation failed"}], "output": ""}
    findings: list[dict[str, str]] = []
    with tempfile.TemporaryDirectory(prefix="second-order-phonology-extracted-") as temporary:
        extracted = Path(temporary) / "artifact"
        extracted.mkdir()
        with zipfile.ZipFile(archive) as handle:
            for information in handle.infolist():
                if not SafeArchiveName(information.filename) or stat.S_ISLNK(information.external_attr >> 16):
                    findings.append({"category": "unsafe_extraction", "detail": information.filename})
                    continue
                destination = extracted.joinpath(*PurePosixPath(information.filename).parts)
                destination.parent.mkdir(parents=True, exist_ok=True)
                destination.write_bytes(handle.read(information))
        manifest_paths = [extracted / "ARTIFACT_MANIFEST.tsv", extracted / "MANIFEST.sha256"]
        before = {path.name: path.read_bytes() for path in manifest_paths if path.is_file()}
        environment = dict(os.environ)
        environment["PYTHONDONTWRITEBYTECODE"] = "1"
        command = [sys.executable, "scripts/validate_package.py", "--machine-closed", "--strict", "--extracted-release"]
        try:
            completed = subprocess.run(
                command,
                cwd=extracted,
                env=environment,
                capture_output=True,
                text=True,
                encoding="utf-8",
                check=False,
                timeout=1800,
            )
            returncode = completed.returncode
            output = completed.stdout + completed.stderr
        except subprocess.TimeoutExpired as error:
            returncode = None
            output = ((error.stdout or "") + (error.stderr or "")) if isinstance(error.stdout, str) and isinstance(error.stderr, str) else ""
            findings.append({"category": "extracted_validation_timeout", "detail": "validation exceeded 1800 seconds"})
        after = {path.name: path.read_bytes() for path in manifest_paths if path.is_file()}
        if before != after or len(before) != 2:
            findings.append({"category": "extracted_manifest_stability", "detail": "validation changed or omitted a release manifest"})
        if returncode != 0:
            findings.append({"category": "extracted_validation", "detail": f"validation exited with status {returncode}"})
    return {"status": "PASS" if not findings else "FAIL", "returncode": returncode, "findings": findings, "output": output[-4000:]}


def BuildRelease() -> dict[str, Any]:
    archive, digest = DeterministicZip()
    validation = ValidateArchive(archive)
    extracted_validation = ValidateExtractedArchive(archive)
    status = "PASS" if validation["status"] == extracted_validation["status"] == "PASS" else "FAIL"
    report = {"status": status, "archive": archive.relative_to(ROOT).as_posix(), "sha256": digest, "validation": validation, "extracted_validation": extracted_validation}
    internal = AuditOutputDirectory()
    WriteJson(internal / "release_archive_validation.json", report)
    build_json = internal / "build_report.json"
    if build_json.is_file():
        build_report = json.loads(build_json.read_text(encoding="utf-8"))
        build_report["release_sha256"] = digest
        WriteJson(build_json, build_report)
    build_markdown = internal / "build_report.md"
    if build_markdown.is_file():
        lines = build_markdown.read_text(encoding="utf-8").splitlines()
        lines = [f"- Release SHA-256: {digest}" if line.startswith("- Release SHA-256:") else line for line in lines]
        build_markdown.write_text("\n".join(lines) + "\n", encoding="utf-8", newline="\n")
    return report


def WriteReleaseNotes() -> None:
    result_rows = ReadRows(ROOT / "registry" / "result_registry.tsv")
    dataset_rows = ReadRows(ROOT / "data" / "dataset_manifest.tsv")
    bibliography = ReadRows(ROOT / "bibliography" / "reference_manifest.tsv")
    figure_rows = ReadRows(ROOT / "registry" / "figure_manifest.tsv")
    table_rows = ReadRows(ROOT / "registry" / "table_manifest.tsv")
    formal = FormalReleaseMetrics()
    lean = LeanReleaseMetrics()
    total_rows = sum(int(row["row_count"]) for row in dataset_rows)
    proof_methods = "; ".join(f"{name}: {count}" for name, count in formal["proof_method_counts"].items())
    foundation_classes = "; ".join(f"{name}: {count}" for name, count in formal["trusted_foundation_class_counts"].items())
    software_versions = "; ".join(f"{name}: {version}" for name, version in formal["software_versions"].items())
    lean_summary = (
        f"- Lean declaration map and kernel audit: {lean['toolchain']}; mathlib {lean['mathlib_input_revision']} "
        f"at commit {lean['mathlib_revision']}; {lean['closed_result_count']} registered results and "
        f"{lean['closed_proof_goal_count']} registered proof goals have exact `lean_closed` declaration mappings; "
        f"independent kernel replay: {lean['kernel_replay_status']}"
    )
    text = "\n".join([
        "# Release notes",
        "",
        "This pre-dissertation artifact preserves the established second-order phonological-calculus result inventory without adding, renaming, merging, or renumbering scientific results.",
        "",
        f"- Registered results: {len(result_rows)}",
        f"- Machine-closed results: {formal['machine_closed_result_count']}",
        f"- Withdrawn results: {formal['withdrawn_result_count']}",
        f"- Registered proof goals discharged: {formal['discharged_proof_goal_count']} / {formal['registered_proof_goal_count']}",
        f"- Replay records by class: {proof_methods}",
        f"- Trusted foundation by class: {foundation_classes}",
        f"- Mutation kill rate: {formal['mutation_kill_rate']} ({formal['mutation_count']} mandatory non-equivalent mutants)",
        f"- Cross-engine agreements: {formal['cross_engine_agreement_count']}",
        "- Complete Python–Wolfram agreement on proof records and result status, with independent mathematical replay for 173 proof goals and Lean-kernel closure for the remaining 45 universal goals.",
        f"- Exact software versions: {software_versions}",
        lean_summary,
        "- Release archive SHA-256: recorded in `release/second_order_phonology_artifact.zip.sha256` after deterministic archive construction; a ZIP cannot contain its own noncircular SHA-256 value.",
        f"- Canonical datasets: {len(dataset_rows)} ({total_rows} rows)",
        f"- Bilingual figure manifest rows: {len(figure_rows)}",
        f"- Bilingual table manifest rows: {len(table_rows)}",
        f"- Bibliography entries: {len(bibliography)}",
        "",
        "Machine verification and written-proof status are independent. This is a result-specific formal-proof artifact with a small exact proof checker, not a general-purpose proof assistant. Data demonstrations replay registered reduced decisions and do not establish language-wide phonological ontology. Source-facing applications delimit consequences of declared formal analyses and do not by themselves select the empirically correct grammar.",
        "",
        "No third-party source PDF or corpus recording is included. A public reuse license, ORCID, and archival DOI are not asserted; human-controlled metadata is recorded in `registry/release_metadata_required.tsv`.",
        "",
    ])
    path = ROOT / "release" / "release_notes.md"
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8", newline="\n")
    lean_summary_pt = (
        f"- Mapa de declarações e auditoria do kernel Lean: {lean['toolchain']}; mathlib "
        f"{lean['mathlib_input_revision']} no commit {lean['mathlib_revision']}; "
        f"{lean['closed_result_count']} resultados registrados e "
        f"{lean['closed_proof_goal_count']} metas de demonstração registradas possuem mapeamentos exatos de declarações `lean_closed`; "
        f"reexecução independente pelo kernel: {lean['kernel_replay_status']}"
    )
    portuguese_text = "\n".join([
        "# Notas de versão",
        "",
        "Este artefato pré-dissertação preserva o inventário estabelecido de resultados do cálculo fonológico de segunda ordem sem acrescentar, renomear, fundir ou renumerar resultados científicos.",
        "",
        f"- Resultados registrados: {len(result_rows)}",
        f"- Resultados fechados por máquina: {formal['machine_closed_result_count']}",
        f"- Resultados retirados: {formal['withdrawn_result_count']}",
        f"- Metas de demonstração registradas e demonstradas: {formal['discharged_proof_goal_count']} / {formal['registered_proof_goal_count']}",
        f"- Registros de reprodução por classe: {proof_methods}",
        f"- Fundação confiável por classe: {foundation_classes}",
        f"- Taxa de eliminação de mutantes: {formal['mutation_kill_rate']} ({formal['mutation_count']} mutantes obrigatórios não equivalentes)",
        f"- Concordâncias entre motores: {formal['cross_engine_agreement_count']}",
        "- Concordância completa entre Python e Wolfram nos registros de demonstração e no estado dos resultados, com reprodução matemática independente de 173 metas de demonstração e fechamento pelo kernel do Lean das 45 metas universais restantes.",
        f"- Versões exatas do software: {software_versions}",
        lean_summary_pt,
        "- SHA-256 do arquivo de distribuição: registrado em `release/second_order_phonology_artifact.zip.sha256` após a construção determinística; um arquivo ZIP não pode conter, sem circularidade, seu próprio valor SHA-256.",
        f"- Conjuntos de dados canônicos: {len(dataset_rows)} ({total_rows} linhas)",
        f"- Linhas do manifesto bilíngue de figuras: {len(figure_rows)}",
        f"- Linhas do manifesto bilíngue de tabelas: {len(table_rows)}",
        f"- Entradas bibliográficas: {len(bibliography)}",
        "",
        "A verificação por máquina e o estado da demonstração escrita são eixos independentes. Este é um artefato de demonstrações formais específico aos resultados e dotado de um pequeno verificador exato de demonstrações; não é um assistente de provas de uso geral. As demonstrações com dados reexecutam decisões reduzidas registradas e não estabelecem uma ontologia fonológica para toda uma língua. As aplicações voltadas às fontes delimitam consequências de análises formais declaradas e, isoladamente, não selecionam a gramática empiricamente correta.",
        "",
        "Nenhum PDF de fonte de terceiros ou gravação de corpus está incluído. Não se afirma uma licença pública de reutilização, ORCID ou DOI de arquivamento; os metadados sob autoridade humana estão registrados em `registry/release_metadata_required.tsv`.",
        "",
    ])
    (ROOT / "release" / "release_notes.pt-BR.md").write_text(portuguese_text, encoding="utf-8", newline="\n")


def FormalReleaseMetrics() -> dict[str, Any]:
    formal_path = ROOT / "formal" / "reports" / "formal_closure.json"
    if formal_path.is_file():
        return json.loads(formal_path.read_text(encoding="utf-8"))
    replay = json.loads((ROOT / "formal" / "reports" / "proof_replay.json").read_text(encoding="utf-8"))
    mutation = json.loads((ROOT / "formal" / "reports" / "mutation_report.json").read_text(encoding="utf-8"))
    agreement = json.loads((ROOT / "verification" / "reports" / "cross_engine_proofs.json").read_text(encoding="utf-8"))
    foundation = json.loads((ROOT / "formal" / "foundation" / "trusted_foundation.json").read_text(encoding="utf-8"))
    wolfram = json.loads((ROOT / "formal" / "traces" / "wolfram" / "machine_closure.json").read_text(encoding="utf-8"))
    environment = json.loads((ROOT / "environment" / "environment_report.json").read_text(encoding="utf-8"))
    proofs = [json.loads(path.read_text(encoding="utf-8")) for path in sorted((ROOT / "formal" / "proofs").glob("*.json"))]
    return {
        "machine_closed_result_count": replay["machine_closed_result_count"],
        "withdrawn_result_count": 0,
        "discharged_proof_goal_count": replay["discharged_proof_goal_count"],
        "registered_proof_goal_count": replay["proof_goal_count"],
        "proof_method_counts": dict(sorted(Counter(value["proof_method"] for value in proofs).items())),
        "trusted_foundation_class_counts": dict(sorted(Counter(value["classification"] for value in foundation["items"]).items())),
        "mutation_kill_rate": mutation["kill_rate"],
        "mutation_count": mutation["mandatory_non_equivalent_count"],
        "cross_engine_agreement_count": agreement["agreement_count"],
        "software_versions": {"python": environment["python"], "wolfram": wolfram["wolfram_version"]},
    }


def LeanReleaseMetrics() -> dict[str, Any]:
    lean_root = ROOT / "lean"
    result_rows = ReadRows(lean_root / "reports" / "result_coverage.tsv")
    proof_goal_rows = ReadRows(lean_root / "reports" / "proof_goal_coverage.tsv")
    result_counts = Counter(row["formalization_status"] for row in result_rows)
    proof_goal_counts = Counter(row["formalization_status"] for row in proof_goal_rows)
    manifest = json.loads((lean_root / "lake-manifest.json").read_text(encoding="utf-8"))
    mathlib = next(package for package in manifest["packages"] if package["name"] == "mathlib")
    checker_log = (lean_root / "logs" / "leanchecker.txt").read_text(encoding="utf-8")
    if len(result_rows) != 68 or result_counts != Counter({"lean_closed": 68}):
        raise ValueError("Lean result coverage must contain exactly 68 lean_closed rows")
    if len(proof_goal_rows) != 218 or proof_goal_counts != Counter({"lean_closed": 218}):
        raise ValueError("Lean proof-goal coverage must contain exactly 218 lean_closed rows")
    return {
        "toolchain": (lean_root / "lean-toolchain").read_text(encoding="utf-8").strip(),
        "mathlib_input_revision": mathlib["inputRev"],
        "mathlib_revision": mathlib["rev"],
        "closed_result_count": result_counts["lean_closed"],
        "closed_proof_goal_count": proof_goal_counts["lean_closed"],
        "kernel_replay_status": "PASS" if "Independent kernel check completed successfully." in checker_log else "FAIL",
    }


def ReadRows(path: Path) -> list[dict[str, str]]:
    with path.open(encoding="utf-8", newline="") as handle:
        return list(csv.DictReader(handle, delimiter="\t"))
