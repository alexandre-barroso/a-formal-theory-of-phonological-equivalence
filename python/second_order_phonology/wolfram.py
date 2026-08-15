from __future__ import annotations

import shutil
import subprocess
import re
import json
from pathlib import Path
from typing import Any

from .common import ROOT, ReadTsv, Sha256File, WriteJson, WriteTsv


MAX_WOLFRAM_SECONDS = 900


def ProcessOutput(value: str | bytes | None) -> str:
    if value is None:
        return ""
    if isinstance(value, bytes):
        return value.decode("utf-8", errors="replace")
    return value


def SanitizeExecutionText(value: str) -> str:
    cleaned = value.replace(str(ROOT), ".")
    cleaned = re.sub("/" + r"Volumes/[^\s]+", "[external-path]", cleaned)
    cleaned = re.sub("/" + r"Users/[^\s]+", "[external-path]", cleaned)
    return cleaned


def WolframExecutable() -> str:
    executable = shutil.which("wolframscript")
    if executable is None:
        raise FileNotFoundError("wolframscript is not available on PATH")
    return executable


def RunWolfram(mode: str, export_data: bool) -> dict[str, Any]:
    executable = WolframExecutable()
    source = ROOT / "verification" / "wolfram" / "SecondOrderPhonologyVerification.wl"
    command = [executable, "-script", str(source), "--run-all", "--mode", mode, "--output", str(ROOT / "verification" / "reports")]
    if export_data:
        command.extend(["--export-data", "--data-output", str(ROOT / "data" / "wolfram_exports")])
    try:
        completed = subprocess.run(command, cwd=ROOT, capture_output=True, text=True, encoding="utf-8", check=False, timeout=MAX_WOLFRAM_SECONDS)
        exit_code = completed.returncode
        stdout = completed.stdout
        stderr = completed.stderr
        timed_out = False
    except subprocess.TimeoutExpired as error:
        exit_code = None
        stdout = ProcessOutput(error.stdout)
        stderr = ProcessOutput(error.stderr) + f"\nExecution exceeded {MAX_WOLFRAM_SECONDS} seconds."
        timed_out = True
    export_validation = ValidateWolframExport(ROOT / "data" / "wolfram_exports") if export_data and exit_code == 0 else {"status": "not_run"}
    accepted_exit = exit_code == 0 if mode != "machine-strict" else exit_code == 1
    if export_data:
        accepted_exit = accepted_exit and export_validation["status"] == "PASS"
    report = {
        "mode": mode,
        "export_data": export_data,
        "exit_code": exit_code,
        "timed_out": timed_out,
        "stdout": SanitizeExecutionText(stdout),
        "stderr": SanitizeExecutionText(stderr),
        "accepted_exit": accepted_exit,
        "export_validation": export_validation,
    }
    WriteJson(ROOT / "verification" / "reports" / f"wolfram_{mode.replace('-', '_')}_execution.json", report)
    return report


def ValidateWolframExport(directory: Path) -> dict[str, Any]:
    names = ["portuguese_embedded.tsv", "english_speaker_embedded.tsv", "english_aggregate_embedded.tsv", "mandarin_embedded.tsv", "wolfram_catalog.json"]
    rows: list[dict[str, Any]] = []
    failures: list[str] = []
    for name in names:
        path = directory / name
        if not path.is_file():
            failures.append(name)
            continue
        if path.suffix == ".tsv":
            row_count = len(ReadTsv(path))
        else:
            value = json.loads(path.read_text(encoding="utf-8"))
            row_count = len(value) if isinstance(value, list) else 1
            if name == "wolfram_catalog.json" and row_count != 68:
                failures.append(name)
        rows.append({"file": f"data/wolfram_exports/{name}", "sha256": Sha256File(path), "row_count": row_count, "engine": "Wolfram Language", "role": "lossless external export of embedded verification input"})
    WriteTsv(directory / "manifest.tsv", rows, ["file", "sha256", "row_count", "engine", "role"])
    return {"status": "PASS" if not failures and len(rows) == 5 else "FAIL", "files": len(rows), "failures": failures}
