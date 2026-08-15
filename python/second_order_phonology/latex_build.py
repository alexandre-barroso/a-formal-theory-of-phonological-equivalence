from __future__ import annotations

import os
import re
import shutil
import subprocess
from pathlib import Path
from typing import Any

from .common import AuditOutputDirectory, ROOT, WriteJson


MAX_LATEX_SECONDS = 600


def SanitizeLogText(value: str) -> str:
    cleaned = value.replace(str(ROOT), ".")
    cleaned = re.sub("/" + r"Volumes/[^\s]+", "[external-path]", cleaned)
    cleaned = re.sub("/" + r"Users/[^\s]+", "[external-path]", cleaned)
    return cleaned


def TeXExecutable() -> str:
    executable = shutil.which("lualatex")
    if executable is not None:
        return executable
    fallback = Path("/usr/local/texlive/2026/bin/universal-darwin/lualatex")
    if fallback.is_file():
        return str(fallback)
    raise FileNotFoundError("LuaLaTeX is required to compile the proof compendia")


def CompileProofCompendia() -> dict[str, Any]:
    executable = TeXExecutable()
    compiled = ROOT / "proofs" / "compiled"
    compiled.mkdir(parents=True, exist_ok=True)
    tex_cache = ROOT / "build" / "texmf-cache"
    tex_cache.mkdir(parents=True, exist_ok=True)
    reports: list[dict[str, Any]] = []
    for locale, output_name in [("en", "proof_compendium_en.pdf"), ("pt_BR", "proof_compendium_pt_BR.pdf")]:
        source_directory = ROOT / "proofs" / locale
        build_directory = ROOT / "build" / "proofs" / locale
        build_directory.mkdir(parents=True, exist_ok=True)
        environment = dict(os.environ)
        environment["SOURCE_DATE_EPOCH"] = "1786233600"
        environment["FORCE_SOURCE_DATE"] = "1"
        environment["TEXMFCACHE"] = str(tex_cache)
        environment["TEXMFVAR"] = str(tex_cache)
        tex_inputs = [str(source_directory), str(ROOT / "proofs" / "shared"), str(ROOT / "bibliography"), ""]
        environment["TEXINPUTS"] = os.pathsep.join(tex_inputs)
        command = [executable, "-interaction=nonstopmode", "-halt-on-error", "-file-line-error", "-output-directory", str(build_directory), "proof_compendium.tex"]
        outputs = []
        exit_code = 0
        for _ in range(3):
            try:
                completed = subprocess.run(command, cwd=source_directory, env=environment, capture_output=True, text=True, encoding="utf-8", check=False, timeout=MAX_LATEX_SECONDS)
                outputs.append(completed.stdout + completed.stderr)
                exit_code = completed.returncode
            except subprocess.TimeoutExpired as error:
                stdout = error.stdout.decode("utf-8", errors="replace") if isinstance(error.stdout, bytes) else (error.stdout or "")
                stderr = error.stderr.decode("utf-8", errors="replace") if isinstance(error.stderr, bytes) else (error.stderr or "")
                outputs.append(stdout + stderr + f"\nCompilation exceeded {MAX_LATEX_SECONDS} seconds.")
                exit_code = 124
            if exit_code != 0:
                break
        generated = build_directory / "proof_compendium.pdf"
        if exit_code == 0 and generated.is_file():
            shutil.copy2(generated, compiled / output_name)
        reports.append({"locale": locale, "exit_code": exit_code, "output_pdf": f"proofs/compiled/{output_name}", "log_tail": SanitizeLogText("\n".join(outputs))[-4000:]})
    shutil.rmtree(ROOT / "build" / "proofs", ignore_errors=True)
    shutil.rmtree(tex_cache, ignore_errors=True)
    report = {"status": "PASS" if all(row["exit_code"] == 0 and (ROOT / row["output_pdf"]).is_file() for row in reports) else "FAIL", "engine": Path(executable).name, "compendia": reports}
    WriteJson(AuditOutputDirectory() / "proof_compilation.json", report)
    return report
