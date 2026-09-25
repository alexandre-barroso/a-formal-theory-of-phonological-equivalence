import argparse
import os
import shutil
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
sys.path.insert(0, str(REPO / "python"))
PYTHON = REPO / "python"
KERNEL_CANDIDATES = ("WolframKernel", "/Applications/Wolfram.app/Contents/MacOS/WolframKernel",
                     "/Applications/Mathematica.app/Contents/MacOS/WolframKernel")
FULL = (("query_discovery.run_all", ["-m", "phonological_grounding.query_discovery.run_all"]),
        ("query_discovery.run_models", ["-m", "phonological_grounding.query_discovery.run_models"]),
        ("query_discovery.run_enlarged", ["-m", "phonological_grounding.query_discovery.run_enlarged"]),
        ("predictions.dev_regions", ["-m", "phonological_grounding.predictions.dev_regions"]),
        ("predictions.separation_length", ["-m", "phonological_grounding.predictions.separation_length"]),
        ("predictions.boundary_sweep", ["-m", "phonological_grounding.predictions.boundary_sweep"]),
        ("predictions.boundary_hypothetical", ["-m", "phonological_grounding.predictions.boundary_hypothetical"]),
        ("predictions.resolver_audit", ["-m", "phonological_grounding.predictions.resolver_audit"]),
        ("predictions.simulate", ["-m", "phonological_grounding.predictions.simulate"]))


def run_python(full: bool) -> int:
    env = {**os.environ, "PYTHONPATH": str(PYTHON)}
    status = 0
    proc = subprocess.run([sys.executable, "-c",
                           "import phonological_opacity.fragments.regression as r; raise SystemExit(r.main())"],
                          env=env, capture_output=True, text=True)
    print(proc.stdout.rstrip() or "  (no output)")
    status |= proc.returncode
    for check in sorted((PYTHON / "verification").glob("factcheck_*.py")):
        proc = subprocess.run([sys.executable, str(check)], env=env, capture_output=True, text=True, cwd=REPO)
        last = proc.stdout.strip().splitlines()[-1] if proc.stdout.strip() else proc.stderr.strip()[-200:]
        print(f"  {check.name}: {last}")
        if proc.returncode:
            print(f"  FAILED {check.name} (exit {proc.returncode})")
            print(proc.stdout.rstrip())
            if proc.stderr.strip():
                print(proc.stderr.rstrip())
        status |= proc.returncode
    steps = [("declaration_language.emit", ["-m", "phonological_grounding.declaration_language.emit"]),
             ("transient_cycle_bounds", ["-m", "phonological_grounding.transient_cycle_bounds"])]
    if full:
        steps += list(FULL)
    for label, argv in steps:
        proc = subprocess.run([sys.executable] + argv, env=env, capture_output=True, text=True, cwd=REPO)
        print(f"  {label}:", "ok" if proc.returncode == 0 else proc.stderr[-400:])
        status |= proc.returncode
    return status


def kernel(explicit: str | None) -> str | None:
    for cand in ([explicit] if explicit else []) + [os.environ.get("WOLFRAM_KERNEL", "")] + list(KERNEL_CANDIDATES):
        if cand and (shutil.which(cand) or Path(cand).is_file()):
            return cand
    return None


def run_wolfram(executable: str) -> int:
    status = 0
    scripts = sorted((REPO / "wolfram" / "phonological_grounding").glob("*.wls")) + \
              sorted((REPO / "wolfram" / "phonological_equivalence").glob("*.wls"))
    for s in scripts:
        proc = subprocess.run([executable, "-noinit", "-noprompt", "-script", str(s)], capture_output=True, text=True, cwd=REPO)
        lines = [l for l in proc.stdout.strip().splitlines() if l.strip()]
        print(f"  {s.relative_to(REPO)}: {lines[-1] if lines else 'no output'}")
        status |= proc.returncode
    return status


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--engine", choices=("python", "wolfram", "all"), default="python")
    ap.add_argument("--full", action="store_true")
    ap.add_argument("--wolfram", default=None)
    a = ap.parse_args()
    status = 0
    if a.engine in ("python", "all"):
        status |= run_python(a.full)
    if a.engine in ("wolfram", "all"):
        k = kernel(a.wolfram)
        if k is None:
            print("WolframKernel not found")
            status |= 1
        else:
            status |= run_wolfram(k)
    print("PASS" if status == 0 else "FAIL")
    return status


if __name__ == "__main__":
    sys.exit(main())
