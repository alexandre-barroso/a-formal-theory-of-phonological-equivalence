import argparse
import os
import shutil
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
sys.path.insert(0, str(REPO / "python"))
WOLFRAM = REPO / "wolfram" / "phonological_opacity"
KERNEL_CANDIDATES = ("WolframKernel", "/Applications/Wolfram.app/Contents/MacOS/WolframKernel",
                     "/Applications/Mathematica.app/Contents/MacOS/WolframKernel")


def run_python() -> int:
    from phonological_opacity.fragments import regression
    from phonological_opacity.gua import check_deletion, check_selection
    from phonological_opacity.lithuanian import check as lithuanian
    status = regression.main()
    for fn in (check_selection.main, check_deletion.main, lithuanian.main):
        status |= int(fn() or 0)
    return status


def kernel(explicit: str | None) -> str | None:
    for cand in ([explicit] if explicit else []) + [os.environ.get("WOLFRAM_KERNEL", "")] + list(KERNEL_CANDIDATES):
        if cand and (shutil.which(cand) or Path(cand).is_file()):
            return cand
    return None


def run_wolfram(executable: str) -> int:
    status = 0
    scripts = [WOLFRAM / "fragments" / "regression.wls", WOLFRAM / "fragments" / "LambdaInterval.wls",
               WOLFRAM / "gua" / "check_selection.wl", WOLFRAM / "gua" / "check_deletion.wl",
               WOLFRAM / "lithuanian" / "check.wl"]
    for s in scripts:
        proc = subprocess.run([executable, "-noinit", "-noprompt", "-script", str(s)], cwd=s.parent,
                              capture_output=True, text=True)
        lines = [l for l in proc.stdout.strip().splitlines() if l.strip()]
        print(f"  {s.relative_to(REPO)}: {lines[-1] if lines else 'no output'}")
        status |= proc.returncode
    return status


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--engine", choices=("python", "wolfram", "all"), default="python")
    ap.add_argument("--wolfram", default=None)
    a = ap.parse_args()
    status = 0
    if a.engine in ("python", "all"):
        status |= run_python()
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
