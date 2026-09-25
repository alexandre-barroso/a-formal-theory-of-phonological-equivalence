import argparse
import filecmp
import json
import math
import re
import os
import shutil
import subprocess
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from phonological_requirements import certificate, paths

REPO = paths.REPO
RESULTS = []
RUNNERS = ("learning_tail", "productive_region_appendix", "productive_region_subject", "huaian_joint", "cross_input_variation", "russian_displayed", "individuation_ablations", "attenuation_gauge", "resolver_transfer", "correspondence_regimes", "discharge_persistence",
           "footprint_soundness", "interaction_cells", "identification_sample", "created_position_quotient", "heterogeneous_sites",
           "self_destructive_feeding", "floating_tone_tie", "transient_environments", "laryngeal_neutralization", "cell_refinement",
           "ocp_repairs", "compensatory_lengthening", "accent_encoding", "cophonologies", "variation_laws", "juncture_coalescence",
           "agreement_by_correspondence", "gapped_inventory", "nonmyopic_harmony", "antigemination", "apocope_counterfeeding",
           "contact_scale", "morphological_accent", "morphological_accent_native", "phonation_tone", "stratal_syncope", "tone_sandhi",
           "interaction_typology", "reduplication_template", "schwa_attenuation", "wellformedness_audit", "generator_operations",
           "noninterference", "interaction_graph", "alignment_automaton", "productive_enlargement", "attenuation_region",
           "core_specialisation", "interaction_regions", "lardil_region", "serial_comparison", "formula_certificates",
           "compensatory_lengthening_region", "poko_comparison", "footprint_support", "product_composition", "word_projection", "definedness", "ocp_region", "ocp_graph_region", "heterogeneous_boundary", "heterogeneous_obstruction", "heterogeneous_fibers", "weighted_cost", "cell_scope", "learning_invariance", "irrational_selection")
EXAMPLES = ("entry_calc", "transfer_tasks", "frontier_lambda_grain", "frontier_gua_endpoint")
WOLFRAM_SCRIPTS = ("learning_tail.wls", "productive_region_appendix.wls", "productive_region_subject.wls", "huaian_joint.wls", "cross_input_variation.wls", "russian_displayed.wls", "transient_environments_region.wl", "accent_encoding_regions.wl", "morphological_accent_orientation.wl",
                   "morphological_accent_typology.wl", "interaction_typology_regions.wl", "modes_check.wls",
                   "feeding_chain_check.wls", "covering_count_check.wls", "quotient_temperature_check.wls",
                   "schwa_law_check.wls", "schwa_attenuation_fit.wls", "tonal_attenuation_fit.wls", "attenuation_region.wls", "heterogeneous_sites_check.wls",
                   "interaction_regions.wls", "lardil_region.wls", "serial_comparison.wls", "formula_certificates.wls",
                   "compensatory_lengthening_region.wls", "poko_comparison.wls", "footprint_support.wls", "product_composition.wls", "word_projection.wls", "definedness.wls", "ocp_region.wls", "ocp_graph_region.wls", "heterogeneous_boundary.wls", "heterogeneous_obstruction.wls", "heterogeneous_fibers.wls", "weighted_cost.wls", "cell_scope.wls", "learning_invariance.wls", "irrational_selection.wls")
KERNEL_CANDIDATES = ("WolframKernel", "/Applications/Wolfram.app/Contents/MacOS/WolframKernel",
                     "/Applications/Mathematica.app/Contents/MacOS/WolframKernel")
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def step(name, fn, required=True):
    t0 = time.time()
    try:
        ok, detail = fn()
    except Exception as e:
        ok, detail = False, f"{type(e).__name__}: {e}"
    RESULTS.append({"step": name, "ok": bool(ok), "required": required, "detail": str(detail)})
    print(f"[{'PASS' if ok else 'FAIL'}] {name}  ({round(time.time() - t0, 1)}s)  {detail}")
    return ok


def run(cmd, cwd=None, timeout=36000, env=None):
    p = subprocess.run(cmd, cwd=cwd or REPO, capture_output=True, text=True, timeout=timeout,
                       env={**os.environ, "PYTHONPATH": str(paths.PYTHON), **(env or {})})
    return p.returncode, (p.stdout or "") + (p.stderr or "")


def last_line(o):
    lines = [l for l in o.strip().splitlines() if l.strip()]
    return lines[-1] if lines else "no output"


def check_reproduce():
    rc1, o1 = run([sys.executable, "python/phonological_opacity/reproduce.py", "--engine", "python"])
    rc2, o2 = run([sys.executable, "python/phonological_grounding/reproduce.py", "--engine", "python"])
    return rc1 == 0 and rc2 == 0, f"opacity {last_line(o1)}; grounding {last_line(o2)}"


def check_opening():
    rc, out = run([sys.executable, "python/verification/factcheck_opening_comparisons.py"])
    kernel = next((shutil.which(k) or (k if Path(k).is_file() else None)
                   for k in KERNEL_CANDIDATES if shutil.which(k) or Path(k).is_file()), None)
    if kernel is None:
        return False, "Wolfram kernel unavailable for opening comparisons"
    rcw, outw = run([kernel, "-noinit", "-noprompt", "-script",
                     "wolfram/phonological_equivalence/OpeningComparisons.wls"])
    return rc == 0 and rcw == 0 and "PASS:" in out and "PASS:" in outw, last_line(out) + "; " + last_line(outw)


def check_script(name):
    def fn():
        rc, o = run([sys.executable, str(paths.VERIFICATION / name)])
        return rc == 0, last_line(o)
    return fn


def check_runners(subset=None):
    names = tuple(subset) if subset is not None else RUNNERS
    if not names:
        return False, "empty runner selection"
    bad = []
    for m in names:
        rc, o = run([sys.executable, "-m", f"phonological_requirements.{m}"], cwd=paths.PYTHON)
        if rc != 0:
            bad.append((m, last_line(o)))
    return (not bad), (f"{len(names)} runners" if not bad else f"failed: {bad}")


def check_examples():
    bad = []
    for m in EXAMPLES:
        rc, o = run([sys.executable, str(paths.PACKAGE / "examples" / f"{m}.py")])
        if rc != 0:
            bad.append((m, last_line(o)))
    return (not bad), (f"{len(EXAMPLES)} examples" if not bad else f"failed: {bad}")


def check_certificates():
    missing = [m for m in RUNNERS if not (paths.CERTIFICATES / f"{m}.json").is_file()]
    n = len(list(paths.CERTIFICATES.glob("*.json")))
    return not missing, f"{n} certificates" if not missing else f"missing: {missing}"


EMITTED_SCRIPTS = ("accent_encoding_regions.wl", "morphological_accent_orientation.wl",
                   "morphological_accent_typology.wl", "transient_environments_region.wl", "interaction_typology_systems.wl")


def check_wolfram_regenerated():
    bad = []
    for name in EMITTED_SCRIPTS:
        f = paths.WOLFRAM / name
        g = paths.GENERATED_WOLFRAM / name
        if not f.is_file():
            bad.append(f"{name}: missing")
        elif not g.is_file():
            bad.append(f"{name}: not regenerated")
        elif not filecmp.cmp(f, g, shallow=False):
            bad.append(f"{name}: differs")
    return not bad, f"{len(EMITTED_SCRIPTS)} emitted scripts identical" if not bad else "; ".join(bad)


def check_registered_export():
    from phonological_requirements import registered_export, formula_certificates
    text, rec = registered_export.render()
    target = paths.LEAN / "PhonologicalRequirements" / "Registered.lean"
    if not target.is_file():
        return False, "Registered.lean missing"
    same = target.read_text(encoding="utf-8") == text
    formula_text, formula_record = formula_certificates.render()
    formula_target = paths.LEAN / "PhonologicalRequirements" / "RegisteredFormulae.lean"
    same_formula = formula_target.is_file() and formula_target.read_text(encoding="utf-8") == formula_text
    return same and same_formula, (f"{rec['sets']} sets, {rec['declarations']} declarations; "
        f"{formula_record['counts']['subject_checks']} formula checks" +
        ("" if same else "; Registered.lean differs from the export") +
        ("" if same_formula else "; RegisteredFormulae.lean missing or differs from the export"))


def kernel():
    for cand in [os.environ.get("WOLFRAM_KERNEL", "")] + list(KERNEL_CANDIDATES):
        if cand and (shutil.which(cand) or Path(cand).is_file()):
            return cand
    return None


def semantic_null_paths(name, result):
                                                                       

                                                                    
                                                                            
                                                                            
       
    allowed = set()
    if name == "cross_input_variation.wls":
        rows = result.get("tables", [])
        if len(rows) != 500 or result.get("infeasible") != 98:
            raise ValueError("cross-input inventory changed")
        for i, row in enumerate(rows):
            empty = row["model"] == 2 and 2 in row["input"]
            if (row["minimum"] is None) != empty:
                raise ValueError("cross-input minimum disagrees with candidate support")
            if empty:
                if row["scores"] != [] or row["winners"] != []:
                    raise ValueError("nonempty data in infeasible cross-input row")
                allowed.add(f"result.tables[{i}].minimum")
        if len(allowed) != 98:
            raise ValueError("cross-input empty-fiber count changed")
    elif name == "weighted_cost.wls":
        rows = result.get("tables", [])
        if len(rows) != 378 or result.get("infeasible_inputs") != 57:
            raise ValueError("weighted-cost inventory changed")
        for i, (model, word, minimum) in enumerate(rows):
            empty = model == 5 and 1 in word
            if (minimum is None) != empty:
                raise ValueError("weighted minimum disagrees with candidate support")
            if empty:
                allowed.add(f"result.tables[{i}][2]")
        if len(allowed) != 57:
            raise ValueError("weighted-cost empty-fiber count changed")
    elif name == "compensatory_lengthening_region.wls":
        expected = [(total, deleted, host)
                    for total in (False, True) for deleted in (False, True)
                    for host in ([None] if not total and deleted else [1, 2, None])]
        rows = result.get("rows", [])
        if [(r["total"], r["deleted"], r["host"]) for r in rows] != expected:
            raise ValueError("compensatory-lengthening candidate inventory changed")
        if result.get("checks") != [True] * 6:
            raise ValueError("compensatory-lengthening checks incomplete")
        allowed = {f"result.rows[{i}].host" for i, row in enumerate(rows)
                   if row["host"] is None}
    return allowed


def unresolved_wolfram(value, path="result", allowed_nulls=frozenset()):
    bad = []
    if isinstance(value, dict):
        for key, item in value.items():
            if key == "timeouts" and item != 0:
                bad.append(f"{path}.{key}: {item}")
            bad.extend(unresolved_wolfram(item, f"{path}.{key}", allowed_nulls))
    elif isinstance(value, list):
        for i, item in enumerate(value):
            bad.extend(unresolved_wolfram(item, f"{path}[{i}]", allowed_nulls))
    elif isinstance(value, str):
        if re.search(r"TIMEOUT|UNVERIFIED|\$Aborted|\$Failed|Indeterminate|ComplexInfinity|(?:Reduce|Resolve|Exists|ForAll|Failure)\[", value):
            bad.append(f"{path}: {value[:120]}")
    elif value is None:
        if path not in allowed_nulls:
            bad.append(f"{path}: {value}")
    elif isinstance(value, float) and not math.isfinite(value):
        bad.append(f"{path}: {value}")
    return bad


def output_stamp(path):
    if not path.is_file():
        return None
    st = path.stat()
    return st.st_mtime_ns, st.st_ctime_ns, st.st_size, st.st_ino


def check_wolfram_scripts():
    k = kernel()
    if k is None:
        return False, "WolframKernel not found"
    if not WOLFRAM_SCRIPTS:
        return False, "no Wolfram scripts"
    bad = []
    for name in WOLFRAM_SCRIPTS:
        out = paths.WOLFRAM_OUT / (Path(name).stem + ".json")
        before = output_stamp(out)
        rc, o = run([k, "-noinit", "-noprompt", "-script", str(paths.WOLFRAM / name)], cwd=paths.WOLFRAM)
        after = output_stamp(out)
        if rc != 0 or after is None:
            bad.append((name, last_line(o)))
        elif before == after:
            bad.append((name, "output was not regenerated"))
        else:
            try:
                result = json.loads(out.read_text(encoding="utf-8"))
                if not isinstance(result, dict) or not result:
                    bad.append((name, "missing result fields"))
                else:
                    allowed_nulls = semantic_null_paths(name, result)
                    bad.extend((name, error) for error in unresolved_wolfram(result, allowed_nulls=allowed_nulls))
                    if name == "formula_certificates.wls" and (
                            result.get("distinct_checks", 0) <= 0 or
                            result.get("passed") != result.get("distinct_checks") or
                            result.get("failed_indices") != []):
                        bad.append((name, "formula certificate checks incomplete"))
            except (OSError, ValueError) as error:
                bad.append((name, str(error)))
    return not bad, f"{len(WOLFRAM_SCRIPTS)} fresh, resolved script outputs" if not bad else f"failed: {bad}"


def check_stress():
    scripts = sorted(paths.VERIFICATION.glob("stress_*.py"))
    if not scripts:
        return False, "no stress suites"
    bad = []
    for s in scripts:
        rc, o = run([sys.executable, str(s)])
        if rc != 0:
            bad.append((s.name, last_line(o)))
    return not bad, f"{len(scripts)} suites" if not bad else f"failed: {bad}"


def check_lean():
    rc, o = run(["lake", "build"], cwd=paths.LEAN)
    lines = [l for l in o.splitlines() if "depends on axioms" in l or "does not depend on any axioms" in l]
    bad = [l for l in lines if "depends on axioms" in l and "does not depend" not in l
           and not set(l.split("[")[-1].rstrip("]").replace(",", " ").split()) <= ALLOWED_AXIOMS]
    return rc == 0 and len(lines) >= 46 and not bad, f"{len(lines)} declarations audited, {len(bad)} outside the allowed axioms"


PHASES = {
    "reproduction": ("reproduction entry points", "bridge", "leakage", "opening comparisons"),
    "runners": ("runners",),
    "examples": ("examples", "certificates", "registered declarations regenerated identically"),
    "wolfram": ("wolfram scripts regenerated identically", "wolfram scripts"),
    "stress": ("stress suites",),
    "lean": ("lean",),
}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--fast", action="store_true")
    ap.add_argument("--phase", choices=("all",) + tuple(PHASES), default="all")
    ap.add_argument("--shard", default="1/1")
    a = ap.parse_args()
    index, count = (int(x) for x in a.shard.split("/"))
    if not (1 <= index <= count):
        raise SystemExit("shard must be i/n with 1 <= i <= n")
    selected = None if a.phase == "all" else set(PHASES[a.phase])
    runner_subset = tuple(RUNNERS[index - 1::count])
    steps = [
        ("reproduction entry points", check_reproduce),
        ("bridge", check_script("factcheck_requirements_bridge.py")),
        ("leakage", check_script("factcheck_requirements_leakage.py")),
        ("opening comparisons", check_opening),
        ("runners", lambda: check_runners(runner_subset)),
        ("examples", check_examples),
        ("certificates", check_certificates),
        ("registered declarations regenerated identically", check_registered_export),
        ("wolfram scripts regenerated identically", check_wolfram_regenerated),
        ("wolfram scripts", check_wolfram_scripts),
        ("stress suites", check_stress),
        ("lean", check_lean),
    ]
    for name, fn in steps:
        if selected is not None and name not in selected:
            continue
        if name == "lean" and a.fast:
            continue
        step(name, fn)
    suffix = "" if a.phase == "all" else f"_{a.phase}" + (f"_{index}of{count}" if count > 1 else "")
    certificate.write(f"audit{suffix}.json", {"phase": a.phase, "shard": a.shard, "results": RESULTS}, paths.RESULTS)
    failed = [r["step"] for r in RESULTS if r["required"] and not r["ok"]]
    print("AUDIT FAILED:" if failed else "AUDIT PASSED:", f"{len(RESULTS) - len(failed)}/{len(RESULTS)} steps")
    for f in failed:
        print("   failed:", f)
    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main())
