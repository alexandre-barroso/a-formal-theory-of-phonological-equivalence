import json
import re
import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
LEAN = REPO / "lean"
PROJECTS = {
    "phonological_equivalence": ("PhonologicalCalculus", ["PhonologicalCalculus.Audit"]),
    "phonological_opacity": ("PhonologicalOpacity", ["PhonologicalOpacity.Audit"]),
    "phonological_grounding": ("PhonologicalGrounding", ["PhonologicalGrounding.Audit"]),
    "phonological_requirements": ("PhonologicalRequirements", []),
}
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN = re.compile(r"\b(sorry|admit|native_decide|sorryAx)\b|^\s*axiom\s", re.M)


def run(cmd, cwd):
    p = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True)
    return p.returncode, (p.stdout or "") + (p.stderr or "")


def sources(project):
    return [p for p in (LEAN / project).rglob("*.lean") if ".lake" not in p.parts]


def scan_sources(project):
    hits = []
    for p in sources(project):
        for m in FORBIDDEN.finditer(p.read_text(encoding="utf-8")):
            hits.append(f"{p.relative_to(LEAN)}:{m.group(0).strip()}")
    return hits


def axioms_of(output):
    found = {}
    for m in re.finditer(r"MODULE_CONSTANT (\S+) MODULE (\S+) AXIOMS \[([^\]]*)\]", output):
        found[m.group(1)] = [a.strip() for a in m.group(3).split(",") if a.strip()]
    for m in re.finditer(r"'([^']+)' depends on axioms: \[([^\]]*)\]", output):
        found[m.group(1)] = [a.strip() for a in m.group(2).split(",") if a.strip()]
    for m in re.finditer(r"'([^']+)' does not depend on any axioms", output):
        found[m.group(1)] = []
    return found


def summaries_of(output):
    out = []
    for m in re.finditer(r"MODULE_AUDIT theorems=(\d+) constants=(\d+) modules=(\d+) axioms=\[([^\]]*)\]", output):
        out.append({"theorems": int(m.group(1)), "constants": int(m.group(2)), "modules": int(m.group(3)),
                    "axioms": [a.strip() for a in m.group(4).split(",") if a.strip()]})
    return out


def main():
    report = {}
    ok_all = True
    for project, (lib, targets) in PROJECTS.items():
        cwd = LEAN / project
        rc, out = run(["lake", "build"], cwd)
        entry = {"build": rc == 0, "sources": len(sources(project)), "forbidden_tokens": scan_sources(project)}
        audited = axioms_of(out)
        summaries = summaries_of(out)
        for t in targets:
            rc2, out2 = run(["lake", "build", t], cwd)
            entry["build"] = entry["build"] and rc2 == 0
            audited.update(axioms_of(out2))
            summaries.extend(summaries_of(out2))
        bad = {n: a for n, a in audited.items() if not set(a) <= ALLOWED}
        bad_summary = [x for x in summaries if not set(x["axioms"]) <= ALLOWED]
        entry["audited_constants"] = len(audited) + sum(x["theorems"] for x in summaries)
        entry["summary_audits"] = summaries
        entry["disallowed_axioms"] = bad
        entry["disallowed_summary_axioms"] = bad_summary
        entry["ok"] = (entry["build"] and not entry["forbidden_tokens"] and not bad and not bad_summary
                       and entry["audited_constants"] > 0)
        ok_all = ok_all and entry["ok"]
        report[project] = entry
        print(f"[{'PASS' if entry['ok'] else 'FAIL'}] {project}: build={entry['build']} sources={entry['sources']} audited={entry['audited_constants']} forbidden={len(entry['forbidden_tokens'])} disallowed={len(bad) + len(bad_summary)}")
    out_dir = REPO / "results" / "lean"
    out_dir.mkdir(parents=True, exist_ok=True)
    (out_dir / "audit.json").write_text(json.dumps(report, indent=1, sort_keys=True) + "\n")
    print("LEAN AUDIT PASSED" if ok_all else "LEAN AUDIT FAILED")
    return 0 if ok_all else 1


if __name__ == "__main__":
    raise SystemExit(main())
