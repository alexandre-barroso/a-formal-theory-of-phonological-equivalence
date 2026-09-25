from __future__ import annotations

from phonological_requirements import certificate, paths
from phonological_requirements.core import UNSCOPED
from phonological_requirements.registry import declaration_sets

LEAN_OUT = paths.GENERATED_LEAN


def lean_string(s) -> str:
    return '"' + str(s).replace("\\", "\\\\").replace('"', '\\"') + '"'


def scope_key(scope) -> str:
    if scope is None or scope == UNSCOPED:
        return "unscoped"
    same = ",".join(scope.same)
    delta = ",".join(f"{k}:{v}" for k, v in sorted(scope.delta.items()))
    mind = ",".join(f"{k}:{v}" for k, v in sorted(scope.min_delta.items()))
    return f"{scope.label}|same={same}|delta={delta}|min={mind}"


def opt(s) -> str:
    return "none" if s is None else f"some {lean_string(s)}"


def slot_literal(s) -> str:
    coord = "[" + ", ".join(f"({lean_string(k)}, {lean_string(v)})" for k, v in s.coord) + "]"
    return (f"⟨{lean_string(s.name)}, {lean_string(s.sort)}, .{s.role}, .{s.kind}, {opt(s.relation)}, "
            f"{lean_string(scope_key(s.scope))}, ({int(s.direction)} : Int), {opt(s.filter)}, {lean_string(s.filter_mode)}, "
            f"{lean_string(s.policy)}, {coord}⟩")


def decl_literal(d) -> str:
    slots = ",\n      ".join(slot_literal(s) for s in d.slots)
    act = "[" + ", ".join(lean_string(n) for n in sorted(d.activation.slots())) + "]"
    cons = "[" + ", ".join(lean_string(n) for n in sorted(d.consequence.slots())) + "]"
    override = "true" if d.definedness_override is not None else "false"
    return f"  {{ slots := [{slots}],\n    actSlots := {act}, consSlots := {cons}, override := {override} }}"


def render() -> tuple[str, dict]:
    sets = declaration_sets()
    lines = [ "import PhonologicalRequirements.Discipline", "",
             "namespace PhonologicalRequirements", "namespace Registered", "open Discipline", ""]
    names = []
    total_decls = 0
    for idx, (name, sigma, D) in enumerate(sets):
        total_sorts = sorted(k for k, sd in sigma.sorts.items() if sd.totality == "total")
        lines.append(f"def total{idx} : String → Bool := fun s => [{', '.join(lean_string(t) for t in total_sorts)}].contains s")
        body = ",\n".join(decl_literal(d) for _, d in sorted(D.items()))
        lines.append(f"def set{idx} : List Decl := [\n{body}]")
        lines.append("")
        names.append((name, idx, len(D)))
        total_decls += len(D)
    lines.append("def registered : List ((String → Bool) × List Decl) := [" + ", ".join(f"(total{i}, set{i})" for _, i, _ in names) + "]")
    lines.append("")
    for _, i, _ in names:
        lines.append(f"theorem set{i}_well_typed : set{i}.all (fun d => wellTyped total{i} d) = true := by decide +kernel")
    lines.append("")
    lines.append("theorem registered_sets : registered.length = " + str(len(names)) + " := rfl")
    lines.append("")
    lines.append("theorem registered_declarations : (registered.map (fun p => p.2.length)).sum = " + str(total_decls) + " := by decide +kernel")
    lines.append("")
    lines.append("theorem registered_well_typed : registered.all (fun p => p.2.all (fun d => wellTyped p.1 d)) = true := by")
    lines.append("  simp only [registered, List.all_cons, List.all_nil, Bool.true_and, Bool.and_true, " + ", ".join(f"set{i}_well_typed" for _, i, _ in names) + "]")
    lines.append("")
    lines.append("end Registered")
    lines.append("end PhonologicalRequirements")
    return "\n".join(lines) + "\n", {"sets": len(names), "declarations": total_decls,
                                    "by_set": [{"index": i, "declarations": n} for _, i, n in names]}


def main() -> int:
    text, rec = render()
    LEAN_OUT.mkdir(parents=True, exist_ok=True)
    (LEAN_OUT / "Registered.lean").write_text(text, encoding="utf-8")
    certificate.write("registered_export.json", rec)
    print(rec["sets"], "sets", rec["declarations"], "declarations")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
