from __future__ import annotations

import itertools
import json

from . import certificate, core, paths, registry, strictness, syntax


def compile_formula(term, indices):
    if type(term) is core.Const:
        return ["constant", term.value]
    if type(term) is core.Not:
        return ["neg", compile_formula(term.a, indices)]
    if type(term) in (core.And, core.Or_):
        tag, unit = ("conj", True) if type(term) is core.And else ("disj", False)
        result = ["constant", unit]
        for part in reversed(term.parts):
            result = [tag, compile_formula(part, indices), result]
        return result
    return ["atom", indices[id(term)]]


def truth_eval(formula, values):
    tag, *args = formula
    if tag == "constant":
        return args[0]
    if tag == "atom":
        return values[args[0]]
    if tag == "neg":
        v = truth_eval(args[0], values)
        return None if v is None else not v
    a, b = (truth_eval(x, values) for x in args)
    if tag == "conj":
        return False if a is False or b is False else (None if a is None or b is None else True)
    if tag == "disj":
        return True if a is True or b is True else (None if a is None or b is None else False)
    raise ValueError(tag)


def lean_truth(value):
    return ".uu" if value is None else (".tt" if value else ".ff")


def possible_eval(formula, allowed):
    tag, *args = formula
    if tag == "constant":
        return {args[0]}
    if tag == "atom":
        return set(allowed[args[0]])
    if tag == "neg":
        return {None if v is None else not v for v in possible_eval(args[0], allowed)}
    results = set()
    left, right = possible_eval(args[0], allowed), possible_eval(args[1], allowed)
    for a in left:
        for b in right:
            if tag == "conj":
                results.add(False if a is False or b is False else (None if a is None or b is None else True))
            elif tag == "disj":
                results.add(True if a is True or b is True else (None if a is None or b is None else False))
            else:
                raise ValueError(tag)
    return results


def lean_formula(formula):
    tag, *args = formula
    if tag == "constant":
        return "(.constant " + lean_truth(args[0]) + ")"
    if tag == "atom":
        return f"(.atom {args[0]})"
    return "(." + tag + " " + " ".join(lean_formula(a) for a in args) + ")"


def render():
    cases, case_indices, bindings = [], {}, []
    tested = 0
    for set_name, sigma, decls in registry.declaration_sets():
        for decl_name, decl in sorted(decls.items()):
            ok, errors = decl.well_typed(sigma)
            if not ok:
                raise ValueError((set_name, decl_name, errors))
            unique = {}
            for atom in strictness.atoms(decl.consequence):
                unique.setdefault(id(atom), atom)
            atoms = list(unique.values())
            indices = {id(a): i for i, a in enumerate(atoms)}
            formula = compile_formula(decl.consequence, indices)
            rows = []
            for slot in sorted(decl.consequence.slots()):
                allowed = []
                for atom in atoms:
                    if type(atom) is core.Resolves and slot in atom.slots():
                        allowed.append([False])
                    elif slot in syntax.undefined_slots(atom):
                        allowed.append([None])
                    else:
                        allowed.append([False, True, None])
                key = json.dumps([formula, allowed], separators=(",", ":"))
                if key not in case_indices:
                    expected, witness, method = True, [], "abstract"
                    if False in possible_eval(formula, allowed):
                        method = "exhaustive"
                        for values in itertools.product(*allowed):
                            tested += 1
                            if truth_eval(formula, values) is False:
                                expected, witness, method = False, list(values), "counterexample"
                                break
                    actual = strictness.subject_strict(decl, slot)[0]
                    if expected != actual:
                        raise ValueError((set_name, decl_name, slot, "native strictness mismatch"))
                    case_indices[key] = len(cases)
                    cases.append({"formula": formula, "allowed": allowed, "expected": expected,
                                  "method": method, "witness": witness})
                rows.append({"slot": slot, "case": case_indices[key]})
            bindings.append({"set": set_name, "declaration": decl_name,
                             "consequence": syntax.encode(decl.consequence),
                             "atoms": [syntax.encode(a) for a in atoms], "cases": rows})
    if not cases or len(bindings) != 527:
        raise ValueError("registered formula inventory changed")
    lines = [
             "import PhonologicalRequirements.FormulaCertificate", "",
             "namespace PhonologicalRequirements.RegisteredFormulae",
             "open FormulaCertificate", "", "set_option maxRecDepth 20000", ""]
    for i, case in enumerate(cases):
        allowed = "[" + ", ".join("[" + ", ".join(map(lean_truth, a)) + "]" for a in case["allowed"]) + "]"
        expected = "true" if case["expected"] else "false"
        witness = "[" + ", ".join(map(lean_truth, case["witness"])) + "]"
        lines.append(f"def case{i} : TestCase := ⟨{lean_formula(case['formula'])}, {allowed}, {expected}, .{case['method']}, {witness}⟩")
        lines.append(f"theorem case{i}_checked : case{i}.checked = true := by decide +kernel")
    lines += ["", "def cases : List TestCase := [" + ", ".join(f"case{i}" for i in range(len(cases))) + "]",
              f"theorem cases_count : cases.length = {len(cases)} := rfl",
              "theorem cases_checked : cases.all TestCase.checked = true := by",
              "  simp only [cases, List.all_cons, List.all_nil, Bool.true_and, Bool.and_true, " +
              ", ".join(f"case{i}_checked" for i in range(len(cases))) + "]", "",
              "end PhonologicalRequirements.RegisteredFormulae", ""]
    return "\n".join(lines), {"cases": cases, "bindings": bindings,
        "counts": {"declarations": len(bindings), "subject_checks": sum(len(b["cases"]) for b in bindings),
                   "distinct_checks": len(cases), "python_assignments_evaluated": tested},
        "scope": "Compositional strong-Kleene strictness under the primitive resolution guards. A false abstract certificate is not a proof of non-strictness on admissible structures."}


def main():
    text, record = render()
    paths.GENERATED_LEAN.mkdir(parents=True, exist_ok=True)
    (paths.GENERATED_LEAN / "RegisteredFormulae.lean").write_text(text, encoding="utf-8")
    certificate.write("formula_certificates.json", record)
    print(json.dumps(record["counts"], sort_keys=True))


if __name__ == "__main__":
    main()
