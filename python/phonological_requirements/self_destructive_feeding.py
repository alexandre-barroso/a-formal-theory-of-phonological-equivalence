from __future__ import annotations
from phonological_requirements import certificate, paths
import json, re, shutil, subprocess, tempfile
from fractions import Fraction as F
from pathlib import Path

import sympy as sp

from . import frag_turkish as TK
from .evaluate import activation, coefficients, score

OUT = paths.CERTIFICATES


def exact_regions(conj):
    candidates = ("WolframKernel", "/Applications/Wolfram.app/Contents/MacOS/WolframKernel",
                  "/Applications/Mathematica.app/Contents/MacOS/WolframKernel")
    kernel = next((p for name in candidates if (p := shutil.which(name))), None)
    if kernel is None:
        raise FileNotFoundError("WolframKernel not found")
    paths.GENERATED_WOLFRAM.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="feeding-", dir=paths.GENERATED_WOLFRAM) as work:
        source, result = Path(work) / "regions.wls", Path(work) / "regions.json"
        text = (
            f'q = TimeConstrained[{{Reduce[{conj} && m>=0 && d>=0 && c>=0 && v>=0 && lam>=0, '
            f'{{m,d,c,v,lam}}, Reals], Reduce[{conj} && m>=0 && d>=0 && c>=0 && v>=0 && lam==0, '
            f'{{m,d,c,v,lam}}, Reals]}}, 120, $Aborted];\n'
            'If[!ListQ[q] || Length[q] != 2 || !FreeQ[q, _Reduce | _Resolve | _Exists | _ForAll | '
            '_Failure | $Aborted | $Failed | Indeterminate | ComplexInfinity], Exit[3]];\n'
            f'Export[{json.dumps(str(result))}, <|"region" -> ToString[q[[1]], InputForm], '
            '"at_zero" -> ToString[q[[2]], InputForm]|>, "RawJSON"];\nExit[0];\n')
        source.write_text(text, encoding="utf-8")
        run = subprocess.run([kernel, "-noinit", "-noprompt", "-script", str(source)],
                             capture_output=True, text=True, timeout=150)
        if run.returncode != 0:
            raise RuntimeError(f"WolframKernel exit {run.returncode}: {run.stderr or run.stdout}")
        if not result.is_file():
            raise RuntimeError("WolframKernel produced no region output")
        record = json.loads(result.read_text(encoding="utf-8"))
        if set(record) != {"region", "at_zero"}:
            raise ValueError("invalid Wolfram region fields")
        for value in record.values():
            if not isinstance(value, str) or not value or re.search(
                    r"TIMEOUT|UNVERIFIED|\$Aborted|\$Failed|Indeterminate|ComplexInfinity|(?:Reduce|Resolve|Exists|ForAll|Failure)\[", value):
                raise ValueError("unresolved Wolfram region")
        return record


def main():
    sg = TK.make_sigma(); D = TK.DECLS
    ref = TK.reference(); acts = activation(sg, ref, D)
    m, d, c, v, lam = sp.symbols('m d c v lam', nonnegative=True)
    Wsym = {"MAX": m, "DEP": d, "*CC#": c, "VELDEL": v}
    sym = []
    for _k, cand in TK.candidates():
        cf = coefficients(sg, ref, cand, D, acts)
        e = sum(Wsym[n] * (sp.Integer(o) + lam * sp.Integer(nn))
                for n, (o, nn) in cf.items())
        sym.append((TK.observe(sg, cand), sp.expand(e),
                    {n: list(x) for n, x in cf.items()}))
    g = [e for o, e, _ in sym if o == "bebein"][0]
    ineq = [str(sp.expand(e - g)) for o, e, _ in sym if o != "bebein"]
    conj = " && ".join(f"({x}) > 0" for x in ineq)
    out = exact_regions(conj)
    W = {"MAX": 4, "DEP": 6, "*CC#": 30, "VELDEL": 30}
    scan = {}
    for l in (F(0), F(1, 16), F(1, 8), F(2, 15), F(3, 20), F(1, 5), F(1, 4)):
        rows = [(score(coefficients(sg, ref, cand, D, acts), W, l), TK.observe(sg, cand))
                for _k, cand in TK.candidates()]
        mn = min(r[0] for r in rows)
        scan[str(l)] = sorted({r[1] for r in rows if r[0] == mn})
    rec = {"symbolic_scores": {o: str(e) for o, e, _ in sym},
           "coefficients": {o: cf for o, _e, cf in sym},
           "conditions_for_bebein": ["0 < " + x for x in ineq],
           "wolfram_region": out["region"],
           "wolfram_region_at_lambda_zero": out["at_zero"],
           "numeric_scan": scan,
           "attested_output": "bebein"}
    expanded = TK.candidates() + [
        ((key, "delete-final-n"), cand.with_real(TK.NodeId("Or", "lex", 5), TK.ABSENT))
        for key, cand in TK.candidates()]
    expanded_rows = []
    for key, cand in expanded:
        cf = coefficients(sg, ref, cand, D, acts)
        e = sp.expand(sum(Wsym[n] * (o + lam * nn) for n, (o, nn) in cf.items()))
        expanded_rows.append({"output": TK.observe(sg, cand), "coefficients": cf,
                              "symbolic_score": str(e)})
    rec["final_consonant_deletion_control"] = {
        "candidate_count": len(expanded_rows), "rows": expanded_rows,
        "correct_fiber": [r for r in expanded_rows if r["output"] == "bebein"],
        "comparison": {"bebek": "m", "bebein": "m + d"},
        "interpretation": "With nonnegative DEP, final-n deletion weakly dominates the complete correct fiber in this eight-candidate domain; retaining ties does not yield only bebein."}
    rec["source_scope"] = {
        "source": "Bakovic 2007, pp. 226–230, examples (10)–(16)",
        "original_domain": "Four fixed candidates; final-n deletion excluded.",
        "additional_source_competitors": "Example (12) explicitly compares final-consonant deletion with epenthesis.",
        "untranslated_conditions": ["The *CC# declaration has no finality guard.",
                                    "VELDEL has no morphological-boundary guard.",
                                    "Contextual faithfulness, turbidity and the underlying-vowel alternative are not reconstructed."],
        "scope": "Finite interaction demonstration, not a complete Turkish grammar or proof that the source analysis fails."}
    OUT.mkdir(parents=True, exist_ok=True)
    certificate.write("self_destructive_feeding.json", rec)
    print("region over all nonnegative parameters:", rec["wolfram_region"])
    print("region at lambda = 0:", rec["wolfram_region_at_lambda_zero"])
    for k, x in scan.items():
        print(f"  lambda={k:5s} -> {x}")


if __name__ == "__main__":
    main()
