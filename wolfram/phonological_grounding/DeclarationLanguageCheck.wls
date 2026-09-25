root = DirectoryName[DirectoryName[DirectoryName[$InputFileName]]];
Get[FileNameJoin[{root, "wolfram", "phonological_grounding", "LCore.wl"}]];

spec = LCore`LoadSpec[FileNameJoin[{root, "wolfram", "phonological_opacity", "fragments", "GuaFragmentSpec.wl"}]];
ast = LCore`LoadSpec[FileNameJoin[{root, "wolfram", "phonological_grounding", "LSchemasSpec.wl"}]];

status = 0;
report[label_, ok_] := (Print[If[ok, "  PASS  ", "  FAIL  "], label];
                        If[! ok, status = 1]);

expected = spec["expected_regression"]["per_input"];

Do[
  Module[{schemas = ast["gua"][variant], results},
    Print["-- variant ", variant, " --"];
    results = Table[
      Module[{fr = LCore`LFragment[spec, u["id"]], ev},
        fr = LCore`LFragment[spec, u["id"]];
        ev = LCore`LEvaluate[fr, schemas];
        ev], {u, spec["inputs"]}];
    Do[Module[{ev = r, exp = expected[r["id"]]},
       report[r["id"] <> " minimum8=" <> ToString[ev["minimum8"]] <>
              " minima=" <> ToString[ev["minima"]] <>
              " fiber=" <> ToString[ev["fiber"]],
              ev["minimum8"] === exp["minimum8"] &&
              ev["minima"] === exp["minima"] &&
              ev["fiber"] === exp["fiber"]]], {r, results}]],
  {variant, {"baseline", "dynamic_next_word"}}];

Print["-- appendix G.6 probe --"];
Do[Module[{pr = LCore`LProbe[spec, ast["gua"][variant], "constructed_A_locality"]},
   Print["   ", variant, "  retained8 = ", pr["retained8"],
         "   readers = ", #["readers"] & /@ pr["rows"]];
   If[variant === "baseline",
      report["baseline reproduces the nonlocality {0,64}", pr["retained8"] === {0, 64}],
      report[variant <> " is scope-safe (equal retained cost)",
             Length[DeleteDuplicates[pr["retained8"]]] === 1]]],
  {variant, {"baseline", "dynamic_next_word", "witness", "origin_bound"}}];

Print["-- frozen policies: exactly 156 changed scores per opaque input --"];
Do[Module[{schemasA = ast["gua"]["baseline"], schemasB = ast["gua"][variant]},
   Do[Module[{fr = LCore`LFragment[spec, id], refA, refB, n},
      refA = LCore`LReaders[fr, schemasA, fr["reference"]];
      refB = LCore`LReaders[fr, schemasB, fr["reference"]];
      n = Count[Table[
            LCore`LScore8[fr, schemasA, LCore`Private`candidateOf[fr, i], refA] =!=
            LCore`LScore8[fr, schemasB, LCore`Private`candidateOf[fr, i], refB],
            {i, 0, fr["size"] - 1}], True];
      report[variant <> " / " <> id <> " changed scores = " <> ToString[n],
             n === If[MemberQ[{"G34a", "G34b"}, id], 156, 0]]],
     {id, {"G34a", "G34b", "N7", "C24ei"}}]],
  {variant, {"witness"}}];

Print["== wolfram cross-check exit ", status, " =="];
Exit[status];
