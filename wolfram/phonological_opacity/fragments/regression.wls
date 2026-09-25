Get[FileNameJoin[{DirectoryName[$InputFileName], "GuaCore.wl"}]];
spec = GuaCore`LoadGuaSpec[
  FileNameJoin[{DirectoryName[$InputFileName], "GuaFragmentSpec.wl"}]];
expected = spec["expected_regression"]["per_input"];
failures = {};
total = 0;
Do[Module[{fr = GuaCore`GuaFragment[spec, u["id"]], r, want},
   r = GuaCore`GuaEvaluate[fr];
   want = expected[u["id"]];
   total += r["states"];
   If[r["states"] =!= want["states"], AppendTo[failures, {u["id"], "states", r["states"]}]];
   If[r["fiber"] =!= want["fiber"], AppendTo[failures, {u["id"], "fiber", r["fiber"]}]];
   If[r["minima"] =!= want["minima"], AppendTo[failures, {u["id"], "minima", r["minima"]}]];
   If[r["minimum8"] =!= want["minimum8"], AppendTo[failures, {u["id"], "minimum8", r["minimum8"]}]];
   ], {u, spec["inputs"]}];
If[total =!= spec["expected_regression"]["total_candidates"],
  AppendTo[failures, {"total", total}]];
probe = GuaCore`GuaProbeReport[spec, "constructed_A_locality"];
If[(#["retained8"] & /@ probe) =!= spec["probes"][[1]]["expected"]["retained8"],
  AppendTo[failures, {"probe", "retained8"}]];
Print["  wolfram shared regression: ", If[failures === {}, "PASS", Row[{"FAIL ", failures}]]];
Exit[If[failures === {}, 0, 1]];
