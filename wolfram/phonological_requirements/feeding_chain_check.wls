root = NestWhile[ParentDirectory, DirectoryName[$InputFileName], !(DirectoryQ[FileNameJoin[{#, "python"}]] && DirectoryQ[FileNameJoin[{#, "wolfram"}]]) &, 1, 8];
outdir = FileNameJoin[{root, "results", "requirements", "wolfram"}];
If[!DirectoryQ[outdir], CreateDirectory[outdir, CreateIntermediateDirectories -> True]];
cost[n_, k_] := Which[k == 0, w, k < n, k wI + lam w, True, n wI];
forced = wI > 0 && w > 0 && lam >= 0 && wI + lam w < w;
runs[n_] := Resolve[ForAll[{wI, w, lam}, forced, Equivalent[And @@ Table[cost[n, n] <= cost[n, k], {k, 0, n}], n wI <= wI + lam w]], Reals];
stops[n_] := Resolve[ForAll[{wI, w, lam}, forced && wI + lam w < n wI, And @@ Table[cost[n, 1] < cost[n, k], {k, DeleteCases[Range[0, n], 1]}]], Reals];
res = <|"runs_to_end_iff" -> Table[runs[n], {n, 2, 9}], "stops_after_first" -> Table[stops[n], {n, 2, 9}],
  "nasal_spreading_threshold" -> Table[With[{cs = Table[cost[n, k], {k, 0, n}] /. {wI -> 1, w -> 8, lam -> 1/2}}, {n, Flatten[Position[cs, Min[cs]]] - 1}], {n, 2, 8}]|>;
Export[FileNameJoin[{outdir, "feeding_chain_check.json"}], res, "JSON"];
Print[res];
If[TrueQ[And @@ Flatten[{res["runs_to_end_iff"], res["stops_after_first"]}]], Exit[0], Exit[1]];
