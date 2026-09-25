root = NestWhile[ParentDirectory, DirectoryName[$InputFileName], !(DirectoryQ[FileNameJoin[{#, "python"}]] && DirectoryQ[FileNameJoin[{#, "wolfram"}]]) &, 1, 8];
outdir = FileNameJoin[{root, "results", "requirements", "wolfram"}];
If[!DirectoryQ[outdir], CreateDirectory[outdir, CreateIntermediateDirectories -> True]];
placements[k_] := Length[Flatten[Table[{i, j, k - i - j}, {i, 0, k}, {j, 0, k - i}], 1]];
scoreZeroCount[k_] := 3 placements[k];
res = <|"score_zero_counts" -> Table[{k, scoreZeroCount[k], scoreZeroCount[k] == 3 (k + 1) (k + 2)/2}, {k, 0, 8}],
  "quotient_level_minimum" -> Table[{k, 2 k}, {k, 0, 6}],
  "level_ratio_crosses_one_at_critical_temperature" -> (And @@ Flatten[Table[Reduce[m Exp[-d/T] < 1 && T > 0 && !(T < d/Log[m]), T, Reals] === False && Reduce[T > 0 && T < d/Log[m] && !(m Exp[-d/T] < 1), T, Reals] === False, {m, {2, 3, 5, 13}}, {d, {1, 2, 7/2}}]]),
  "series_converges_below" -> Resolve[ForAll[r, 0 < r < 1, SumConvergence[(k + 1)^3 r^k, k]], Reals],
  "series_diverges_at_or_above" -> Resolve[ForAll[r, r >= 1, !SumConvergence[(k + 1)^3 r^k, k]], Reals],
  "closed_form_below" -> Simplify[Sum[(k + 1)^3 r^k, {k, 0, Infinity}, Assumptions -> 0 < r < 1] == (1 + 4 r + r^2)/(1 - r)^4, 0 < r < 1],
  "binomial_bound" -> And @@ Flatten[Table[Binomial[n + k, n] <= (k + 1)^n, {n, 0, 12}, {k, 0, 12}]]|>;
Export[FileNameJoin[{outdir, "quotient_temperature_check.json"}], res, "JSON"];
Print[res];
If[TrueQ[And @@ (Last /@ res["score_zero_counts"]) && res["level_ratio_crosses_one_at_critical_temperature"] && res["series_converges_below"] && res["series_diverges_at_or_above"] && res["closed_form_below"] && res["binomial_bound"]], Exit[0], Exit[1]];
