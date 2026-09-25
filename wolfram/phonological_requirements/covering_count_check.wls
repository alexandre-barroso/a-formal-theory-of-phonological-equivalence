root = NestWhile[ParentDirectory, DirectoryName[$InputFileName], !(DirectoryQ[FileNameJoin[{#, "python"}]] && DirectoryQ[FileNameJoin[{#, "wolfram"}]]) &, 1, 8];
outdir = FileNameJoin[{root, "results", "requirements", "wolfram"}];
If[!DirectoryQ[outdir], CreateDirectory[outdir, CreateIntermediateDirectories -> True]];
pathCost[d_, wI_, w_] := Module[{prev = 0, t = 0}, Do[t += If[b == 1, wI, If[prev == 1, 0, w]]; prev = b, {b, d}]; t];
doubles[d_] := Count[Partition[Prepend[d, 0], 2, 1], {1, 1}];
cycleCost[d_, r_, w_] := r Total[d] + w Count[Range[Length[d]], j_ /; d[[j]] == 0 && d[[Mod[j - 2, Length[d]] + 1]] == 0];
pathCheck[n_] := Module[{ds = Tuples[{0, 1}, n], wI = 1, w = 3, lam = 1/4, costs, best, mins, mins2},
  costs = pathCost[#, wI, w] & /@ ds; best = Min[costs]; mins = Pick[ds, costs, best];
  mins2 = With[{c2 = costs + lam w doubles /@ ds}, Pick[ds, c2, Min[c2]]];
  {n, best == wI Ceiling[n/2], Length[mins] == If[EvenQ[n], 1, (n + 1)/2], mins2 == {Table[Boole[OddQ[k]], {k, n}]}}];
cycleCheck[k_] := Module[{ds = Tuples[{0, 1}, k], r = 1, w = 3, costs, best, mins},
  costs = cycleCost[#, r, w] & /@ ds; best = Min[costs]; mins = Pick[ds, costs, best];
  {k, best == r Ceiling[k/2], Length[mins] == If[OddQ[k], k, 2]}];
res = <|"path_covering" -> Table[pathCheck[n], {n, 1, 13}], "destruction_cycles" -> Table[cycleCheck[k], {k, 2, 13}]|>;
Export[FileNameJoin[{outdir, "covering_count_check.json"}], res, "JSON"];
Print[res];
If[TrueQ[And @@ Flatten[Rest /@ Join[res["path_covering"], res["destruction_cycles"]]]], Exit[0], Exit[1]];
