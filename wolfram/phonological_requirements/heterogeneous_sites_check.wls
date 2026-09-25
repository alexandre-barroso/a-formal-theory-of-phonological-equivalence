root = NestWhile[ParentDirectory, DirectoryName[$InputFileName], !(DirectoryQ[FileNameJoin[{#, "python"}]] && DirectoryQ[FileNameJoin[{#, "wolfram"}]]) &, 1, 8];
outdir = FileNameJoin[{root, "results", "requirements", "wolfram"}];
If[!DirectoryQ[outdir], CreateDirectory[outdir, CreateIntermediateDirectories -> True]];
energy[x_, h_, m_] := h Total[Max[#, 0]^2 & /@ Differences[-Prepend[x, 1]]] + m . x;
cumulative[m_] := Reverse[Accumulate[Reverse[m]]];
exactQuadratic[h_, m_] := Module[{M = cumulative[m], n = Length[m], eta, d, k},
  d = Max[#, 0]/(2 h) & /@ M;
  If[Total[d] <= 1, Return[{d, 0}]];
  For[k = n, k >= 1, k--,
    eta = (Total[M[[1 ;; k]]] - 2 h)/k;
    If[eta >= 0 && M[[k]] > eta && (k == n || M[[k + 1]] <= eta), Return[{Max[#, 0]/(2 h) & /@ (M - eta), eta}]]];
  $Failed];
SeedRandom[20260918];
trials = Table[Module[{n = RandomInteger[{3, 7}], h, m, d, eta, x, val, ok},
  h = RandomInteger[{1, 9}]; m = RandomInteger[{0, 6}, n];
  {d, eta} = exactQuadratic[h, m]; x = 1 - Accumulate[d]; val = energy[x, h, m];
  ok = And @@ Table[Module[{y = Clip[x + RandomInteger[{-2, 2}, n]/8, {0, 1}], ry}, ry = FoldList[Min, y]; energy[ry, h, m] >= val], {40}];
  {n, Total[d] <= 1, And @@ (# >= 0 & /@ d), OrderedQ[Reverse[d]], And @@ (# >= 0 & /@ x), ok, eta >= 0}], {16}];
extension = Table[Module[{n = RandomInteger[{3, 6}], h, m, extra, d1, eta1, d2, eta2},
  h = RandomInteger[{1, 4}]; m = RandomInteger[{1, 6}, n]; extra = RandomInteger[{0, 5}, RandomInteger[{1, 3}]];
  {d1, eta1} = exactQuadratic[h, m]; {d2, eta2} = exactQuadratic[h, Join[m, extra]];
  {Total[d1] == 1, If[Total[d1] == 1, d2[[1 ;; n]] == d1 && And @@ (# == 0 & /@ d2[[n + 1 ;;]]), True]}], {16}];
obstruction = Module[{h = 5, m = {1, 1, -4, 1, 1, 1}, grid = Range[0, 8]/8, witness = {3/4, 5/8, 1, 3/4, 1/2, 3/8}, mono = {7/8, 7/8, 7/8, 5/8, 3/8, 1/4}, monoProfiles, best},
  monoProfiles = Select[Tuples[grid, 6], And @@ Thread[Prepend[#, 1] >= Append[#, -1]] &];
  best = Min[energy[#, h, m] & /@ monoProfiles];
  {energy[witness, h, m] == 3/32, energy[mono, h, m] == 9/32, best == 9/32, Length[monoProfiles] == 3003}];
res = <|"nonnegative_sites_exact_trials" -> trials, "saturated_extension_stability" -> extension, "obstruction" -> obstruction|>;
Export[FileNameJoin[{outdir, "heterogeneous_sites_check.json"}], res, "JSON"];
Print[res];
If[TrueQ[And @@ Flatten[{Rest /@ trials, Last /@ extension, obstruction}]], Exit[0], Exit[1]];
