tensor = {
  {{0,0,0,0},{0,1,1,0},{1,0,0,1},{1,1,1,1}},
  {{0,0,0,1},{0,1,0,0},{1,0,0,2},{1,1,0,1}},
  {{0,0,1,0},{0,1,2,0},{1,0,0,0},{1,1,1,0}},
  {{0,0,1,1},{0,1,1,0},{1,0,0,1},{1,1,0,0}}};
rankings = Permutations[{1,2,3,4}];
winner[i_, r_] := Module[{keys, best, ties},
  keys = Table[tensor[[i, k]][[r]], {k, 4}];
  best = First[SortBy[keys, Identity]];
  ties = Flatten[Position[keys, best]];
  If[Length[ties] =!= 1, Abort[]];
  First[ties]];
winnerMaps = Table[Table[winner[i, r], {i, 4}], {r, rankings}];
mappings = Flatten[Table[{i, s}, {i, 4}, {s, 4}], 1];
event[m_] := Select[Range[Length[winnerMaps]], winnerMaps[[#, m[[1]]]] === m[[2]] &];
implications = Select[Tuples[mappings, 2],
   #[[1]] =!= #[[2]] && SubsetQ[event[#[[2]]], event[#[[1]]]] &];
live = Select[implications, event[#[[1]]] =!= {} &];
Print["nonreflexive implications: ", Length[implications]];
Print["empty antecedents: ", Length[implications] - Length[live]];
Print["live: ", Length[live]];
Print["distinct winner maps: ", Length[DeleteDuplicates[winnerMaps]]];

vars = {a, b, c, d};
mu[i_, s_] := Times @@ (vars^tensor[[i, s]]);
zed[i_] := Sum[mu[i, s], {s, 4}];
poly[{{i_, s_}, {j_, t_}}] := mu[j, t] zed[i] - mu[i, s] zed[j];
domain = 0 < a <= 1 && 0 < b <= 1 && 0 < c <= 1 && 0 < d <= 1;

liveConds = And @@ (poly[#] >= 0 & /@ live);
allConds  = And @@ (poly[#] >= 0 & /@ implications);
coneConds = d - b^2 c >= 0 && c - a^2 d >= 0;

Print["live but outside the declared cone: ",
  Reduce[domain && liveConds && !coneConds, vars, Reals]];
Print["in the declared cone but not live: ",
  Reduce[domain && coneConds && !liveConds, vars, Reals]];
Print["all 121 rows: ", Reduce[domain && allConds, vars, Reals]];
Print["interior witness a=b=c=d=1/2 satisfies the cone: ",
  coneConds /. {a -> 1/2, b -> 1/2, c -> 1/2, d -> 1/2}];
