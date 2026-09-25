ClearAll["Global`*"];
root = DirectoryName[DirectoryName[DirectoryName[$InputFileName]]];
assert[x_, tag_] := If[!TrueQ[x], Print["FAIL ", tag]; Quit[1]];
windows[u_] := Partition[Join[{0, 0}, u + 1, {0, 0}], 5, 1];
menu[m_, x_] := Which[MemberQ[{0, 3}, m], {-1, 0, 1}, x == 0, {0}, x == 1, {-1, 0, 1}, m == 2, {}, True, {-1}];
full[m_, u_, v_] := Module[{w = windows[u], live, zs, deletionSum, padded},
  live = Select[Range[Length[v]], v[[#]] >= 0 &];
  zs = (w[[#]].{1, 2, 3, 5, 7} + 13 (v[[#]] + 1)) & /@ live;
  deletionSum = Total[(Mod[Total[w[[#]]] + m + 3, 21] &) /@ Select[Range[Length[v]], v[[#]] == -1 &]];
  padded = Partition[Join[{0, 0}, zs, {0, 0}], 5, 1];
  If[m == 3, 0, deletionSum + Total[Mod[#.{11, 17, 1, 19, 23} + m, 21] & /@ padded]]];
common[u_, v_] := Module[{k = 0}, While[k < Min[Length[u], Length[v]] && u[[k + 1]] == v[[k + 1]], k++]; k];
short = Flatten[Table[Tuples[{0, 1, 2}, n], {n, 0, 4}], 1];
long = Join[Table[Join[ConstantArray[0, n - 3], {1, 2, 1}], {n, {7, 19, 43, 120}}],
  Table[Join[ConstantArray[0, n - 2], {2, 1}], {n, {7, 19, 43, 120}}]];
tables = {}; candidates = 0; infeasible = 0; pairs = 0; longPairs = 0; ties = 0;
Do[
  rows = {};
  Do[
    seqs = Tuples[menu[m, #] & /@ u];
    vals = full[m, u, #] & /@ seqs;
    candidates += Length[vals];
    minimum = If[vals === {}, Null, Min[vals]];
    winners = If[vals === {}, {}, Pick[seqs, (# == minimum &) /@ vals]];
    If[minimum === Null, infeasible++];
    If[m == 3, assert[Length[winners] == Length[seqs], "all ties"]; ties += Length[winners]];
    row = <|"model" -> m, "input" -> u, "minimum" -> minimum, "winners" -> winners, "scores" -> vals|>;
    AppendTo[rows, row]; AppendTo[tables, row],
    {u, If[MemberQ[{1, 2}, m], Join[short, long], short]}];
  feasible = Select[rows, #["minimum"] =!= Null &];
  c = If[m == 3, 0, 20];
  Do[
    u = a["input"]; v = b["input"]; k = common[u, v]; n = Max[0, k - 2];
    assert[Take[windows[u], n] === Take[windows[v], n], "annotation prefix"];
    assert[Abs[(a["minimum"] - b["minimum"])/7] <= c/7 (4 + Length[u] + Length[v] - 2 k), "cross input"];
    splice = Join[Take[First[a["winners"]], n], Drop[First[b["winners"]], n]];
    assert[And @@ MapThread[MemberQ[menu[m, #1], #2] &, {v, splice}], "product membership"];
    assert[full[m, v, splice] <= a["minimum"] + c (4 + Length[v] - k), "one-sided construction"];
    If[Max[Length[u], Length[v]] < 7, pairs++, longPairs++],
    {a, feasible}, {b, feasible}],
  {m, 0, 3}];
assert[Length[tables] == 500 && candidates == 15932 && infeasible == 98 && pairs == 44884 && longPairs == 2000 && ties == 7381, "expected counts"];
result = <|"status" -> "PASS", "candidate_scores" -> candidates, "short_pair_bounds" -> pairs,
  "long_pair_bounds" -> longPairs, "infeasible" -> infeasible, "all_tied_candidates" -> ties, "tables" -> tables|>;
Export[FileNameJoin[{root, "results", "requirements", "wolfram", "cross_input_variation.json"}], result, "RawJSON"];
Print[KeyDrop[result, "tables"]];
Quit[0];
