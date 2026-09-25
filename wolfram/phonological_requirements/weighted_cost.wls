ClearAll["Global`*"];
root = DirectoryName[DirectoryName[DirectoryName[$InputFileName]]];
assert[x_, label_] := If[!TrueQ[x], Print["FAIL: ", label]; Quit[1]];
windows[u_] := Partition[Join[{None, None}, u, {None, None}], 5, 1];
menu[j_, c_] := If[j == 5 && c == 1, {}, Range[0, If[MemberQ[{3, 4}, j], 2, 1]]];
wgt[j_, q_, w_, o_] := If[j == 0, 0,
  Mod[(q + 1) (w[[3]] + 2) + (o + 1) j +
    Sum[k If[w[[k]] === None, 0, w[[k]] + 1], {k, 5}], 7]];
fin[j_, q_] := If[j == 0, 0, Mod[j (q + 1), 4]];
fullScore[j_, u_, v_] := Module[{s},
  s = Fold[Function[{state, pair}, {pair[[2]], state[[2]] + wgt[j, state[[1]], pair[[1]], pair[[2]]]}],
    {0, 0}, Transpose[{windows[u], v}]];
  s[[2]] + fin[j, s[[1]]]];
advance[j_, s_, w_] := If[s[[2]] === {}, s, Module[{raw, m, norm, reduced},
  raw = Flatten[Table[{o, p[[2]] + wgt[j, p[[1]], w, o]}, {p, s[[2]]}, {o, menu[j, w[[3]]]}], 1];
  If[raw === {}, {Null, {}},
    m = Min[raw[[All, 2]]];
    norm = ({#[[1]], #[[2]] - m} &) /@ Select[raw, #[[2]] <= m + If[j == 0, 0, 6] &];
    reduced = ({#[[1, 1]], Min[#[[All, 2]]]} &) /@ GatherBy[norm, First];
    {s[[1]] + m, reduced}]]];
vectorCost[j_, u_] := Module[{s},
  s = Fold[advance[j, #1, #2] &, {0, {{0, 0}}}, windows[u]];
  If[s[[2]] === {}, Null, s[[1]] + Min[(#[[2]] + fin[j, #[[1]]] &) /@ s[[2]]]]];
tables = {}; count = 0; infeasible = 0;
Do[
  Do[
    seqs = Tuples[menu[j, #] & /@ u];
    vals = fullScore[j, u, #] & /@ seqs;
    target = If[vals === {}, Null, Min[vals]];
    got = vectorCost[j, u];
    assert[got === target, {j, u, target, got}];
    count += Length[vals]; If[target === Null, infeasible++];
    AppendTo[tables, {j, u, target}],
    {u, Tuples[{0, 1}, n]}],
  {j, 0, 5}, {n, 0, 5}];
assert[Length[tables] == 378 && count == 22820 && infeasible == 57, "nonzero coverage"];
Export[FileNameJoin[{root, "results", "requirements", "wolfram", "weighted_cost.json"}],
  <|"raw_inputs" -> Length[tables], "candidate_scores" -> count, "infeasible_inputs" -> infeasible,
    "tables" -> tables, "scope" -> "Independent natural-cost vector normalization and exhaustive original objective, including terminal values and empty fibers"|>, "RawJSON"];
Print[<|"raw_inputs" -> Length[tables], "candidate_scores" -> count, "infeasible_inputs" -> infeasible, "status" -> "PASS"|>];
Quit[0];
