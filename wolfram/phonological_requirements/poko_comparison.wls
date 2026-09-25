ClearAll[graph, faith];
root = DirectoryName[$InputFileName, 3];
graph[t_, e_, removed_, added_] := {Complement[t, removed], Union[Select[e, !MemberQ[removed, #[[1]]] &], added]};
faith[ref_, c_] := {Count[Complement[ref[[1]], c[[1]]], t_ /; StringStartsQ[t, "H"]],
  Count[Complement[c[[2]], ref[[2]]], {t_, _} /; StringStartsQ[t, "H"]],
  Count[Complement[ref[[1]], c[[1]]], t_ /; StringStartsQ[t, "M"]],
  Count[Complement[ref[[2]], c[[2]]], {t_, _} /; StringStartsQ[t, "M"]]};
positive = {{"M0", "M1", "H1", "M2"}, {{"M0", 0}, {"M1", 1}, {"M2", 2}}};
negative = {{"M0", "H0", "M1", "H1"}, {{"M0", 0}, {"M1", 1}}};
rows = {faith[positive, graph[positive[[1]], positive[[2]], {"H1"}, {}]],
  faith[positive, graph[positive[[1]], positive[[2]], {"M2"}, {{"H1", 2}}]],
  faith[negative, graph[negative[[1]], negative[[2]], {"H0", "H1"}, {}]],
  faith[negative, graph[negative[[1]], negative[[2]], {"M1", "H1"}, {{"H0", 1}}]]};
scores = (# . {h, d, m, a}) & /@ rows;
checks = {rows === {{1,0,0,0}, {0,1,1,1}, {2,0,0,0}, {1,1,1,1}},
  Resolve[ForAll[{h,d,m,a}, Equivalent[scores[[2]] < scores[[1]], d+m+a<h]], Reals],
  Resolve[ForAll[{h,d,m,a}, Equivalent[scores[[3]] < scores[[4]], h<d+m+a]], Reals],
  SameQ[Reduce[scores[[2]]<scores[[1]] && scores[[3]]<scores[[4]], {h,d,m,a}, Reals], False],
  Resolve[ForAll[{h,d,m,a}, Equivalent[scores[[2]]<=scores[[1]] && scores[[3]]<=scores[[4]], h==d+m+a]], Reals],
  Resolve[ForAll[{n,i,j,f,h}, Equivalent[f*(n-1)+h==f*(n-1)+h, True]], Reals],
  Resolve[ForAll[{total,i,j}, Equivalent[total-(n-1-i)<total-(n-1-j), i<j]], Reals]};
out = FileNameJoin[{root, "results", "requirements", "wolfram", "poko_comparison.json"}];
If[!DirectoryQ[DirectoryName[out]], CreateDirectory[DirectoryName[out], CreateIntermediateDirectories -> True]];
Export[out, <|"source_rows" -> rows, "checks" -> checks|>, "RawJSON"];
Print[InputForm[checks]];
If[Length[checks] != 7 || !And @@ (TrueQ /@ checks), Exit[1]];
