ClearAll[generate, inspect, selects];
root = DirectoryName[$InputFileName, 3];
generate[total_] := Flatten[Table[
  Table[<|"total" -> total, "deleted" -> deleted, "host" -> host|>,
    {host, If[!total && deleted, {Null}, {1, 2, Null}]}], {deleted, {False, True}}], 1];
inspect[c_] := Module[{ms, nodes, links, q, long, observed},
  ms = If[c["total"] || !c["deleted"], {0, 1}, {0}];
  nodes = If[c["deleted"], {0, 1}, {0, 1, 2}];
  links = Join[{{0, 1}}, If[MemberQ[ms, 1] && c["host"] =!= Null, {{1, c["host"]}}, {}]];
  q = {Length[Complement[{0, 1, 2}, nodes]],
    Count[nodes, z_ /; z != 1 && !AnyTrue[nodes, # > z &]],
    Count[ms, z_ /; !AnyTrue[links, #[[1]] == z && MemberQ[nodes, #[[2]]] &]],
    Count[Select[{{0, 1}, {1, 2}}, MemberQ[ms, #[[1]]] &], z_ /; !MemberQ[links, z]]};
  long = Count[links, {_, 1}] == 2;
  observed = StringJoin[Table[{"t", "i", "k"}[[j + 1]] <> If[j == 1 && long, "ː", ""], {j, nodes}]];
  Join[c, <|"coefficients" -> q, "output" -> observed,
    "compensates" -> (c["deleted"] && long)|>]];
rows = inspect /@ Join[generate[False], generate[True]];
selects[domain_, key_] := Module[{scores = (# ["coefficients"] . {m, n, l*u, k}) & /@ domain},
  And @@ Table[Implies[And @@ Thread[scores[[i]] <= scores], domain[[i]][key]], {i, Length[domain]}]];
total = Select[rows, TrueQ[#["total"]] &];
derived = Select[rows, SameQ[#["total"], False] &];
assumptions = m >= 0 && n >= 0 && u >= 0 && k >= 0 && l >= 0;
checks = {Length[rows] == 10, Length[total] == 6, Length[derived] == 4,
  Resolve[ForAll[{m, n, u, k, l}, Implies[assumptions,
    Equivalent[selects[total, "compensates"], m+k < n && k < l*u]]], Reals],
  Resolve[ForAll[{m, n, u, k, l}, Implies[assumptions,
    Equivalent[selects[derived, "deleted"], m < n]]], Reals],
  And @@ (SameQ[#["compensates"], False] & /@ derived)};
out = FileNameJoin[{root, "results", "requirements", "wolfram", "compensatory_lengthening_region.json"}];
If[!DirectoryQ[DirectoryName[out]], CreateDirectory[DirectoryName[out], CreateIntermediateDirectories -> True]];
Export[out, <|"rows" -> rows, "checks" -> checks|>, "RawJSON"];
Print[InputForm[checks]];
If[Length[checks] != 6 || !And @@ (TrueQ /@ checks), Exit[1]];
