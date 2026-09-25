ClearAll[truth, knot, kand, kor, ev, possible, check];
root = DirectoryName[$InputFileName, 3];
data = Import[FileNameJoin[{root, "results", "requirements", "certificates", "formula_certificates.json"}], "RawJSON"];
If[!AssociationQ[data] || !KeyExistsQ[data, "cases"] || Length[data["cases"]] == 0, Exit[2]];
truth[x_] := Switch[x, True, 1, False, 0, Null, 2, _, Exit[3]];
knot[x_] := {1, 0, 2}[[x + 1]];
kand[x_, y_] := If[x == 0 || y == 0, 0, If[x == 1 && y == 1, 1, 2]];
kor[x_, y_] := If[x == 1 || y == 1, 1, If[x == 0 && y == 0, 0, 2]];
ev[f_, v_] := Switch[f[[1]],
  "constant", truth[f[[2]]], "atom", v[[f[[2]] + 1]],
  "neg", knot[ev[f[[2]], v]],
  "conj", kand[ev[f[[2]], v], ev[f[[3]], v]],
  "disj", kor[ev[f[[2]], v], ev[f[[3]], v]], _, Exit[4]];
possible[f_, a_] := Switch[f[[1]],
  "constant", {truth[f[[2]]]}, "atom", a[[f[[2]] + 1]],
  "neg", Union[knot /@ possible[f[[2]], a]],
  "conj", Union[Flatten[Outer[kand, possible[f[[2]], a], possible[f[[3]], a]], 1]],
  "disj", Union[Flatten[Outer[kor, possible[f[[2]], a], possible[f[[3]], a]], 1]], _, Exit[5]];
check[c_] := Module[{a = Map[truth, c["allowed"], {2}], f = c["formula"], w = truth /@ c["witness"]},
  Switch[c["method"],
    "abstract", TrueQ[c["expected"]] && !MemberQ[possible[f, a], 0],
    "counterexample", SameQ[c["expected"], False] && Length[w] == Length[a] &&
      And @@ MapThread[MemberQ, {a, w}] && ev[f, w] == 0,
    "exhaustive", (And @@ ((ev[f, #] != 0) & /@ Tuples[a])) === c["expected"], _, False]];
checks = check /@ data["cases"];
result = <|"distinct_checks" -> Length[checks], "passed" -> Count[checks, True],
  "failed_indices" -> Pick[Range[0, Length[checks] - 1], TrueQ /@ checks, False],
  "methods" -> Counts[Lookup[data["cases"], "method"]]|>;
out = FileNameJoin[{root, "results", "requirements", "wolfram", "formula_certificates.json"}];
If[!DirectoryQ[DirectoryName[out]], CreateDirectory[DirectoryName[out], CreateIntermediateDirectories -> True]];
Export[out, result, "RawJSON"];
Print[result];
If[!TrueQ[And @@ checks], Exit[1]];
Exit[0];
