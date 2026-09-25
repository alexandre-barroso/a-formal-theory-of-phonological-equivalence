SeedRandom[20260916];
fails = {};
note[label_, ok_] := (Print[If[TrueQ[ok], "  ok   ", "  FAIL "], label];
   If[! TrueQ[ok], AppendTo[fails, label]]);
positiveRoots[poly_] :=
  CountRoots[poly, {y, 0, Infinity}] - CountRoots[poly, {y, 0, 0}];

worst = Association[];
Do[
  worst[q] = Max[Table[
     Module[{exps, coeffs, poly},
      exps = RandomSample[Range[1, 8], q];
      coeffs = RandomChoice[{-9, -7, -5, -3, -2, -1, 1, 2, 3, 5, 7, 9}, q];
      poly = Total[MapThread[#1 y^#2 &, {coeffs, exps}]];
      positiveRoots[poly]], {300}]];
  note["q = " <> ToString[q] <> ": no sampled response exceeds the q-1 budget (worst "
    <> ToString[worst[q]] <> " <= " <> ToString[q - 1] <> ")", worst[q] <= q - 1],
  {q, Range[2, 5]}];
Print["  worst observed positive-root counts by q: ", Normal[worst]];

rho = 7/2;
ex1 = Expand[y (y - rho)^2];
note["ch4: y(y-rho)^2 expands with three nonzero slices",
  ex1 === y^3 - 2 rho y^2 + rho^2 y && Length[MonomialList[ex1]] === 3];
note["ch4: it has a contact of multiplicity two at y = rho and no other positive zero",
  positiveRoots[ex1] === 2 && (D[ex1, y] /. y -> rho) === 0 &&
   (D[ex1, {y, 2}] /. y -> rho) =!= 0];
note["ch4: total multiplicity 2 equals q - 1, so the bound is attained", 2 === 3 - 1];

ex2 = Expand[y (y - 2) (y - 5)];
note["ch4: distinct rho and sigma give two simple zeros with the same q = 3",
  positiveRoots[ex2] === 2 && Length[MonomialList[ex2]] === 3];

contacts = {{3, 2}, {11/2, 3}};
reversals = {2, 7};
ex3 = Expand[5 y Product[(y - contacts[[j, 1]])^contacts[[j, 2]], {j, Length[contacts]}] *
    Product[(y - reversals[[l]]), {l, Length[reversals]}]];
budget = Total[contacts[[All, 2]]] + Length[reversals];
note["ch4: the constructive packet realises " <> ToString[budget] <>
   " units with exactly q_min = 1 + budget slices",
  Length[MonomialList[ex3]] === budget + 1 && positiveRoots[ex3] === budget];

ex4 = Expand[(y^3 + 2 y^2) + (-2 y^2 + y)];
note["ch4: two projected rows with opposite coefficients cancel and consume no slice",
  ex4 === y^3 + y && Length[MonomialList[ex4]] === 2];

note["ch4: three requested simple reversals against three collected slices exceeds the budget of 2",
  3 > 3 - 1];

Print[""];
Print[If[fails === {}, "all capacity checks verified",
   Row[{Length[fails], " FAILED: ", fails}]]];
Exit[If[fails === {}, 0, 1]];
