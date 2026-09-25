root = NestWhile[ParentDirectory, DirectoryName[$InputFileName], !(DirectoryQ[FileNameJoin[{#, "python"}]] && DirectoryQ[FileNameJoin[{#, "wolfram"}]]) &, 1, 8];
outdir = FileNameJoin[{root, "results", "requirements", "wolfram"}];
If[!DirectoryQ[outdir], CreateDirectory[outdir, CreateIntermediateDirectories -> True]];
pos = rA > 0 && rB > 0 && wA > 0 && wB > 0;
neither = wA + wB; aOnly[cB_] := rA + If[cB, 0, wB]; bOnly[cA_] := rB + If[cA, 0, wA]; both = rA + rB;
res = <|
  "counterbleeding_not_carried_iff" -> Resolve[ForAll[{rA, rB, wA, wB}, pos, Equivalent[both < bOnly[False], rA < wA]], Reals],
  "counterbleeding_carried_never" -> Resolve[ForAll[{rA, rB, wA, wB}, pos, !(both < bOnly[True])], Reals],
  "bleeding_iff_carried" -> Resolve[ForAll[{rA, rB, wA, wB}, pos && rA < wA, (bOnly[True] < both) && !(bOnly[False] < both)], Reals],
  "mutual_both_apply_iff" -> And @@ Flatten[Table[Resolve[ForAll[{rA, rB, wA, wB}, pos, Equivalent[both < aOnly[cB] && both < bOnly[cA] && both < neither, !cA && !cB && rA < wA && rB < wB]], Reals], {cA, {False, True}}, {cB, {False, True}}]],
  "feeding_needs_positive_attenuation" -> Resolve[ForAll[{rB, wB, lam}, rB >= 0 && wB > 0 && lam >= 0, Implies[rB < lam wB, lam > 0]], Reals],
  "counterfeeding_needs_attenuation_below_one" -> Resolve[ForAll[{rB, wB, lam}, rB >= 0 && wB > 0 && lam >= 0 && rB < wB, Implies[lam wB < rB, lam < 1]], Reals]
|>;
Export[FileNameJoin[{outdir, "modes_check.json"}], res, "JSON"];
Print[res];
If[TrueQ[And @@ Values[res]], Exit[0], Exit[1]];
