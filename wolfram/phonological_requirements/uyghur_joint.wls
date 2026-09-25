ClearAll["Global`*"];
root = DirectoryName[DirectoryName[DirectoryName[$InputFileName]]];
output = FileNameJoin[{root, "build", "uyghur", "algebra", "wolfram.json"}];
If[!DirectoryQ[DirectoryName[output]], CreateDirectory[DirectoryName[output], CreateIntermediateDirectories -> True]];
truth[x_] := If[TrueQ[x], 1, 0];
active[old_, previous_, raised_, value_] := truth[If[raised, previous, old] == value];
initial[old_, value_, partial_] := If[partial, 0, truth[old == value]];
cost[old_, previous_, raised_, suffix_, partial_:False] :=
  Sum[h (initial[old, value, partial] truth[suffix != value] +
    ell (1 - initial[old, value, partial]) active[old, previous, raised, value] truth[suffix != value]), {value, 0, 1}];
current[old_, previous_, raised_, suffix_] := Sum[h active[old, previous, raised, value] truth[suffix != value], {value,0,1}];
checks = {};
Do[
  expected = If[raised && previous != old, If[suffix == old, ell h, h], If[suffix == old, 0, h]];
  AppendTo[checks, FullSimplify[cost[old,previous,raised,suffix] == expected]];
  AppendTo[checks, FullSimplify[cost[old,previous,raised,suffix,True] == ell current[old,previous,raised,suffix]]];
  rival = (1-ell/2) h truth[suffix != old] + ell h/2 truth[suffix != If[raised,previous,old]];
  difference = If[raised && previous != old, ell h/2, 0];
  AppendTo[checks, FullSimplify[cost[old,previous,raised,suffix] - rival == difference]],
  {old,0,1},{previous,0,1},{raised,{False,True}},{suffix,0,1}];
Do[
  unraised = cost[old,previous,False,1-old]-cost[old,previous,False,old];
  raised = cost[old,previous,True,1-old]-cost[old,previous,True,old];
  AppendTo[checks, FullSimplify[unraised == h]];
  AppendTo[checks, FullSimplify[raised == If[old==previous,h,(1-ell)h]]];
  AppendTo[checks, FullSimplify[raised-unraised == If[old==previous,0,-ell h]]],
  {old,0,1},{previous,0,1}];
odds[previous_] := Total[Table[Exp[-r-cost[1,previous,True,suffix]],{suffix,0,1}]] /
 Total[Table[Exp[-u-cost[1,previous,False,suffix]],{suffix,0,1}]];
factor = (Exp[-ell h]+Exp[-h])/(1+Exp[-h]);
AppendTo[checks, FullSimplify[odds[0]/odds[1] == factor, Assumptions -> Element[{r,u,h,ell},Reals]]];
AppendTo[checks, FullSimplify[0 < factor <= 1, Assumptions -> h>=0 && ell>=0]];
AppendTo[checks, FullSimplify[factor < 1, Assumptions -> h>0 && ell>0]];
AppendTo[checks, FullSimplify[1-factor == (1-Exp[-ell h])/(1+Exp[-h]), Assumptions -> Element[{h,ell},Reals]]];
AppendTo[checks, FullSimplify[cost[1,0,True,0] /. ell->1] == h && current[1,0,True,0] == 0];
failures = Select[Range[Length[checks]], checks[[#]] =!= True &];
result = <|"status" -> If[failures==={},"FRAGMENT_ALGEBRA_CHECKS_PASS","FAIL_OR_UNRESOLVED"],
 "checks"->Length[checks], "failures"->failures, "results"->(ToString[#,InputForm]& /@ checks),
 "wolfram_version"->$Version, "script_sha256"->FileHash[$InputFileName,"SHA256","HexString"],
 "scope"->"Declared two-root-vowel/one-suffix feature fragment. No corpus mapping, empirical finding or Lean theorem certification."|>;
Export[output,result,"RawJSON"];
Print[ExportString[result,"RawJSON"]];
Exit[If[failures==={},0,1]];
