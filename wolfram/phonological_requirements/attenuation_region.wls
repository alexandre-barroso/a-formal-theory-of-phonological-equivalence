root = NestWhile[ParentDirectory, DirectoryName[$InputFileName], !(DirectoryQ[FileNameJoin[{#, "python"}]] && DirectoryQ[FileNameJoin[{#, "wolfram"}]]) &, 1, 8];
outdir = FileNameJoin[{root, "results", "requirements", "wolfram"}];
If[!DirectoryQ[outdir], CreateDirectory[outdir, CreateIntermediateDirectories -> True]];
modeldir = FileNameJoin[{root, "wolfram", "phonological_opacity", "gua"}];
Get[FileNameJoin[{modeldir, "model.wl"}]];
Get[FileNameJoin[{modeldir, "GuaData.wl"}]];
alpha = grammar["alphabet"]; inv = grammar["inventory"];
newCoefficients[r_] := Table[Module[{p, a, c},
 p = MapThread[And[#1,Not[#2]]&, {r[[2,k]],r[[3,k]]}];
 c = r[[1,k]];
 If[5 <= k <= 8,
 a = MapThread[And[#1,#2,Not[#3]]&, {initial[[1,k]], initial[[2,k]], initial[[3,k]]}];
 {Total[MapThread[Boole[#1 && #2]&, {p,a}]], Total[MapThread[Boole[#1 && !#2 && #3]&, {p,a,c}]]},
 {Total[MapThread[Boole[#1 && #2]&, {p,c}]],0}]], {k,9}];
subjectA[s_,r_] := Module[{live,old=0,new=0,n,defined,p,a,c},
 live = Select[Range[Length[s]],TrueQ[ft[s[[#]]]["present"]]&];
 Do[n=If[MemberQ[live,q],SelectFirst[live,#>q&,0],0];
 defined = n>0 && words[[n]]==words[[q]]+1 && phrases[[words[[n]]+1]]==phrases[[words[[q]]+1]];
 p=defined && s[[q]]=!=s[[n]];
 c=r[[1,6,q]];
 a=MemberQ[initialPairs,{q,n}];
 old+=Boole[p&&a];new+=Boole[p&&!a&&c],{q,Length[s]}];{old,new}];
allInputs=Join[inputsSelection,inputsDeletion];allObs=Join[observationsSelection,observationsDeletion];
allRecords={}; witness = {3-4 lam,1,1-2 lam,2-2 lam,2,4,4,4,4};
goals=<|"G34a"->774,"G34b"->957,"N7"->82,"G37c"->1584,"C24ei"->63,"OR38"->1261,"C21b"->117,"C23UE"->159|>;
marginPolys={}; fibers=<||>; changed=<||>; comparisons=0;
Do[
 name=input["id"];origin=Lookup[input["slots"],"phone"];words=Lookup[input["slots"],"word"];focal=input["focal"]+1;phrases=input["phrases"];origft=ft/@origin;
 tuples=Tuples[Range[0,12],Length[focal]];initial=readState[origin];
 referenceLive=Select[Range[Length[origin]],TrueQ[ft[origin[[#]]]["present"]]&];
 initialPairs=Table[If[initial[[1,6,q]]&&initial[[2,6,q]]&&!initial[[3,6,q]],{q,SelectFirst[referenceLive,#>q&,0]},Nothing],{q,Length[origin]}];
 rows=Table[s=expandState[tuples[[i+1]]];r=readState[s];cf=newCoefficients[r];cs=ReplacePart[cf,6->subjectA[s,r]];{i,realizeState[s],cf,cs},{i,0,Length[tuples]-1}];
 observed=SelectFirst[allObs,#["id"]==name&]["allowed"];
 correct=Select[rows,MemberQ[observed,#[[2]]]&][[All,1]];AssociateTo[fibers,name->correct];AssociateTo[changed,name->Count[rows,x_/;x[[3]]=!=x[[4]]]];
 wrong=Select[rows,!MemberQ[observed,#[[2]]]&];goal=rows[[goals[name]+1]];
 Do[delta=row[[variant]]-goal[[variant]];poly=Expand[(delta[[All,1]]+lam delta[[All,2]]).witness];AppendTo[marginPolys,poly];comparisons++,{variant,{3,4}},{row,wrong}];
 AppendTo[allRecords,<|"id"->name,"correct"->correct,"rows"->rows|>];Print[name," complete ",Length[rows]],
 {input,allInputs}];
unique=DeleteDuplicates[marginPolys];checks=Table[TimeConstrained[Resolve[ForAll[lam,Implies[0<=lam<1/2,p>0]],Reals],20,$Aborted],{p,unique}];
getCf[id_,i_] := SelectFirst[allRecords,#["id"]==id&]["rows"][[i+1,3]];
db=getCf["G34b",1126]-getCf["G34b",957];dc=getCf["G37c",1571]-getCf["G37c",1584];
wb=Array[w,9];pb=Expand[(db[[All,1]]+lam db[[All,2]]).wb];pc=Expand[(dc[[All,1]]+lam dc[[All,2]]).wb];
dualIdentity=Expand[pb+pc-(1-2 lam)w[5]]===0;
necessary=Resolve[ForAll[{lam,w[5]},Implies[lam>=1/2&&w[5]>=0,(1-2 lam)w[5]<=0]],Reals];
weightCheck=Resolve[ForAll[lam,Implies[0<=lam<1/2,And@@Thread[witness>=0]]],Reals];
res=<|"candidates"->Total[Length[#["rows"]]&/@allRecords],"comparisons"->comparisons,"distinct_polynomials"->Length[unique],"polynomial_checks"->checks,"fibers"->fibers,"subject_changes"->changed,"witness_nonnegative"->weightCheck,"critical_G34b"->ToString[pb,InputForm],"critical_G37c"->ToString[pc,InputForm],"dual_identity"->dualIdentity,"dual_nonpositive"->necessary,"exact_region"->"0 <= lam < 1/2"|>;
Export[FileNameJoin[{outdir,"attenuation_region.json"}],res,"RawJSON"];
Export[FileNameJoin[{outdir,"attenuation_region_coefficients.json"}],allRecords,"RawJSON"];
Print[res];
If[res["candidates"]===9464&&comparisons===18908&&And@@(TrueQ/@checks)&&TrueQ[weightCheck]&&dualIdentity&&TrueQ[necessary],Exit[0],Exit[1]];
