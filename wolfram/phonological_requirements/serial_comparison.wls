root = NestWhile[ParentDirectory, DirectoryName[$InputFileName], !(DirectoryQ[FileNameJoin[{#, "python"}]] && DirectoryQ[FileNameJoin[{#, "wolfram"}]]) &, 1, 8];
outdir = FileNameJoin[{root, "results", "requirements", "wolfram"}];
If[!DirectoryQ[outdir], CreateDirectory[outdir, CreateIntermediateDirectories -> True]];
observations={{"gahe","gahe"},{"gaht","gat"},{"mae","mae"},{"mat","mat"},{"mar@mu","marmu"},{"ah@pt","ah@pt"},{"ah@pr@mu","ah@pr@mu"},{"gahr@mu","gar@mu"},{"ah@pe","ahpe"}};
cs=Characters["ghrmpt"];vs=Characters["a@ue"];
active[s_,i_,r_]:=Module[{l=DeleteCases[Take[s,i-1],Null],q=DeleteCases[Drop[s,i],Null]},
If[r=="H",s[[i]]==="h"&&Length[q]>=1&&MemberQ[cs,First[q]],s[[i]]==="@"&&Length[l]>=2&&MemberQ[cs,Last[l]]&&MemberQ[vs,l[[-2]]]&&Length[q]>=2&&MemberQ[cs,First[q]]&&MemberQ[vs,q[[2]]]]];
step[s_,i_,r_]:=If[active[s,i,r],ReplacePart[s,i->Null],s];
global[s_,order_]:=Fold[Function[{c,r},Table[If[active[c,i,r],Null,c[[i]]],{i,Length[c]}]],Characters[s],order];
block[s_,order_,rtl_]:=Module[{c=Characters[s]},Do[Do[c=step[c,i,r],{r,order}],{i,If[rtl,Reverse[Range[StringLength[s]]],Range[StringLength[s]]]}];c];
surface[s_]:=StringJoin[DeleteCases[s,Null]];
records={};Do[pred=Table[{p[[1]],surface[If[kind=="global",global[p[[1]],order],block[p[[1]],order,kind=="blockRL"]]]},{p,observations}];AppendTo[records,<|"order"->StringJoin[order],"architecture"->kind,"predictions"->Association[Rule@@@pred],"failurecount"->Count[MapThread[Unequal,{Last/@pred,Last/@observations}],True]|>],{order,{{"H","S"},{"S","H"}}},{kind,{"global","blockLR","blockRL"}}];
finalblock[s_,order_]:=Module[{c=Characters[s]},Do[Do[If[c[[i]]===r&&DeleteCases[Drop[c,i],Null]==={},c[[i]]=Null],{r,order}],{i,Length[c]}];surface[c]];
checks=Flatten[Table[{finalblock["CVC",order]==="CV",finalblock["CVCV",order]==="CVC"},{order,{{"C","V"},{"V","C"}}}]];
report=<|"records"->records,"evaluations"->54,"finalblockchecks"->checks|>;
Export[FileNameJoin[{outdir,"serial_comparison.json"}],report,"RawJSON"];
Print[report];If[AllTrue[records,#["failurecount"]>0&]&&And@@checks,Exit[0],Exit[1]];
