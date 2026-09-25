ClearAll[parse, voice, coeff, rows, score];
run = DirectoryName[DirectoryName[DirectoryName[$InputFileName]]];
fixture = Import[FileNameJoin[{run,"results","requirements","certificates","gapped_scope.json"}], "RawJSON"];
pairs = Transpose[{Characters["ptksfčţxʂʃ"], Characters["bdgzvǰʣɣʐʒ"]}];
choices = Association[Flatten[Map[Function[p, {p[[1]] -> p, p[[2]] -> p}],pairs]]];
AssociateTo[choices, {"Č"->{"č","ǰ"},"Ţ"->{"ţ","ʣ"},"X"->{"x","ɣ"},"Ʃ"->{"ʃ","ʒ"}}];
classes = <|"NO_VOICED_AFF"->Characters["čǰţʣČŢ"],"NO_VOICED_DORFRIC"->Characters["xɣX"],"NO_VOICED_PALFRIC"->Characters["ʃʒƩ"]|>;
voice[c_] := If[MemberQ[Characters["ČŢXƩ"],c], -1, Boole[MemberQ[Characters["bdgzvǰʣɣʐʒ"],c]]];
parse[text_] := Module[{word=0,segs={},words={}},
 Scan[If[#==" ",word++,If[# != "-",AppendTo[segs,#];AppendTo[words,word]]]&,Characters[text]];{segs,words}];
coeff[u_, y_, words_, names_] := Module[{r=Association[Thread[names->ConstantArray[{0,0},Length[names]]]], old,cur,change,pre,inc},
 inc[key_,j_] := (r[key]=ReplacePart[r[key],j->(r[key][[j]]+1)]);
 Do[If[KeyExistsQ[choices,u[[j]]],
 old=voice[u[[j]]];cur=voice[y[[j]]];change=old != -1 && old != cur;
 If[change,inc["ID_VOICE",1]];
 pre=j<Length[u] && words[[j]]==words[[j+1]] && MemberQ[Characters["aeioumnlrwj"],u[[j+1]]];
 If[change&&pre,inc["ID_PRESON_VOICE",1]];
 If[cur==1,inc["NO_VOICE",If[old==1,1,2]];
   Scan[If[KeyExistsQ[r,#]&&MemberQ[classes[#],u[[j]]],inc[#,If[old==1,1,2]]]&,Keys[classes]]];
 If[j<Length[u]&&KeyExistsQ[choices,u[[j+1]]]&&cur != -1 &&voice[y[[j+1]]] != -1&&cur != voice[y[[j+1]]],
   inc["AGREE_BOTH",If[old != -1&&voice[u[[j+1]]] != -1&&old != voice[u[[j+1]]],1,2]]]],{j,Length[u]}];r];
rows[text_,names_] := Module[{u,words,ys},
 {u,words}=parse[text];ys=Tuples[Map[If[KeyExistsQ[choices,#],choices[#],{#}]&,u]];
 Map[Function[y,{StringJoin[Table[If[j>1&&words[[j]]!=words[[j-1]]," ",""]<>y[[j]],{j,Length[y]}]], coeff[u,y,words,names]}],ys]];
score[c_,w_,l_] := Total[KeyValueMap[Function[{k,v},w[k]*(v[[1]]+l*v[[2]])],c]];
checks=0; failures={}; outputs={};
Do[
 rr=rows[row["lexical"],Keys[row["weights"]]];l=ToExpression[row["lambda"]];
 costs=Map[score[#[[2]],row["weights"],l]&,rr];best=Min[costs];
 wins=Sort[Pick[rr[[All,1]],Map[#==best&,costs]]];
 If[wins!=row["winners"]||best!=ToExpression[row["score"]]||Length[rr]!=row["candidates"],AppendTo[failures,row]];
 checks+=Length[rr];AppendTo[outputs,<|"branch"->row["branch"],"lambda"->row["lambda"],"input"->row["input"],"candidates"->Length[rr],"winners"->wins,"score"->ToString[best,InputForm]|>],
 {row,fixture["finite"]}];
contradiction = Reduce[k>0 && n>(i+p-v)/k && n*k+v<=i+p,{i,p,v,k,n},Reals];
allOK = Length[failures]==0 && checks==1596 && contradiction===False;
report=<|"passed"->allOK,"complete_candidate_checks"->checks,"finite_comparisons"->Length[outputs],"archimedean_inequality_counterexample_region"->ToString[contradiction,InputForm],"failures"->failures,"finite"->outputs|>;
Export[FileNameJoin[{run,"results","requirements","wolfram","gapped_scope.json"}],report,"RawJSON"];
Print[KeyDrop[report,{"finite","failures"}]];
If[!allOK,Exit[1]];
