root=NestWhile[ParentDirectory,DirectoryName[$InputFileName],!(DirectoryQ[FileNameJoin[{#,"python"}]]&&DirectoryQ[FileNameJoin[{#,"wolfram"}]])&,1,8];
out=FileNameJoin[{root,"results","requirements","wolfram"}];
If[!DirectoryQ[out],CreateDirectory[out,CreateIntermediateDirectories->True]];
check[q_,tag_]:=If[!TrueQ[q],Print["FAIL ",tag," ",InputForm[q]];Exit[1]];
source=<|"experiment1"-><|"counts"-><|"T2T3T1"-><|"T2T3T1"->259|>,"T3T3T1"-><|"T3T3T1"->7,"T2T3T1"->242|>,"T2T1T1"-><|"T2T1T1"->74,"T2T3T1"->167|>,"T3T1T1"-><|"T3T1T1"->59,"T3T3T1"->46,"T2T3T1"->131|>|>|>,"experiment2"-><|"counts"-><|"T2T3T4"-><|"T2T3T4"->386|>,"T3T3T4"-><|"T3T3T4"->20,"T2T3T4"->368|>,"T2T4T4"-><|"T2T4T4"->156,"T2T3T4"->212|>,"T3T4T4"-><|"T3T4T4"->98,"T3T3T4"->213,"T2T3T4"->68|>|>|>|>;
decode[s_]:=ToExpression /@ StringCases[s,DigitCharacter];
encode[s_]:=StringJoin[("T"<>ToString[#])& /@ s];
reg={1,0,0,1};cont={1,2,3,4};
rules={{3,2},{1,3},{4,3}};
names={"S33","S11","S44","IDENT_REG","IDENT_CONT","IDENT_R","IDENT_FINAL"};
read[ref_,cand_]:=Module[{old=ConstantArray[0,7],new=ConstantArray[0,7],n=Length[ref],a,c,p},
 Do[Do[
   a=i<n && ref[[i]]==rules[[j,1]] && ref[[i+1]]==rules[[j,1]];
   c=i<n && cand[[i]]==rules[[j,1]] && cand[[i+1]]==rules[[j,1]];
   p=i<n && cand[[i+1]]==rules[[j,1]] && cand[[i]]!=rules[[j,2]];
   old[[j]]+=Boole[a && p];new[[j]]+=Boole[!a && c && p],{j,3}];
  old[[4]]+=Boole[reg[[ref[[i]]]]!=reg[[cand[[i]]]]];
  old[[5]]+=Boole[cont[[ref[[i]]]]!=cont[[cand[[i]]]]];
  old[[6]]+=Boole[i>1 && ref[[i-1]]==ref[[i]] && ref[[i]]!=cand[[i]]];
  old[[7]]+=Boole[i==n && ref[[i]]!=cand[[i]]],{i,n}];{old,new}];
records={};groups=<||>;
Do[table=source[ex]["counts"];
 groups[ex]=Table[
  ref=decode[ur];cands=Tuples[Range[4],Length[ref]];
  check[Length[cands]==64 && DuplicateFreeQ[cands],"candidate exhaustiveness"];
  ab=read[ref,#]& /@ cands;
  Do[AppendTo[records,<|"input"->ur,"output"->encode[cands[[i]]],"old"->ab[[i,1]],"new"->ab[[i,2]]|>],{i,64}];
  <|"a"->ab[[All,1]],"b"->ab[[All,2]],"y"->(Lookup[table[ur],encode[#],0]& /@ cands)|>,{ur,Keys[table]}],
 {ex,{"experiment1","experiment2"}}];
Export[FileNameJoin[{out,"tonal_attenuation_coefficients.json"}],<|"names"->names,"records"->records|>,"RawJSON"];
check[Length[records]==512,"nonzero expected count"];

loss[ex_,weights_,lam_]:=Total[Function[g,
  With[{sc=(g["a"]+lam*g["b"]).weights},g["y"].sc+Total[g["y"]]*Log[Total[Exp[-sc]]]]]/@groups[ex]];
w1={ts1,tf1,0,tr1,tc1,60,60};w2={ts2,0,tf2,tr2,tc2,60,60};
obj1=loss["experiment1",w1,tl];obj2=loss["experiment2",w2,tl];
constraints1=And@@Join[Thread[0<={ts1,tr1,tc1,tf1}],Thread[{ts1,tr1,tc1,tf1}<=60]];
constraints2=And@@Join[Thread[0<={ts2,tr2,tc2,tf2}],Thread[{ts2,tr2,tc2,tf2}<=60]];
Print["512 candidate coefficient vectors constructed; beginning numerical fits."];
f1=FindMinimum[{obj1,constraints1 && 0<=tl<=1},{{ts1,6},{tr1,30},{tc1,3},{tf1,35},{tl,1/2}},
 WorkingPrecision->35,AccuracyGoal->10,PrecisionGoal->10,MaxIterations->1000];
Print["experiment1 ",InputForm[f1]];
f2=FindMinimum[{obj2,constraints2 && 0<=tl<=1},{{ts2,6},{tr2,30},{tc2,3},{tf2,35},{tl,1/4}},
 WorkingPrecision->35,AccuracyGoal->10,PrecisionGoal->10,MaxIterations->1000];
Print["experiment2 ",InputForm[f2]];
fj=FindMinimum[{obj1+obj2,constraints1 && constraints2 && 0<=tl<=1},
 {{ts1,8},{tr1,30},{tc1,3},{tf1,35},{ts2,6},{tr2,30},{tc2,3},{tf2,35},{tl,1/4}},
 WorkingPrecision->35,AccuracyGoal->10,PrecisionGoal->10,MaxIterations->1000];
Print["shared ",InputForm[fj]];
check[MatchQ[f1,{_?NumericQ,{__Rule}}] && MatchQ[f2,{_?NumericQ,{__Rule}}] && MatchQ[fj,{_?NumericQ,{__Rule}}],"fit returned numeric results"];
result=<|"candidate_vectors"->Length[records],"locus_declaration_reads"->10752,"working_precision"->35,
 "experiment1"-><|"nll"->N[f1[[1]],16],"lambda"->N[tl/.f1[[2]],16],"weights"->N[{ts1,tr1,tc1,tf1}/.f1[[2]],16]|>,
 "experiment2"-><|"nll"->N[f2[[1]],16],"lambda"->N[tl/.f2[[2]],16],"weights"->N[{ts2,tr2,tc2,tf2}/.f2[[2]],16]|>,
 "shared"-><|"nll"->N[fj[[1]],16],"lambda"->N[tl/.fj[[2]],16],"weights"->N[{ts1,tr1,tc1,tf1,ts2,tr2,tc2,tf2}/.fj[[2]],16]|>,
 "deviance"->N[2*(fj[[1]]-f1[[1]]-f2[[1]]),16],
 "source"->"Du and Durvasula2022 Tables2 and5, printedpp573 and579; aggregate counts",
 "scope"->"Independent high-precision numerical local optimization; not a proof of global optimality or sampling assumptions."|>;
Export[FileNameJoin[{out,"tonal_attenuation_fit.json"}],result,"RawJSON"];
Print[InputForm[result]];
Exit[0];
