root=NestWhile[ParentDirectory,DirectoryName[$InputFileName],!(DirectoryQ[FileNameJoin[{#,"python"}]]&&DirectoryQ[FileNameJoin[{#,"wolfram"}]])&,1,8];
out=FileNameJoin[{root,"results","requirements","wolfram"}];
If[!DirectoryQ[out],CreateDirectory[out,CreateIntermediateDirectories->True]];
check[q_,tag_]:=If[!TrueQ[q],Print["FAIL ",tag," ",InputForm[q]];Exit[1]];
contexts=Tuples[{{0,1},{0,1},{0,1}}];
rates={90,122,683,833,562,648,914,938}/1000;
counts=Round[162*rates];
check[counts=={15,20,111,135,91,105,148,152},"source rounding convention"];
word[l_,s_,b_,g_,m_,d_,c_,x_,y_]:=c*(1-x)+b*x+g*y-l*s-d;
clitic[l_,s_,b_,g_,m_,d_,c_,x_,y_]:=l*(c*(1-x)+b*x+g*y)+m-s;
oldNew=Table[With[{k=ctx[[1]],x=ctx[[2]],y=ctx[[3]]},
 If[k==0,{{0,x,y,0,-1,1-x},{-1,0,0,0,0,0}},
           {{-1,0,0,1,0,0},{0,x,y,0,0,1-x}}]],{ctx,contexts}];
Export[FileNameJoin[{out,"schwa_attenuation_coefficients.json"}],<|"contexts"->contexts,"old_new_score_differences"->oldNew|>,"RawJSON"];
check[Expand[clitic[l,s,b,g,m,d,c,x1,y1]-clitic[l,s,b,g,m,d,c,x0,y0]-
 l*(word[l,s,b,g,m,d,c,x1,y1]-word[l,s,b,g,m,d,c,x0,y0])]==0,"common-effect identity"];
check[Expand[word[l,s,b,g,m,d,c,1,y]-word[l,s,b,g,m,d,c,0,y]]==b-c,"cluster contrast"];
check[Reduce[0<=l<1 && c>=0 && c>=aw && (1-l*l)*c>=aw-l*ac &&
 0<=l*c-ac && c-l*(l*c-ac)-aw<0,{l,c,aw,ac},Reals]===False,"interior chart nonnegative Dep branch"];
check[Reduce[c>=aw && c-aw<0,{c,aw},Reals]===False,"interior chart zero branch"];
check[Simplify[(1/(1+3)+3/(1+3))/2]==1/2,"mixture baseline"];
check[(3/(1+3)+27/(1+27))/2==6/7,"mixture word"];
check[(1/(1+1)+9/(1+9))/2==7/10,"mixture clitic"];
check[((7/10)/(1-7/10))^2!=((6/7)/(1-6/7)),"pooled attenuation counterexample"];
eta=Table[If[ctx[[1]]==0,aw+be*ctx[[2]]+ga*ctx[[3]],ac+la*be*ctx[[2]]+la*ga*ctx[[3]]],{ctx,contexts}];
objective=Total[162*Log[1+Exp[eta]]-counts*eta];
saturated=Total[counts*Log[counts/162]+(162-counts)*Log[(162-counts)/162]];
fit=FindMinimum[{objective,ga>=0 && 0<=la<=1},{{aw,-2},{ac,1/4},{be,3},{ga,1/2},{la,3/5}},
 WorkingPrecision->35,AccuracyGoal->10,PrecisionGoal->10,MaxIterations->1000];
check[MatchQ[fit,{_?NumericQ,{__Rule}}],"free numerical fit"];
profile[lambda_?NumericQ]:=Module[{r},
 r=FindMinimum[{objective/.la->lambda,ga>=0 && If[lambda==1,aw<=ac,True]},{{aw,-2},{ac,1/4},{be,3},{ga,1/2}},
  WorkingPrecision->35,AccuracyGoal->10,PrecisionGoal->10,MaxIterations->1000];
 {N[2*(r[[1]]+saturated),16],r[[2]]}];
threshold=N[InverseCDF[ChiSquareDistribution[1],95/100],30];
dv=N[2*(fit[[1]]+saturated),16];
profileDifference[z_?NumericQ]:=First[profile[z]]-dv-threshold;
lo=z/.FindRoot[profileDifference[z],{z,48/100,49/100},AccuracyGoal->8,PrecisionGoal->8];
hi=z/.FindRoot[profileDifference[z],{z,80/100,82/100},AccuracyGoal->8,PrecisionGoal->8];
check[0<lo<(la/.fit[[2]])<hi<1,"profile interval in parameter domain"];
check[Abs[profileDifference[lo]]<10^-6 && Abs[profileDifference[hi]]<10^-6,"profile endpoint residuals"];
result=<|"independent_contexts"->8,"algebra_checks"->8,"requested_working_precision"->35,
 "lambda"->N[la/.fit[[2]],16],"deviance"->dv,"observable_coefficients"->N[{aw,ac,be,ga}/.fit[[2]],16],
 "profile95"->N[{lo,hi},16],"fixed_lambda_deviances"->Association[Table[ToString[q,InputForm]->First[profile[q]],{q,{0,1/8,1}}]],
 "source"->"Smith and Pater2020 Table14p24; Flemming2021 supplemental schwa_models.R rounds162 times those proportions",
 "scope"->"Aggregate reconstructed-count reference likelihood; numerical optimizer results cross-checked separately, not a proof of sampling adequacy or maximum attainable numerical precision."|>;
Export[FileNameJoin[{out,"schwa_attenuation_fit.json"}],result,"RawJSON"];
Print[InputForm[result]];
Exit[0];
