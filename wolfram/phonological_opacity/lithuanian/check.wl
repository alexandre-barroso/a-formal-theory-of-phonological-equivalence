ClearAll["Global`*"];
base=DirectoryName[$InputFileName];
inputs={{"PG",{"p","b"},{"k","g"},"auti",1,0,"abgauti"},
 {"PB",{"p","b"},{"p","b"},"erti",1,1,"apiberti"},
 {"TT",{"t","d"},{"t","d"},"aiki:ti",0,1,"atitaiki:ti"}};
configs={{"O",0,-1},{"RR",0,1/8},{"SR",1,1/8},{"RS",2,1/8},{"SS",3,1/8},{"RR0",0,0}};
bits[j_]:=IntegerDigits[j,2,3];
marks[h_,j_]:=With[{b=bits[j]}, {Boole[b[[3]]==0&&b[[1]]!=b[[2]]],Boole[b[[3]]==0&&h==1&&b[[1]]==b[[2]]]}];
readers[h_,mode_,j_]:=Module[{b=bits[j],ct,df,gd,p},Table[
 ct=1-b[[3]];df=Boole[BitAnd[mode,2^k]!=0||b[[3]]==0];
 gd=If[k==0,Boole[b[[1]]==b[[2]]],Boole[!(h==1&&b[[1]]==b[[2]])]];
 p=df*(1-gd);{ct,df,gd,p,ct*p},{k,0,1}]];
coeff[yu_,h_,mode_,j_]:=Module[{b=bits[j],m=marks[h,2*yu],rr=readers[h,mode,j]},
 {b[[1]],Boole[b[[2]]!=yu],b[[3]],m[[1]]*rr[[1,4]],(1-m[[1]])*rr[[1,5]],m[[2]]*rr[[2,4]],(1-m[[2]])*rr[[2,5]]}];
pressure[yu_,h_,mode_,j_,ll_]:=coeff[yu,h,mode,j].{c,r,d,a,ll*a,n,ll*n};
ordinary[yu_,h_,j_]:=Take[coeff[yu,h,0,j],3].{c,r,d}+marks[h,j].{a,n};
body=Table[Module[{id=inp[[1]],ps=inp[[2]],ss=inp[[3]],tail=inp[[4]],yu=inp[[5]],h=inp[[6]],target=inp[[7]],rows,fibers,summaries},
 rows=Table[Module[{b=bits[j],view,m,fr,cc},
  view="a"<>ps[[b[[1]]+1]]<>If[b[[3]]==1,"i",""]<>"-"<>ss[[b[[2]]+1]]<>tail;
  m=marks[h,j];fr=(1-b[[3]])*Boole[b[[1]]!=yu];
  cc=Table[Module[{name=cfg[[1]],mode=cfg[[2]],ll=cfg[[3]],co,rr,score},
   co=coeff[yu,h,mode,j];rr=readers[h,mode,j];
   If[rr[[All,5]]=!=m,Print["FAILED M=Cp"];Exit[1]];
   score=If[ll==-1,ordinary[yu,h,j],pressure[yu,h,mode,j,ll]]/.{c->1,r->4,d->2,a->16,n->16};
   <|"name"->name,"initial"->readers[h,mode,2*yu],"current"->rr,"coefficients"->co,"score8"->8*score|>],{cfg,configs}];
  <|"j"->j,"bits"->b,"morph"->view,"observation"->StringReplace[view,"-"->""],"ordinary"->m,
    "tabulated"->{1-b[[3]],1,Boole[b[[1]]==yu],Boole[b[[1]]!=yu],fr},"tabulated_agrees"->Boole[fr==m[[1]]],"configs"->cc|>],{j,0,7}];
 fibers=Table[<|"observation"->row["observation"],"members"->(# ["j"]&/@Select[rows,#["observation"]==row["observation"]&])|>,{row,rows}];
 summaries=Table[Module[{v,ms},v=Min[Table[rows[[j]]["configs"][[k]]["score8"],{j,1,8}]];
  ms=Select[Range[0,7],rows[[#+1]]["configs"][[k]]["score8"]==v&];
  <|"name"->configs[[k,1]],"minimum8"->v,"minima"->ms,"outputs"->(rows[[#+1]]["observation"]&/@ms)|>],{k,1,6}];
 <|"id"->id,"input"->"a"<>ps[[1]]<>"-"<>ss[[yu+1]]<>tail,"input_index"->2*yu,"h"->h,"target"->target,
   "correct_fiber"->(#["j"]&/@Select[rows,#["observation"]==target&]),"rows"->rows,"fibers"->fibers,"summaries"->summaries|>],{inp,inputs}];
nonnegative=And@@Thread[{c,r,d,a,n,lam}>=0];
joint=And@@Flatten[Table[With[{yu=inp[[5]],h=inp[[6]],g={6,3,1}[[k]]},
 Table[If[j==g,True,pressure[yu,h,0,g,lam]<pressure[yu,h,0,j,lam]],{j,0,7}]],{k,1,3},{inp,{inputs[[k]]}}]];
region=0<c&&c<d&&c<r&&d<a&&d<n&&d<c+lam*n&&d<c+lam*a;
regMismatch=Reduce[nonnegative&&Xor[joint,region],{c,r,d,a,n,lam},Reals];
oJoint=And@@Flatten[Table[With[{yu=inputs[[k,5]],h=inputs[[k,6]],g={6,3,1}[[k]]},
 Table[If[j==g,True,ordinary[yu,h,g]<ordinary[yu,h,j]],{j,0,7}]],{k,1,3}]];
oRegion=0<c&&c<d&&c<r&&d<a&&d<n;
oMismatch=Reduce[nonnegative&&Xor[oJoint,oRegion],{c,r,d,a,n,lam},Reals];
zero=Reduce[nonnegative&&(joint/.lam->0),{c,r,d,a,n,lam},Reals];
deltaA=Table[Expand[pressure[1,1,mode,7,lam]-pressure[1,1,mode,3,lam]],{mode,{1,3}}];
deltaN=Table[Expand[pressure[0,1,mode,1,lam]-pressure[0,1,mode,0,lam]],{mode,{2,3}}];
If[regMismatch=!=False||oMismatch=!=False||zero=!=False||deltaA=!={c-a,c-a}||deltaN=!={d,d},Print["FAILED symbolic",{regMismatch,oMismatch,zero,deltaA,deltaN}];Exit[1]];
 "ordinary_region_mismatch"->ToString[oMismatch,InputForm],"rr_zero_joint"->ToString[zero,InputForm],
 "surviving_A_deltas"->(ToString[#,InputForm]&/@deltaA),"surviving_N_deltas"->(ToString[#,InputForm]&/@deltaN)|>,"RawJSON"];
Print[$Version];Print["24 states, 144 scores; full bodies and symbolic region/bounds exported."];
