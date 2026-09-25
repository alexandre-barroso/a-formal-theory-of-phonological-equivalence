score[bits_,r_,w_] := r Total[bits]+w Total[MapThread[(1-#1)(1-#2)&,{bits,RotateRight[bits]}]];
rows=Flatten[Table[Module[{states=Tuples[{0,1},n],scores,best,winners,formula,r=pair[[1]],w=pair[[2]]},scores=score[#,r,w]&/@states;best=Min[scores];winners=Pick[states,scores,best];formula=Select[states,Total[#]==Ceiling[n/2]&&Total[MapThread[(1-#1)(1-#2)&,{#,RotateRight[#]}]]==0&];If[0<r<w&&Sort[winners]=!=Sort[formula],Print["FAIL"];Exit[1]];<|"n"->n,"r"->ToString[r,InputForm],"w"->ToString[w,InputForm],"best"->ToString[best,InputForm],"count"->Length[winners]|>],{n,1,12},{pair,{{0,0},{0,1},{1,0},{1,1},{1/3,2/3},{2,1}}}],1];
region=Reduce[Exists[{w,f,d,v},w>=0&&f>=0&&d>=0&&v>=0&&f<w&&l w<f&&d+l w<v]&&l>=0,l,Reals];
Print[region];
If[!TrueQ[Resolve[ForAll[l,Equivalent[region,0<=l<1]],Reals]],Exit[2]];
witness=FullSimplify[(w>=0&&f>=0&&d>=0&&v>=0&&f<w&&l w<f&&d+l w<v)/.{w->2,f->1+l,d->1,v->2+2l},Assumptions->0<=l<1];
If[!TrueQ[witness],Exit[3]];
If[Length[rows]!=72||!AllTrue[rows,AssociationQ],Exit[4]];
Print["cycle systems ",Length[rows],"; region and witness verified"];
