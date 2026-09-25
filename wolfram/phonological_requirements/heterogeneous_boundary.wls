ClearAll[c,x,y,z,t,h,f];
f[c_,x_,y_]:=Max[1-x,0]^2+Max[x-y,0]^2+c*x;
checks={
 TimeConstrained[Resolve[ForAll[{c,x,y},0<=c<=2&&0<=x<=1&&0<=y<=1,Equivalent[f[c,x,y]==c-c^2/4,x==1-c/2&&x<=y]],Reals],60,"TIMEOUT"],
 TimeConstrained[Resolve[ForAll[{c,x,y},0<=c<=2&&0<=x<=1&&0<=y<=1,f[c,x,y]>=c-c^2/4],Reals],60,"TIMEOUT"],
 TimeConstrained[Resolve[ForAll[{t},0<=t<=1,f[2,0,t]==1],Reals],60,"TIMEOUT"],
 TimeConstrained[Resolve[ForAll[{x,y,z},0<=x<=1&&0<=y<=1&&0<=z<=1,Equivalent[Max[1-x,0]^2+Max[x-y,0]^2+Max[y-z,0]^2==0,x==1&&y==1&&z==1]],Reals],60,"TIMEOUT"],
 TimeConstrained[Resolve[ForAll[{x},0<=x<=1,Equivalent[Max[1-x,0]^2-x==-1,x==1]],Reals],60,"TIMEOUT"],
 TimeConstrained[Resolve[ForAll[{x},0<=x<=1,Max[1-x,0]^2-x>=-1],Reals],60,"TIMEOUT"]
};
out=FileNameJoin[{DirectoryName[DirectoryName[DirectoryName[$InputFileName]]],"results","requirements","wolfram"}];
If[!DirectoryQ[out],CreateDirectory[out,CreateIntermediateDirectories->True]];
Export[FileNameJoin[{out,"heterogeneous_boundary.json"}],<|"version"->$Version,"checks"->checks,"scope"->"Exact real two-site argmin, original-cube witnesses, all-zero three-site control and harmless negative single-site control; universal all-N zero theorem is in Lean."|>,"RawJSON"];
Print[checks];
If[checks!=ConstantArray[True,6],Exit[1]];
