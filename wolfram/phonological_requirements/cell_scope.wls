ClearAll[w,lam,c,r,a,b,wp,lp,f,fp,m,n];
checks={
 And@@Flatten[Table[Resolve[ForAll[{w,lam},w>0,Equivalent[w(a b+lam(1-a)c b)>0&&c b==0,a==1&&c==0&&b==1]],Reals],{a,0,1},{c,0,1},{b,0,1}]],
 Resolve[ForAll[{w,m,n,f,fp},m==n&&fp<f,w m+fp<w n+f],Reals],
 Resolve[ForAll[{w,wp,f,fp,m,n},w>=0&&wp>=0&&f<=fp&&m<=n,w f+wp m<=w fp+wp n],Reals],
 Resolve[ForAll[{w,wp,f,fp,m,n},w>0&&wp>=0&&f<fp&&m<=n,w f+wp m<w fp+wp n],Reals],
 Resolve[ForAll[{c,lam,w,r},Equivalent[c+lam w<c+r,lam w<r]&&Equivalent[c+lam w==c+r,lam w==r]],Reals],
 Resolve[ForAll[{a,b,w,wp,lam,lp},lp>0&&lam>=0&&w>=0&&wp>=0,w a+(lam/lp)wp lp b==w a+wp lam b&&(lam/lp)wp>=0],Reals],
 (1*0==0&&1!=0)&&(2*0+1*1<2*1+1*0)&&(1*0+2*1>1*1+2*0)&&(0*1==0*0)&&(1/8*4<1)&&(1/8*4+2>1)
};
out=FileNameJoin[{DirectoryName[DirectoryName[DirectoryName[$InputFileName]]],"results","requirements","wolfram"}];
If[!DirectoryQ[out],CreateDirectory[out,CreateIntermediateDirectories->True]];
Export[FileNameJoin[{out,"cell_scope.json"}],<|"version"->$Version,"checks"->checks,"scope"->"Exact real local cell identities, finite-coordinate cancellation/dominance, isolated thresholds, rescaling and counterexamples."|>,"RawJSON"];
Print[checks];If[checks!=ConstantArray[True,7],Exit[1]];
