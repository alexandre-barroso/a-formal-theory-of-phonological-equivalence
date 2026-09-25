ClearAll[a,b,c,d,e,f,z,v];
xs={a,b,c,d,e,f};zs=Prepend[Most[xs],1]-xs;
weights={1,1,-4,1,1,1};
energy=5 Total[Max[#,0]^2&/@zs]+weights.xs;
original={4/5,7/10,1,7/10,1/2,2/5};
monotone={9/10,9/10,9/10,3/5,2/5,3/10};
originalDrops={1/5,1/10,0,3/10,1/5,1/10};
monotoneDrops={1/10,0,0,3/10,1/5,1/10};
remainder[vs_]:=5 Total[MapThread[Max[#1,0]^2-2 #1 #2+#2^2&,{zs,vs}]];
checks={
 Resolve[ForAll[{z,v},v>=0,Max[z,0]^2-2 v z+v^2>=0],Reals],
 Expand[energy-1/20-remainder[originalDrops]-(1-c)]===0,
 Expand[energy-1/4-remainder[monotoneDrops]-(b-c)]===0,
 (energy/.Thread[xs->original])===1/20,
 (energy/.Thread[xs->monotone])===1/4,
 And@@Thread[0<=original]&&And@@Thread[original<=1],
 And@@Thread[0<=monotone]&&And@@Thread[Differences[Prepend[monotone,1]]<=0],
 1/20<1/4
};
out=FileNameJoin[{DirectoryName[DirectoryName[DirectoryName[$InputFileName]]],"results","requirements","wolfram"}];
If[!DirectoryQ[out],CreateDirectory[out,CreateIntermediateDirectories->True]];
Export[FileNameJoin[{out,"heterogeneous_obstruction.json"}],<|"version"->$Version,"checks"->checks,"original_minimum"->"1/20","monotone_minimum"->"1/4","scope"->"Universal hinge-square support inequality plus exact nonnegative-remainder identities on original and monotone domains."|>,"RawJSON"];
Print[checks];If[checks!=ConstantArray[True,8],Exit[1]];
