base=DirectoryName[$InputFileName];
out=FileNameJoin[{base,"..","..","results","requirements","wolfram","product_composition.json"}];
If[!DirectoryQ[DirectoryName[out]],CreateDirectory[DirectoryName[out],CreateIntermediateDirectories->True]];
matrices=Partition[#,2]& /@ Tuples[{0,1},4];
weights=Tuples[{-1,0,1},2];
closures=0;minima=0;failures={};
Do[
 joint=KroneckerProduct[ma,IdentityMatrix[2]]+KroneckerProduct[IdentityMatrix[2],mb];
 reach=Sign[MatrixPower[IdentityMatrix[4]+joint,3]];
 ra=Sign[IdentityMatrix[2]+ma];rb=Sign[IdentityMatrix[2]+mb];
 Do[
  da=Flatten[Position[ra[[a]],1]];db=Flatten[Position[rb[[b]],1]];
  dp=Flatten[Position[reach[[2(a-1)+b]],1]];
  expected=Sort[Flatten[Table[2(x-1)+y,{x,da},{y,db}]]];
  If[dp=!=expected,AppendTo[failures,{"closure",ma,mb,a,b}]];closures++;
  Do[
   costs=Flatten[Outer[Plus,f,g]];
   selected=Select[dp,costs[[#]]==Min[costs[[dp]]]&];
   la=Select[da,f[[#]]==Min[f[[da]]]&];lb=Select[db,g[[#]]==Min[g[[db]]]&];
   target=Sort[Flatten[Table[2(x-1)+y,{x,la},{y,lb}]]];
   If[selected=!=target,AppendTo[failures,{"argmin",ma,mb,a,b,f,g}]];minima++,
   {f,weights},{g,weights}],
  {a,1,2},{b,1,2}],
 {ma,matrices},{mb,matrices}];
record=<|"relation_pairs"->Length[matrices]^2,"reachable_product_cases"->closures,"all_minimizer_cases"->minima,"failures"->failures,"method"->"Exact Boolean reachability via adjacency matrix powers, then all minimum score fibers."|>;
Export[out,record,"RawJSON"];Print[record];Exit[If[closures==1024 && minima==82944 && failures=={},0,1]];
