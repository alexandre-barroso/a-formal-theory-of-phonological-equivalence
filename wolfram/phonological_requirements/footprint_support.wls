base = DirectoryName[$InputFileName];
out = FileNameJoin[{base,"..","..","results","requirements","wolfram","footprint_support.json"}];
If[!DirectoryQ[DirectoryName[out]],CreateDirectory[DirectoryName[out],CreateIntermediateDirectories->True]];
Clear[pick,resolve];
pick[vals_,ord_,stop_] := Module[{present,hits,k},
  present=Select[ord,vals[[#+1]]!=0&];
  hits=If[stop,Take[present,UpTo[1]],Select[present,vals[[#+1]]==2&]];
  If[hits=={},Return[{}]];
  k=First[hits];If[vals[[k+1]]==2,{k,2},{}]
];
resolve[vals_,ord_,stop_,admitted_] := Module[{p=pick[vals,ord,stop]},
 If[p=={} || !MemberQ[admitted,First[p]],{},p]];
checks=0; failures={};
Do[
 ord=Range[0,n-1];
 Do[
  adm=Pick[ord,Table[BitGet[mask,k],{k,ord}],1];
  limit=If[adm=={},0,Max[adm]+1];
  lhs=resolve[vals,ord,stop,adm];rhs=resolve[vals,Take[ord,limit],stop,adm];
  If[lhs=!=rhs,AppendTo[failures,{vals,mask,stop,lhs,rhs}]];
  checks++,
  {vals,Tuples[Range[0,2],n]},{mask,0,2^n-1},{stop,{False,True}}],
 {n,0,4}];
controls={resolve[{1,2},{0,1},True,{1}] == {},
          resolve[{1,2},{1},True,{1}] == {1,2},
          resolve[{1,2},{0,1},False,{0,1}] == {1,2},
          resolve[{1,2},{0,1},True,{0,1}] == {}};
record=<|"finite_cases"->checks,"prefix_failures"->failures,"mutation_controls"->controls,
 "scope"->"Finite independent stopping and prefix-support calculations; universal statements proved in Lean."|>;
Export[out,record,"RawJSON"];
Print[record];
Exit[If[checks==3110 && failures=={} && controls==ConstantArray[True,4],0,1]];
