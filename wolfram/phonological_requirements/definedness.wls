base=DirectoryName[$InputFileName];out=FileNameJoin[{base,"..","..","results","requirements","wolfram","definedness.json"}];
truth={-1,0,1};defined[x_]:=x!=0;pressure[x_]:=Boole[x==-1];
cases=Tuples[truth,2];
sufficiency=And@@Table[If[defined[p[[1]]]&&defined[p[[2]]],defined[Min@@p]&&defined[Max@@p],True],{p,cases}];
checks={sufficiency,Max[1,0]==1,Min[-1,0]==-1,pressure[Max[1,0]]==0,defined[Max[1,0]],pressure[Min[-1,0]]==1,And@@Table[(pressure[v]==0)==(v==0||v==1),{v,truth}]};
If[!DirectoryQ[DirectoryName[out]],CreateDirectory[DirectoryName[out],CreateIntermediateDirectories->True]];
record=<|"truth_pairs"->Length[cases],"checks"->checks,"method"->"Strong Kleene conjunction/disjunction as minimum/maximum on false < undefined < true; pressure is the false indicator."|>;
Export[out,record,"RawJSON"];Print[record];Exit[If[Length[cases]==9&&And@@(TrueQ/@checks),0,1]];
