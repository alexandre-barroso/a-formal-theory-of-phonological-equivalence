base=DirectoryName[$InputFileName];
out=FileNameJoin[{base,"..","..","results","requirements","wolfram","word_projection.json"}];
If[!DirectoryQ[DirectoryName[out]],CreateDirectory[DirectoryName[out],CreateIntermediateDirectories->True]];
Clear[wordStates];
wordStates[n_,k_,w_,offset_]:=Module[{patterns,lexical,created},
 patterns=DeleteDuplicates[Permutations[Join[ConstantArray[0,n],ConstantArray[1,k]]]];
 lexical=Tuples[{"a","t","absent"},n];
 Flatten[Table[Module[{i=0,j=0},Table[If[pattern[[p]]==0,i++;{w,offset+i,values[[i]]},j++;{w,0,"n"}],{p,n+k}]],{pattern,patterns},{values,lexical}],1]];
records={};failures={};
Do[
 n=lengths[[1]];m=lengths[[2]];
 states=Flatten[Table[Flatten[Table[Join[x,y],{x,wordStates[n,i,0,0]},{y,wordStates[m,j,1,n]}],1],{i,0,bound},{j,0,bound-i}],2];
 unique=DeleteDuplicates[states];
 expected=Sum[Binomial[n+i,i]Binomial[m+j,j]3^(n+m),{i,0,bound},{j,0,bound-i}];
 If[Length[unique]!=expected,AppendTo[failures,{lengths,bound,Length[unique],expected}]];
 AppendTo[records,<|"lengths"->lengths,"bound"->bound,"canonical_count"->Length[unique],"formula_count"->expected|>],
 {lengths,{{1,1},{1,2},{2,2},{3,1}}},{bound,0,2}];
Export[out,<|"cases"->records,"failures"->failures,"method"->"Independent lexical/created-position interleavings with explicit word tags; created identities are omitted, so counted structures are canonical classes."|>,"RawJSON"];
Print[records];Print[failures];Exit[If[Length[records]==12 && failures=={},0,1]];
