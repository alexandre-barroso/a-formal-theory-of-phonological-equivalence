root=DirectoryName[DirectoryName[DirectoryName[$InputFileName]]];
here=FileNameJoin[{root,"wolfram","phonological_opacity","fragments"}];
Get[FileNameJoin[{here,"GuaCore.wl"}]];
spec=GuaCore`LoadGuaSpec[FileNameJoin[{here,"GuaFragmentSpec.wl"}]];
w0={3,1,1,2,2,4,4,4,4};w1={-4,0,-2,-2,0,0,0,0,0};
cf[fr_,s_,ref_,mode_]:=Module[{cur=GuaCore`Private`readersOf[fr,s],origins=fr["origins"],live,initialLive,nxt,initialNext},
 live=Select[Range[fr["n"]],TrueQ[GuaCore`Private`featureOf[fr["spec"],s[[#]]]["present"]]&];
 initialLive=Select[Range[fr["n"]],TrueQ[GuaCore`Private`featureOf[fr["spec"],fr["reference"][[#]]]["present"]]&];
 nxt=Association[Thread[Most[live]->Rest[live]]];initialNext=Association[Thread[Most[initialLive]->Rest[initialLive]]];
 Table[Total[Table[Module[{rd=cur[{k,q}],a=GuaCore`Private`markedOf[ref[{k,q}]],p,next,defined},
 p=GuaCore`Private`pressureOf[rd];
 If[mode==="subject"&&k==="A",next=Lookup[nxt,q,Missing[]];defined=!MissingQ[next]&&origins[[next]]["word"]===origins[[q]]["word"]+1&&origins[[next]]["phrase"]===origins[[q]]["phrase"];
 p=Boole[defined&&!TrueQ[rd[[3]]]];a=a Boole[next===Lookup[initialNext,q,Missing[]]]];
 If[MemberQ[{"H","A","GL","D"},k],{a p,(1-a) Boole[TrueQ[rd[[1]]]] p},{GuaCore`Private`markedOf[rd],0}]],{q,fr["n"]}]],{k,GuaCore`Private`schemaNames}]];
runProductiveRegion[mode_]:=(
input=Import[FileNameJoin[{root,"results","requirements","certificates","productive_region_"<>mode<>".json"}],"RawJSON"];
cases=input["cases"];
result={};checks=0;failures={};total=0;
Do[
 fr=GuaCore`GuaFragment[spec,product["id"]];ref=GuaCore`Private`readersOf[fr,fr["reference"]];recs=product["records"];
 good=Select[recs,TrueQ[#["correct"]]&];goal=First@SortBy[good,w0.#["coefficients"][[All,1]]&];gc=cf[fr,goal["state"],ref,mode];
 minA=Infinity;minEndpoint=Infinity;
 Do[c=cf[fr,row["state"],ref,mode];checks++;total+=row["multiplicity"];
 If[c=!=row["coefficients"],AppendTo[failures,{product["id"],row["state"],"coefficients"}]];
 If[(GuaCore`Private`observeOf[fr,row["state"]]===fr["record"]["observation"])=!=row["correct"],AppendTo[failures,{product["id"],row["state"],"observer"}]];
 If[!TrueQ[row["correct"]],diff=c-gc;aa=w0.diff[[All,1]];bb=w1.diff[[All,1]]+w0.diff[[All,2]];cc=w1.diff[[All,2]];
 minA=Min[minA,aa];minEndpoint=Min[minEndpoint,2aa+bb];
 If[!(aa>0&&2aa+bb>=0&&cc==0),AppendTo[failures,{product["id"],row["state"],"margin",{aa,bb,cc}}]]],{row,recs}];
 AppendTo[result,<|"id"->product["id"],"classes"->Length[recs],"minimumA"->minA,"minimumTwiceEndpoint"->minEndpoint|>];Print[Last[result]];
 Null,{product,cases}];
Clear[aa,bb,l,a,h];
lemmas={Resolve[ForAll[{aa,bb,l},Implies[aa>0&&2aa+bb>=0&&0<=l<1/2,aa+bb l>0]],Reals],
 Resolve[ForAll[l,Implies[0<=l<1/2,And@@Thread[w0+l w1>=0]]],Reals],
 Resolve[ForAll[l,Equivalent[Exists[{a,h},l>=0&&h>=0&&a>=0&&a-l h>0&&(1-l)h-a>0],0<=l<1/2]],Reals]};
out=<|"mode"->mode,"checks"->checks,"candidates"->total,"records"->result,"failures"->failures,"universalResults"->lemmas|>;
outdir=FileNameJoin[{root,"results","requirements","wolfram"}];
If[!DirectoryQ[outdir],CreateDirectory[outdir,CreateIntermediateDirectories->True]];
Export[FileNameJoin[{outdir,"productive_region_"<>mode<>".json"}],out,"RawJSON"];
If[Length[failures]!=0||checks<1||total!=15967796||lemmas=!={True,True,True},Exit[1]];
Print["PASS ",checks," classes, ",total," structures, three universal algebraic lemmas"];
);
