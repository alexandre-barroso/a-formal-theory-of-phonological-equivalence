here=DirectoryName[DirectoryName[DirectoryName[$InputFileName]]];
obs[p_,v_]:={p,v}; vowel={-1,-1}; absent={-2,-2};
present[x_]:=x=!=absent; obstruent[x_]:=x[[1]]>=0;
next[ss_,q_]:=SelectFirst[Range[q+1,Length[ss]],present[ss[[#]]]&,0];
partner[rr_,ss_,q_,h_]:=If[h==1,next[rr,q],next[ss,q]];
rbad[rr_,ss_,q_,h_,kind_]:=Module[{j=partner[rr,ss,q,h]},
 If[j==0||!obstruent[ss[[q]]]||!obstruent[ss[[j]]],0,
 If[kind==0,Boole[ss[[q,2]]!=ss[[j,2]]],Boole[ss[[q,1]]==ss[[j,1]]&&ss[[q,2]]==ss[[j,2]]]]]];
checks=0;bad={};
Do[
 ref={vowel,obs[0,v1],absent,obs[1-e,v2]};cand={vowel,obs[0,x],If[z==1,vowel,absent],obs[1-e,y]};
 If[boundary==1,AppendTo[ref,vowel];AppendTo[cand,vowel]];
 faith=Total[Table[If[obstruent[ref[[q]]]&&obstruent[cand[[q]]],If[q<=2,pp,ss] Boole[ref[[q,2]]!=cand[[q,2]]],0]+dd Boole[!present[ref[[q]]]&&present[cand[[q]]]]+mm Boole[present[ref[[q]]]&&!present[cand[[q]]]],{q,4}]];
 marked=Total[Table[Sum[With[{h=If[kind==0,ha,hn],old=If[kind==0,aa,nn],new=If[kind==0,an,nnnew]},With[{a=rbad[ref,ref,q,h,kind]},(a old+(1-a)new)rbad[ref,cand,q,h,kind]]],{kind,0,1}],{q,4}]];
 expected=pp Boole[x!=v1]+ss Boole[y!=v2]+dd z+
 Boole[x!=y] Boole[ha==1||z==0] If[v1!=v2,aa,an]+
 e Boole[x==y] Boole[hn==1||z==0] If[v1==v2,nn,nnnew];
 checks++;If[Expand[faith+marked+tailConstant-(expected+tailConstant)]=!=0,AppendTo[bad,{v1,v2,e,ha,hn,x,y,z,boundary}]],
 {v1,0,1},{v2,0,1},{e,0,1},{ha,0,1},{hn,0,1},{x,0,1},{y,0,1},{z,0,1},{boundary,0,1}];
outdir=FileNameJoin[{here,"results","requirements","wolfram"}];
If[!DirectoryQ[outdir],CreateDirectory[outdir,CreateIntermediateDirectories->True]];
Export[FileNameJoin[{outdir,"learning_tail.json"}],<|"checks"->checks,"failures"->bad,"scope"->"All Boolean local patterns, real symbolic weights, both permitted boundary cases; common tail contribution cancels. Arbitrary tail recursion and observer are Lean obligations, not inferred from this finite enumeration."|>,"RawJSON"];
If[checks!=512||Length[bad]!=0,Exit[1]];Print["PASS ",checks," symbolic coefficient identities"];Exit[0];
