SetDirectory[DirectoryName[$InputFileName]];
Get["model.wl"];
Get["GuaData.wl"];
inputs=inputsDeletion;observations=observationsDeletion;
alpha=grammar["alphabet"];inv=grammar["inventory"];weights={20,1,1,2,4,8,8,24,1};
check[x_,label_]:=If[!TrueQ[x],Print["FAILED ",label];Exit[1]];
countsDeletion[r_]:=Table[Total[Table[
 p=r[[2,k,q]]&&!r[[3,k,q]];b=r[[1,k,q]];
 If[5<=k<=8,a=initial[[1,k,q]];v=a&&initial[[2,k,q]]&&!initial[[3,k,q]];
 Boole/@{p&&a,p&&!a&&b,p&&v,p&&!v&&b,p&&b&&v,p&&b&&!v},
 v=p&&b;Boole/@{v,False,v,False,v,False}],{q,Length[origin]}]],{k,9}];
coefficientsDeletion[cs_,pol_]:=Table[Which[k==8&&pol==1,{0,0},k==8&&pol==2,cs[[k,5;;6]],True,cs[[k,3;;4]]],{k,9}];
scoreDeletion[cs_,pol_]:=With[{r=coefficientsDeletion[cs,pol]},weights.(8 r[[All,1]]+r[[All,2]])];
setupInput[input_]:=(origin=Lookup[input["slots"],"phone"];words=Lookup[input["slots"],"word"];
 focal=input["focal"]+1;phrases=input["phrases"];origft=ft/@origin;initial=readState[origin];
 tuples=Tuples[Range[0,12],Length[focal]];powers=13^Reverse[Range[0,Length[focal]-1]]);
cases=Table[
 setupInput[input];name=input["id"];start=Total[(First[FirstPosition[alpha,#]]-1&/@origin[[focal]])powers];
 records=Table[s=expandState[co=tuples[[i+1]]];r=readState[s];cs=countsDeletion[r];
 {i,co,s,realizeState[s],lexicalView[s],r[[1]],r[[2]],r[[3]],r[[4]],cs,Table[scoreDeletion[cs,pol],{pol,0,2}]},
 {i,0,Length[tuples]-1}];
 observation=SelectFirst[observations,#["id"]==name&];fiber=Select[Range[0,Length[tuples]-1],MemberQ[observation["allowed"],records[[#+1,4]]]&];
 global=Table[ps=records[[All,11,pol+1]];minimum=Min[ps];wins=Flatten[Position[ps,minimum]]-1;wrong=Complement[wins,fiber];
 <|"policy"->pol,"minimum8"->minimum,"winners"->wins,"outputs"->Sort[DeleteDuplicates[records[[wins+1,4]]]],
 "exclusively_correct"->(wrong=={}),"correct_minima"->Intersection[wins,fiber],"wrong_minima"->wrong,
 "correct_fiber_scores8"->Table[{i,ps[[i+1]]},{i,fiber}],"best_wrong8"->Min[ps[[Complement[Range[Length[ps]],fiber+1]]]]|>,{pol,0,2}];
 Print[name," fiber ",fiber," minima ",global];
 <|"id"->name,"start"->start,"fiber"->fiber,"global_results"->global,"records"->records|>,{input,inputs}];
check[#["fiber"]&/@cases=={{1189,1261},{9,117},{159}},"entire observation fibers"];
vars=Array[ww,9];
sym[case_,i_,pol_]:=With[{c=coefficientsDeletion[cases[[case]]["records"][[i+1,10]],pol]},vars.(c[[All,1]]+ll c[[All,2]])];
Do[
 a23=sym[3,159,pol];b23=sym[3,3,pol];escape=sym[2,161,pol];fiberCosts=sym[2,#,pol]&/@cases[[2]]["fiber"];
 check[{a23,b23,escape,fiberCosts}=={ww[4],ww[1],ww[4],{ww[1]+ww[3]+ww[9],ww[1]}},"reader-derived all-weight costs"];
 check[Reduce[And@@Thread[vars>=0]&&a23<b23&&Or@@Thread[fiberCosts<=escape],vars,Reals]===False,"all-weight incompatibility including both fiber states"],{pol,{1,2}}];
Block[{cases},Get["check_selection.wl"];old=<|"cases"->cases|>];
baseline=Table[
 rs=c["records"];st=rs[[c["start"]+1]];
 check[!Or@@MapThread[And[#1,#2,Not[#3]]&,{st[[6,8]],st[[7,8]],st[[8,8]]}],"no initial deletion violation in the five products"];
 check[AllTrue[rs,#[[10,8,3;;4]]==#[[10,8,5;;6]]&],"current-deletion identity on the saved selection records"];
 ps=scoreDeletion[#[[10]],1]&/@rs;mn=Min[ps];wins=Flatten[Position[ps,mn]]-1;
 check[wins==c["fiber"],"removed-deletion ablation preserves the five selections"];
 check[AllTrue[Select[rs,ps[[#[[1]]+1]]<=28&],#[[10,1,3]]==0&],"MAX budget"];
 <|"id"->c["id"],"minimum8"->mn,"winners"->wins,"current_identity"->True,"initial_D_loci"->{},"max_budget8"->160,
 "low_budget_states"->Select[Range[0,Length[rs]-1],ps[[#+1]]<=28&]|>,{c,old["cases"]}];
pr=probe;setupInput[pr];
check[initial[[1,6,1]]&&initial[[2,6,1]]&&!initial[[3,6,1]],"initial A violation"];
probe=Table[r=readState[s];p=r[[2,6,1]]&&!r[[3,6,1]];
 next=SelectFirst[Range[2,Length[s]],TrueQ[ft[s[[#]]]["present"]]&]-1;
 <|"state"->s,"nextLive"->next,"context"->r[[1,6,1]],"defined"->r[[2,6,1]],"good"->r[[3,6,1]],"retained8"->64 Boole[p]|>,{s,pr["states"]}];
check[(#["retained8"]&/@probe)=={0,64}&&AllTrue[probe,#["nextLive"]==2&&!#["context"]&],"cross-phrase retained A"];
Print["PASS three deletion products, symbolic obstruction and deletion ablation; ",$Version];
