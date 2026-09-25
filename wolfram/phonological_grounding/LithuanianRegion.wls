root = DirectoryName[DirectoryName[DirectoryName[$InputFileName]]];

voi = <|"p" -> 0, "b" -> 1, "t" -> 0, "d" -> 1, "k" -> 0, "g" -> 1, "i" -> 1|>;
place = <|"p" -> "lab", "b" -> "lab", "t" -> "cor", "d" -> "cor",
          "k" -> "dor", "g" -> "dor", "i" -> "vowel"|>;
obstruent = <|"p" -> True, "b" -> True, "t" -> True, "d" -> True,
              "k" -> True, "g" -> True, "i" -> False|>;

inputs = {
  <|"id" -> "PG", "prefix" -> {"p", "b"}, "stem" -> {"k", "g"},
    "refBits" -> {0, 1, 0}, "h" -> 0, "correct" -> 6|>,
  <|"id" -> "PB", "prefix" -> {"p", "b"}, "stem" -> {"p", "b"},
    "refBits" -> {0, 1, 0}, "h" -> 1, "correct" -> 3|>,
  <|"id" -> "TT", "prefix" -> {"t", "d"}, "stem" -> {"t", "d"},
    "refBits" -> {0, 0, 0}, "h" -> 1, "correct" -> 1|>};

stateOf[rec_, j_] := Module[{x = Quotient[j, 4], y = Mod[Quotient[j, 2], 2], z = Mod[j, 2]},
  {rec["prefix"][[x + 1]], If[z === 1, "i", "\[EmptySet]"], rec["stem"][[y + 1]]}];

refOf[rec_] := stateOf[rec, 4 rec["refBits"][[1]] + 2 rec["refBits"][[2]] + rec["refBits"][[3]]];

presentQ[s_] := s =!= "\[EmptySet]";

resolvePartner[policy_, st_] := Module[{},
  Switch[policy,
    "witness",      If[presentQ[st[[2]]], Missing[], 3],
    "dynamic_stop", If[presentQ[st[[2]]],
                       If[TrueQ[obstruent[st[[2]]]], 2, Missing[]], 3],
    "dynamic_skip", If[presentQ[st[[2]]] && TrueQ[obstruent[st[[2]]]], 2, 3],
    "origin_bound", 3,
    _, Missing[]]];

readersA[policy_, st_] := Module[{p = resolvePartner[policy, st]},
  If[MissingQ[p], {False, False, False},
     {True, True, voi[st[[1]]] === voi[st[[p]]]}]];

readersN[policy_, st_, h_] := Module[{p = resolvePartner[policy, st]},
  If[MissingQ[p], {False, False, False},
     {True, True, ! (place[st[[1]]] === place[st[[p]]] &&
                     voi[st[[1]]] === voi[st[[p]]])}]];

pressure[{_, d_, g_}] := If[TrueQ[d] && ! TrueQ[g], 1, 0];
marked[{c_, d_, g_}] := If[TrueQ[c] && TrueQ[d] && ! TrueQ[g], 1, 0];

scoreSym[policy_, rec_, j_, c_, r_, d_, a_, n_, lam_] := Module[
  {st = stateOf[rec, j], ref = refOf[rec], x, y, z, ra, rn, ra0, rn0, aOld, nOld},
  x = Quotient[j, 4]; y = Mod[Quotient[j, 2], 2]; z = Mod[j, 2];
  ra = readersA[policy, st]; rn = readersN[policy, st, rec["h"]];
  ra0 = readersA[policy, ref]; rn0 = readersN[policy, ref, rec["h"]];
  aOld = marked[ra0]; nOld = marked[rn0];
  c Boole[x =!= 0] + r Boole[y =!= rec["refBits"][[2]]] + d z
   + a (If[aOld === 1, pressure[ra], lam marked[ra]])
   + n (If[nOld === 1, pressure[rn], lam marked[rn]])];

Clear[c, r, d, a, n, lam];
vars = {c, r, d, a, n, lam};
nonneg = And @@ (# >= 0 & /@ vars);

status = 0;
Do[
 Module[{conds, region},
  Print["-- policy ", policy, " --"];
  conds = And @@ Flatten[Table[
     Module[{rec = u, w = u["correct"]},
       Table[scoreSym[policy, rec, w, c, r, d, a, n, lam] <
             scoreSym[policy, rec, j, c, r, d, a, n, lam],
             {j, DeleteCases[Range[0, 7], w]}]],
     {u, inputs}]];
  region = Reduce[conds && nonneg, vars, Reals];
  Print["   Reduce -> ", region];
  If[region === False,
     Print["   EXCLUDED for every nonnegative parameter vector"],
     Module[{w = FindInstance[conds && nonneg, vars, Reals, 1]},
       Print["   witness: ", w];
       If[w === {}, status = 1]]]],
 {policy, {"witness", "dynamic_stop", "dynamic_skip", "origin_bound"}}];

pt = {c -> 1, r -> 4, d -> 2, a -> 16, n -> 16, lam -> 1/8};
Do[Module[{ok = And @@ Flatten[Table[
     Module[{rec = u, w = u["correct"]},
       Table[(scoreSym[policy, rec, w, c, r, d, a, n, lam] <
              scoreSym[policy, rec, j, c, r, d, a, n, lam]) /. pt,
             {j, DeleteCases[Range[0, 7], w]}]],
     {u, inputs}]]},
   Print["   declared point (1,4,2,16,16,1/8) in ", policy, ": ", ok];
   If[MemberQ[{"witness", "dynamic_stop"}, policy] && ok =!= True, status = 1];
   If[MemberQ[{"dynamic_skip", "origin_bound"}, policy] && ok === True, status = 1]],
 {policy, {"witness", "dynamic_stop", "dynamic_skip", "origin_bound"}}];

Print["== lithuanian region exit ", status, " =="];
Exit[status];
