Get[FileNameJoin[{DirectoryName[$InputFileName], "GuaCore.wl"}]];
spec = GuaCore`LoadGuaSpec[
  FileNameJoin[{DirectoryName[$InputFileName], "GuaFragmentSpec.wl"}]];

If[!AssociationQ[spec] || !KeyExistsQ[spec, "inputs"] || Length[spec["inputs"]] != 8,
  Print["  FAIL  fragment specification did not load; nothing was checked"]; Exit[2]];

readers = GuaCore`Private`readersOf;
candidate = GuaCore`Private`candidateOf;
observe = GuaCore`Private`observeOf;
pressureOf = GuaCore`Private`pressureOf;
markedOf = GuaCore`Private`markedOf;
schemaNames = GuaCore`Private`schemaNames;
markednessNames = GuaCore`Private`markednessNames;

status = 0;
report[label_, ok_] := (Print[If[TrueQ[ok], "  PASS  ", "  FAIL  "], label]; If[!TrueQ[ok], status = 1]);

oldNew[fr_, segs_, refReaders_] := Module[{cur = readers[fr, segs], spec = fr["spec"], O = 0, N = 0},
  Do[Module[{old = 0, new = 0, w = spec["weights"][s]},
    Do[Module[{p = pressureOf[cur[{s, q}]], m = markedOf[cur[{s, q}]], a},
      If[MemberQ[markednessNames, s],
        a = markedOf[refReaders[{s, q}]];
        If[a === 1, old += p, new += m],
        old += m]], {q, Range[fr["n"]]}];
    O += w old; N += w new], {s, schemaNames}];
  {O, N}];

invariant = {"G34a", "N7", "C24ei", "C21b", "C23UE"};
rivals = <|"G34b" -> 1126, "G37c" -> 1753, "OR38" -> 1430|>;

Do[Module[{fr = GuaCore`GuaFragment[spec, u["id"]], refReaders, table, O, N, argmin, w, rest, obs},
  refReaders = readers[fr, fr["reference"]];
  table = Table[oldNew[fr, candidate[fr, i], refReaders], {i, 0, fr["size"] - 1}];
  O = table[[All, 1]]; N = table[[All, 2]];
  argmin[lam_] := Flatten[Position[O + lam N, Min[O + lam N]]] - 1;
  w = argmin[1/8];
  report[u["id"] <> ": unique minimiser at 1/8", Length[w] == 1];
  w = First[w];
  report[u["id"] <> ": minimiser realises the documented observation",
    observe[fr, candidate[fr, w]] === u["observation"]];
  rest = Complement[Range[0, fr["size"] - 1], {w}];
  report[u["id"] <> ": invariant on [0, 1/4)",
    AllTrue[rest, (O[[# + 1]] > O[[w + 1]] && 4 O[[# + 1]] + N[[# + 1]] >= 4 O[[w + 1]] + N[[w + 1]]) &]];
  report[u["id"] <> ": argmin at 0 and at 24/100 is {w}", argmin[0] === {w} && argmin[24/100] === {w}];
  If[MemberQ[invariant, u["id"]],
    report[u["id"] <> ": winner has N = 0 and survives lambda = 1", N[[w + 1]] == 0 && argmin[1] === {w}],
    Module[{r = rivals[u["id"]]},
      report[u["id"] <> ": N_w - N_r = 4 and O_r - O_w = 1", N[[w + 1]] - N[[r + 1]] == 4 && O[[r + 1]] - O[[w + 1]] == 1];
      report[u["id"] <> ": tie at 1/4 is exactly {w, r}", Sort[argmin[1/4]] === Sort[{w, r}]];
      report[u["id"] <> ": rival wins alone at 1", argmin[1] === {r}];
      report[u["id"] <> ": rival's observation is not the documented one",
        observe[fr, candidate[fr, r]] =!= u["observation"]]]]],
  {u, spec["inputs"]}];

Print["== wolfram lambda interval exit ", status, " =="];
Exit[status];
