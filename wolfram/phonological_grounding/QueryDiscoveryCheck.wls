root = DirectoryName[$InputFileName, 3];
Get[FileNameJoin[{root, "wolfram", "phonological_opacity", "fragments", "GuaCore.wl"}]];

spec = GuaCore`LoadGuaSpec[FileNameJoin[{root, "wolfram", "phonological_opacity", "fragments", "GuaFragmentSpec.wl"}]];
licence = Get[FileNameJoin[{root, "wolfram", "phonological_grounding", "GuaLicenceSpec.wl"}]];

readers = GuaCore`Private`readersOf;
candidate = GuaCore`Private`candidateOf;
observe = GuaCore`Private`observeOf;
featureOf = GuaCore`Private`featureOf;
pressure = GuaCore`Private`pressureOf;
marked = GuaCore`Private`markedOf;
schemaNames = GuaCore`Private`schemaNames;
markednessNames = GuaCore`Private`markednessNames;

inputIds = {"G34a", "G34b", "N7", "G37c", "C24ei", "OR38", "C21b", "C23UE"};

nuclearQ[seg_] := TrueQ[featureOf[spec, seg]["nuclear"]];
presentQ[seg_] := TrueQ[featureOf[spec, seg]["present"]];

focalPolicy[rec_] := Module[{words = rec["words"], phrases = rec["phrases"], starts, chosen = {}, run = 0},
  starts = Table[Module[{s = run}, run += Length[words[[i]]]; s], {i, Length[words]}];
  Do[If[phrases[[left]] === phrases[[left + 1]],
     Module[{ln, rn},
       ln = Select[Range[Length[words[[left]]]], nuclearQ[words[[left]][[#]]] &];
       rn = Select[Range[Length[words[[left + 1]]]], nuclearQ[words[[left + 1]][[#]]] &];
       If[ln =!= {}, AppendTo[chosen, starts[[left]] + Last[ln] - 1]];
       If[rn =!= {}, AppendTo[chosen, starts[[left + 1]] + First[rn] - 1]]]],
   {left, Length[words] - 1}];
  Sort[DeleteDuplicates[chosen]]];

focalCheck = Table[Module[{rec = SelectFirst[spec["inputs"], #["id"] === id &]},
    {id, focalPolicy[rec] === rec["focal"]}], {id, inputIds}];
Print["focal policy reproduces the declared focal lists: ",
  AllTrue[focalCheck, Last], " ", focalCheck];

toneOf[id_] := licence["tone"]["per_input"][id]["tones"];

segBridge[fr_, segs_] := observe[fr, segs];
segToneBridge[fr_, segs_, tones_] := Module[{n = fr["n"]},
  Table[If[presentQ[segs[[q]]],
      {segs[[q]], If[nuclearQ[segs[[q]]], tones[[q]], Null]}, Nothing], {q, n}]];

toneReport = Table[Module[
    {fr = GuaCore`GuaFragment[spec, id], tones = toneOf[id], segs, sv, tv, groups,
     merged = 0, resolved = 0, residual = 0},
    segs = Table[candidate[fr, i], {i, 0, fr["size"] - 1}];
    sv = segBridge[fr, #] & /@ segs;
    tv = segToneBridge[fr, #, tones] & /@ segs;
    groups = Select[GatherBy[Range[Length[sv]], sv[[#]] &], Length[#] > 1 &];
    Do[Module[{g = grp},
       Do[Module[{i = g[[a]], j = g[[b]]},
          merged++;
          If[tv[[i]] =!= tv[[j]], resolved++, residual++]],
         {a, Length[g] - 1}, {b, a + 1, Length[g]}]], {grp, groups}];
    <|"id" -> id, "states" -> fr["size"],
      "image_B_seg" -> Length[DeleteDuplicates[sv]],
      "image_B_segtone" -> Length[DeleteDuplicates[tv]],
      "merged_pairs_B_seg" -> merged, "resolved_by_tone" -> resolved,
      "residual_after_tone" -> residual,
      "focal_origin_tones" -> (tones[[# + 1]] & /@ fr["focal"])|>],
  {id, inputIds}];

Print["tone bridge report:"];
Do[Print["  ", r["id"], " states=", r["states"], " imgSeg=", r["image_B_seg"],
    " imgTone=", r["image_B_segtone"], " merged=", r["merged_pairs_B_seg"],
    " resolved=", r["resolved_by_tone"], " residual=", r["residual_after_tone"],
    " focalTones=", r["focal_origin_tones"]], {r, toneReport}];

score8At[fr_, segs_, refReaders_] := GuaCore`Private`score8Of[fr, segs, refReaders];

correspondence[id_, focalIdx_] := Module[{fr, refReaders, segs, focalValues},
  fr = GuaCore`GuaFragment[spec, id];
  refReaders = readers[fr, fr["reference"]];
  segs = fr["reference"];
  focalValues = spec["alphabet"][[# + 1]] & /@ focalIdx;
  MapThread[(segs[[#1 + 1]] = #2) &, {fr["focal"], focalValues}];
  <|"focal" -> focalValues, "B_seg" -> observe[fr, segs],
    "B_segtone" -> segToneBridge[fr, segs, toneOf[id]],
    "score8" -> score8At[fr, segs, refReaders]|>];

pairReport = <|
  "OR38" -> {correspondence["OR38", {7, 0, 6}], correspondence["OR38", {7, 6, 0}]},
  "C21b" -> {correspondence["C21b", {0, 9}], correspondence["C21b", {9, 0}]}|>;

Print["two correspondences:"];
Do[Print["  ", k, ": ", (#["focal"] -> {#["B_seg"], #["score8"]}) & /@ pairReport[k],
    "  toneSeparates=", pairReport[k][[1]]["B_segtone"] =!= pairReport[k][[2]]["B_segtone"]],
  {k, Keys[pairReport]}];

locusVector[fr_, segs_, refReaders_] := Module[{cur = readers[fr, segs]},
  Table[Module[{old = 0, new = 0, curTotal = 0},
    Do[Module[{p = pressure[cur[{s, q}]], m = marked[cur[{s, q}]], a},
       curTotal += m;
       If[MemberQ[markednessNames, s],
         a = marked[refReaders[{s, q}]];
         If[a === 1, old += p, new += m],
         old += m]], {q, Range[fr["n"]]}];
    {old, new, curTotal}], {s, schemaNames}]];

baseWeights = Association[Table[s -> spec["weights"][s], {s, schemaNames}]];
baseLambda = spec["lambda"]["num"]/spec["lambda"]["den"];

variantScore8[vec_, weights_, lam_, modes_] := 8 Total[Table[Module[
    {mode = Lookup[modes, schemaNames[[i]], "retained"], w = weights[schemaNames[[i]]],
     t = vec[[i]]},
    Switch[mode, "off", 0, "current", w t[[3]], _, w (t[[1]] + lam t[[2]])]],
  {i, Length[schemaNames]}]];

allRetained = Association[Table[s -> "retained", {s, schemaNames}]];
currentMarkedness = Association[Table[s -> If[MemberQ[markednessNames, s], "current", "retained"],
   {s, schemaNames}]];

instances = Join[
  {<|"id" -> "RET", "lam" -> baseLambda, "modes" -> allRetained|>,
   <|"id" -> "CUR", "lam" -> baseLambda, "modes" -> currentMarkedness|>,
   <|"id" -> "RET_lam0", "lam" -> 0, "modes" -> allRetained|>,
   <|"id" -> "RET_lam1", "lam" -> 1, "modes" -> allRetained|>},
  Flatten[Table[{
     <|"id" -> "CUR_" <> s, "lam" -> baseLambda,
       "modes" -> Append[allRetained, s -> "current"]|>,
     <|"id" -> "OFF_" <> s, "lam" -> baseLambda,
       "modes" -> Append[allRetained, s -> "off"]|>}, {s, markednessNames}]]];

bridgeValues[fr_, segs_, tones_] := <|
  "B_seg" -> observe[fr, segs],
  "B_segtone" -> segToneBridge[fr, segs, tones],
  "B_count" -> Count[segs, _?presentQ],
  "B_atr" -> Table[If[presentQ[s] && nuclearQ[s],
      featureOf[spec, s]["atr"] /. {True -> "+", False -> "-", Null -> "0"}, Nothing], {s, segs}]|>;

modelSignature = Table[Module[
    {fr = GuaCore`GuaFragment[spec, id], refReaders, segsAll, vecs, tones = toneOf[id]},
    refReaders = readers[fr, fr["reference"]];
    segsAll = Table[candidate[fr, i], {i, 0, fr["size"] - 1}];
    vecs = locusVector[fr, #, refReaders] & /@ segsAll;
    Table[Module[{vals, best, minima},
       vals = variantScore8[#, baseWeights, inst["lam"], inst["modes"]] & /@ vecs;
       best = Min[vals];
       minima = Flatten[Position[vals, best]];
       Table[k -> Sort[DeleteDuplicates[
           Table[bridgeValues[fr, segsAll[[m]], tones][k], {m, minima}]]],
         {k, {"B_seg", "B_segtone", "B_count", "B_atr"}}]],
      {inst, instances}]],
  {id, inputIds}];

signatures = Table[Table[modelSignature[[j]][[i]], {j, Length[inputIds]}],
   {i, Length[instances]}];
classes = GatherBy[Range[Length[instances]], signatures[[#]] &];

Print["model-level depth-0 kernel: |M| = ", Length[instances],
  ", classes = ", Length[classes]];
Print["  class members: ", (instances[[#]]["id"] & /@ # ) & /@ classes];

inputCost = Association[Table[
   id -> 1 + Max[0, Length[SelectFirst[spec["inputs"], #["id"] === id &]["words"]] - 1],
   {id, inputIds}]];
bridgeCost = <|"B_seg" -> 0, "B_atr" -> 0, "B_count" -> 0, "B_segtone" -> 1|>;

protocols = Flatten[Table[{id, k}, {id, inputIds},
    {k, {"B_seg", "B_segtone", "B_count", "B_atr"}}], 1];
columns = Association[Table[p -> Table[
     (p[[2]] /. modelSignature[[FirstPosition[inputIds, p[[1]]][[1]]]][[i]]),
     {i, Length[instances]}],
   {p, protocols}]];

separates[sub_] := Module[{joint},
  joint = Table[Table[columns[p][[i]], {p, sub}], {i, Length[instances]}];
  Length[GatherBy[Range[Length[instances]], joint[[#]] &]] === Length[classes]];

costOf[sub_] := Total[(inputCost[#[[1]]] + bridgeCost[#[[2]]]) & /@ sub];

best = Infinity; optima = {};
Do[Module[{subs = Subsets[protocols, {size}]},
   Do[If[costOf[sub] <= best && separates[sub],
      If[costOf[sub] < best, best = costOf[sub]; optima = {sub},
         AppendTo[optima, sub]]], {sub, subs}]],
  {size, 1, 3}];
Print["minimum-cost separating battery over depth-0 protocols (sizes 1-3): cost = ", best,
  ", tied optima = ", Length[optima]];
Print["  one optimum: ", First[optima, {}]];

status = 0;
report[label_, ok_] := (Print[If[TrueQ[ok], "  PASS  ", "  FAIL  "], label]; If[!TrueQ[ok], status = 1]);
toneOfId[id_] := SelectFirst[toneReport, #["id"] === id &];
report["focal policy reproduces every declared focal list", AllTrue[focalCheck, Last]];
report["tone bridge resolves the atSOsiku merge (OR38): resolved pairs > 0",
  toneOfId["OR38"]["resolved_by_tone"] > 0];
report["tone bridge does not resolve the wUsUsE merge (C21b): resolved pairs = 0",
  toneOfId["C21b"]["resolved_by_tone"] == 0];
report["minimum-cost separating battery costs 8", best == 8];
report["fourteen tied optima", Length[optima] == 14];
Print["== wolfram query-discovery check exit ", status, " =="];
Exit[status];
