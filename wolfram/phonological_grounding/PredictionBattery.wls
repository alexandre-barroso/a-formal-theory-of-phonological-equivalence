root = DirectoryName[$InputFileName, 3];
Get[FileNameJoin[{root, "wolfram", "phonological_opacity", "fragments", "GuaCore.wl"}]];

spec = Get[FileNameJoin[{root, "wolfram", "phonological_opacity", "fragments", "GuaFragmentSpec.wl"}]];
battery = Get[FileNameJoin[{root, "wolfram", "phonological_grounding", "BatterySpec.wl"}]];

withCell[cell_] := Module[{sh = spec},
  sh["inputs"] = Append[spec["inputs"],
    <|"id" -> cell["id"], "words" -> cell["words"], "phrases" -> cell["phrases"],
      "focal" -> cell["focal"], "observation" -> cell["opaque_observation"]|>];
  sh];

retainedRow[cell_] := Module[{sh, fr, ev},
  sh = withCell[cell];
  fr = GuaCore`GuaFragment[sh, cell["id"]];
  ev = GuaCore`GuaEvaluate[fr];
  <|"id" -> cell["id"], "states" -> ev["states"], "minimum8" -> ev["minimum8"],
    "minima" -> ev["minima"], "fiber" -> ev["fiber"],
    "exclusively_correct" -> ev["exclusively_correct"]|>];

ft[sg_] := Lookup[spec["features"], sg, spec["default_segment_features"]];
isPresent[sg_] := TrueQ[ft[sg]["present"]];
isNuclear[sg_] := TrueQ[ft[sg]["nuclear"]];
isHigh[sg_] := TrueQ[ft[sg]["high"]];
atrOf[sg_] := ft[sg]["atr"];
qualOf[sg_] := ft[sg]["quality"];

originsOf[words_, phrases_] := Module[{res = {}, w = 0},
  Do[Do[AppendTo[res, <|"segment" -> sg, "word" -> w, "phrase" -> phrases[[w + 1]]|>],
        {sg, word}]; w++, {word, words}];
  res];

activityAssoc[segs_, tier_] := Module[{res = <||>, i = 1, j, n},
  While[i <= Length[tier],
   j = i;
   While[j < Length[tier] && atrOf[segs[[tier[[j + 1]]]]] === atrOf[segs[[tier[[i]]]]], j++];
   n = j - i + 1;
   Do[res[tier[[k]]] = 1/n, {k, i, j}];
   i = j + 1];
  res];

saViolations[origins_, refsegs_, segs_, phraseGuard_ : True] := Module[
  {n = Length[origins], tier, act, live, nxt, consecutive, markA = 0, markH = 0,
   idInit = 0, idPlusG = 0, idMinus = 0, idQual = 0, idHigh = 0, maxV = 0,
   idNuc = 0, idPlus = 0},
  tier = Select[Range[n], isPresent[segs[[#]]] && isNuclear[segs[[#]]] &];
  act = activityAssoc[segs, tier];
  live = Select[Range[n], isPresent[segs[[#]]] &];
  nxt = Association[Thread[Most[live] -> Rest[live]]];
  consecutive[p_, q_] := origins[[q]]["word"] == origins[[p]]["word"] + 1 &&
     (!phraseGuard || origins[[q]]["phrase"] == origins[[p]]["phrase"]);
  Do[If[consecutive[tier[[k]], tier[[k + 1]]] &&
        atrOf[segs[[tier[[k]]]]] === False && atrOf[segs[[tier[[k + 1]]]]] === True,
      markA++], {k, 1, Length[tier] - 1}];
  Do[Module[{q = Lookup[nxt, p, Missing[]]},
     If[! MissingQ[q] && consecutive[p, q] &&
        isNuclear[segs[[p]]] && isNuclear[segs[[q]]] &&
        ! isHigh[segs[[p]]] && ! isHigh[segs[[q]]] && segs[[p]] =!= segs[[q]],
       markH++]], {p, live}];
  Do[Module[{r = refsegs[[q]], f = segs[[q]], wordInitial},
     wordInitial = (q == 1) || origins[[q - 1]]["word"] =!= origins[[q]]["word"];
     If[isNuclear[r] && wordInitial && f =!= r, idInit++];
     If[isNuclear[r] && atrOf[r] === True && ! (isNuclear[f] && atrOf[f] === True),
       idPlus++;
       If[KeyExistsQ[act, q], idPlusG += 1 - act[q], idPlusG += 1]];
     If[isNuclear[r] && atrOf[r] === False && isNuclear[f] && atrOf[f] === True, idMinus++];
     If[! isPresent[f], maxV++];
     If[isPresent[f] && qualOf[f] =!= Null && qualOf[r] =!= Null && qualOf[f] =!= qualOf[r], idQual++];
     If[isPresent[f] && isHigh[f] =!= isHigh[r], idHigh++];
     If[isPresent[f] && isNuclear[f] =!= isNuclear[r], idNuc++]], {q, Range[n]}];
  <|"MARK_ATR" -> markA, "MARK_HIA" -> markH, "ID_INIT_V" -> idInit,
    "ID_PLUS_ATR_G" -> idPlusG, "ID_MINUS_ATR" -> idMinus, "ID_QUAL" -> idQual,
    "ID_HIGH" -> idHigh, "MAX" -> maxV, "ID_NUC" -> idNuc, "ID_PLUS_ATR" -> idPlus|>];

posterWeights = <|"MARK_ATR" -> 23, "MARK_HIA" -> 22, "ID_INIT_V" -> 22,
  "ID_PLUS_ATR_G" -> 21, "ID_MINUS_ATR" -> 1, "ID_QUAL" -> 0, "ID_HIGH" -> 0,
  "MAX" -> 0, "ID_NUC" -> 0, "ID_PLUS_ATR" -> 0|>;

saPenalty[v_, w_] := Total[KeyValueMap[#2*Lookup[w, #1, 0] &, v]];

rs[x_] := If[Head[x] === Rational, ToString[Numerator[x]] <> "/" <> ToString[Denominator[x]], x];
rsAll[a_Association] := Association[KeyValueMap[#1 -> rs[#2] &, a]];

posterRows = Module[{rows = battery["poster_rows"]["rows"]},
  Function[r, Module[{o, v},
     o = originsOf[r["words"], r["phrases"]];
     v = saViolations[o, r["reference"], r["candidate"]];
     <|"row" -> r["row"], "cells" -> rsAll[v],
       "poster_total" -> rs[saPenalty[v, posterWeights]],
       "poster_abs_H" -> r["poster_abs_H"],
       "repaired_abs_H" -> Lookup[r, "repaired_abs_H", "n/a"],
       "matched_against" -> If[TrueQ[saPenalty[v, posterWeights] == r["poster_abs_H"]],
          "printed", If[TrueQ[saPenalty[v, posterWeights] == Lookup[r, "repaired_abs_H", -1]],
          "repaired by definition (11), see DECISIONS D2", "NO MATCH"]],
       "matches" -> TrueQ[saPenalty[v, posterWeights] == r["poster_abs_H"] ||
          saPenalty[v, posterWeights] == Lookup[r, "repaired_abs_H", -1]]|>]] /@ rows];

cellThreshold[cell_] := Module[{o, ref, opaque, transparent, vOp, vTr, v1, v3},
  v1 = cell["v1"]; v3 = cell["v3"];
  o = originsOf[cell["words"], cell["phrases"]];
  ref = cell["reference_segments"];
  opaque = cell["opaque_segments"];
  transparent = cell["transparent_segments"];
  vOp = saViolations[o, ref, opaque];
  vTr = saViolations[o, ref, transparent];
  <|"id" -> cell["id"], "v1" -> v1, "v3" -> v3,
    "opaque_cells" -> rsAll[vOp], "transparent_cells" -> rsAll[vTr],
    "idPlusG_opaque" -> rs[vOp["ID_PLUS_ATR_G"]],
    "idPlusG_transparent" -> rs[vTr["ID_PLUS_ATR_G"]],
    "threshold_ratio" -> rs[v1/((1 + v3) (v1 + 1 + v3))],
    "threshold_from_cells" -> rs[vTr["ID_PLUS_ATR_G"] - vOp["ID_PLUS_ATR_G"]],
    "opaque_observation" -> cell["opaque_observation"],
    "transparent_observation" -> cell["transparent_observation"]|>];

result = <|
  "poster_rows" -> posterRows,
  "retained_on_cells" -> (retainedRow /@ battery["cells"]),
  "retained_on_controls" -> (retainedRow[Append[#, "opaque_observation" -> ""]] & /@
     battery["transparent_controls"]),
  "shared_activity_thresholds" -> (cellThreshold /@ battery["cells"]),
  "development_bound_from_G34a" -> rs[2/((1 + 3) (2 + 1 + 3))]
|>;

Print[Grid[Prepend[
  {#["id"], #["v1"], #["v3"], #["idPlusG_opaque"], #["idPlusG_transparent"],
    #["threshold_ratio"], #["threshold_from_cells"]} & /@
   result["shared_activity_thresholds"],
  {"cell", "v1", "v3", "Id+g(op)", "Id+g(tr)", "ratio", "gap"}], Frame -> All]];
Print[Grid[Prepend[
  {#["id"], #["states"], #["minimum8"], ToString[#["minima"]], ToString[#["fiber"]],
    ToString[#["exclusively_correct"]]} & /@ result["retained_on_cells"],
  {"cell", "states", "8P", "minima", "fibre", "excl"}], Frame -> All]];
Print[Grid[Prepend[
  {#["row"], #["poster_total"], ToString[#["poster_abs_H"]],
    ToString[#["repaired_abs_H"]], #["matched_against"]} & /@ result["poster_rows"],
  {"poster row", "reconstructed", "printed", "repaired", "matched against"}], Frame -> All]];
