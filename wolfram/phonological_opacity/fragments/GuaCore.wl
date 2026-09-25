BeginPackage["GuaCore`"];

LoadGuaSpec::usage = "LoadGuaSpec[path] imports the declarative fragment specification.";
GuaFragment::usage = "GuaFragment[spec, id] builds the evaluator record for one input.";
GuaEvaluate::usage = "GuaEvaluate[fragment] returns fiber, minima and the exact minimum times 8.";
GuaProbeReport::usage = "GuaProbeReport[spec, probeId] returns the G.6 locus report.";

Begin["`Private`"];

LoadGuaSpec[path_String] := Get[path];

featureOf[spec_, seg_] := Lookup[spec["features"], seg, spec["default_segment_features"]];

buildOrigins[rec_] := Module[{res = {}, w = 0},
  Do[Do[AppendTo[res, <|"segment" -> seg, "word" -> w, "phrase" -> rec["phrases"][[w + 1]]|>],
       {seg, word}]; w++, {word, rec["words"]}];
  res];

GuaFragment[spec_, id_String] := Module[{rec, origins, n, focal, alphabet, radix, powers},
  rec = SelectFirst[spec["inputs"], #["id"] === id &];
  origins = buildOrigins[rec];
  n = Length[origins];
  focal = rec["focal"];
  alphabet = spec["alphabet"];
  radix = Length[alphabet];
  powers = Table[radix^e, {e, Reverse[Range[0, Length[focal] - 1]]}];
  <|"spec" -> spec, "record" -> rec, "origins" -> origins, "n" -> n,
    "focal" -> focal, "alphabet" -> alphabet, "radix" -> radix, "powers" -> powers,
    "size" -> radix^Length[focal],
    "reference" -> (#["segment"] & /@ origins)|>];

candidateOf[fr_, idx_] := Module[{digits, rest = idx, segs = fr["reference"]},
  digits = Table[Module[{q = Quotient[rest, p]}, rest = Mod[rest, p]; q], {p, fr["powers"]}];
  MapThread[(segs[[#1 + 1]] = fr["alphabet"][[#2 + 1]]) &, {fr["focal"], digits}];
  segs];

observeOf[fr_, segs_] := StringJoin[Select[segs, TrueQ[featureOf[fr["spec"], #]["present"]] &]];

readersOf[fr_, segs_] := Module[
  {spec = fr["spec"], n = fr["n"], origins = fr["origins"], refsegs = fr["reference"],
   fs, rf, live, nxt, prv, nuclei, lastNuc, out},
  fs = featureOf[spec, #] & /@ segs;
  rf = featureOf[spec, #] & /@ refsegs;
  live = Select[Range[n], TrueQ[fs[[#]]["present"]] &];
  nxt = Association[Thread[Most[live] -> Rest[live]]];
  prv = Association[Thread[Rest[live] -> Most[live]]];
  nuclei = Select[live, TrueQ[fs[[#]]["nuclear"]] &];
  lastNuc = Association[]; Do[lastNuc[origins[[q]]["word"]] = q, {q, nuclei}];
  out = Association[];
  Do[Module[{f = fs[[q]], r = rf[[q]], o = origins[[q]], nq, pq, src, hC, cross, aC, aG,
             neighbour, glC, dC, initC, initD, initG},
    nq = Lookup[nxt, q, Missing[]]; pq = Lookup[prv, q, Missing[]];
    out[{"MAX", q}] = {True, True, TrueQ[f["present"]]};
    out[{"IDENT_ATR", q}] = {True, TrueQ[f["nuclear"]] && TrueQ[r["nuclear"]], f["atr"] === r["atr"]};
    out[{"IDENT_QUAL", q}] = {True,
       TrueQ[f["present"]] && !MatchQ[f["quality"], Null] && !MatchQ[r["quality"], Null],
       f["quality"] === r["quality"]};
    out[{"IDENT_NUC", q}] = {True, TrueQ[f["present"]], TrueQ[f["nuclear"]] === TrueQ[r["nuclear"]]};
    src = SelectFirst[nuclei,
       # > q && origins[[#]]["word"] > o["word"] && origins[[#]]["phrase"] === o["phrase"] &,
       Missing[]];
    hC = TrueQ[f["nuclear"]] && Lookup[lastNuc, o["word"], Missing[]] === q &&
         !MissingQ[src] && fs[[src]]["atr"] === True;
    out[{"H", q}] = {hC, TrueQ[f["nuclear"]], f["atr"] === True};
    cross = !MissingQ[nq] && origins[[nq]]["word"] === o["word"] + 1 &&
            origins[[nq]]["phrase"] === o["phrase"];
    aC = TrueQ[f["nuclear"]] && !TrueQ[f["high"]] && cross &&
         TrueQ[fs[[nq]]["nuclear"]] && !TrueQ[fs[[nq]]["high"]];
    aG = !TrueQ[f["present"]] || (!MissingQ[nq] && segs[[q]] === segs[[nq]]);
    out[{"A", q}] = {aC, True, aG};
    neighbour = AnyTrue[{pq, nq}, (!MissingQ[#] &&
         Abs[origins[[#]]["word"] - o["word"]] === 1 &&
         origins[[#]]["phrase"] === o["phrase"] &&
         TrueQ[fs[[#]]["nuclear"]] && !TrueQ[fs[[#]]["high"]]) &];
    glC = TrueQ[f["nuclear"]] && TrueQ[f["high"]] && neighbour;
    out[{"GL", q}] = {glC, True, !TrueQ[f["nuclear"]]};
    dC = TrueQ[f["nuclear"]] && TrueQ[f["high"]] && !MissingQ[pq] &&
         origins[[pq]]["word"] + 1 === o["word"] &&
         origins[[pq]]["phrase"] === o["phrase"] &&
         TrueQ[fs[[pq]]["nuclear"]] && TrueQ[fs[[pq]]["high"]];
    out[{"D", q}] = {dC, True, !TrueQ[f["present"]]};
    initC = TrueQ[r["nuclear"]] && (q === 1 || origins[[q - 1]]["word"] =!= o["word"]);
    initD = TrueQ[f["present"]] && !MatchQ[f["quality"], Null];
    initG = (f["quality"] === r["quality"]) && (!TrueQ[f["nuclear"]] || f["atr"] === r["atr"]);
    out[{"INITIAL_FEATURE", q}] = {initC, initD, initG};
    ], {q, Range[n]}];
  out];

schemaNames = {"MAX", "IDENT_ATR", "IDENT_QUAL", "IDENT_NUC", "H", "A", "GL", "D", "INITIAL_FEATURE"};
markednessNames = {"H", "A", "GL", "D"};

pressureOf[{_, d_, g_}] := Boole[TrueQ[d] && !TrueQ[g]];
markedOf[{c_, d_, g_}] := Boole[TrueQ[c] && TrueQ[d] && !TrueQ[g]];

score8Of[fr_, segs_, refReaders_] := Module[{cur, spec = fr["spec"], lam, total = 0},
  cur = readersOf[fr, segs];
  lam = spec["lambda"]["num"] / spec["lambda"]["den"];
  Do[Module[{old = 0, new = 0, w = spec["weights"][s]},
    Do[Module[{p = pressureOf[cur[{s, q}]], m = markedOf[cur[{s, q}]], a},
      If[MemberQ[markednessNames, s],
        a = markedOf[refReaders[{s, q}]];
        If[a === 1, old += p, new += m],
        old += m]], {q, Range[fr["n"]]}];
    total += w (old + lam new)], {s, schemaNames}];
  8 total];

GuaEvaluate[fr_] := Module[{refReaders, vals, obs, target, fiber, best, minima},
  refReaders = readersOf[fr, fr["reference"]];
  vals = Table[score8Of[fr, candidateOf[fr, i], refReaders], {i, 0, fr["size"] - 1}];
  obs = Table[observeOf[fr, candidateOf[fr, i]], {i, 0, fr["size"] - 1}];
  target = fr["record"]["observation"];
  fiber = Flatten[Position[obs, target]] - 1;
  best = Min[vals];
  minima = Flatten[Position[vals, best]] - 1;
  <|"id" -> fr["record"]["id"], "states" -> fr["size"], "fiber" -> fiber,
    "minima" -> minima, "minimum8" -> best,
    "exclusively_correct" -> SubsetQ[fiber, minima]|>];

GuaProbeReport[spec_, probeId_String] := Module[{rec, shim, fr, refReaders, schema, q, out},
  rec = SelectFirst[spec["probes"], #["id"] === probeId &];
  shim = Append[rec, "observation" -> ""];
  fr = GuaFragment[Append[spec, "inputs" -> Append[spec["inputs"], shim]], probeId];
  refReaders = readersOf[fr, fr["reference"]];
  schema = rec["locus"]["schema"]; q = rec["locus"]["origin"] + 1;
  out = Table[Module[{cur = readersOf[fr, state], p, a},
      p = pressureOf[cur[{schema, q}]]; a = markedOf[refReaders[{schema, q}]];
      <|"state" -> state, "context" -> cur[{schema, q}][[1]], "defined" -> cur[{schema, q}][[2]],
        "good" -> cur[{schema, q}][[3]], "reference_marked" -> (a === 1),
        "retained8" -> 8 spec["weights"][schema] If[a === 1, p, 0]|>],
    {state, rec["states"]}];
  out];

End[];
EndPackage[];
