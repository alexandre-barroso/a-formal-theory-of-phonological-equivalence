BeginPackage["LCore`"];

LoadSpec::usage = "LoadSpec[path] imports a declarative JSON file.";
LFragment::usage = "LFragment[spec, id] builds the evaluator record for one input.";
LReaders::usage = "LReaders[fr, schemas, segs] returns <|{name,q} -> {C,Def,G}|>.";
LScore8::usage = "LScore8[fr, schemas, segs, refReaders] returns the integer 8 P_U.";
LEvaluate::usage = "LEvaluate[fr, schemas] returns fiber, minima and minimum8.";
LProbe::usage = "LProbe[spec, schemas, probeId] returns the G.6 locus report.";

Begin["`Private`"];

LoadSpec[path_String] := Get[path];

kNot[Undef] := Undef;
kNot[b_] := Not[b];
kAnd[args___] := Which[
  MemberQ[{args}, False], False,
  MemberQ[{args}, Undef], Undef,
  True, True];
kOr[args___] := Which[
  MemberQ[{args}, True], True,
  MemberQ[{args}, Undef], Undef,
  True, False];
kEq[a_, b_] := If[a === Undef || b === Undef, Undef, a === b];
collapse[v_] := TrueQ[v === True];

featRaw[spec_, seg_] := Lookup[spec["features"], seg, spec["default_segment_features"]];

feat[spec_, seg_, name_String] := Module[{row = featRaw[spec, seg], present, v},
  present = TrueQ[row["present"]];
  If[name === "present", Return[present]];
  v = Lookup[row, name, Null];
  Which[
    v === Null, Undef,
    (name === "nuclear" || name === "high") && ! present, Undef,
    True, v]];

buildOrigins[rec_] := Module[{res = {}, w = 0},
  Do[Do[AppendTo[res, <|"segment" -> seg, "word" -> w,
                        "phrase" -> rec["phrases"][[w + 1]]|>], {seg, word}];
     w++, {word, rec["words"]}];
  res];

LFragment[spec_, id_String] := Module[{rec, origins, focal, alphabet, radix, powers},
  rec = SelectFirst[Join[Lookup[spec, "inputs", {}], Lookup[spec, "probes", {}]],
                    #["id"] === id &];
  origins = buildOrigins[rec];
  focal = Lookup[rec, "focal", {}];
  alphabet = spec["alphabet"];
  radix = Length[alphabet];
  powers = Table[radix^e, {e, Reverse[Range[0, Length[focal] - 1]]}];
  <|"spec" -> spec, "record" -> rec, "origins" -> origins,
    "n" -> Length[origins], "focal" -> focal, "alphabet" -> alphabet,
    "radix" -> radix, "powers" -> powers, "size" -> radix^Length[focal],
    "reference" -> (#["segment"] & /@ origins),
    "weights" -> spec["weights"],
    "lambda" -> spec["lambda"]["num"]/spec["lambda"]["den"]|>];

candidateOf[fr_, idx_] := Module[{rest = idx, segs = fr["reference"], digits},
  digits = Table[Module[{q = Quotient[rest, p]}, rest = Mod[rest, p]; q], {p, fr["powers"]}];
  MapThread[(segs[[#1 + 1]] = fr["alphabet"][[#2 + 1]]) &, {fr["focal"], digits}];
  segs];

observeOf[fr_, segs_] := StringJoin[Select[segs, TrueQ[feat[fr["spec"], #, "present"]] &]];

admits[fr_, scope_, anchor_, other_] := Module[{a = fr["origins"][[anchor]],
                                                b = fr["origins"][[other]], dw},
  dw = b["word"] - a["word"];
  And[
    If[TrueQ[scope["same_phrase"]], a["phrase"] === b["phrase"], True],
    If[scope["word_delta"] === Null, True, dw === scope["word_delta"]],
    If[scope["min_word_delta"] === Null, True, dw >= scope["min_word_delta"]]]];

passesFilter[fr_, filt_, seg_] := Which[
  filt === Null, True,
  filt === "present", TrueQ[feat[fr["spec"], seg, "present"]],
  filt === "nuclear", feat[fr["spec"], seg, "nuclear"] === True,
  filt === "nuclear_nonhigh", feat[fr["spec"], seg, "nuclear"] === True &&
                              feat[fr["spec"], seg, "high"] =!= True,
  filt === "obstruent", feat[fr["spec"], seg, "obstruent"] === True,
  True, True];

liveOf[fr_, segs_] := Select[Range[fr["n"]], TrueQ[feat[fr["spec"], segs[[#]], "present"]] &];

stepCandidates[live_, anchor_, dir_] :=
  If[dir > 0, Select[live, # > anchor &], Reverse[Select[live, # < anchor &]]];

firstMatch[fr_, seq_, anchor_, slot_, segs_] := Module[{cands, res = Missing[]},
  cands = stepCandidates[seq, anchor, slot["direction"]];
  Do[If[passesFilter[fr, slot["filter"], segs[[i]]],
        res = i; Break[],
        If[slot["filter_mode"] === "stop", res = Missing[]; Break[]]], {i, cands}];
  res];

resolveSlot[fr_, slot_, anchor_, segs_] := Module[
  {live, liveRef, partner, lo, hi},
  Which[
    slot["kind"] === "anchor", anchor,
    slot["kind"] === "searched",
      Module[{res = Missing[], cands},
        live = liveOf[fr, segs];
        cands = stepCandidates[live, anchor, slot["direction"]];
        Do[If[admits[fr, slot["scope"], anchor, i] &&
              passesFilter[fr, slot["filter"], segs[[i]]], res = i; Break[]], {i, cands}];
        res],
    slot["policy"] === "dynamic",
      (live = liveOf[fr, segs];
       partner = firstMatch[fr, live, anchor, slot, segs];
       If[MissingQ[partner] || ! admits[fr, slot["scope"], anchor, partner],
          Missing[], partner]),
    True,
      (liveRef = liveOf[fr, fr["reference"]];
       partner = firstMatch[fr, liveRef, anchor, slot, fr["reference"]];
       Which[
         MissingQ[partner] || ! admits[fr, slot["scope"], anchor, partner], Missing[],
         ! TrueQ[feat[fr["spec"], segs[[anchor]], "present"]], Missing[],
         ! TrueQ[feat[fr["spec"], segs[[partner]], "present"]], Missing[],
         slot["policy"] === "origin_bound", partner,
         True,
           (lo = Min[anchor, partner]; hi = Max[anchor, partner];
            If[AnyTrue[Range[lo + 1, hi - 1],
                       TrueQ[feat[fr["spec"], segs[[#]], "present"]] &],
               Missing[], partner])])]];

assignOf[fr_, decl_, anchor_, segs_] :=
  Association[Table[s["name"] -> resolveSlot[fr, s, anchor, segs], {s, decl["slots"]}]];

realisation[fr_, segs_, o_, where_] :=
  If[where === "reference", fr["reference"][[o]], segs[[o]]];

positional[fr_, segs_, kind_, o_] := Module[{rec = fr["origins"][[o]], nuclei},
  Which[
    kind === "first_of_word",
      o === 1 || fr["origins"][[o - 1]]["word"] =!= rec["word"],
    kind === "last_nucleus_of_word",
      (nuclei = Select[liveOf[fr, segs],
          fr["origins"][[#]]["word"] === rec["word"] &&
          feat[fr["spec"], segs[[#]], "nuclear"] === True &];
       Length[nuclei] > 0 && Last[nuclei] === o),
    True, Undef]];

evalTerm[fr_, t_, alpha_, segs_] := Module[{op = t["op"], o, o2, a, b},
  Which[
    op === "const", If[t["value"] === Null, Undef, t["value"]],
    op === "resolves", ! MissingQ[Lookup[alpha, t["slot"], Missing[]]],
    op === "present",
      (o = Lookup[alpha, t["slot"], Missing[]];
       If[MissingQ[o], Undef, TrueQ[feat[fr["spec"], realisation[fr, segs, o, t["where"]], "present"]]]),
    op === "feat",
      (o = Lookup[alpha, t["slot"], Missing[]];
       If[MissingQ[o], Undef,
          kEq[feat[fr["spec"], realisation[fr, segs, o, t["where"]], t["feature"]], t["value"]]]),
    op === "sameFeat",
      (o = Lookup[alpha, t["left"][[1]], Missing[]];
       o2 = Lookup[alpha, t["right"][[1]], Missing[]];
       If[MissingQ[o] || MissingQ[o2], Undef,
          kEq[feat[fr["spec"], realisation[fr, segs, o, t["left"][[2]]], t["feature"]],
              feat[fr["spec"], realisation[fr, segs, o2, t["right"][[2]]], t["feature"]]]]),
    op === "sameSeg",
      (o = Lookup[alpha, t["left"][[1]], Missing[]];
       o2 = Lookup[alpha, t["right"][[1]], Missing[]];
       If[MissingQ[o] || MissingQ[o2], Undef,
          realisation[fr, segs, o, t["left"][[2]]] === realisation[fr, segs, o2, t["right"][[2]]]]),
    op === "positional",
      (o = Lookup[alpha, t["slot"], Missing[]];
       If[MissingQ[o], Undef, positional[fr, segs, t["kind"], o]]),
    op === "inScope",
      (o = Lookup[alpha, t["slot"], Missing[]];
       a = Lookup[alpha, t["anchor"], Missing[]];
       If[MissingQ[o] || MissingQ[a], Undef, admits[fr, t["scope"], a, o]]),
    op === "not", kNot[evalTerm[fr, t["arg"], alpha, segs]],
    op === "and", kAnd @@ (evalTerm[fr, #, alpha, segs] & /@ t["args"]),
    op === "or", kOr @@ (evalTerm[fr, #, alpha, segs] & /@ t["args"]),
    True, Undef]];

readOne[fr_, decl_, anchor_, segs_] := Module[{alpha, v, defined, good, ctx},
  alpha = assignOf[fr, decl, anchor, segs];
  v = evalTerm[fr, decl["consequence"], alpha, segs];
  defined = If[decl["definedness_override"] === Null,
               v =!= Undef,
               collapse[evalTerm[fr, decl["definedness_override"], alpha, segs]]];
  good = (v === True);
  ctx = collapse[evalTerm[fr, decl["activation"], alpha, segs]];
  {ctx, defined, good}];

LReaders[fr_, schemas_, segs_] := Association[
  Flatten[Table[Table[{name, q} -> readOne[fr, schemas[name], q, segs],
                      {q, fr["n"]}], {name, Keys[schemas]}]]];

pressureOf[{_, d_, g_}] := If[TrueQ[d] && ! TrueQ[g], 1, 0];
markedOf[{c_, d_, g_}] := If[TrueQ[c] && TrueQ[d] && ! TrueQ[g], 1, 0];

markednessNames = {"H", "A", "GL", "D"};

LScore8[fr_, schemas_, segs_, refReaders_] := Module[{cur, total = 0, old, new},
  cur = LReaders[fr, schemas, segs];
  Do[old = 0; new = 0;
     Do[Module[{tri = cur[{name, q}], a},
        If[MemberQ[markednessNames, name],
           a = markedOf[refReaders[{name, q}]];
           If[a === 1, old += pressureOf[tri], new += markedOf[tri]],
           old += markedOf[tri]]], {q, fr["n"]}];
     total += fr["weights"][name] (old + fr["lambda"] new), {name, Keys[schemas]}];
  8 total];

LEvaluate[fr_, schemas_] := Module[{ref, vals, obs, target, fiber, best, minima},
  ref = LReaders[fr, schemas, fr["reference"]];
  vals = Table[LScore8[fr, schemas, candidateOf[fr, i], ref], {i, 0, fr["size"] - 1}];
  obs = Table[observeOf[fr, candidateOf[fr, i]], {i, 0, fr["size"] - 1}];
  target = fr["record"]["observation"];
  fiber = Flatten[Position[obs, target]] - 1;
  best = Min[vals];
  minima = Flatten[Position[vals, best]] - 1;
  <|"id" -> fr["record"]["id"], "states" -> fr["size"], "fiber" -> fiber,
    "minima" -> minima, "minimum8" -> best,
    "exclusively_correct" -> SubsetQ[fiber, minima]|>];

LProbe[spec_, schemas_, probeId_] := Module[{fr, rec, q, name, w, ref, rows},
  fr = LFragment[spec, probeId];
  rec = fr["record"];
  q = rec["locus"]["origin"] + 1;
  name = rec["locus"]["schema"];
  w = fr["weights"][name];
  ref = LReaders[fr, schemas, fr["reference"]];
  rows = Table[Module[{tri = readOne[fr, schemas[name], q, st]},
      <|"state" -> st, "readers" -> tri,
        "retained8" -> 8 w (If[markedOf[ref[{name, q}]] === 1, pressureOf[tri], 0])|>],
    {st, rec["states"]}];
  <|"probe" -> probeId, "rows" -> rows,
    "retained8" -> (#["retained8"] & /@ rows)|>];

End[];
EndPackage[];
