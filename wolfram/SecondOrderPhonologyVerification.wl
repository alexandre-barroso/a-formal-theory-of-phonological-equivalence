(*
Second-Order Phonological Calculus: Executable Mathematical Verification

Purpose
This package provides an exact, self-contained computational appendix for a
dissertation in formal phonology.  It verifies encoded algebraic identities,
finite constructions, finite exhaustive domains, reduction proofs, and
fixed application arithmetic.  Symbolic verification closes exact formulas
under printed assumptions; exhaustive verification checks every element of a
declared finite domain; reduction proofs check an explicit map and its
sign, restriction, and size proof goals; numerical regressions are separately
labelled diagnostics and never discharge a registered exact proof goal.

Loading without execution:
  Get["verification/wolfram/SecondOrderPhonologyVerification.wl"]

Headless execution:
  wolframscript -file verification/wolfram/SecondOrderPhonologyVerification.wl --run-all --mode dissertation-release --output verification/reports
  wolframscript -file verification/wolfram/SecondOrderPhonologyVerification.wl --run-group CHG --mode machine-strict --output verification/reports
  wolframscript -file verification/wolfram/SecondOrderPhonologyVerification.wl --run-result-id CHG-B2 --mode diagnostics --output verification/reports

Some WolframScript releases consume trailing long options in `-file` mode.
Direct `-file` execution therefore defaults to the full suite; `-script` is
the portable form when group, mode, or output selectors must be forwarded.

Scope
The package verifies the formalized mathematics and exact application
arithmetic encoded below.  It is not a proof-assistant formalization, does not
establish literature priority or empirical truth, and does not replace human
inspection of the correspondence between this encoding and the dissertation.
*)

BeginPackage["SecondOrderPhonologyVerification`"];

VerificationCatalog::usage =
  "VerificationCatalog[] returns the stable catalog of theorem, application, regression, and decision-ledger verification results.";
RunResultVerification::usage =
  "RunResultVerification[id, opts] runs one catalog result and returns a detailed exact-verification association.";
RunVerificationGroup::usage =
  "RunVerificationGroup[group, opts] runs every catalog result in the named group in stable catalog order.";
RunAllVerification::usage =
  "RunAllVerification[opts] runs the complete verification catalog; the default mode is \"full\".";
ExportVerificationReport::usage =
  "ExportVerificationReport[report, directory] exports exact JSON and readable Markdown reports with separate machine and dissertation-proof closure.";
ExportCanonicalData::usage =
  "ExportCanonicalData[directory] exports the embedded exact decision ledgers and exact catalog values as public TSV and JSON files.";

Begin["`Private`"];

$HistoryLength = 0;

ClearAll[
  $packageVersion, $packageTitle, $packageSourcePath, $packageSourceHash,
  $packageRoot, $proofStatusCache,
  $expectedResultIDs, $mandatoryPassStatuses, $allStatuses,
  $randomSeed, $catalogCache, $runCache
];

$packageVersion = "1.1.0";
$packageTitle = "Second-Order Phonological Calculus: Executable Mathematical Verification";
$packageSourcePath = If[StringQ[$InputFileName] && StringLength[$InputFileName] > 0,
  ExpandFileName[$InputFileName], Missing["SourcePathUnavailable"]];
$packageSourceHash = If[StringQ[$packageSourcePath] && FileExistsQ[$packageSourcePath],
  IntegerString[FileHash[$packageSourcePath, "SHA256"], 16, 64],
  Missing["SourceHashUnavailable"]];
$packageRoot = If[StringQ[$packageSourcePath],
  DirectoryName[DirectoryName[DirectoryName[$packageSourcePath]]],
  Missing["PackageRootUnavailable"]];
$proofStatusCache =.;
$randomSeed = 2718281828;
$catalogCache =.;
$runCache = <||>;

$allStatuses = {
  "ExactSymbolicPass", "ExactConstructivePass", "ExhaustiveFinitePass",
  "ReductionProofPass", "SupplementaryNumericalPass", "BuildFailure",
  "LeanKernelProofReferenceCheck"
};
$mandatoryPassStatuses = {
  "ExactSymbolicPass", "ExactConstructivePass", "ExhaustiveFinitePass",
  "ReductionProofPass", "LeanKernelProofReferenceCheck"
};

$expectedResultIDs = Join[
  {"CALC-F1"}, Table["CALC-R" <> IntegerString[index, 10, 2], {index, 15}],
  Table["FIN-A" <> ToString[index], {index, 7}],
  Table["CHG-B" <> ToString[index], {index, 16}],
  Table["CTX-C" <> ToString[index], {index, 2}],
  Table["FLUX-D" <> ToString[index], {index, 5}],
  Table["SUP-E" <> ToString[index], {index, 4}],
  Table["SEL-F" <> ToString[index], {index, 2}],
  Table["MAX-G" <> ToString[index], {index, 9}],
  {"APP-MCC-GRID", "APP-MCC-LENGTH", "APP-MCC-COMP", "APP-BASIC",
   "DATA-PT-R1", "DATA-EN-R1", "DATA-ZH-R1"}
];

(* Verification-result data model and exact report utilities *)

ClearAll[
  inputFormString, heldInputFormString, exactJSONValue, exactAssociation,
  makeProofGoal, makeResultSpecification, publicCatalogRow, statusCompleteQ,
  statementText, statementHash, proofStatusRegistry, proofStatusRow,
  publicResultMetadata, releaseClosedQ,
  sourceIdentity, executionIdentity, captureEvaluation, runProofGoal,
  summarizeProofGoals, combineResultStatus, normalizeMode, validLimitQ,
  formatSeconds, markdownEscape, markdownTableCell, reportSummary,
  failedResultQ, mandatoryResultCompleteQ, reportDisclaimer
];

inputFormString[expression_] := ToString[Unevaluated[expression], InputForm,
  CharacterEncoding -> "UTF-8"];
heldInputFormString[expression_] := inputFormString[HoldComplete[expression]];

exactJSONValue[value_] := Which[
  AssociationQ[value] && AllTrue[Keys[value], StringQ],
    Map[exactJSONValue, value],
  AssociationQ[value], <|"WolframAssociationEntries" ->
    KeyValueMap[
      <|"KeyInputForm" -> heldInputFormString[#1],
        "Value" -> exactJSONValue[#2]|> &,
      value]|>,
  ListQ[value], exactJSONValue /@ value,
  StringQ[value] || IntegerQ[value] || TrueQ[value] || value === False ||
    value === Null, value,
  Head[value] === Real, inputFormString[value],
  MissingQ[value] || FailureQ[value], inputFormString[value],
  True, inputFormString[value]
];

exactAssociation[rules___Rule] := Association[rules];

SetAttributes[makeProofGoal, HoldRest];
makeProofGoal[id_String, title_String, classification_String, expression_, expected_,
    method_String, mandatory_: True, note_: ""] := <|
  "ProofGoalID" -> id,
  "Title" -> title,
  "Classification" -> classification,
  "Mandatory" -> TrueQ[mandatory],
  "Expression" -> HoldComplete[expression],
  "Expected" -> HoldComplete[expected],
  "ProofMethod" -> method,
  "Note" -> note
|>;

makeResultSpecification[id_String, title_String, group_String, classification_String,
    mandatory_, statement_, assumptions_, sourceReference_String, scope_String,
    nonClaims_String, method_String, proofGoals_List] := <|
  "ResultID" -> id,
  "Title" -> title,
  "Group" -> group,
  "Classification" -> classification,
  "Mandatory" -> TrueQ[mandatory],
  "Statement" -> HoldComplete[statement],
  "Assumptions" -> HoldComplete[assumptions],
  "SourceReference" -> sourceReference,
  "Scope" -> scope,
  "NonClaims" -> nonClaims,
  "Method" -> method,
  "ProofGoals" -> proofGoals
|>;

statementText[spec_Association] := Replace[spec["Statement"],
  HoldComplete[value_String] :> value];
statementHash[spec_Association] := IntegerString[
  Hash[statementText[spec], "SHA256"], 16, 64];

proofStatusRegistry[] := Module[{path, rows, header},
  If[AssociationQ[$proofStatusCache], Return[$proofStatusCache]];
  path = If[StringQ[$packageRoot],
    FileNameJoin[{$packageRoot, "registry", "result_status.tsv"}], ""];
  If[path === "" || ! FileExistsQ[path], Return[<||>]];
  rows = Import[path, "TSV"];
  If[! ListQ[rows] || Length[rows] < 2, Return[<||>]];
  header = First[rows];
  $proofStatusCache = Association@Table[
    With[{row = AssociationThread[header, record]}, row["result_id"] -> row],
    {record, Rest[rows]}];
  $proofStatusCache
];

proofStatusRow[id_String] := Lookup[proofStatusRegistry[], id, <|
  "machine_status" -> "BuildFailure",
  "dissertation_proof_status" -> "MissingWrittenProof",
  "written_proof_en" -> "",
  "written_proof_pt_BR" -> "",
  "statement_sha256" -> ""|>];

publicResultMetadata[spec_Association] := Module[
  {row, proofEN, proofPT, hash},
  row = proofStatusRow[spec["ResultID"]];
  hash = statementHash[spec];
  proofEN = Lookup[row, "written_proof_en", ""];
  proofPT = Lookup[row, "written_proof_pt_BR", ""];
  <|
    "ResultRegistryID" -> spec["ResultID"],
    "StatementSHA256" -> hash,
    "NormativeSourceAnchor" -> "res:" <> spec["ResultID"],
    "ProofFileEN" -> proofEN,
    "ProofFilePTBR" -> proofPT,
    "ProofLabel" -> "proof:" <> spec["ResultID"],
    "DissertationProofStatus" -> Lookup[row,
      "dissertation_proof_status", "MissingWrittenProof"],
    "StatementHashMatched" -> TrueQ[Lookup[row, "statement_sha256", ""] === hash],
    "WrittenProofFilesPresent" -> TrueQ[StringQ[$packageRoot] &&
      proofEN =!= "" && proofPT =!= "" &&
      FileExistsQ[FileNameJoin[{$packageRoot, proofEN}]] &&
      FileExistsQ[FileNameJoin[{$packageRoot, proofPT}]]]
  |>
];

publicCatalogRow[spec_Association] := Join[
  KeyDrop[spec, {"ProofGoals"}] /. {
    HoldComplete[value_] :> inputFormString[HoldComplete[value]]
  }, publicResultMetadata[spec]];

statusCompleteQ[status_String] := MemberQ[$mandatoryPassStatuses, status];
validLimitQ[value_] := IntegerQ[value] && value > 0;
formatSeconds[value_] := ToString[NumberForm[N[value], {Infinity, 4}], OutputForm];

reportDisclaimer =
  "This artifact verifies the encoded proof goals under their printed assumptions. It does not establish literature priority or empirical truth, and it does not guarantee that the encoding exhausts the dissertation statement.";

sourceIdentity[] := <|
  "PackageTitle" -> $packageTitle,
  "PackageVersion" -> $packageVersion,
  "SourceFile" -> If[StringQ[$packageSourcePath],
    FileNameTake[$packageSourcePath], Missing["SourcePathUnavailable"]],
  "SourceSHA256" -> $packageSourceHash
|>;

executionIdentity[mode_String, timeLimit_, memoryLimit_] := <|
  "WolframVersion" -> $Version,
  "WolframVersionNumber" -> $VersionNumber,
  "WolframReleaseNumber" -> $ReleaseNumber,
  "SystemID" -> $SystemID,
  "OperatingSystem" -> $OperatingSystem,
  "ProcessorType" -> $ProcessorType,
  "Timestamp" -> DateString[Now,
    {"ISODate", "T", "Time", "TimeZoneName"}],
  "Mode" -> mode,
  "PerResultTimeLimitSeconds" -> timeLimit,
  "PerResultMemoryLimitBytes" -> memoryLimit,
  "RandomSeed" -> $randomSeed
|>;

captureEvaluation[held_HoldComplete, timeLimit_, memoryLimit_] := Module[
  {started, value, messages, elapsed, outcome},
  started = AbsoluteTime[];
  Block[{$MessageList = {}},
    value = TimeConstrained[
      MemoryConstrained[ReleaseHold[held], memoryLimit, $Failed],
      timeLimit,
      $Aborted
    ];
    messages = $MessageList;
  ];
  elapsed = AbsoluteTime[] - started;
  outcome = Which[
    value === $Aborted, "TimedOut",
    value === $Failed, "MemoryOrEvaluationFailure",
    MatchQ[value, _ConditionalExpression], "Conditional",
    ! FreeQ[value, GeneratedParameters | C[_Integer]], "FreeParametersRemain",
    True, "Evaluated"
  ];
  <|"Value" -> value, "Messages" -> messages,
    "ElapsedSeconds" -> elapsed, "Outcome" -> outcome|>
];

runProofGoal[proofGoal_Association, timeLimit_, memoryLimit_] := Module[
  {evaluation, expected, comparison, test, testReport, success, declaredClass,
   status, actual},
  evaluation = captureEvaluation[proofGoal["Expression"], timeLimit, memoryLimit];
  actual = evaluation["Value"];
  expected = ReleaseHold[proofGoal["Expected"]];
  comparison = canonicalAnswer[actual] === canonicalAnswer[expected];
  test = VerificationTest[comparison, True,
    TestID -> proofGoal["ProofGoalID"], SameTest -> SameQ];
  testReport = TestReport[{test}];
  success = TrueQ[testReport["TestsSucceededCount"] === 1 &&
    testReport["TestsFailedCount"] === 0];
  declaredClass = proofGoal["Classification"];
  status = Which[
    evaluation["Outcome"] === "TimedOut", "BuildFailure",
    evaluation["Outcome"] =!= "Evaluated", "BuildFailure",
    success && MemberQ[$mandatoryPassStatuses, declaredClass], declaredClass,
    success && declaredClass === "SupplementaryNumericalPass", declaredClass,
    True, "BuildFailure"
  ];
  <|
    "ProofGoalID" -> proofGoal["ProofGoalID"],
    "Title" -> proofGoal["Title"],
    "Classification" -> declaredClass,
    "Mandatory" -> proofGoal["Mandatory"],
    "ProofMethod" -> proofGoal["ProofMethod"],
    "Note" -> proofGoal["Note"],
    "Status" -> status,
    "ExactResult" -> actual,
    "Expected" -> expected,
    "Messages" -> evaluation["Messages"],
    "ElapsedSeconds" -> evaluation["ElapsedSeconds"]
  |>
];

combineResultStatus[proofGoalResults_List, defaultClass_String] := Module[
  {mandatory = Select[proofGoalResults, TrueQ[#Mandatory] &], statuses},
  statuses = Lookup[mandatory, "Status", {}];
  Which[
    MemberQ[statuses, "BuildFailure"], "BuildFailure",
    statuses === {}, "BuildFailure",
    AllTrue[statuses, statusCompleteQ] && MemberQ[statuses, "ReductionProofPass"],
      "ReductionProofPass",
    AllTrue[statuses, statusCompleteQ] && MemberQ[statuses, "ExhaustiveFinitePass"],
      "ExhaustiveFinitePass",
    AllTrue[statuses, statusCompleteQ] && MemberQ[statuses, "ExactConstructivePass"],
      "ExactConstructivePass",
    AllTrue[statuses, statusCompleteQ] && MemberQ[statuses, "ExactSymbolicPass"],
      "ExactSymbolicPass",
    True, "BuildFailure"
  ]
];

summarizeProofGoals[results_List] := Counts[Lookup[results, "Status", {}]];
mandatoryResultCompleteQ[result_Association] :=
  ! TrueQ[result["Mandatory"]] || statusCompleteQ[result["Status"]];
failedResultQ[result_Association] := ! mandatoryResultCompleteQ[result];

normalizeMode[mode_] := If[
  MemberQ[{"core", "full", "stress", "machine-strict",
    "dissertation-release", "diagnostics"}, mode],
  mode, Failure["InvalidMode", <|"Message" ->
    "Mode must be machine-strict, dissertation-release, diagnostics, core, full, or stress."|>]];

(* Exact finite-set, relation, partition, and map helpers *)

ClearAll[
  duplicateFreeFiniteListQ, validFiniteDomainQ, totalMapQ, partialMapQ,
  mapValue, mapImage, mapKernel, mapCollisions, equivalenceRelationQ,
  equivalenceClasses, partitionQ, relationSaturatedQ, reachableVertices,
  reachableImage, composeMaps, injectiveMapQ, leftInverseOnImage,
  inducedOrbitMap, orbitCollisionSet, bellProduct, totalizePartialValue,
  directObservationPartition, contextualObservationPartition,
  validManySortedStructureQ, strongCongruenceQ, quotientStateCount,
  queryFactorsThroughQ, addedConsumerPrice, firstLossIndex, jointQueryKernel,
  consumerRedundancyClosure, collisionPairs,
  allPartitions, allEquivalenceRelations
];

duplicateFreeFiniteListQ[list_] := ListQ[list] && DuplicateFreeQ[list];
validFiniteDomainQ[list_] := duplicateFreeFiniteListQ[list];

totalMapQ[domain_List, codomain_List, map_Association] :=
  validFiniteDomainQ[domain] && validFiniteDomainQ[codomain] &&
  Sort[Keys[map]] === Sort[domain] && SubsetQ[codomain, Values[map]];

partialMapQ[domain_List, codomain_List, map_Association] :=
  validFiniteDomainQ[domain] && validFiniteDomainQ[codomain] &&
  SubsetQ[domain, Keys[map]] && SubsetQ[codomain, Values[map]];

mapValue[map_Association, key_] := Lookup[map, Key[key], Missing["Undefined", key]];
mapImage[domain_List, map_Association] := DeleteDuplicates[mapValue[map, #] & /@ domain];
mapKernel[domain_List, map_Association] := Select[Tuples[domain, 2],
  mapValue[map, #[[1]]] === mapValue[map, #[[2]]] &];
mapCollisions[domain_List, map_Association] := Select[Subsets[domain, {2}],
  mapValue[map, #[[1]]] === mapValue[map, #[[2]]] &];
injectiveMapQ[domain_List, map_Association] := mapCollisions[domain, map] === {};

composeMaps[first_Association, second_Association, domain_List] := Association[
  Table[element -> mapValue[second, mapValue[first, element]], {element, domain}]
];

leftInverseOnImage[domain_List, map_Association] /; injectiveMapQ[domain, map] :=
  Association[Reverse /@ Normal[KeyTake[map, domain]]];
leftInverseOnImage[___] := Failure["NotInjective", <||>];

equivalenceRelationQ[domain_List, relation_List] := Module[{pairs},
  pairs = DeleteDuplicates[relation];
  SubsetQ[Tuples[domain, 2], pairs] &&
  SubsetQ[pairs, ({#, #} & /@ domain)] &&
  AllTrue[pairs, MemberQ[pairs, Reverse[#]] &] &&
  AllTrue[Select[Tuples[domain, 3],
    MemberQ[pairs, #[[{1, 2}]]] && MemberQ[pairs, #[[{2, 3}]]] &],
    MemberQ[pairs, #[[{1, 3}]]] &]
];

equivalenceClasses[domain_List, relation_List] := DeleteDuplicates[
  Sort /@ Map[Function[outer,
    Select[domain, Function[inner, MemberQ[relation, {outer, inner}]]]], domain]
];

partitionQ[domain_List, blocks_List] := If[domain === {}, blocks === {},
  blocks =!= {} &&
    AllTrue[blocks, ListQ[#] && # =!= {} && DuplicateFreeQ[#] &] &&
    Sort[Flatten[blocks]] === Sort[domain] &&
    Total[Length /@ blocks] === Length[domain]
];

relationSaturatedQ[relation_List, classes_List] := Module[{classOf},
  classOf[value_] := FirstCase[classes, block_ /; MemberQ[block, value] :> block,
    Missing["Class"]];
  AllTrue[Tuples[Flatten[classes], 2],
    Function[pair,
      With[{leftClass = classOf[pair[[1]]], rightClass = classOf[pair[[2]]]},
        SameQ @@ (MemberQ[relation, #] & /@ Tuples[{leftClass, rightClass}])
      ]
    ]
  ]
];

reachableVertices[initial_List, edges_List] := FixedPoint[
  Union[#, Cases[edges, {from_, to_} /; MemberQ[#, from] :> to]] &,
  DeleteDuplicates[initial]
];
reachableImage[initial_List, maps_List] := Fold[
  DeleteDuplicates[mapValue[#2, #] & /@ #1] &, initial, maps];

inducedOrbitMap[sourceOrbits_List, targetOrbits_List, map_Association] := Association[
  Table[
    sourceOrbit -> FirstCase[targetOrbits,
      targetOrbit_ /; MemberQ[targetOrbit, mapValue[map, First[sourceOrbit]]] :> targetOrbit,
      Missing["TargetOrbit"]],
    {sourceOrbit, sourceOrbits}
  ]
];

orbitCollisionSet[orbitMap_Association] := Select[Subsets[Keys[orbitMap], {2}],
  mapValue[orbitMap, #[[1]]] === mapValue[orbitMap, #[[2]]] &];

bellProduct[sortSizes_List] := Times @@ (BellB /@ sortSizes);

totalizePartialValue[map_Association, element_] := If[KeyExistsQ[map, element],
  {"Defined", map[element]}, {"ConsumerUndefined"}];

directObservationPartition[domain_List, consumers_List] := GatherBy[domain,
  Function[element, totalizePartialValue[#, element] & /@ consumers]];

contextualObservationPartition[domain_List, consumers_List, contexts_List] :=
  GatherBy[domain, Function[element,
    Flatten[Table[
      With[{contextValue = mapValue[context, element]},
        If[MissingQ[contextValue], {"ContextUndefined"},
          totalizePartialValue[consumer, contextValue]]],
      {context, contexts}, {consumer, consumers}], 1]
  ]];

validManySortedStructureQ[structure_Association] := Module[
  {carriers, operations, validCarriers},
  carriers = Lookup[structure, "Carriers", <||>];
  operations = Lookup[structure, "Operations", {}];
  validCarriers = AssociationQ[carriers] && AllTrue[Values[carriers], validFiniteDomainQ];
  validCarriers && AllTrue[operations, Function[operation,
    KeyExistsQ[operation, "InputSorts"] && KeyExistsQ[operation, "OutputSort"] &&
    KeyExistsQ[operation, "Table"] &&
    SubsetQ[Keys[carriers], operation["InputSorts"]] &&
    KeyExistsQ[carriers, operation["OutputSort"]]
  ]]
];

strongCongruenceQ[domain_List, operation_Association, classes_List] := Module[
  {classIndex, tuples, definedness, outputs},
  If[! partitionQ[domain, classes], Return[False]];
  classIndex[value_] := FirstPosition[classes, block_ /; MemberQ[block, value],
    Missing["Class"]];
  tuples = Tuples[domain, Lookup[operation, "Arity", 1]];
  AllTrue[GatherBy[tuples, classIndex /@ # &], Function[group,
    definedness = KeyExistsQ[operation["Table"], #] & /@ group;
    If[! SameQ @@ definedness, False,
      If[! First[definedness], True,
        outputs = operation["Table"] /@ group;
        SameQ @@ (classIndex /@ outputs)
      ]
    ]
  ]]
];

quotientStateCount[partition_List] := Length[partition];
queryFactorsThroughQ[domain_List, reduction_Association, query_Association] :=
  AllTrue[mapKernel[domain, reduction],
    mapValue[query, #[[1]]] === mapValue[query, #[[2]]] &];

addedConsumerPrice[domain_List, consumers_List, newConsumer_Association] :=
  Length[directObservationPartition[domain, Append[consumers, newConsumer]]] -
  Length[directObservationPartition[domain, consumers]];

jointQueryKernel[domain_List, consumers_List] := If[consumers === {},
  Tuples[domain, 2], Apply[Intersection, mapKernel[domain, #] & /@ consumers]];

consumerRedundancyClosure[domain_List, universe_List, selected_List] := Module[
  {selectedKernel = jointQueryKernel[domain, universe[[selected]]]},
  Select[Range[Length[universe]],
    SubsetQ[mapKernel[domain, universe[[#]]], selectedKernel] &]
];

collisionPairs[domain_List, map_Association] := Sort[mapCollisions[domain, map]];

firstLossIndex[domain_List, maps_List, query_Association] := Module[
  {identity, prefixes, position},
  identity = AssociationThread[domain, domain];
  prefixes = Rest@FoldList[composeMaps[#1, #2, domain] &, identity, maps];
  position = FirstPosition[
    queryFactorsThroughQ[domain, #, query] & /@ prefixes,
    False,
    Missing["NoLoss"]
  ];
  If[MissingQ[position], position, First[position]]
];

allPartitions[{}] := {{}};
allPartitions[list_List] := Module[{element = First[list], smaller},
  smaller = allPartitions[Rest[list]];
  DeleteDuplicates@Flatten[
    Function[partition,
      Join[
        {Prepend[partition, {element}]},
        Table[
          ReplacePart[partition,
            index -> Prepend[partition[[index]], element]],
          {index, Length[partition]}
        ]
      ]
    ] /@ smaller,
    1
  ]
];

allEquivalenceRelations[domain_List] := Flatten[
  Function[blocks, Flatten[Tuples[#, 2] & /@ blocks, 1]] /@ allPartitions[domain], 0];

(* Finite evaluator and analysis-contract implementations *)

ClearAll[
  strictOTEvaluate, harmonicGrammarEvaluate, maxEntCandidateLaw,
  maxEntConsequenceLaw, structuralNonterminationQ,
  validFormalContractQ, externalScientificStatusQ, preservationClassifier,
  validMatchedRowsQ, validAnswerTransportQ, exactAnswerQ, answerTypeTag,
  registeredQueryTypeQ, registeredLayerQ, registeredEvaluatorQ,
  validPresentationActionQ, attachScientificStatus,
  qConservativeResult, qNonconservativeResult, notEvaluatedResult,
  finiteTerminationMeasure, validateContractFormation, validateComparison,
  validateEvaluator, validateLayerPresentation, executeFiniteComparison
];

strictOTEvaluate[candidates_List, violationRows_Association, ranking_List] := Module[
  {keys, orderedRows, winnerRows, preorder, bestRow},
  keys = candidates;
  orderedRows = AssociationMap[violationRows[#][[ranking]] &, keys];
  preorder = SortBy[keys, orderedRows];
  bestRow = orderedRows[First[preorder]];
  winnerRows = Select[keys, orderedRows[#] === bestRow &];
  <|"Support" -> candidates, "WinnerSet" -> winnerRows,
    "Preorder" -> preorder, "OrderedViolations" -> orderedRows|>
];

harmonicGrammarEvaluate[candidates_List, violationRows_Association,
    weights_List] := Module[{scores, minimum},
  scores = AssociationMap[weights.violationRows[#] &, candidates];
  minimum = Min[Values[scores]];
  <|"Support" -> candidates,
    "Scores" -> scores,
    "WinnerSet" -> Keys@Select[scores, # === minimum &],
    "PairwiseDifferences" -> Association@Table[
      {left, right} -> (scores[left] - scores[right]),
      {left, candidates}, {right, candidates}]
  |>
];

maxEntCandidateLaw[candidates_List, energies_Association, baseMasses_Association,
    temperature_] := Module[{masses, normalizer},
  masses = AssociationMap[baseMasses[#] Exp[-energies[#]/temperature] &, candidates];
  normalizer = Total[Values[masses]];
  AssociationMap[Together[masses[#]/normalizer] &, candidates]
];

maxEntConsequenceLaw[candidateLaw_Association, consequenceMap_Association] :=
  Merge[KeyValueMap[consequenceMap[#1] -> #2 &, candidateLaw], Total];

structuralNonterminationQ[initial_List, edges_List, stopStates_List] := Module[
  {nonstopEdges, reachable},
  nonstopEdges = Cases[edges, {from_, _, to_} /;
    ! MemberQ[stopStates, from] && ! MemberQ[stopStates, to] :> {from, to}];
  reachable = reachableVertices[initial, nonstopEdges];
  AnyTrue[reachable, Function[vertex,
    MemberQ[nonstopEdges, {vertex, vertex}] ||
      AnyTrue[DeleteCases[reachable, vertex], Function[other,
        MemberQ[reachableVertices[{vertex}, nonstopEdges], other] &&
          MemberQ[reachableVertices[{other}, nonstopEdges], vertex]]]
  ]]
];

externalScientificStatusQ[status_Association] :=
  Sort[Keys[status]] === Sort[{"roots", "gauge", "anchors", "fit", "freeze",
    "reader", "source", "empirics"}] &&
  AllTrue[Values[status], MemberQ[{"AUDITED FOR THE NAMED SET", "INCOMPLETE",
    "UNSUPPORTED"}, #] &];

registeredQueryTypeQ[value_] := MemberQ[{
  "Nominal", "Relation", "PartialOperation", "Order", "Additive",
  "Probability", "Winner", "Preorder", "Difference", "CandidateLaw",
  "ConsequenceLaw", "Local", "Prefix", "Trace", "Terminal",
  "RankPartition", "Locus", "Product"}, value];

registeredEvaluatorQ[value_] := MemberQ[{
  "StrictOT", "HG", "MaxEnt", "SerialSet", "SerialProbability",
  "WeightedSeries", "Prefix"}, value];

registeredLayerQ[value_] := MemberQ[{
  "Grammar", "Acquisition", "PhoneticRealization", "ObservationAnnotation",
  "ListenerResponse", "CorpusInference"}, value];

validPresentationActionQ[action_] := AssociationQ[action] && Length[action] > 0 &&
  KeyExistsQ[action, "Identity"] && action["Identity"] === Identity;

exactAnswerQ[value_] := FreeQ[value,
  _Missing | _Failure | _Real | Indeterminate | ComplexInfinity |
    DirectedInfinity];

answerTypeTag[value_Association] := "Association";
answerTypeTag[value_List] := "List";
answerTypeTag[value_?NumberQ] := "ExactNumber";
answerTypeTag[value_String] := "Nominal";
answerTypeTag[True | False] := "Boolean";
answerTypeTag[value_Symbol] := "Symbol";
answerTypeTag[value_] := Head[value];

validMatchedRowsQ[domain_List, sourceAnswers_Association,
    targetAnswers_Association, rows_List] := Module[{sourceKeys, targetKeys},
  sourceKeys = Keys[sourceAnswers]; targetKeys = Keys[targetAnswers];
  DuplicateFreeQ[rows] &&
    AllTrue[rows, ListQ[#] && Length[#] === 2 &] &&
    AllTrue[rows, KeyExistsQ[sourceAnswers, #[[1]]] &&
      KeyExistsQ[targetAnswers, #[[2]]] &] &&
    Sort[sourceKeys] === Sort[domain] &&
    (rows === {} ||
      (Sort[DeleteDuplicates[rows[[All, 1]]]] === Sort[domain] &&
       Sort[DeleteDuplicates[rows[[All, 2]]]] === Sort[targetKeys]))
];

validAnswerTransportQ[sourceAnswers_Association, targetAnswers_Association,
    rows_List, transport_Association] := Module[{sourceImage},
  sourceImage = DeleteDuplicates[Values[sourceAnswers]];
  SubsetQ[Keys[transport], sourceImage] &&
    AllTrue[Join[Values[sourceAnswers], Values[targetAnswers], Values[transport]],
      exactAnswerQ] &&
    AllTrue[rows, Function[row,
      With[{source = sourceAnswers[row[[1]]], target = targetAnswers[row[[2]]]},
        answerTypeTag[transport[source]] === answerTypeTag[target]
      ]
    ]]
];

validFormalContractQ[contract_Association] := Module[
  {required, domain, sourceAnswers, targetAnswers, rows, transport},
  required = {"Domain", "SourceAnswers", "TargetAnswers", "MatchedRows",
    "Transport", "QueryType", "Evaluator", "Layer", "PresentationAction",
    "ScientificStatus"};
  If[! SubsetQ[Keys[contract], required], Return[False]];
  domain = contract["Domain"];
  sourceAnswers = contract["SourceAnswers"];
  targetAnswers = contract["TargetAnswers"];
  rows = contract["MatchedRows"];
  transport = contract["Transport"];
  validFiniteDomainQ[domain] && AssociationQ[sourceAnswers] &&
    AssociationQ[targetAnswers] && Length[targetAnswers] > 0 && ListQ[rows] &&
    AssociationQ[transport] && registeredQueryTypeQ[contract["QueryType"]] &&
    registeredEvaluatorQ[contract["Evaluator"]] &&
    registeredLayerQ[contract["Layer"]] &&
    validPresentationActionQ[contract["PresentationAction"]] &&
    externalScientificStatusQ[contract["ScientificStatus"]] &&
    validMatchedRowsQ[domain, sourceAnswers, targetAnswers, rows] &&
    validAnswerTransportQ[sourceAnswers, targetAnswers, rows, transport]
];

qConservativeResult[rows_List] := <|"Class" -> "Q-CONSERVATIVE",
  "Proof" -> rows, "Witnesses" -> {}|>;
qNonconservativeResult[rows_List, witnesses_List] := <|
  "Class" -> "Q-NONCONSERVATIVE", "Proof" -> rows,
  "Witnesses" -> witnesses|>;
notEvaluatedResult[dependencies_List] := <|"Class" -> "NOT EVALUATED",
  "Dependencies" -> DeleteDuplicates[dependencies]|>;

validateContractFormation[contract_Association] := If[validFormalContractQ[contract],
  <|"Status" -> "PASS"|>, <|"Status" -> "FAIL", "Witness" -> "MalformedContract"|>];
validateComparison[contract_Association] := If[contract["MatchedRows"] === {},
  <|"Status" -> "FAIL", "Witness" -> "QUERY SEMANTICS NOT COMPARABLE"|>,
  <|"Status" -> "PASS"|>];
validateEvaluator[contract_Association] := If[
  registeredEvaluatorQ[contract["Evaluator"]],
  <|"Status" -> "PASS"|>, <|"Status" -> "FAIL", "Witness" -> "EVALUATOR MISMATCH"|>];
validateLayerPresentation[contract_Association] := If[
  registeredLayerQ[contract["Layer"]] &&
    validPresentationActionQ[contract["PresentationAction"]],
  <|"Status" -> "PASS"|>,
  <|"Status" -> "FAIL", "Witness" -> "PRESENTATION DEPENDENT"|>];

executeFiniteComparison[contract_Association] := Module[{rows, compared, witnesses},
  rows = contract["MatchedRows"];
  compared = Table[
    With[{source = contract["SourceAnswers"][row[[1]]],
      target = contract["TargetAnswers"][row[[2]]]},
      <|"Row" -> row,
        "TransportedSource" -> contract["Transport"][source],
        "Target" -> target,
        "Equal" -> SameQ[
          canonicalAnswer[contract["Transport"][source]],
          canonicalAnswer[target]]|>
    ], {row, rows}];
  witnesses = Select[compared, ! TrueQ[#Equal] &];
  If[witnesses === {}, qConservativeResult[compared],
    qNonconservativeResult[compared, witnesses]]
];

attachScientificStatus[result_Association, contract_Association] := Join[result,
  <|"ScientificStatus" -> Lookup[contract, "ScientificStatus",
    Missing["ScientificStatusUnavailable"]]|>];

preservationClassifier[contract_Association] := Module[
  {formation, comparison, evaluator, layer, result},
  formation = validateContractFormation[contract];
  If[formation["Status"] =!= "PASS",
    Return[attachScientificStatus[notEvaluatedResult[{formation}], contract]]];
  comparison = validateComparison[contract];
  evaluator = validateEvaluator[contract];
  layer = validateLayerPresentation[contract];
  If[! AllTrue[{comparison, evaluator, layer}, #["Status"] === "PASS" &],
    Return[attachScientificStatus[
      notEvaluatedResult[Select[{comparison, evaluator, layer},
        #["Status"] =!= "PASS" &]], contract]]];
  result = executeFiniteComparison[contract];
  attachScientificStatus[result, contract]
];

finiteTerminationMeasure[contract_Association] := <|
  "DomainSize" -> Length[Lookup[contract, "Domain", {}]],
  "MatchedRowCount" -> Length[Lookup[contract, "MatchedRows", {}]],
  "SourceTableSize" -> Length[Lookup[contract, "SourceAnswers", <||>]],
  "TargetTableSize" -> Length[Lookup[contract, "TargetAnswers", <||>]]
|>;

ClearAll[canonicalAnswer];
canonicalAnswer[value_Association] := Sort[
  (First[#] -> canonicalAnswer[Last[#]]) & /@ Normal[value]];
canonicalAnswer[value_List] := canonicalAnswer /@ value;
canonicalAnswer[value_] := value;

(* Exact continuous-HG, response, and finite-MaxEnt helpers *)

ClearAll[
  positivePart, powerConjugate, inactiveDecrease, supportPowerSum,
  supportIndexExact, directionalHGObjective, monotoneDecreaseObjective,
  quadraticSupportIndex, quadraticUnsaturatedDecreases,
  quadraticSaturatedDecreases, quadraticProfile, exactProfileFromDecreases,
  normalizedPhaseDecreases, normalizedPhaseProfile, poweredGapConstant,
  latticeAllBackStatus, persistencePhaseBounds, phaseUpperBoundary,
  supportBirthCoefficient, mccollumCompiler, compilerLabelCount,
  pathFluxDeformation, pathFluxPotential, contactPhaseMinimumSlices,
  polynomialCoefficientAssociation, maxEntRelativePolynomial,
  namedProbabilityFromActivity, normalizedLaw, responseEnvelope,
  logOddsPotential, projectedMass, multiplicitySensitiveRows,
  exactBellNumber, exactConvexHullInterval
];

positivePart[value_] := Max[value, 0];
powerConjugate[exponentP_] := 1/(exponentP - 1);

inactiveDecrease[harmonyWeight_, markednessWeight_, exponentP_, rank_] :=
  (markednessWeight rank/(exponentP harmonyWeight))^powerConjugate[exponentP];

supportPowerSum[harmonyWeight_, markednessWeight_, exponentP_,
    index_Integer?Positive] :=
  Times[
    (markednessWeight/(exponentP harmonyWeight))^powerConjugate[exponentP],
    Sum[rank^powerConjugate[exponentP], {rank, 1, index}]
  ];

supportIndexExact[harmonyWeight_, markednessWeight_, exponentP_] /;
    TrueQ[harmonyWeight > 0 && markednessWeight > 0 && exponentP > 1] :=
  Module[{index = 1},
    While[! TrueQ[supportPowerSum[harmonyWeight, markednessWeight,
        exponentP, index] >= 1], index++];
    index
  ];

directionalHGObjective[coordinates_List, harmonyWeight_, markednessWeight_,
    exponentP_] := Module[{previous},
  previous = Most[Prepend[coordinates, 1]];
  harmonyWeight Total[(positivePart /@ (previous - coordinates))^exponentP] +
    markednessWeight Total[coordinates]
];

monotoneDecreaseObjective[decreases_List, harmonyWeight_, markednessWeight_,
    exponentP_] := harmonyWeight Total[decreases^exponentP] -
  markednessWeight Range[Length[decreases], 1, -1].decreases +
  markednessWeight Length[decreases];

quadraticSupportIndex[harmonyWeight_, markednessWeight_] /;
    TrueQ[harmonyWeight > 0 && markednessWeight > 0] :=
  Ceiling[(Sqrt[1 + 16 harmonyWeight/markednessWeight] - 1)/2];

quadraticUnsaturatedDecreases[harmonyWeight_, markednessWeight_,
    horizon_Integer?Positive] :=
  (markednessWeight/(2 harmonyWeight)) Range[horizon, 1, -1];

quadraticSaturatedDecreases[harmonyWeight_, markednessWeight_] := Module[
  {supportIndex = quadraticSupportIndex[harmonyWeight, markednessWeight],
   scale = markednessWeight/(2 harmonyWeight)},
  Table[1/supportIndex + scale ((supportIndex + 1)/2 - index),
    {index, supportIndex}]
];

exactProfileFromDecreases[decreases_List] :=
  Prepend[1 - Accumulate[decreases], 1];

quadraticProfile[harmonyWeight_, markednessWeight_,
    horizon_Integer?Positive] := Module[{supportIndex, decreases},
  supportIndex = quadraticSupportIndex[harmonyWeight, markednessWeight];
  decreases = If[horizon < supportIndex,
    quadraticUnsaturatedDecreases[harmonyWeight, markednessWeight, horizon],
    PadRight[quadraticSaturatedDecreases[harmonyWeight, markednessWeight], horizon]];
  exactProfileFromDecreases[decreases]
];

normalizedPhaseDecreases[exponentP_, supportIndex_Integer?Positive, tau_] :=
  Module[{q = powerConjugate[exponentP], denominator},
    denominator = Sum[(rank - tau)^q, {rank, 1, supportIndex}];
    Table[(supportIndex - index + 1 - tau)^q/denominator,
      {index, supportIndex}]
  ];

normalizedPhaseProfile[exponentP_, supportIndex_Integer?Positive, tau_] :=
  exactProfileFromDecreases[
    normalizedPhaseDecreases[exponentP, supportIndex, tau]];

poweredGapConstant[harmonyWeight_, markednessWeight_, exponentP_] :=
  markednessWeight/(exponentP harmonyWeight);

latticeAllBackStatus[harmonyWeight_, markednessWeight_, exponentP_,
    horizon_, step_] := Which[
  harmonyWeight step^(exponentP - 1) > horizon markednessWeight, "UniqueWinner",
  harmonyWeight step^(exponentP - 1) == horizon markednessWeight, "BoundaryTie",
  True, "NotWinner"
];

persistencePhaseBounds[exponentP_, supportIndex_Integer?Positive] := Module[
  {q = powerConjugate[exponentP], lower, upper},
  lower = If[supportIndex == 1, 0,
    Sum[rank^q, {rank, 1, supportIndex - 1}]^(exponentP - 1)/exponentP];
  upper = Sum[rank^q, {rank, 1, supportIndex}]^(exponentP - 1)/exponentP;
  {lower, upper}
];

phaseUpperBoundary[exponentP_, supportIndex_Integer?Positive] :=
  Last[persistencePhaseBounds[exponentP, supportIndex]];

supportBirthCoefficient[exponentP_, supportIndex_Integer?Positive] := Module[
  {q = powerConjugate[exponentP], activeSum, derivativeSum},
  activeSum = Sum[rank^q, {rank, 1, supportIndex}];
  derivativeSum = Sum[rank^(q - 1), {rank, 1, supportIndex}];
  Piecewise[{
    {(1/activeSum) (exponentP activeSum^(2 - exponentP)/derivativeSum)^q,
      1 < exponentP < 2},
    {2/((supportIndex + 1) activeSum), exponentP == 2},
    {q exponentP activeSum^(1 - exponentP), exponentP > 2}
  }]
];

mccollumCompiler[harmonyWeight_, markednessWeight_] /;
    TrueQ[harmonyWeight > 0 && markednessWeight > 0] := Module[
  {supportIndex, profiles},
  supportIndex = quadraticSupportIndex[harmonyWeight, markednessWeight];
  profiles = Table[quadraticProfile[harmonyWeight, markednessWeight, horizon],
    {horizon, 1, supportIndex}];
  <|"SupportIndex" -> supportIndex, "Profiles" -> profiles,
    "Labels" -> Join[{"Trigger"}, Flatten[
      Table[{horizon, position}, {horizon, supportIndex},
        {position, horizon}], 1]]|>
];

compilerLabelCount[compiler_Association] := Length[compiler["Labels"]];

pathFluxDeformation[flux_, period_, epsilon_] :=
  flux + epsilon period/(2 Pi) Sin[2 Pi flux/period];

pathFluxPotential[drop_, curvature_, period_, epsilon_] :=
  curvature drop^2/2 + Times[
    epsilon period^2/(4 Pi^2 curvature),
    1 - Cos[2 Pi curvature drop/period]
  ];

contactPhaseMinimumSlices[contactMultiplicities_List,
    reversals_Integer?NonNegative] := 1 + Total[contactMultiplicities] + reversals;

polynomialCoefficientAssociation[polynomial_, variables_List] :=
  Association[CoefficientRules[Expand[polynomial], variables]];

maxEntRelativePolynomial[namedRowA_List, alternativesA_List,
    namedRowB_List, alternativesB_List, variables_List] := Module[
  {relativeA, relativeB, exponents, shift, laurent},
  relativeA = alternativesA - ConstantArray[namedRowA, Length[alternativesA]];
  relativeB = alternativesB - ConstantArray[namedRowB, Length[alternativesB]];
  laurent = Expand[
    Total[(Times @@ (variables^#)) & /@ relativeA] -
    Total[(Times @@ (variables^#)) & /@ relativeB]];
  exponents = Join[relativeA, relativeB];
  shift = If[exponents === {}, ConstantArray[0, Length[variables]],
    Map[Max[0, -Min[#]] &, Transpose[exponents]]];
  Expand[laurent Times @@ (variables^shift)]
];

namedProbabilityFromActivity[alternativeExponents_List, activity_] :=
  Together[1/(1 + Total[activity^alternativeExponents])];

normalizedLaw[masses_List] := Together[masses/Total[masses]];
exactConvexHullInterval[values_List] := {Min[values], Max[values]};
responseEnvelope[rowsA_List, rowsB_List] :=
  exactConvexHullInterval[Flatten[Outer[Subtract, rowsB, rowsA]]];

projectedMass[rows_List, masses_List, direction_List, parameter_] :=
  Total[MapThread[#1 Exp[-parameter direction.#2] &, {masses, rows}]];

logOddsPotential[rowsA_List, massesA_List, rowsB_List, massesB_List,
    direction_List, parameter_] := Together[Log[
  projectedMass[rowsA, massesA, direction, parameter]/
  projectedMass[rowsB, massesB, direction, parameter]]];

multiplicitySensitiveRows[rows_List] := Sort[Normal[Counts[rows]]];
exactBellNumber[size_Integer?NonNegative] := BellB[size];

(* CALC-F1 and the fifteen finite-calculus regressions *)

ClearAll[
  auditedScientificStatus, incompleteScientificStatus, finiteBaseContract,
  buildCalculusSpecifications, buildFiniteSpecifications
];

auditedScientificStatus[] := AssociationThread[
  {"roots", "gauge", "anchors", "fit", "freeze", "reader", "source", "empirics"},
  ConstantArray["AUDITED FOR THE NAMED SET", 8]
];

incompleteScientificStatus[] := ReplacePart[auditedScientificStatus[],
  "source" -> "INCOMPLETE"];

finiteBaseContract[] := <|
  "Domain" -> {"s1", "s2"},
  "SourceAnswers" -> <|"s1" -> "A", "s2" -> "B"|>,
  "TargetAnswers" -> <|"t1" -> "A", "t2" -> "B"|>,
  "MatchedRows" -> {{"s1", "t1"}, {"s2", "t2"}},
  "Transport" -> <|"A" -> "A", "B" -> "B"|>,
  "QueryType" -> "Winner",
  "Evaluator" -> "StrictOT",
  "Layer" -> "Grammar",
  "PresentationAction" -> <|"Identity" -> Identity|>,
  "ScientificStatus" -> auditedScientificStatus[]
|>;

(*
CALC-F1 - Qualified finite decision theorem
Statement source: normative finite-calculus specification, Theorem F1.
Assumptions: a fully specified finite contract and a decidable registered
query, with every called subprocedure exact and terminating.
Machine-checked proof goals: formation, comparison, evaluator and layer
admission; independent source and target evaluation; three-way progress;
complete mismatch construction; and explicit finite loop measures.
Verification method: exact constructive proofs and exhaustive finite
regressions.  The result is contract-relative and does not establish external
scientific completeness.
*)
buildCalculusSpecifications[] := Module[{baseSource},
  baseSource = "Finite calculus formal specification, Sections 2-13";
  {
    makeResultSpecification[
      "CALC-F1", "Qualified finite decision theorem", "CALC",
      "New phonological formal theorem", True,
      "Every admitted finite request terminates and returns exactly one of Q-CONSERVATIVE, Q-NONCONSERVATIVE, or NOT EVALUATED, soundly and completely relative to its contract.",
      "Finite duplicate-free domains; exact terminating subprocedures; complete matched rows; typed transport, evaluator, layer, and presentation fields.",
      baseSource,
      "Fully specified finite analysis contracts and decidable registered queries.",
      "No external scientific completeness, tractability, continuum decision, or cognitive ontology claim.",
      "Constructive classifier proof and bounded finite enumeration.",
      {
        makeProofGoal["CALC-F1.ADMISSION.01", "Formation and admission fields",
          "ExactConstructivePass",
          Module[{contract = finiteBaseContract[]},
            And[
              validateContractFormation[contract]["Status"] === "PASS",
              validateComparison[contract]["Status"] === "PASS",
              validateEvaluator[contract]["Status"] === "PASS",
              validateLayerPresentation[contract]["Status"] === "PASS"
            ]], True, "Independent exact field validators"],
        makeProofGoal["CALC-F1.PROGRESS.02", "Three-way progress",
          "ExhaustiveFinitePass",
          Module[{good, changed, refused, classes},
            good = finiteBaseContract[];
            changed = ReplacePart[good, "TargetAnswers" -> <|"t1" -> "A", "t2" -> "C"|>];
            refused = ReplacePart[good, "MatchedRows" -> {}];
            classes = preservationClassifier /@ {good, changed, refused};
            Lookup[classes, "Class"]],
          {"Q-CONSERVATIVE", "Q-NONCONSERVATIVE", "NOT EVALUATED"},
          "Exhaustive declared outcome partition over three exact contracts"],
        makeProofGoal["CALC-F1.WITNESS.03", "Complete mismatch witness",
          "ExactConstructivePass",
          Module[{contract, result},
            contract = ReplacePart[finiteBaseContract[],
              "TargetAnswers" -> <|"t1" -> "A", "t2" -> "C"|>];
            result = preservationClassifier[contract];
            {result["Class"], Lookup[First[result["Witnesses"]], "Row"],
              Lookup[First[result["Witnesses"]], "Equal"]}],
          {"Q-NONCONSERVATIVE", {"s2", "t2"}, False},
          "Independent target value and complete changed row"],
        makeProofGoal["CALC-F1.TERMINATION.04", "Finite structural measure",
          "ExactConstructivePass",
          finiteTerminationMeasure[finiteBaseContract[]],
          <|"DomainSize" -> 2, "MatchedRowCount" -> 2,
            "SourceTableSize" -> 2, "TargetTableSize" -> 2|>,
          "Explicit bounded enumeration measures"],
        makeProofGoal["CALC-F1.REFUSALS.05",
          "Malformed-contract refusal matrix", "ExhaustiveFinitePass",
          Module[{base = finiteBaseContract[], malformed, results},
            malformed = {
              ReplacePart[base, "SourceAnswers" -> <||>],
              ReplacePart[base, "Transport" -> <||>],
              ReplacePart[base, "QueryType" -> "UnregisteredNonsense"],
              ReplacePart[base, "PresentationAction" -> <||>],
              ReplacePart[base, "Layer" -> "UnregisteredLayer"],
              ReplacePart[base, "MatchedRows" -> {{"s1", "t1"}}],
              ReplacePart[base, "Transport" -> <|"A" -> 1, "B" -> 2|>]
            };
            results = preservationClassifier /@ malformed;
            {Lookup[results, "Class"],
              Lookup[First /@ Lookup[results, "Dependencies"], "Witness"]}],
          {ConstantArray["NOT EVALUATED", 7],
            ConstantArray["MalformedContract", 7]},
          "Missing answers, transport, registration, action, coverage, and type are refused before comparison"]
      }
    ],

    (* CALC-R01 - direct and contextual carriers split. *)
    makeResultSpecification["CALC-R01", "Direct and contextual carriers split", "CALC",
      "Mandatory regression", True,
      "A direct observation kernel may be strictly coarser than the operation-closed contextual carrier.",
      "Finite carrier X={a,b,c}, total query q, total unary operation f, and complete identity/f context image.",
      baseSource <> ", Regression 1", "Fixed finite carrier and retained operation.",
      "Does not identify mental representations or license an incomplete context policy.",
      "Exact finite partition construction.",
      {makeProofGoal["CALC-R01.PARTITION.01", "Three-state split",
        "ExhaustiveFinitePass",
        Module[{domain = {"a", "b", "c"}, q, identity, f, direct, contextual},
          q = <|"a" -> 0, "b" -> 0, "c" -> 1|>;
          identity = AssociationThread[domain, domain];
          f = <|"a" -> "a", "b" -> "c", "c" -> "c"|>;
          direct = Sort[Sort /@ directObservationPartition[domain, {q}]];
          contextual = Sort[Sort /@ contextualObservationPartition[domain, {q}, {identity, f}]];
          {direct, contextual}],
        {{{"c"}, {"a", "b"}}, {{"a"}, {"b"}, {"c"}}},
        "Complete enumeration of three states and two contexts"],
       makeProofGoal["CALC-R01.SORTS.02", "Many-sorted formation guard",
        "ExactConstructivePass",
        Module[{valid, invalid},
          valid = <|"Carriers" -> <|"Segment" -> {"a", "b"},
              "Feature" -> {0, 1}|>,
            "Operations" -> {<|"InputSorts" -> {"Segment"},
              "OutputSort" -> "Feature", "Table" -> <|{"a"} -> 0,
                {"b"} -> 1|>|>}|>;
          invalid = ReplacePart[valid,
            {"Operations", 1, "InputSorts"} -> {"UnregisteredSort"}];
          {validManySortedStructureQ[valid], validManySortedStructureQ[invalid]}],
        {True, False}, "Input and output sorts are checked against the finite carrier registry"],
       makeProofGoal["CALC-R01.PARTIAL.03", "Partial consumer and empty-battery guard",
        "ExhaustiveFinitePass",
        Module[{domain = {"a", "b", "c"}, partial, partialCarrier,
          emptyCarrier, admittedBattery},
          partial = <|"a" -> 0, "b" -> 0|>;
          partialCarrier = Sort[Sort /@ directObservationPartition[domain, {partial}]];
          emptyCarrier = directObservationPartition[domain, {}];
          admittedBattery = {} =!= {};
          {partialCarrier, emptyCarrier, admittedBattery}],
        {{{"c"}, {"a", "b"}}, {{"a", "b", "c"}}, False},
        "Undefinedness is totalized explicitly; an empty battery is visible and fails admission"]}
    ],

    (* CALC-R02 - optimizer coimage specialization. *)
    makeResultSpecification["CALC-R02", "Optimizer coimage specialization", "CALC",
      "Mandatory regression", True,
      "With no operations and one total optimizer consumer, the direct carrier is exactly the optimizer kernel quotient.",
      "One finite sort, identity context only, total optimizer map.",
      baseSource <> ", Regression 2", "Direct-answer carrier only.",
      "No contextual or cross-evaluator preservation follows.",
      "Exact kernel and image enumeration.",
      {makeProofGoal["CALC-R02.COIMAGE.01", "Kernel-image equality",
        "ExhaustiveFinitePass",
        Module[{domain = {1, 2, 3, 4}, optimizer = <|1 -> "A", 2 -> "A", 3 -> "B", 4 -> "C"|>},
          {Length[directObservationPartition[domain, {optimizer}]],
            Length[DeleteDuplicates[Values[optimizer]]],
            Sort[mapKernel[domain, optimizer]]}],
        {3, 3, Sort[{{1, 1}, {1, 2}, {2, 1}, {2, 2}, {3, 3}, {4, 4}}]},
        "Independent kernel pairs and optimizer image"],
       makeProofGoal["CALC-R02.PARTIAL.02", "Partial-consumer coimage",
        "ExhaustiveFinitePass",
        Module[{domain = {1, 2, 3, 4}, optimizer, carrier, totalizedImage},
          optimizer = <|1 -> "A", 2 -> "A"|>;
          carrier = Sort[Sort /@ directObservationPartition[domain, {optimizer}]];
          totalizedImage = DeleteDuplicates[totalizePartialValue[optimizer, #] & /@ domain];
          {carrier, Length[carrier], Length[totalizedImage]}],
        {{{1, 2}, {3, 4}}, 2, 2},
        "Defined A and consumer-undefined are distinct exact direct answers"]}
    ],

    (* CALC-R03 - pair-totality refusal. *)
    makeResultSpecification["CALC-R03", "Feasible world with no licensed pair", "CALC",
      "Mandatory regression", True,
      "A feasible world with no licensed compatible pair is not comparable and never reaches preservation equality.",
      "Well-formed finite contract except for an empty matched-row family.",
      baseSource <> ", Regression 3", "Pair-totality admission.",
      "An empty comparison is not a vacuous conservativity proof.",
      "Exact refusal construction.",
      {makeProofGoal["CALC-R03.REFUSAL.01", "Empty pair family",
        "ExactConstructivePass",
        Module[{result = preservationClassifier[
            ReplacePart[finiteBaseContract[], "MatchedRows" -> {}]]},
          KeyTake[result, {"Class", "Dependencies"}]],
        <|"Class" -> "NOT EVALUATED", "Dependencies" ->
          {<|"Status" -> "FAIL", "Witness" ->
            "QUERY SEMANTICS NOT COMPARABLE"|>}|>,
        "Structured dependency refusal"]}
    ],

    (* CALC-R04 - pair-orbit surjectivity. *)
    makeResultSpecification["CALC-R04", "Pair-orbit surjectivity is load-bearing", "CALC",
      "Mandatory regression", True,
      "A lower compatible-pair orbit omitted by the upper-to-lower pair map blocks safe reduct closure.",
      "Finite upper orbit {A}, lower orbits {B1,B2}, map A->B1.",
      baseSource <> ", Regression 4", "Fixed-index reduct admission.",
      "A commuting square on the image cannot stand for the omitted orbit.",
      "Exact image and missing-orbit calculation.",
      {makeProofGoal["CALC-R04.SURJECTIVITY.01", "Missing lower orbit",
        "ExhaustiveFinitePass",
        Complement[{"B1", "B2"}, Values[<|"A" -> "B1"|>]], {"B2"},
        "Complete finite codomain difference"],
       makeProofGoal["CALC-R04.FRONTIER.02", "Preorder frontier is not image-complete",
        "ExhaustiveFinitePass",
        Module[{lower = {"B1", "B2", "B3"}, strictEdges, frontier, pairMap},
          strictEdges = {{"B3", "B1"}, {"B3", "B2"}};
          frontier = Select[lower,
            Cases[strictEdges, {#, _}] === {} &];
          pairMap = <|"A" -> "B1"|>;
          {Sort[frontier], Complement[frontier, Values[pairMap]]}],
        {{"B1", "B2"}, {"B2"}},
        "The omitted maximal lower pair remains visible under the declared preorder"]}
    ],

    (* CALC-R05 - witness-set naturality. *)
    makeResultSpecification["CALC-R05", "Gauge-swapped shortest witnesses", "CALC",
      "Mandatory regression", True,
      "A presentation involution exchanging equal-length witnesses preserves their complete orbit but neither singleton.",
      "Two witnesses and the swap action.",
      baseSource <> ", Regression 5", "Complete witness sets and orbits.",
      "No canonical singleton selector is inferred.",
      "Exact action on the witness set.",
      {makeProofGoal["CALC-R05.ORBIT.01", "Complete set versus singleton",
        "ExhaustiveFinitePass",
        Module[{swap = <|"w1" -> "w2", "w2" -> "w1"|>, set = {"w1", "w2"}},
          {Sort[mapValue[swap, #] & /@ set] === Sort[set],
            mapValue[swap, "w1"] === "w1", mapValue[swap, "w2"] === "w2"}],
        {True, False, False}, "Finite group action"]}
    ],

    (* CALC-R06 - orbit recovery without raw recovery. *)
    makeResultSpecification["CALC-R06", "Raw collapse without semantic loss", "CALC",
      "Mandatory regression", True,
      "Two raw representatives in one source orbit may collapse while the induced orbit map remains invertible.",
      "Source orbit {a,b}, target orbit {c}, weakening a,b->c.",
      baseSource <> ", Regression 6", "Semantic orbit and representative recovery coordinates.",
      "Raw representative recovery remains unlicensed.",
      "Exact orbit-map and raw-collision enumeration.",
      {makeProofGoal["CALC-R06.ORBITS.01", "Semantic inverse and raw collision",
        "ExhaustiveFinitePass",
        Module[{map = <|"a" -> "c", "b" -> "c"|>, orbitMap},
          orbitMap = inducedOrbitMap[{{"a", "b"}}, {{"c"}}, map];
          {orbitCollisionSet[orbitMap], mapCollisions[{"a", "b"}, map],
            If[orbitCollisionSet[orbitMap] === {}, "SEMANTIC RECOVERY: PASS",
              "SEMANTIC RECOVERY: FAIL"],
            If[injectiveMapQ[{"a", "b"}, map], "REPRESENTATIVE RECOVERY: PASS",
              "REPRESENTATIVE RECOVERY: FAIL"]}],
        {{}, {{"a", "b"}}, "SEMANTIC RECOVERY: PASS",
          "REPRESENTATIVE RECOVERY: FAIL"},
        "Orbit and raw collision sets generate two distinct typed statuses"]}
    ],

    (* CALC-R07 - target image stability before restriction. *)
    makeResultSpecification["CALC-R07", "Target-action escape before restriction", "CALC",
      "Mandatory regression", True,
      "Target-policy arrows leaving the raw image are recorded before the policy is restricted.",
      "Source {a}, target {c,d}, image {c}, arrow c->d.",
      baseSource <> ", Regression 7", "Representative recovery admission.",
      "Restriction may not erase an outbound witness.",
      "Exact outbound-arrow enumeration.",
      {makeProofGoal["CALC-R07.OUTBOUND.01", "Complete outbound set",
        "ExhaustiveFinitePass",
        Select[{{"k", "c", "d"}}, MemberQ[{"c"}, #[[2]]] && ! MemberQ[{"c"}, #[[3]]] &],
        {{"k", "c", "d"}}, "Finite target action policy"]}
    ],

    (* CALC-R08 - typed empty-image statuses. *)
    makeResultSpecification["CALC-R08", "Distinct empty-image statuses", "CALC",
      "Mandatory regression", True,
      "Empty semantic and representative images receive distinct vacuity statuses and no positive recovery inference.",
      "Empty licensed source image.",
      baseSource <> ", Regression 8", "Recovery-status product.",
      "Mathematical injectivity of the empty function is not scientific evidence.",
      "Exact typed status construction.",
      {makeProofGoal["CALC-R08.STATUS.01", "Two typed vacuity labels",
        "ExactConstructivePass",
        Module[{sourceOrbitImage = {}, rawSourceImage = {}, semantic, representative},
          semantic = If[sourceOrbitImage === {},
            "EMPTY LICENSED SOURCE IMAGE: SEMANTIC INVERSE VACUOUS", "RECOVERY TESTED"];
          representative = If[rawSourceImage === {},
            "REPRESENTATIVE INVERSE VACUOUS: EMPTY LICENSED SOURCE IMAGE",
            "RECOVERY TESTED"];
          {semantic, representative}],
        {"EMPTY LICENSED SOURCE IMAGE: SEMANTIC INVERSE VACUOUS",
          "REPRESENTATIVE INVERSE VACUOUS: EMPTY LICENSED SOURCE IMAGE"},
        "Statuses are derived from separate empty semantic-orbit and raw images"]}
    ],

    (* CALC-R09 - disabled empty stopping cannot discard mass. *)
    makeResultSpecification["CALC-R09", "Positive initial stop mass with empty stopping disabled", "CALC",
      "Mandatory regression", True,
      "Disabling the empty stopped word while retaining positive initial stop mass violates total mass unless a typed failure receives it.",
      "Initial stop mass 1/3 and no failure route.",
      baseSource <> ", Regression 9", "Exact stochastic stopped semantics.",
      "No mass is silently renormalized or discarded.",
      "Exact rational mass identity.",
      {makeProofGoal["CALC-R09.MASS.01", "Missing one-third mass",
        "ExactConstructivePass",
        Module[{initialStopMass = 1/3, continuedStoppedLaw, observedMass,
          failureRoute, status},
          continuedStoppedLaw = <|"a" -> 2/3|>;
          observedMass = Total[Values[continuedStoppedLaw]];
          failureRoute = Missing["NoTypedFailureRoute"];
          status = If[observedMass + If[MissingQ[failureRoute], 0,
                initialStopMass] === 1, "PASS", "NOT EVALUATED"];
          <|"ObservedStoppedMass" -> observedMass,
            "UnroutedInitialStopMass" -> initialStopMass,
            "TotalWithNoFailureRoute" -> observedMass,
            "Status" -> status|>],
        <|"ObservedStoppedMass" -> 2/3, "UnroutedInitialStopMass" -> 1/3,
          "TotalWithNoFailureRoute" -> 2/3, "Status" -> "NOT EVALUATED"|>,
        "The disabled empty word leaves an exact mass deficit and the contract is refused"]}
    ],

    (* CALC-R10 - structural and stochastic nontermination differ. *)
    makeResultSpecification["CALC-R10", "Zero-probability cycle is not stochastic nontermination", "CALC",
      "Mandatory regression", True,
      "A reachable structural cycle of probability zero contributes to set nontermination but not probability mass at infinity.",
      "One non-stop state, zero self-loop, probability-one stop transition.",
      baseSource <> ", Regression 10", "Set and exact stochastic serial types.",
      "No implicit cast between structural reachability and positive-probability behavior.",
      "Finite positive-support graph comparison.",
      {makeProofGoal["CALC-R10.CYCLE.01", "Typed cycle contrast",
        "ExhaustiveFinitePass",
        Module[{structuralEdges, positiveEdges, structuralNontermination,
          stochasticNonterminationMass},
          structuralEdges = {{"s", "a", "s"}, {"s", "b", "z"}};
          positiveEdges = Cases[{{"s", "a", "s", 0}, {"s", "b", "z", 1}},
            {from_, label_, to_, probability_} /; probability > 0 :> {from, label, to}];
          structuralNontermination = structuralNonterminationQ[{"s"},
            structuralEdges, {"z"}];
          stochasticNonterminationMass = Limit[0, n -> Infinity];
          {structuralNontermination,
            structuralNonterminationQ[{"s"}, positiveEdges, {"z"}],
            stochasticNonterminationMass}],
        {True, False, 0},
        "Structural and positive-support graphs plus the exact tail limit are computed independently"]}
    ],

    (* CALC-R11 - word probabilities aggregate paths. *)
    makeResultSpecification["CALC-R11", "Two paths bearing one word are summed", "CALC",
      "Mandatory regression", True,
      "Distinct first-hit paths with the same stopped word contribute their exact summed mass.",
      "Two branches labelled a with probabilities 1/3 and 2/3.",
      baseSource <> ", Regression 11", "Exact stopped-word probability law.",
      "The semantic object is not a path list.",
      "Exact fibre sum.",
      {makeProofGoal["CALC-R11.FIBRE.01", "Same-word path aggregation",
        "ExactSymbolicPass", Merge[{"a" -> 1/3, "a" -> 2/3}, Total], <|"a" -> 1|>,
        "Exact rational fibre aggregation"]}
    ],

    (* CALC-R12 - finite presentation of infinite stopped support. *)
    makeResultSpecification["CALC-R12", "Infinite stopped support with finite exact presentation", "CALC",
      "Mandatory regression", True,
      "The law P(a^k b)=(1-p)p^k has infinite support, total mass one, and a finite rational-series presentation.",
      "Exact 0<p<1 and one loop plus one stopping edge.",
      baseSource <> ", Regression 12", "Rational stochastic stopped series.",
      "Word-by-word finite enumeration is neither required nor claimed.",
      "Exact geometric sum and finite presentation tuple.",
      {makeProofGoal["CALC-R12.SERIES.01", "Geometric stopped law",
        "ExactSymbolicPass",
        Module[{presentation, totalMass, infinityMass, firstCoefficients},
          presentation = <|"States" -> {"loop", "stop"},
            "Initial" -> "loop", "Loop" -> <|"Label" -> "a", "Weight" -> p|>,
            "Stop" -> <|"Label" -> "b", "Weight" -> 1 - p|>|>;
          totalMass = FullSimplify[Sum[(1 - p) p^k, {k, 0, Infinity}],
            Assumptions -> 0 < p < 1];
          infinityMass = Limit[p^n, n -> Infinity, Assumptions -> 0 < p < 1];
          firstCoefficients = Table[(1 - p) p^k, {k, 0, 3}];
          {Length[presentation["States"]], firstCoefficients, totalMass,
            infinityMass}],
        {2, {1 - p, (1 - p) p, (1 - p) p^2, (1 - p) p^3}, 1, 0},
        "Finite two-state rational presentation, infinite-support coefficients, total mass, and p-infinity"]}
    ],

    (* CALC-R13 - full property mismatch. *)
    makeResultSpecification["CALC-R13", "Complete property-mismatch enumeration", "CALC",
      "Mandatory regression", True,
      "Every source value satisfying a registered property whose weakened image fails the target property is returned.",
      "Source domain {-1,0,1}; sign-to-order weakening; printed predicates.",
      baseSource <> ", Regression 13", "Finite property transport.",
      "A well-typed weakening is not automatically property preserving.",
      "Complete three-value enumeration.",
      {makeProofGoal["CALC-R13.MISMATCH.01", "Complete mismatch set",
        "ExhaustiveFinitePass",
        Select[{-1, 0, 1},
          (# > 0) && Lookup[<|-1 -> "loss", 0 -> "tie", 1 -> "win"|>, #] =!= "tie" &],
        {1}, "All source property values"]}
    ],

    (* CALC-R14 - sortwise Bell accounting. *)
    makeResultSpecification["CALC-R14", "Many-sorted Bell accounting", "CALC",
      "Mandatory regression", True,
      "Sortwise partition tuples number the product of Bell numbers, with translations counted separately.",
      "Two sort sizes 2 and 3.",
      baseSource <> ", Regression 14", "Many-sorted partition enumeration.",
      "No Bell bound is assigned to cross-signature translations.",
      "Exact integer arithmetic.",
      {makeProofGoal["CALC-R14.BELL.01", "Product of Bell numbers",
        "ExactSymbolicPass", {BellB[2] BellB[3], BellB[3]}, {10, 5},
        "Exact Bell-number evaluation"]}
    ],

    (* CALC-R15 - formal and scientific status are independent. *)
    makeResultSpecification["CALC-R15", "Formal success does not repair external incompleteness", "CALC",
      "Mandatory regression", True,
      "An internal preservation pass leaves an independently incomplete scientific-status field unchanged.",
      "Admitted formal contract with source status INCOMPLETE.",
      baseSource <> ", Regression 15", "Formal/scientific product result.",
      "The classifier never upgrades external evidence.",
      "Exact association-field preservation.",
      {makeProofGoal["CALC-R15.EXTERNAL.01", "Incomplete source remains incomplete",
        "ExactConstructivePass",
        Module[{contract = ReplacePart[finiteBaseContract[],
            "ScientificStatus" -> incompleteScientificStatus[]], result},
          result = preservationClassifier[contract];
          {result["Class"], result["ScientificStatus", "source"]}],
        {"Q-CONSERVATIVE", "INCOMPLETE"}, "Independent status vector"]}
    ]
  }
];

(* FIN-A1 through FIN-A7 - finite algebra, recovery, and response import.
Each result below states its finite assumptions, checks an exact proof or
counterwitness, and preserves the distinction between direct answers,
contextual operations, semantic orbits, representatives, and external
response codes.  Generic set and quotient facts are classified as inherited
or specialized rather than presented as new mathematics.
*)
buildFiniteSpecifications[] := Module[{source},
  source = "Mathematical contribution, Component A; finite specification, Sections 8-9";
  {
    makeResultSpecification["FIN-A1", "Semantic orbit recovery", "FIN",
      "Inherited verbatim", True,
      "The induced finite orbit map is invertible onto its image exactly when its complete orbit-collision set is empty.",
      "Finite semantic action groupoids and an action-respecting weakening; nonempty image for positive recovery.",
      source, "Finite semantic orbit sets.",
      "No raw representative inverse, public reverse term, or scientific adequacy follows.",
      "Exact orbit construction, collision enumeration, and inverse table.",
      {
        makeProofGoal["FIN-A1.INVERSE.01", "Four equivalent recovery conditions",
          "ExhaustiveFinitePass",
          Module[{sourceOrbits = {{"a"}, {"b", "c"}}, targetOrbits = {{1}, {2}, {3}},
            map = <|"a" -> 1, "b" -> 2, "c" -> 2|>, induced, image, inverse},
            induced = inducedOrbitMap[sourceOrbits, targetOrbits, map];
            image = DeleteDuplicates[Values[induced]];
            inverse = Association[Reverse /@ Normal[induced]];
            {injectiveMapQ[sourceOrbits, induced], orbitCollisionSet[induced] === {},
              AllTrue[sourceOrbits, inverse[induced[#]] === # &],
              Length[image] == Length[sourceOrbits]}],
          {True, True, True, True}, "Complete two-orbit map"],
        makeProofGoal["FIN-A1.EMPTY.02", "Empty image is vacuous",
          "ExactConstructivePass",
          If[{} === {}, "EMPTY LICENSED SOURCE IMAGE: SEMANTIC INVERSE VACUOUS", "Recovery"],
          "EMPTY LICENSED SOURCE IMAGE: SEMANTIC INVERSE VACUOUS",
          "Typed empty-domain boundary"],
        makeProofGoal["FIN-A1.EQUIVARIANCE.03",
          "Complete action and equivariance proof", "ExhaustiveFinitePass",
          Module[{domain = {"a", "b", "c"}, target = {1, 2, 3},
            map, sourceAction, targetAction, sourceOrbits, targetOrbits, induced},
            map = <|"a" -> 1, "b" -> 2, "c" -> 2|>;
            sourceAction = <|"a" -> "a", "b" -> "c", "c" -> "b"|>;
            targetAction = <|1 -> 1, 2 -> 2, 3 -> 3|>;
            sourceOrbits = {{"a"}, {"b", "c"}};
            targetOrbits = {{1}, {2}, {3}};
            induced = inducedOrbitMap[sourceOrbits, targetOrbits, map];
            {totalMapQ[domain, domain, sourceAction],
              totalMapQ[target, target, targetAction],
              AllTrue[domain, map[sourceAction[#]] === targetAction[map[#]] &],
              FreeQ[Values[induced], _Missing]}],
          {True, True, True, True},
          "Every supplied action arrow is total and the weakening commutes with it"],
        makeProofGoal["FIN-A1.NEGATIVE.04",
          "Orbit-collision negative equivalence case", "ExactConstructivePass",
          Module[{sourceOrbits = {{"a"}, {"b", "c"}},
            targetOrbits = {{1}, {2}}, map, induced},
            map = <|"a" -> 1, "b" -> 1, "c" -> 1|>;
            induced = inducedOrbitMap[sourceOrbits, targetOrbits, map];
            {injectiveMapQ[sourceOrbits, induced], orbitCollisionSet[induced],
              FailureQ[leftInverseOnImage[sourceOrbits, induced]]}],
          {False, {{{"a"}, {"b", "c"}}}, True},
          "The same finite equivalences fail together when two source orbits collide"]
      }
    ],

    makeResultSpecification["FIN-A2", "Representative recovery", "FIN",
      "Direct specialization with project-specific phonological admission package", True,
      "Representative recovery requires raw injectivity, target-image stability before restriction, and a coherent action lift.",
      "Finite raw source/target sets and a complete requested target action policy.",
      source, "Finite representative policies.",
      "Semantic orbit recovery alone is insufficient.",
      "Exact inverse, outbound-arrow, identity, and composition proofs.",
      {
        makeProofGoal["FIN-A2.PROOF.01", "Stable coherent inverse",
          "ExactConstructivePass",
          Module[{map = <|"a" -> "c", "b" -> "d"|>, inverse,
            targetArrows = {{"idc", "c", "c"}, {"idd", "d", "d"}}},
            inverse = leftInverseOnImage[{"a", "b"}, map];
            {injectiveMapQ[{"a", "b"}, map],
              Select[targetArrows, ! MemberQ[Values[map], #[[3]]] &],
              AssociationMap[inverse[mapValue[map, #]] &, {"a", "b"}]}],
          {True, {}, <|"a" -> "a", "b" -> "b"|>},
          "Raw inverse and complete target identity policy"],
        makeProofGoal["FIN-A2.OUTBOUND.02", "Outbound target swap",
          "ExactConstructivePass",
          Select[{{"swap", "c", "d"}, {"swapInverse", "d", "c"}},
            MemberQ[{"c"}, #[[2]]] && ! MemberQ[{"c"}, #[[3]]] &],
          {{"swap", "c", "d"}}, "Pre-restriction image-stability check"],
        makeProofGoal["FIN-A2.COHERENCE.03",
          "Identity and composition preserving arrow lift", "ExhaustiveFinitePass",
          Module[{domain = {"a", "b"}, target = {"c", "d"}, map,
            sourceIdentity, sourceSwap, targetIdentity, targetSwap,
            compose},
            map = <|"a" -> "c", "b" -> "d"|>;
            sourceIdentity = AssociationThread[domain, domain];
            sourceSwap = <|"a" -> "b", "b" -> "a"|>;
            targetIdentity = AssociationThread[target, target];
            targetSwap = <|"c" -> "d", "d" -> "c"|>;
            compose[left_, right_, set_] := AssociationMap[
              right[left[#]] &, set];
            {AllTrue[domain, map[sourceIdentity[#]] === targetIdentity[map[#]] &],
              AllTrue[domain, map[sourceSwap[#]] === targetSwap[map[#]] &],
              compose[sourceSwap, sourceSwap, domain] === sourceIdentity,
              compose[targetSwap, targetSwap, target] === targetIdentity,
              Sort[Values[map]] === Sort[target]}],
          {True, True, True, True, True},
          "The complete two-arrow policy commutes and the swap square composes to identity"]
      }
    ],

    makeResultSpecification["FIN-A3", "Typed finite serial decisions", "FIN",
      "New phonological integration package; algorithms and counterexamples inherited or elementary", True,
      "Stopped set language, stopped probability plus nontermination, generic weighted series, and prefix semantics remain distinct exact types.",
      "Finite state/action graphs and a declared exact coefficient domain, stop policy, readout, and equality method.",
      source, "Finite serial analyses.",
      "No implicit conditioning, probability interpretation of a generic series, or prefix/stopped cast.",
      "Exact finite laws and counterproofs.",
      {
        makeProofGoal["FIN-A3.MARGINALS.01", "Marginals do not determine joint readout",
          "ExactConstructivePass",
          Module[{p, q, marginal},
            p = <|{0, 0} -> 1/2, {1, 1} -> 1/2|>;
            q = <|{0, 1} -> 1/2, {1, 0} -> 1/2|>;
            marginal[law_, coordinate_] := Merge[
              KeyValueMap[#[[coordinate]] -> #2 &, law], Total];
            {canonicalAnswer[marginal[p, 1]] === canonicalAnswer[marginal[q, 1]],
              canonicalAnswer[marginal[p, 2]] === canonicalAnswer[marginal[q, 2]],
              canonicalAnswer[p] === canonicalAnswer[q]}],
          {True, True, False}, "Independent marginalization and joint comparison"],
        makeProofGoal["FIN-A3.NONTERMINATION.02", "Conditioning hides nontermination mass",
          "ExactConstructivePass",
          Module[{first = <|"Stopped" -> <|"w" -> 1|>, "Infinity" -> 0|>,
            second = <|"Stopped" -> <|"w" -> 1/2|>, "Infinity" -> 1/2|>},
            {normalizedLaw[Values[first["Stopped"]]],
              normalizedLaw[Values[second["Stopped"]]], first === second}],
          {{1}, {1}, False}, "Exact stopped-mass objects"],
        makeProofGoal["FIN-A3.EDGECASES.03", "Empty word, path sum, deadlock, and zero cycle",
          "ExhaustiveFinitePass",
          Module[{stoppedPaths, stoppedLaw, states, edges, stopStates,
            deadlockState, structuralCycle, probabilityInfinityMass},
            stoppedPaths = {
              <|"Word" -> "", "Weight" -> 1/4|>,
              <|"Word" -> "a", "Weight" -> 1/3|>,
              <|"Word" -> "a", "Weight" -> 2/3|>};
            stoppedLaw = Merge[
              (#1["Word"] -> #1["Weight"] &) /@ stoppedPaths, Total];
            states = {"start", "dead", "stop"};
            edges = {{"start", "dead"}};
            stopStates = {"stop"};
            deadlockState = SelectFirst[states,
              ! MemberQ[stopStates, #] &&
                Cases[edges, {#, _}] === {} &, Missing["NoDeadlock"]];
            structuralCycle = structuralNonterminationQ[{"cycle"},
              {{"cycle", "epsilon", "cycle"}}, {}];
            probabilityInfinityMass = Limit[0, n -> Infinity];
            <|"EmptyWordMass" -> stoppedLaw[""],
              "SummedWordMass" -> stoppedLaw["a"],
              "DeadlockState" -> deadlockState,
              "StructuralCycle" -> structuralCycle,
              "ProbabilityInfinityMass" -> probabilityInfinityMass|>],
          <|"EmptyWordMass" -> 1/4, "SummedWordMass" -> 1,
            "DeadlockState" -> "dead", "StructuralCycle" -> True,
            "ProbabilityInfinityMass" -> 0|>,
          "Four edge cases are computed from path, graph, and exact-limit objects"],
        makeProofGoal["FIN-A3.TYPES.04", "Four serial answer types remain distinct",
          "ExactConstructivePass",
          Module[{setLanguage, stoppedProbability, weightedSeries, allPrefixes},
            setLanguage = <|"Type" -> "StoppedSet", "Words" -> {"ab"}|>;
            stoppedProbability = <|"Type" -> "StoppedProbability",
              "Law" -> <|"ab" -> 3/4|>, "NonterminationMass" -> 1/4|>;
            weightedSeries = <|"Type" -> "WeightedSeries",
              "Coefficients" -> <|"ab" -> 5|>, "CoefficientDomain" -> Integers|>;
            allPrefixes = <|"Type" -> "AllPrefixes",
              "Words" -> {"", "a", "ab"}|>;
            {Lookup[{setLanguage, stoppedProbability, weightedSeries, allPrefixes},
                "Type"],
              DuplicateFreeQ[Lookup[
                {setLanguage, stoppedProbability, weightedSeries, allPrefixes},
                "Type"]],
              Total[Values[stoppedProbability["Law"]]] +
                stoppedProbability["NonterminationMass"],
              Total[Values[weightedSeries["Coefficients"]]]}],
          {{"StoppedSet", "StoppedProbability", "WeightedSeries", "AllPrefixes"},
            True, 1, 5},
          "Typed constructors retain probability normalization, generic coefficients, and prefix policy separately"]
      }
    ],

    makeResultSpecification["FIN-A4", "Query and consumer monotonicity", "FIN",
      "Direct specialization", True,
      "A stronger query factors to a weaker query, so strong preservation implies weak preservation; added consumers refine behavioral classes.",
      "Finite maps and a prospectively fixed reachable domain.",
      source, "Finite direct queries and deterministic chains.",
      "Neither converse is licensed; unreachable states are outside a reachable-image claim.",
      "Exact kernel inclusions and counterexamples.",
      {
        makeProofGoal["FIN-A4.KERNEL.01", "Strong-to-weak chain",
          "ExhaustiveFinitePass",
          Module[{domain = {"a", "b", "c"}, strong, weak, reduction},
            strong = <|"a" -> 1, "b" -> 2, "c" -> 3|>;
            weak = <|"a" -> 0, "b" -> 0, "c" -> 1|>;
            reduction = <|"a" -> "a", "b" -> "b", "c" -> "c"|>;
            {queryFactorsThroughQ[domain, reduction, strong],
              queryFactorsThroughQ[domain, reduction, weak],
              SubsetQ[mapKernel[domain, weak], mapKernel[domain, strong]]}],
          {True, True, True}, "Complete finite kernels"],
        makeProofGoal["FIN-A4.CONVERSES.02", "Forbidden converses",
          "ExactConstructivePass",
          Module[{domain = {"a", "b"}, reduction = <|"a" -> 0, "b" -> 0|>,
            strong = <|"a" -> 0, "b" -> 1|>, weak = <|"a" -> 0, "b" -> 0|>},
            {queryFactorsThroughQ[domain, reduction, weak],
              queryFactorsThroughQ[domain, reduction, strong],
              Length[directObservationPartition[domain, {weak, strong}]] >
                Length[directObservationPartition[domain, {weak}]]}],
          {True, False, True}, "Two-state counterexample"]
        ,makeProofGoal["FIN-A4.REACHABLE.03", "Reachable-image qualification",
          "ExactConstructivePass",
          Module[{domain = {"a", "b", "c"}, reachable = {"a", "b"},
            reduction, query},
            reduction = <|"a" -> "x", "b" -> "y", "c" -> "x"|>;
            query = <|"a" -> "A", "b" -> "B", "c" -> "C"|>;
            {queryFactorsThroughQ[domain, reduction, query],
              queryFactorsThroughQ[reachable, reduction, query],
              Complement[domain, reachable]}],
          {False, True, {"c"}},
          "A collision outside the prospectively fixed reachable image does not defeat the qualified claim"]
      }
    ],

    makeResultSpecification["FIN-A5", "Proof algebra and irreversible loss", "FIN",
      "Direct specialization", True,
      "Product-query kernels give joint factorization, minimum direct carriers, exact added-consumer price, and earliest irreversible deterministic loss.",
      "Finite direct-answer queries and deterministic maps; stochastic suffix sees only the reduced value.",
      source, "Direct-answer carrier and registered chain.",
      "No operation-closed quotient or omitted side-channel conclusion follows.",
      "Exact partitions, images, block prices, and chain witnesses.",
      {
        makeProofGoal["FIN-A5.CARRIER.01", "Joint minimum carrier and product bounds",
          "ExhaustiveFinitePass",
          Module[{domain = Range[4], q1, q2, product, partition},
            q1 = <|1 -> 0, 2 -> 0, 3 -> 1, 4 -> 1|>;
            q2 = <|1 -> 0, 2 -> 1, 3 -> 0, 4 -> 1|>;
            product = AssociationMap[{q1[#], q2[#]} &, domain];
            partition = directObservationPartition[domain, {q1, q2}];
            {Length[partition], Length[DeleteDuplicates[Values[product]]],
              Max[Length[DeleteDuplicates[Values[q1]]], Length[DeleteDuplicates[Values[q2]]]],
              Length[DeleteDuplicates[Values[q1]]] Length[DeleteDuplicates[Values[q2]]]}],
          {4, 4, 2, 4}, "Complete two-bit product carrier"],
        makeProofGoal["FIN-A5.PRICE.02", "Exact added-consumer price",
          "ExhaustiveFinitePass",
          Module[{domain = Range[4], q1, q2},
            q1 = <|1 -> 0, 2 -> 0, 3 -> 1, 4 -> 1|>;
            q2 = <|1 -> 0, 2 -> 1, 3 -> 0, 4 -> 1|>;
            addedConsumerPrice[domain, {q1}, q2]], 2,
          "Old blocks split into four realized product states"],
        makeProofGoal["FIN-A5.LOSS.03", "Earliest irreversible loss",
          "ExactConstructivePass",
          Module[{domain = {1, 2, 3}, query, stage1, stage2},
            query = <|1 -> "A", 2 -> "B", 3 -> "C"|>;
            stage1 = <|1 -> "x", 2 -> "y", 3 -> "z"|>;
            stage2 = <|"x" -> "u", "y" -> "u", "z" -> "v"|>;
            {firstLossIndex[domain, {stage1, stage2}, query],
              mapValue[stage1, 1] =!= mapValue[stage1, 2],
              mapValue[stage2, mapValue[stage1, 1]] ===
                mapValue[stage2, mapValue[stage1, 2]],
              query[1] =!= query[2]}],
          {2, True, True, True},
          "The first stage transports the query; the second introduces the first reachable loss"],
        makeProofGoal["FIN-A5.FACTORIZATION.04",
          "Kernel inclusion iff exact factorization", "ExhaustiveFinitePass",
          Module[{domain = {1, 2, 3, 4}, reduction, query, reader},
            reduction = <|1 -> "x", 2 -> "x", 3 -> "y", 4 -> "y"|>;
            query = <|1 -> "A", 2 -> "A", 3 -> "B", 4 -> "B"|>;
            reader = <|"x" -> "A", "y" -> "B"|>;
            {queryFactorsThroughQ[domain, reduction, query],
              SubsetQ[mapKernel[domain, query], mapKernel[domain, reduction]],
              AllTrue[domain, reader[reduction[#]] === query[#] &],
              Length[DeleteDuplicates[Values[reduction]]] ===
                Length[DeleteDuplicates[Values[query]]]}],
          {True, True, True, True},
          "The explicit reader witnesses factorization and the equality case of minimum carrier size"],
        makeProofGoal["FIN-A5.REDUNDANCY.05",
          "Fibre-sum price and redundancy boundary", "ExhaustiveFinitePass",
          Module[{domain = Range[4], old, redundant, splitting, oldBlocks,
            fibreFormula},
            old = <|1 -> 0, 2 -> 0, 3 -> 1, 4 -> 1|>;
            redundant = <|1 -> "a", 2 -> "a", 3 -> "b", 4 -> "b"|>;
            splitting = <|1 -> "a", 2 -> "b", 3 -> "a", 4 -> "b"|>;
            oldBlocks = directObservationPartition[domain, {old}];
            fibreFormula[consumer_] := Total[(Length[
                DeleteDuplicates[consumer /@ #]] - 1) & /@ oldBlocks];
            {addedConsumerPrice[domain, {old}, redundant],
              fibreFormula[redundant],
              addedConsumerPrice[domain, {old}, splitting],
              fibreFormula[splitting]}],
          {0, 0, 2, 2},
          "The added-consumer price is zero exactly for a consumer constant on every old block"],
        makeProofGoal["FIN-A5.POSTPROCESS.06",
          "Deterministic and Markov postprocessing cannot restore a collapsed distinction",
          "ExactConstructivePass",
          Module[{reduction, deterministicSuffix, markovSuffix},
            reduction = <|"a" -> "x", "b" -> "x", "c" -> "y"|>;
            deterministicSuffix = <|"x" -> "u", "y" -> "v"|>;
            markovSuffix = <|"x" -> <|"u" -> 1/3, "v" -> 2/3|>,
              "y" -> <|"u" -> 3/4, "v" -> 1/4|>|>;
            {deterministicSuffix[reduction["a"]] ===
                deterministicSuffix[reduction["b"]],
              canonicalAnswer[markovSuffix[reduction["a"]]] ===
                canonicalAnswer[markovSuffix[reduction["b"]]],
              canonicalAnswer[markovSuffix[reduction["a"]]] =!=
                canonicalAnswer[markovSuffix[reduction["c"]]]}],
          {True, True, True},
          "Both suffixes receive only the reduced value and no bypassing side information"],
        makeProofGoal["FIN-A5.UNIVERSAL.07", "Injectivity is universal query preservation",
          "ExhaustiveFinitePass",
          Module[{domain = {1, 2, 3}, injective, collapsed, binaryQueries},
            injective = <|1 -> "a", 2 -> "b", 3 -> "c"|>;
            collapsed = <|1 -> "a", 2 -> "a", 3 -> "c"|>;
            binaryQueries = AssociationThread[domain, #] & /@ Tuples[{0, 1}, 3];
            {AllTrue[binaryQueries,
                queryFactorsThroughQ[domain, injective, #] &],
              AllTrue[binaryQueries,
                queryFactorsThroughQ[domain, collapsed, #] &],
              SelectFirst[binaryQueries,
                ! queryFactorsThroughQ[domain, collapsed, #] &]}],
          {True, False, <|1 -> 0, 2 -> 1, 3 -> 0|>},
          "Exhaustive binary consumers include a separating witness for every raw collision"],
        makeProofGoal["FIN-A5.COLLISIONS.08", "Collision decomposition along a chain",
          "ExhaustiveFinitePass",
          Module[{domain = {1, 2, 3, 4}, first, second, composite,
            oldCollisions, totalCollisions, newCollisions},
            first = <|1 -> "a", 2 -> "a", 3 -> "b", 4 -> "c"|>;
            second = <|"a" -> "x", "b" -> "x", "c" -> "y"|>;
            composite = composeMaps[first, second, domain];
            oldCollisions = collisionPairs[domain, first];
            totalCollisions = collisionPairs[domain, composite];
            newCollisions = Complement[totalCollisions, oldCollisions];
            {oldCollisions, newCollisions,
              Sort[Union[oldCollisions, newCollisions]] === totalCollisions}],
          {{{1, 2}}, {{1, 3}, {2, 3}}, True},
          "The composite collision set is the disjoint union of inherited and newly introduced collisions"]
      }
    ],

    makeResultSpecification["FIN-A6", "Finite consumer-battery information lattice", "FIN",
      "Direct specialization", True,
      "Kernel intersections form the registered information lattice; fixed-signature contextual carriers intersect as strong congruences, and nonuniform definedness blocks universal joins.",
      "Finite carrier, finite registered battery, fixed complete partial signature.",
      source, "Finite direct and fixed-signature contextual carriers.",
      "No lattice is asserted across changing evaluators, signatures, roots, or scientific policies.",
      "Exhaustive finite partitions, closure operator, and strong-congruence witnesses.",
      {
        makeProofGoal["FIN-A6.LATTICE.01", "Two-bit incomparable carrier lattice",
          "ExhaustiveFinitePass",
          Module[{domain = Tuples[{0, 1}, 2], firstBit, secondBit, p1, p2, joint},
            firstBit = AssociationMap[First, domain];
            secondBit = AssociationMap[Last, domain];
            p1 = directObservationPartition[domain, {firstBit}];
            p2 = directObservationPartition[domain, {secondBit}];
            joint = directObservationPartition[domain, {firstBit, secondBit}];
            {Length[p1], Length[p2], Length[joint],
              Sort[Sort /@ p1] =!= Sort[Sort /@ p2]}],
          {2, 2, 4, True}, "Complete four-state Boolean carrier"],
        makeProofGoal["FIN-A6.CLOSURE.02", "Redundancy closure laws",
          "ExhaustiveFinitePass",
          Module[{domain = Tuples[{0, 1}, 2], universe, subsets, closure,
            extensive, idempotent, monotone},
            universe = {
              AssociationMap[First, domain],
              AssociationMap[Last, domain],
              AssociationMap[1 - First[#] &, domain],
              AssociationMap[Mod[Total[#], 2] &, domain]};
            subsets = Subsets[Range[Length[universe]]];
            closure[subset_] := consumerRedundancyClosure[
              domain, universe, subset];
            extensive = AllTrue[subsets, SubsetQ[closure[#], #] &];
            idempotent = AllTrue[subsets,
              closure[closure[#]] === closure[#] &];
            monotone = AllTrue[Tuples[subsets, 2],
              ! SubsetQ[#[[2]], #[[1]]] ||
                SubsetQ[closure[#[[2]]], closure[#[[1]]]] &];
            {extensive, monotone, idempotent, closure[{1}], closure[{1, 2}]}],
          {True, True, True, {1, 3}, {1, 2, 3, 4}},
          "Exact kernel-induced closure checked on every one of sixteen batteries and every inclusion pair"],
        makeProofGoal["FIN-A6.DEFINEDNESS.03", "Universal-join definedness refusal",
          "ExactConstructivePass",
          Module[{domain = {"a", "b"}, operation, universal},
            operation = <|"Arity" -> 1, "Table" -> <|{"a"} -> "a"|>|>;
            universal = {{"a", "b"}};
            {strongCongruenceQ[domain, operation, universal],
              0 < Length[Keys[operation["Table"]]] < Length[domain]}],
          {False, True}, "Partial-operation domain witness"],
        makeProofGoal["FIN-A6.LATTICEOPS.04", "Closed-set meet and join laws",
          "ExhaustiveFinitePass",
          Module[{domain = Tuples[{0, 1}, 2], universe, closure, closed,
            pairs},
            universe = {
              AssociationMap[First, domain],
              AssociationMap[Last, domain],
              AssociationMap[1 - First[#] &, domain],
              AssociationMap[Mod[Total[#], 2] &, domain]};
            closure[subset_] := consumerRedundancyClosure[
              domain, universe, subset];
            closed = Select[Subsets[Range[4]], closure[#] === # &];
            pairs = Tuples[closed, 2];
            {Length[closed],
              AllTrue[pairs, MemberQ[closed, Intersection @@ #] &],
              AllTrue[pairs, MemberQ[closed, closure[Union @@ #]] &]}],
          {5, True, True},
          "Meet is intersection and join is closure of union on the frozen finite consumer universe"],
        makeProofGoal["FIN-A6.CONTEXT.05",
          "Fixed-signature contextual intersection", "ExhaustiveFinitePass",
          Module[{domain = {"a", "b", "c", "d"}, operation, q1, q2,
            p1, p2, joint, relation},
            operation = <|"Arity" -> 1,
              "Table" -> Association[({#} -> #) & /@ domain]|>;
            q1 = <|"a" -> 0, "b" -> 0, "c" -> 1, "d" -> 1|>;
            q2 = <|"a" -> 0, "b" -> 1, "c" -> 0, "d" -> 1|>;
            p1 = directObservationPartition[domain, {q1}];
            p2 = directObservationPartition[domain, {q2}];
            joint = directObservationPartition[domain, {q1, q2}];
            relation[partition_] := Sort[Flatten[Tuples[#, 2] & /@ partition, 1]];
            {strongCongruenceQ[domain, operation, p1],
              strongCongruenceQ[domain, operation, p2],
              strongCongruenceQ[domain, operation, joint],
              Intersection[relation[p1], relation[p2]] === relation[joint]}],
          {True, True, True, True},
          "The two contextual carriers and their joint use one complete fixed partial signature"]
      }
    ],

    makeResultSpecification["FIN-A7", "Proof-carrying symbolic response import", "FIN",
      "Project-specialized bridge theorem; generic factorization inherited", True,
      "An external infinite response enters the finite classifier only through an exact finite code, interpretation, equality procedure, reachable image, descended transformation, and required witness section.",
      "Finite sort set and finite reachable symbolic-code image with exact semantic interpretation.",
      source, "Externally solved response families with proof-carrying finite codes.",
      "The finite classifier does not become a raw-continuum decider; a missing section blocks only the lifted source-witness claim.",
      "Exact commuting diagram and structured refusal.",
      {
        makeProofGoal["FIN-A7.DIAGRAM.01", "Commuting finite-code import",
          "ExactConstructivePass",
          Module[{domain = {1, 2, 3}, code, transform, descended, response, interpreted},
            code = <|1 -> "odd", 2 -> "even", 3 -> "odd"|>;
            transform = <|1 -> 3, 2 -> 2, 3 -> 1|>;
            descended = <|"odd" -> "odd", "even" -> "even"|>;
            response = <|1 -> 1, 2 -> 0, 3 -> 1|>;
            interpreted = <|"odd" -> 1, "even" -> 0|>;
            And @@ Table[
              descended[code[element]] === code[transform[element]] &&
                interpreted[code[element]] === response[element], {element, domain}]],
          True, "Complete finite reachable image"],
        makeProofGoal["FIN-A7.SECTION.02", "Carrier mismatch without source section",
          "ExactConstructivePass",
          Module[{sourceCarrier = {"odd", "even"}, descent,
            sourceInterpretation, targetInterpretation, mismatches, preimages,
            sectionAvailable},
            descent = <|"odd" -> "merged", "even" -> "merged"|>;
            sourceInterpretation = <|"odd" -> 1, "even" -> 0|>;
            targetInterpretation = <|"merged" -> 0|>;
            mismatches = Select[sourceCarrier,
              sourceInterpretation[#] =!= targetInterpretation[descent[#]] &];
            preimages = Select[sourceCarrier, descent[#] === "merged" &];
            sectionAvailable = Length[preimages] === 1;
            <|"CarrierClass" -> If[mismatches === {}, "Q-CONSERVATIVE",
                "Q-NONCONSERVATIVE"],
              "CarrierMismatchCodes" -> mismatches,
              "UniqueSourceSectionAvailable" -> sectionAvailable,
              "SourceWitnessStatus" -> If[sectionAvailable, "AVAILABLE",
                "NOT EVALUATED"]|>],
          <|"CarrierClass" -> "Q-NONCONSERVATIVE",
            "CarrierMismatchCodes" -> {"odd"},
            "UniqueSourceSectionAvailable" -> False,
            "SourceWitnessStatus" -> "NOT EVALUATED"|>,
          "The carrier mismatch is computed; only the unregistered source-representative lift is refused"],
        makeProofGoal["FIN-A7.CODE.03", "Typed response-code formation and equality",
          "ExactConstructivePass",
          Module[{required, responseCode, semanticEqual},
            required = {"Sort", "Parameters", "CodeCarrier", "Interpretation",
              "SemanticEquality", "ReachableImage", "Reader", "Descent"};
            responseCode = <|"Sort" -> "DirectionalHGResponse",
              "Parameters" -> <|"h" -> 5, "m" -> 1, "p" -> 2|>,
              "CodeCarrier" -> {"K4", "K5"},
              "Interpretation" -> <|"K4" -> {1, 3/5, 3/10, 1/10, 0},
                "K5" -> {1, 13/20, 3/8, 7/40, 1/20, 0}|>,
              "SemanticEquality" -> SameQ,
              "ReachableImage" -> {"K4", "K5"},
              "Reader" -> <|"K4" -> 3, "K5" -> 4|>,
              "Descent" -> <|"K4" -> "K4", "K5" -> "K5"|>|>;
            semanticEqual[left_, right_] :=
              responseCode["SemanticEquality"][left, right];
            {SubsetQ[Keys[responseCode], required],
              DuplicateFreeQ[responseCode["CodeCarrier"]],
              Sort[responseCode["ReachableImage"]] ===
                Sort[responseCode["CodeCarrier"]],
              semanticEqual[responseCode["Interpretation", "K4"],
                {1, 3/5, 3/10, 1/10, 0}],
              ! semanticEqual[responseCode["Interpretation", "K4"],
                responseCode["Interpretation", "K5"]]}],
          {True, True, True, True, True},
          "Every finite-code field is present and semantic equality is exact"],
        makeProofGoal["FIN-A7.POSITIVESECTION.04", "Effective positive section",
          "ExhaustiveFinitePass",
          Module[{source = {1, 2, 3}, code, section, carrier},
            code = <|1 -> "odd", 2 -> "even", 3 -> "primeOdd"|>;
            carrier = Values[code];
            section = Association[Reverse /@ Normal[code]];
            {injectiveMapQ[source, code], Sort[Keys[section]] === Sort[carrier],
              AllTrue[source, section[code[#]] === # &]}],
          {True, True, True},
          "An injective finite code supplies an effective section and source-witness lift"],
        makeProofGoal["FIN-A7.REFUSALS.05", "Response-import refusal matrix",
          "ExhaustiveFinitePass",
          Module[{dependencies, decide},
            dependencies = {"CodeCarrier", "Interpretation", "SemanticEquality",
              "ReachableImage", "Reader", "Descent", "SourceSection"};
            decide[missing_] := <|"Missing" -> missing,
              "CarrierDecision" -> If[missing === "SourceSection",
                "AVAILABLE", "NOT EVALUATED"],
              "SourceWitness" -> "NOT EVALUATED"|>;
            decide /@ dependencies],
          {<|"Missing" -> "CodeCarrier", "CarrierDecision" -> "NOT EVALUATED",
              "SourceWitness" -> "NOT EVALUATED"|>,
            <|"Missing" -> "Interpretation", "CarrierDecision" -> "NOT EVALUATED",
              "SourceWitness" -> "NOT EVALUATED"|>,
            <|"Missing" -> "SemanticEquality", "CarrierDecision" -> "NOT EVALUATED",
              "SourceWitness" -> "NOT EVALUATED"|>,
            <|"Missing" -> "ReachableImage", "CarrierDecision" -> "NOT EVALUATED",
              "SourceWitness" -> "NOT EVALUATED"|>,
            <|"Missing" -> "Reader", "CarrierDecision" -> "NOT EVALUATED",
              "SourceWitness" -> "NOT EVALUATED"|>,
            <|"Missing" -> "Descent", "CarrierDecision" -> "NOT EVALUATED",
              "SourceWitness" -> "NOT EVALUATED"|>,
            <|"Missing" -> "SourceSection", "CarrierDecision" -> "AVAILABLE",
              "SourceWitness" -> "NOT EVALUATED"|>},
          "A missing section blocks only source-witness lifting; every earlier missing field blocks carrier decision"]
      }
    ]
  }
];

(*
CHG-B1 through CHG-B16 - directional power-HG verification
Statement source: mathematical contribution, Component B.
Assumptions: each result states its own restrictions; the core family has
harmonyWeight>0, markednessWeight>0, exponentP>1, x0=1, and a finite box.
Machine-checked proof goals: exact reductions, KKT identities, support and
phase boundaries, equality ownership, limits, and fixed rational anchors.
Verification method: exact symbolic algebra, constructive KKT proofs,
and finite independent objective comparisons.  These results concern only the
declared directional family and do not identify acoustic, articulatory, or
cognitive quantities.
*)

ClearAll[buildContinuousHGSpecifications];
buildContinuousHGSpecifications[] := Module[{source},
  source = "Mathematical contribution, Component B; final research results, continuous-HG theorem family";
  {
    makeResultSpecification["CHG-B1", "Monotone normal form", "CHG",
      "New theorem for the declared continuous family", True,
      "Running-minimum normalization weakly lowers the directional-HG objective and converts every optimizer to a solid-simplex decrease problem with a strictly convex reduced objective for p>1.",
      "Finite horizon, x0=1, xi in [0,1], h>0, m>0, p>1.",
      source, "Declared directional positive-part power-HG path.",
      "Terminal zero is not assumed and no raw phonetic interpretation is licensed.",
      "Exact energy comparison, coordinate transformation, and Hessian proof.",
      {
        makeProofGoal["CHG-B1.RUNMIN.01", "Running-minimum energy inequality",
          "ExactSymbolicPass",
          Module[{x = {4/5, 9/10, 1/2}, y, h = 7/3, m = 5/4, p = 2},
            y = Rest[FoldList[Min, 1, x]];
            {y, directionalHGObjective[y, h, m, p] <=
              directionalHGObjective[x, h, m, p]}],
          {{4/5, 4/5, 1/2}, True},
          "Independent exact nonmonotone witness"],
        makeProofGoal["CHG-B1.SIMPLEX.02", "Solid-simplex identity",
          "ExactSymbolicPass",
          FullSimplify[
            directionalHGObjective[{1 - d1, 1 - d1 - d2, 1 - d1 - d2 - d3},
              h, m, p] == monotoneDecreaseObjective[{d1, d2, d3}, h, m, p],
            Assumptions -> h > 0 && m > 0 && p > 1 && d1 >= 0 && d2 >= 0 &&
              d3 >= 0 && d1 + d2 + d3 <= 1],
          True, "Exact symbolic substitution without terminal-zero premise"],
        makeProofGoal["CHG-B1.CONVEX.03", "Positive diagonal Hessian interior",
          "ExactSymbolicPass",
          FullSimplify[And @@ Thread[
            {h p (p - 1) d1^(p - 2),
              h p (p - 1) d2^(p - 2), h p (p - 1) d3^(p - 2)} > 0],
            Assumptions -> h > 0 && p > 1 && d1 > 0 && d2 > 0 && d3 > 0],
          True, "Strict convexity proof on the relative interior"]
      }
    ],

    makeResultSpecification["CHG-B2", "All-horizon finite persistence", "CHG",
      "New theorem for the declared continuous family", True,
      "The unique optimizer has an exact first-zero index Kp, positive support through Kp-1, and an extension-stable positive prefix.",
      "h>0, m>0, p>1, positive integer horizon, x0=1.",
      source, "Directional power harmony plus positive linear markedness.",
      "No theorem about all continuous HG, all vowel harmony, or phonetic trajectories.",
      "Exact KKT identities, active-set proof, extension identity, and anchor cases.",
      {
        makeProofGoal["CHG-B2.ASSUMPTIONS.01", "Assumptions are satisfiable",
          "ExactSymbolicPass",
          Resolve[Exists[{h, m, p}, h > 0 && m > 0 && p > 1], Reals], True,
          "Exact real satisfiability"],
        makeProofGoal["CHG-B2.KKT.02", "Inactive KKT stationarity",
          "ExactSymbolicPass",
          FullSimplify[
            p h ((m r/(p h))^(1/(p - 1)))^(p - 1) == m r,
            Assumptions -> h > 0 && m > 0 && r > 0 && p > 1],
          True, "Exact positive-power stationarity"],
        makeProofGoal["CHG-B2.EXTENSION.03", "Extension multiplier identity",
          "ExactSymbolicPass",
          FullSimplify[
            m (n - i + 1) - (eta + m (n - k)) ==
              m (k - i + 1) - eta,
            Assumptions -> Element[{n, k, i}, Integers] && n > k >= i >= 1],
          True, "Exact affine multiplier shift"],
        makeProofGoal["CHG-B2.BOUNDARY.04", "Equality lies on zero side",
          "ExactConstructivePass",
          Module[{h = 5, m = 1, p = 2, k, profile},
            k = supportIndexExact[h, m, p]; profile = quadraticProfile[h, m, k + 2];
            {k, profile, Count[Rest[profile], value_ /; value > 0],
              profile[[k + 1]]}],
          {4, {1, 3/5, 3/10, 1/10, 0, 0, 0}, 3, 0},
          "Independent exact equality-boundary anchor"],
        makeProofGoal["CHG-B2.ANCHORS.05", "Three exact support anchors",
          "ExactConstructivePass",
          {{supportIndexExact[20, 3, 2], quadraticProfile[20, 3, 5]},
            {supportIndexExact[5, 1, 2], quadraticProfile[5, 1, 5]},
            {supportIndexExact[21, 1, 2], quadraticProfile[21, 1, 1]}},
          {{5, {1, 13/20, 3/8, 7/40, 1/20, 0}},
            {4, {1, 3/5, 3/10, 1/10, 0, 0}},
            {9, {1, 41/42}}},
          "Closed forms evaluated independently at printed weights"]
      }
    ],

    makeResultSpecification["CHG-B3", "Complete quadratic active set", "CHG",
      "New theorem for the declared continuous family", True,
      "For p=2 the unsaturated and saturated optimizer profiles, first-zero formula, projection form, and ratio sensitivity are exact.",
      "h>0, m>0, positive integer horizon.",
      source, "Quadratic member of the directional path family.",
      "Projection nonexpansiveness does not preserve support at phase boundaries.",
      "Exact formulas, KKT residuals, phase inequalities, and fixed anchors.",
      {
        makeProofGoal["CHG-B3.UNSATURATED.01", "Unsaturated closed form",
          "ExactSymbolicPass",
          Module[{h = 21, m = 1, n = 3, d, x},
            d = quadraticUnsaturatedDecreases[h, m, n];
            x = exactProfileFromDecreases[d];
            {d, x, Total[d] < 1}],
          {{1/14, 1/21, 1/42}, {1, 13/14, 37/42, 6/7}, True},
          "Independent finite-horizon calculation"],
        makeProofGoal["CHG-B3.SATURATED.02", "Saturated KKT profile",
          "ExactSymbolicPass",
          Module[{d = quadraticSaturatedDecreases[5, 1], profile},
            profile = exactProfileFromDecreases[d];
            {d, Total[d], profile}],
          {{2/5, 3/10, 1/5, 1/10}, 1, {1, 3/5, 3/10, 1/10, 0}},
          "Exact active-set mass and profile"],
        makeProofGoal["CHG-B3.SUPPORT.03", "Strict support formula",
          "ExhaustiveFinitePass",
          Table[
            {h, m, quadraticSupportIndex[h, m] - 1,
              Max[Select[Range[0, 20], m # (# + 1) < 4 h &]]},
            {h, {5, 20, 21}}, {m, {1, 3}}] // Flatten[#, 1] &,
          Table[{h, m, quadraticSupportIndex[h, m] - 1,
            quadraticSupportIndex[h, m] - 1}, {h, {5, 20, 21}}, {m, {1, 3}}] //
            Flatten[#, 1] &,
          "Complete stated finite parameter grid"],
        makeProofGoal["CHG-B3.PROJECTION.04", "Projection sensitivity bound",
          "ExactSymbolicPass",
          Module[{w = {3, 2, 1}, rho1 = 5, rho2 = 6, v1, v2},
            v1 = w/(2 rho1); v2 = w/(2 rho2);
            Norm[v1 - v2]^2 <= (Norm[w]^2/4) (1/rho1 - 1/rho2)^2],
          True, "Exact squared Euclidean bound"]
      }
    ],

    makeResultSpecification["CHG-B4", "Endpoint obstruction", "CHG",
      "Elementary but useful", True,
      "A one-follower all-back endpoint cannot be locally optimal when the directional penalty is o(epsilon) and markedness has positive linear slope.",
      "h>0, m>0, phi(0)=0, phi(epsilon)=o(epsilon) from the right.",
      source, "One-follower endpoint of the declared family.",
      "No general empirical endpoint claim.",
      "Exact little-o reduction proof and quadratic optimizer.",
      {
        makeProofGoal["CHG-B4.LITTLEO.01", "Normalized endpoint difference",
          "ReductionProofPass",
          Module[{proof},
            proof = <|"Premise" -> "Limit[phi(e)/e,e->0+]=0",
              "ReducedLimit" -> -m, "SignUnderMPositive" -> True|>;
            proof],
          <|"Premise" -> "Limit[phi(e)/e,e->0+]=0",
            "ReducedLimit" -> -m, "SignUnderMPositive" -> True|>,
          "Linearity of the normalized limit under the printed premise"],
        makeProofGoal["CHG-B4.QUADRATIC.02", "One-follower quadratic winner",
          "ExactSymbolicPass",
          FullSimplify[
            (x /. First@Solve[2 h (x - 1) + m == 0, x]) == 1 - m/(2 h),
            Assumptions -> h > 0 && m > 0 && m < 2 h],
          True, "Exact interior stationarity"]
      }
    ],

    makeResultSpecification["CHG-B5", "Complete exponent boundary at p=1", "CHG",
      "Elementary but useful", True,
      "Sublinear, linear, and superlinear edge penalties respectively favor concentrated repair, indifferent distribution, and distributed repair, with distinct endpoint optimizer sets.",
      "Finite solid simplex, h>0, m>0; separate branches 0<p<1, p=1, p>1.",
      source, "Exponent phase boundary of the declared path objective.",
      "The exponent is not estimated from acoustic data.",
      "Exact endpoint energies, equality faces, and finite repair inequalities.",
      {
        makeProofGoal["CHG-B5.ENDPOINTS.01", "Sublinear and linear equality sets",
          "ExhaustiveFinitePass",
          Module[{n = 3, grid = Range[0, 1, 1/4], sublinear, linear},
            sublinear = Select[grid,
              3 #^(1/2) - 3 # == Min[3 grid^(1/2) - 3 grid] &];
            linear = Select[grid, 3 # - 3 # == 0 &];
            {sublinear, linear}],
          {{0, 1}, {0, 1/4, 1/2, 3/4, 1}},
          "Complete exact equality-face grid plus endpoint formula"],
        makeProofGoal["CHG-B5.REPAIR.02", "Repair-distribution phase",
          "ExactSymbolicPass",
          Module[{d = 1, r = 4},
            {r (d/r)^2 < d^2,
              r (d/r) == d,
              r Sqrt[d/r] > Sqrt[d]}],
          {True, True, True}, "Exact uniform versus concentrated witnesses"]
      }
    ],

    makeResultSpecification["CHG-B6", "Exact uniform-lattice boundary", "CHG",
      "New theorem for the declared continuous family", True,
      "On a uniform lattice and p>=1, the all-back profile wins exactly when h delta^(p-1)>=N m, with the printed boundary tie set.",
      "Uniform step delta with integer reciprocal, positive h,m, integer N, p>=1.",
      source, "Uniformly discretized declared directional family.",
      "No extension to sublinear powers or irregular grids.",
      "Exact lower bound and one-step necessity witness.",
      {
        makeProofGoal["CHG-B6.CLASSIFY.01", "Winner, boundary, nonwinner",
          "ExhaustiveFinitePass",
          {latticeAllBackStatus[21, 1, 2, 1, 1/10],
            latticeAllBackStatus[10, 1, 2, 1, 1/10],
            latticeAllBackStatus[9, 1, 2, 1, 1/10]},
          {"UniqueWinner", "BoundaryTie", "NotWinner"},
          "Three exact rational boundary cases"],
        makeProofGoal["CHG-B6.ONESTEP.02", "One-step necessity",
          "ExactSymbolicPass",
          FullSimplify[
            directionalHGObjective[{1 - delta, 1 - delta, 1 - delta}, h, m, p] -
              directionalHGObjective[{1, 1, 1}, h, m, p] ==
              delta (h delta^(p - 1) - 3 m),
            Assumptions -> h > 0 && m > 0 && p >= 1 && 0 < delta <= 1],
          True, "Exact competitor difference"]
      }
    ],

    makeResultSpecification["CHG-B7", "Weight gauge and persistence phases", "CHG",
      "Inherited deterministic-HG scale invariance combined with new family-specific phase results", True,
      "Common positive weight scaling preserves deterministic order, and Kp partitions the ratio h/m into exact phase cells with explicit asymptotic scaling.",
      "h,m,lambda>0, p>1.",
      source, "Deterministic winner behavior of the declared path family.",
      "Absolute weights are not identified and the phase law is not a learning curve.",
      "Exact scale identity, phase bounds, widths, and quadratic asymptotic anchor.",
      {
        makeProofGoal["CHG-B7.GAUGE.01", "Common-scale invariance",
          "ExactSymbolicPass",
          FullSimplify[
            directionalHGObjective[{x1, x2}, lambda h, lambda m, p] ==
              lambda directionalHGObjective[{x1, x2}, h, m, p],
            Assumptions -> lambda > 0 && h > 0 && m > 0 && p > 1 &&
              1 >= x1 >= x2 >= 0], True, "Exact symbolic scaling"],
        makeProofGoal["CHG-B7.PHASE.02", "Exact quadratic phase cells",
          "ExhaustiveFinitePass",
          Table[{k, persistencePhaseBounds[2, k]}, {k, 1, 5}],
          {{1, {0, 1/2}}, {2, {1/2, 3/2}}, {3, {3/2, 3}},
            {4, {3, 5}}, {5, {5, 15/2}}},
          "All first five exact cells"],
        makeProofGoal["CHG-B7.ASYMPTOTIC.03", "Quadratic reach constant",
          "ExactSymbolicPass",
          Limit[(Sqrt[s^2 + 16] - s)/2, s -> 0,
            Direction -> "FromAbove"], 2,
          "Exact symbolic limit"]
      }
    ],

    makeResultSpecification["CHG-B8", "Support-resolution duality", "CHG",
      "Elementary but useful", True,
      "The dimensionless ratio N m/(h delta^(p-1)) exactly classifies the uniform-lattice all-back outcome and yields weak and strict maximum horizons.",
      "Uniform lattice, p>1, positive h,m,delta, positive integer N.",
      source, "Uniform-lattice support query.",
      "No categorical ontology or irregular-grid theorem.",
      "Exact algebraic rearrangement and boundary examples.",
      {
        makeProofGoal["CHG-B8.RATIO.01", "Support ratio classification",
          "ExactSymbolicPass",
          Module[{ratio = 3*1/(20*(1/10))},
            {ratio, ratio > 1, latticeAllBackStatus[20, 1, 2, 3, 1/10]}],
          {3/2, True, "NotWinner"}, "Exact rational ratio"],
        makeProofGoal["CHG-B8.HORIZON.02", "Weak and unique maximum horizons",
          "ExactSymbolicPass",
          Module[{value = 5*(1/10)},
            {Floor[value], Ceiling[value] - 1}], {0, 0},
          "Exact floor/ceiling boundary"]
      }
    ],

    makeResultSpecification["CHG-B9", "Normalized phase profile and powered-gap linearity", "CHG",
      "New theorem for the declared continuous family", True,
      "Within a saturated phase the normalized shifted-power profile is exact and consecutive powered decreases differ by 1/(p rho).",
      "p>1, fixed saturated phase K, unique tau in [0,1).",
      source, "Active set of the declared directional family.",
      "The profile is grammar-internal and not a token probability or acoustic curve.",
      "Exact normalized mass, profile identity, and powered-gap residuals.",
      {
        makeProofGoal["CHG-B9.NORMALIZE.01", "Normalized active mass",
          "ExactSymbolicPass",
          FullSimplify[Total[normalizedPhaseDecreases[2, 4, tau]] == 1,
            Assumptions -> 0 <= tau < 1], True,
          "Exact rational-function normalization"],
        makeProofGoal["CHG-B9.GAPS.02", "Powered gaps form an arithmetic progression",
          "ExactSymbolicPass",
          Module[{d = normalizedPhaseDecreases[2, 4, 0]},
            Differences[d]], {-1/10, -1/10, -1/10},
          "Exact quadratic phase anchor"],
        makeProofGoal["CHG-B9.PROFILE.03", "Profile from remaining mass",
          "ExactConstructivePass",
          normalizedPhaseProfile[2, 4, 0], {1, 3/5, 3/10, 1/10, 0},
          "Independent cumulative sum"]
      }
    ],

    makeResultSpecification["CHG-B10", "Comparative statics and extension stability", "CHG",
      "New theorem for the declared continuous family", True,
      "Coordinates are nondecreasing in h/m, profiles paste continuously across support phases, and Kp is the first horizon whose prefix is stable under every extension.",
      "Fixed p>1 and positive weights.",
      source, "Declared finite-horizon path family.",
      "No acoustic monotonicity or population prediction.",
      "Exact phase-boundary identities and extension comparisons.",
      {
        makeProofGoal["CHG-B10.MONOTONE.01", "Ratio comparative statics anchor",
          "ExhaustiveFinitePass",
          And @@ Thread[quadraticProfile[6, 1, 4] >= quadraticProfile[5, 1, 4]],
          True, "Exact coordinatewise comparison"],
        makeProofGoal["CHG-B10.EXTENSION.02", "First stable horizon",
          "ExactConstructivePass",
          Module[{profiles = Table[quadraticProfile[5, 1, n], {n, 1, 7}]},
            Min[Select[Range[1, 6],
              Function[n, And @@ Table[Take[profiles[[m]], n + 1] ===
                profiles[[n]], {m, n, 7}]]]]], 4,
          "Complete exact horizons one through seven"],
        makeProofGoal["CHG-B10.BOUNDARY.03", "Continuous phase paste",
          "ExactSymbolicPass",
          Limit[normalizedPhaseProfile[2, 5, tau], tau -> 1,
            Direction -> "FromBelow"],
          {1, 3/5, 3/10, 1/10, 0, 0}, "Exact one-sided limit"]
      }
    ],

    makeResultSpecification["CHG-B11", "Query-relative parameter identifiability", "CHG",
      "New theorem for the declared continuous family", True,
      "Persistence identifies a phase cell, two powered gaps identify h/m for known p, and an admissible log-concave triple locally identifies p and the ratio; common scale remains a gauge.",
      "Exact grammar-internal active decreases and the complete family-admission conditions.",
      source, "Declared constant-p, constant-weight path family.",
      "An isolated triple is not global admission and no acoustic estimator is supplied.",
      "Exact phase intervals, gap inversion, and unique positive-root witness.",
      {
        makeProofGoal["CHG-B11.PHASE.01", "Persistence phase interval",
          "ExactConstructivePass", persistencePhaseBounds[2, 4], {3, 5},
          "Exact ratio cell"],
        makeProofGoal["CHG-B11.RATIO.02", "Powered-gap ratio recovery",
          "ExactSymbolicPass",
          Module[{d = quadraticSaturatedDecreases[5, 1]},
            1/(2 (d[[1]] - d[[2]]))], 5,
          "Exact consecutive-gap inversion"],
        makeProofGoal["CHG-B11.TRIPLE.03", "Unique local exponent proof",
          "ExactSymbolicPass",
          Module[{g},
            g[t_] := (3/2)^t + (1/2)^t - 2;
            {g[1], FullSimplify[g'[0] < 0], FullSimplify[g'[1] > 0],
              FullSimplify[g''[t] > 0, Assumptions -> t > 0]}],
          {0, True, True, True},
          "Exact strict-convexity and endpoint proof for the sole positive root"],
        makeProofGoal["CHG-B11.SCALE.04", "Absolute common scale is unidentified",
          "ExactSymbolicPass",
          quadraticProfile[5, 1, 5] === quadraticProfile[35, 7, 5], True,
          "Exact common-scale gauge witness"]
      }
    ],

    makeResultSpecification["CHG-B12", "Lattice convergence without exact identity", "CHG",
      "Direct specialization", True,
      "Dense uniform lattices converge to the unique continuum optimizer, yet a continuum optimizer absent from every lattice is never exactly reproduced for the identity query.",
      "Fixed finite horizon, p>1, compact solid simplex, unique continuum minimizer, lattice steps tending to zero.",
      source, "Optimization approximation versus exact query preservation.",
      "Convergence does not make a finite lattice the same GEN.",
      "Exact quadratic approximation sequence and denominator proof.",
      {
        makeProofGoal["CHG-B12.SEQUENCE.01", "Exact decimal-grid minimizers approach 41/42",
          "ExactSymbolicPass",
          Module[{targets = Table[Round[10^j 41/42]/10^j, {j, 1, 6}]},
            {targets, Abs[Last[targets] - 41/42] < 1/10^6,
              FreeQ[targets, 41/42]}],
          {{1, 49/50, 122/125, 4881/5000, 97619/100000,
              97619/100000}, True, True},
          "Independent exact nearest-lattice values"],
        makeProofGoal["CHG-B12.DENOMINATOR.02", "No terminating-decimal identity",
          "ReductionProofPass",
          {FactorInteger[Denominator[41/42]], FactorInteger[10]},
          {{{2, 1}, {3, 1}, {7, 1}}, {{2, 1}, {5, 1}}},
          "Prime-denominator obstruction"]
      }
    ],

    makeResultSpecification["CHG-B13", "Asymptotic self-similarity and shape-reach separation", "CHG",
      "New theorem for the declared continuous family", True,
      "After normalization by Kp, saturated profiles converge to (1-u)^(p/(p-1)) and decreases to its derivative density; h/m controls reach while p controls shape.",
      "Fixed p>1 and ratio h/m tending to infinity.",
      source, "Long-support limit of the declared grammar-internal profile.",
      "No physical-time, acoustic, or universal harmony law.",
      "Exact power-sum limits and quadratic specialization.",
      {
        makeProofGoal["CHG-B13.PARABOLA.01", "Quadratic profile at normalized one-third",
          "ExactSymbolicPass",
          Limit[(4/9 + 2/(3 k))/(1 + 1/k), k -> Infinity], 4/9,
          "Exact polynomial-ratio limit"],
        makeProofGoal["CHG-B13.DENSITY.02", "Quadratic decrease density",
          "ExactSymbolicPass",
          {Integrate[2 (1 - u), {u, 0, 1}],
            Integrate[u 2 (1 - u), {u, 0, 1}]}, {1, 1/3},
          "Exact integrals"],
        makeProofGoal["CHG-B13.QUANTILE.03", "Repair quantile identity",
          "ExactSymbolicPass",
          FullSimplify[(1 - (1 - alpha)^(1/2)) /. alpha -> 3/4], 1/2,
          "Exact p=2 quantile anchor"]
      }
    ],

    makeResultSpecification["CHG-B14", "Continuous support bifurcation and onset order", "CHG",
      "New theorem for the declared continuous family", True,
      "Crossing a phase boundary adds one positive position continuously from zero, with onset order q for 1<p<2 and order one for p>=2.",
      "Fixed integer phase k, p>1, ratio approaches the upper phase boundary from above.",
      source, "Support entry in the declared directional family.",
      "The onset is not an acoustic threshold or reranking theorem.",
      "Separate exact q>1, q=1, and q<1 series branches and coefficient anchors.",
      {
        makeProofGoal["CHG-B14.REGIMES.01", "Three onset exponents",
          "ExactConstructivePass",
          {powerConjugate[3/2], 1, 1}, {2, 1, 1},
          "Exact branch exponents at p=3/2,2,3"],
        makeProofGoal["CHG-B14.COEFFICIENT.02", "Quadratic leading coefficient",
          "ExactSymbolicPass",
          supportBirthCoefficient[2, 4], 1/25,
          "Exact B14 coefficient formula"],
        makeProofGoal["CHG-B14.CONTINUITY.03", "New coordinate is born at zero",
          "ExactSymbolicPass",
          Limit[Last[normalizedPhaseDecreases[2, 5, tau]], tau -> 1,
            Direction -> "FromBelow"], 0, "Exact one-sided limit"]
      }
    ],

    makeResultSpecification["CHG-B15", "Singular linear boundary and path-dependent tie selection", "CHG",
      "New theorem for the declared continuous family", True,
      "As p approaches one from above, fixed h/m selects the linear endpoints off equality and 1-exp(-1) on equality; joint approaches select the entire tie segment.",
      "Fixed finite N and positive ratio, with separate equality and off-equality paths.",
      source, "Singular p-to-one limit of the declared family.",
      "The selected point is not a canonical ontology or maximum-entropy rule.",
      "Exact exponential limits, variational minimizer, and set inequality.",
      {
        makeProofGoal["CHG-B15.EQUALITY.01", "Fixed-ratio equality selection",
          "ExactSymbolicPass",
          1 - Exp[-SeriesCoefficient[Log[1 + t], {t, 0, 1}]],
          1 - Exp[-1], "Exact symbolic limit"],
        makeProofGoal["CHG-B15.VARIATIONAL.02", "First-order selector",
          "ExactSymbolicPass",
          t /. First@Solve[D[t Log[t], t] == 0 && 0 < t < 1, t, Reals],
          Exp[-1], "Exact stationary point and interval premise"],
        makeProofGoal["CHG-B15.PATH.03", "Path-dependent tie member",
          "ExactSymbolicPass",
          Limit[1 - Exp[-(1 + c)], c -> 0], 1 - Exp[-1],
          "Exact joint-path anchor"],
        makeProofGoal["CHG-B15.UPCAST.04", "Limit winner set is strictly smaller",
          "ExactConstructivePass",
          MemberQ[{0, Exp[-1], 1}, 1/2], False,
          "Finite witness to forbidden set equality"]
      }
    ],

    makeResultSpecification["CHG-B16", "Hard-exponent support-magnitude separation", "CHG",
      "New theorem for the declared continuous family", True,
      "For fixed positive h/m and p tending to infinity, Kp is eventually two; throughout that eventual finite-p phase one follower remains strictly positive while its magnitude tends to zero logarithmically.",
      "Fixed positive ratio and finite positive horizon; finite-p positivity is asserted only when p (h/m) > 1.",
      source, "Hard-exponent limit of the declared directional family.",
      "Exact support at finite p and metric convergence are different queries.",
      "Exact limits, phase inequalities, and finite support anchors.",
      {
        makeProofGoal["CHG-B16.LAMBDA.01", "Logarithmic scale tends to zero",
          "ExactSymbolicPass",
          Limit[Log[p rho]/(p - 1), p -> Infinity,
            Assumptions -> rho > 0], 0, "Exact symbolic limit"],
        makeProofGoal["CHG-B16.ONEFOLLOWER.02", "One-follower exact expression",
          "ExactSymbolicPass",
          FullSimplify[1 - (1/(p rho))^(1/(p - 1)) ==
            1 - Exp[-Log[p rho]/(p - 1)],
            Assumptions -> p > 1 && rho > 0], True,
          "Exact logarithmic identity without a positivity upcast"],
        leanKernelProofGoal["CHG-B16.POSITIVITY.03",
          "Finite-p positivity phase equivalence",
          "The registered Lean theorem proves positivity exactly when p rho > 1; the former unrestricted finite-p wording has been withdrawn."],
        makeProofGoal["CHG-B16.SUPPORT.04", "Eventual finite-p support anchor",
          "ExhaustiveFinitePass",
          {supportIndexExact[5, 1, 10], supportIndexExact[5, 1, 20],
            supportIndexExact[5, 1, 50]}, {2, 2, 2},
          "Exact algebraic phase checks at three large exponents"],
        makeProofGoal["CHG-B16.NONCOMMUTE.05", "Finite positive anchor versus zero metric limit",
          "ExactConstructivePass",
          {1 - (1/2)^(1/(2 - 1)) > 0,
            Limit[Log[p rho]/(p - 1), p -> Infinity,
              Assumptions -> rho > 0] /. rho -> 1},
          {True, 0}, "Exact p=2 support anchor and exact hard-exponent magnitude limit"]
      }
    ]
  }
];

(* Contextual interaction, path-flux response, and support continuation *)

ClearAll[
  leanKernelProofGoal, powerRatioFromPhase, twoTriggerFreeSlopes,
  twoTriggerCentralSum, twoTriggerCenterValue, directionalPathEnergy,
  absolutePathEnergy, quadraticLedgerMatrix, gaugeDerivativeLowerBound,
  quadraticEdgePerturbation, contactGamma, raisedCosineKappa,
  contactResponseCoefficient, matchedDecayEquation,
  matchedContinuationCoefficient, buildContextSpecifications,
  buildFluxSpecifications, buildSupportSpecifications
];

leanKernelProofGoal[id_String, title_String, note_String] :=
  makeProofGoal[id, title, "LeanKernelProofReferenceCheck", True, True,
    "Pinned Lean declaration and evidence-bundle reference check; the proof itself is checked by the Lean kernel",
    True, note];

powerRatioFromPhase[supportIndex_Integer?Positive, phase_, exponentP_] :=
  Sum[(rank - 1 + phase)^powerConjugate[exponentP],
    {rank, 1, supportIndex}]^(exponentP - 1)/exponentP;

twoTriggerFreeSlopes[span_Integer?Positive, ratio_, exponentP_] :=
  Table[
    Sign[span + 1 - 2 index]
      (Abs[span + 1 - 2 index]/(2 exponentP ratio))^
        powerConjugate[exponentP],
    {index, span}
  ];

twoTriggerCentralSum[span_Integer?Positive, ratio_, exponentP_] :=
  Max[Accumulate[twoTriggerFreeSlopes[span, ratio, exponentP]]];

twoTriggerCenterValue[span_Integer?Positive, ratio_, exponentP_] :=
  Max[0, 1 - twoTriggerCentralSum[span, ratio, exponentP]];

directionalPathEnergy[path_List, ratio_, exponentP_] :=
  ratio Total[(positivePart /@ (Most[path] - Rest[path]))^exponentP] +
    Total[Rest[path]];

absolutePathEnergy[path_List, ratio_, exponentP_] :=
  ratio Total[Abs[Most[path] - Rest[path]]^exponentP] + Total[Rest[path]];

quadraticLedgerMatrix[distances_List, period_, curvature_, order_Integer?Positive] :=
  Table[
    Integrate[Sin[2 Pi harmonic curvature t/period], {t, 0, distance},
      Assumptions -> period > 0 && curvature > 0],
    {distance, distances}, {harmonic, order}
  ];

gaugeDerivativeLowerBound[curvature_, coefficients_List] :=
  curvature - 2 Pi Total[Range[Length[coefficients]] Abs[coefficients]];

quadraticEdgePerturbation[distance_, period_, curvature_, coefficients_List] :=
  Total[Table[
    coefficients[[harmonic]] Integrate[
      Sin[2 Pi harmonic curvature t/period], {t, 0, distance}],
    {harmonic, Length[coefficients]}]];

contactGamma[contactOrder_Integer?Positive, exponentP_] :=
  contactOrder Min[1, exponentP - 1];

raisedCosineKappa[index_Integer?NonNegative, responseScale_] :=
  (2 Pi)^(2 index)/((2 index + 1) Binomial[2 index, index]
    responseScale^(2 index));

contactResponseCoefficient[exponentP_, kappa_, responseScale_, activeA_,
    contactOrder_Integer?Positive] := Piecewise[{
  {kappa/responseScale, 1 < exponentP < 2},
  {(kappa/responseScale) (1 + activeA^(-contactOrder)), exponentP == 2},
  {kappa/(responseScale activeA^contactOrder), exponentP > 2}
}];

matchedDecayEquation[harmonyWeight_, markednessWeight_, exponentP_, lambda_] :=
  Times[
    harmonyWeight/markednessWeight,
    (1 - lambda)^(exponentP - 1),
    1 - lambda^(exponentP - 1)
  ] - lambda^(exponentP - 1);

matchedContinuationCoefficient[harmonyWeight_, exponentP_, lambda_] :=
  harmonyWeight (1 - lambda)^(exponentP - 1);

buildContextSpecifications[] := Module[{source},
  source = "Mathematical contribution, contextual interaction theorems";
  {
    makeResultSpecification["CTX-C1", "All-exponent two-trigger interaction", "CTX",
      "New theorem for the declared continuous family", True,
      "Two equal endpoint triggers reveal a half-phase support bit invisible to the one-trigger first-zero index.",
      "p>1, K>=1, 0<u<=1, equal endpoints, fixed positive edge/site ratio.",
      source, "Two-trigger support in the declared absolute-edge path family.",
      "No universal long-distance harmony or acoustic interaction claim.",
      "Exact phase conversion and finite witnesses; the arbitrary-parameter proof is separately exposed.",
      {
        makeProofGoal["CTX-C1.PHASE.01", "Exact low/high phase ratios",
          "ExactSymbolicPass",
          {powerRatioFromPhase[4, 1/4, 2],
            powerRatioFromPhase[4, 3/4, 2]}, {7/2, 9/2},
          "Exact phase-coordinate conversion"],
        makeProofGoal["CTX-C1.CENTER.02", "Center support separation",
          "ExactConstructivePass",
          {twoTriggerCenterValue[8, 7/2, 2],
            twoTriggerCenterValue[8, 9/2, 2]}, {0, 1/9},
          "Exact eight-edge center values"],
        makeProofGoal["CTX-C1.CARRIER.03", "Two-bit carrier witness",
          "ExhaustiveFinitePass",
          {{4, Boole[1/4 > 1/2]}, {4, Boole[3/4 > 1/2]}},
          {{4, 0}, {4, 1}}, "Exact minimality-side witness"],
        leanKernelProofGoal["CTX-C1.GENERAL.04",
          "Arbitrary-p,K support-regime proof",
          "The arbitrary-p,K KKT and phase theorem is checked by the registered Lean declarations; Wolfram verifies their exact reference metadata."]
      }
    ],
    makeResultSpecification["CTX-C2", "Direction is not identified by one-trigger winners", "CTX",
      "Project-derived supporting theorem", True,
      "Directional and absolute edge penalties share every one-trigger winner but differ on complete orders and opposite-trigger support.",
      "p>1 and complete declared candidate/order queries; opposite endpoint probe for direction.",
      source, "Evaluator direction under one- and two-trigger probes.",
      "Winner coincidence does not imply margin, preorder, or evaluator identity.",
      "Exact order reversal and shortest binary support witness.",
      {
        makeProofGoal["CTX-C2.ORDER.01", "Finite complete-order reversal",
          "ExactConstructivePass",
          Module[{a = {1, 0, 1/2}, b = {1, 1, 0}},
            {{directionalPathEnergy[a, 3, 2], directionalPathEnergy[b, 3, 2]},
              {absolutePathEnergy[a, 3, 2], absolutePathEnergy[b, 3, 2]}}],
          {{7/2, 4}, {17/4, 4}}, "Exact two-candidate reversal"],
        makeProofGoal["CTX-C2.SHORTEST.02", "Shortest opposite-trigger separator",
          "ExactConstructivePass",
          Module[{rho = powerRatioFromPhase[2, 1/4, 2]},
            {Rest[quadraticProfile[rho, 1, 2]],
              {twoTriggerCenterValue[3, rho, 2],
                twoTriggerCenterValue[3, rho, 2]}}],
          {{1/6, 0}, {1/3, 1/3}}, "Exact K=2,u=1/4 separator"],
        leanKernelProofGoal["CTX-C2.GENERAL.03",
          "All-one-trigger winner equivalence and shortestness",
          "The running-minimum and arbitrary-K shortestness theorems are checked by the registered Lean declarations; Wolfram verifies their exact reference metadata."]
      }
    ]
  }
];

buildFluxSpecifications[] := Module[{source},
  source = "Mathematical contribution, constitutive response and identification theorems";
  {
    makeResultSpecification["FLUX-D1", "Fixed-load path-flux equivalence", "FLUX",
      "New constitutive-gauge theorem", True,
      "On arbitrary complete box-path families, strict monotonicity and the fixed-load shift law preserve winners relative to baseline and transformed exact path-KKT contracts; conversely, winner equality over the complete free two-edge probe family forces the shift law.",
      "Fixed load and strict monotonicity; separate baseline and transformed exact path-KKT iff global-winner contracts. Sufficiency ranges over arbitrary complete box-path families; necessity is only for complete free two-edge winner-probe families.",
      source, "Path-winner response at one declared load.",
      "Finite candidate preorders and margins are not preserved automatically.",
      "Exact shift, derivative, convexity, and finite reversal proofs.",
      {
        makeProofGoal["FLUX-D1.SHIFT.01", "Periodic flux shift",
          "ExactSymbolicPass",
          FullSimplify[pathFluxDeformation[y + delta, delta, epsilon] -
            pathFluxDeformation[y, delta, epsilon],
            Assumptions -> delta > 0], delta, "Exact trigonometric period"],
        makeProofGoal["FLUX-D1.POTENTIAL.02", "Integrated marginal identity",
          "ExactSymbolicPass",
          FullSimplify[D[pathFluxPotential[d, c, delta, epsilon], d] ==
            pathFluxDeformation[c d, delta, epsilon],
            Assumptions -> c > 0 && delta > 0], True,
          "Exact symbolic differentiation"],
        makeProofGoal["FLUX-D1.REVERSAL.03", "Candidate-order nonpreservation",
          "ExactConstructivePass",
          FullSimplify[1/100 + (-9 + Sqrt[5])/(32 Pi^2) < 0], True,
          "Exact algebraic-transcendental sign proof"],
        leanKernelProofGoal["FLUX-D1.NECESSITY.04", "Unrestricted-probe necessity",
          "Lean checks arbitrary complete box-path sufficiency and complete free two-edge winner-probe necessity relative to separate baseline and transformed exact KKT-to-winner contracts."]
      }
    ],
    makeResultSpecification["FLUX-D2", "Multiple-load and topology rigidity", "FLUX",
      "New constitutive-gauge theorem", True,
      "Commensurate loads retain a common periodic gauge. Identity follows either from two complete free two-edge winner-probe families at loads with irrational ratio, continuous F with F(0)=0, and separate baseline/transformed exact path-KKT contracts, or from complete degree-three star winner equality, continuous odd F, a nonzero load, and separate baseline/transformed exact star-KKT contracts.",
      "The two-path branch requires complete free two-edge winner equality at both loads, separate baseline/transformed exact path-KKT iff global-winner contracts, continuity, F(0)=0, and an irrational load ratio. The star branch requires complete degree-three winner equality, separate baseline/transformed exact star-KKT iff global-winner contracts, continuity, oddness, and a nonzero load.",
      source, "Multiple-load and branching response architecture.",
      "A finite load set with rational ratios does not identify the constitutive law.",
      "Exact common period and star-gradient witness; density/Cauchy antecedents exposed.",
      {
        makeProofGoal["FLUX-D2.PERIOD.01", "McCollum common rational period",
          "ExactSymbolicPass", {1/5/(1/105), 1/21/(1/105)}, {21, 5},
          "Exact integer period ratios"],
        makeProofGoal["FLUX-D2.STAR.02", "Star additivity defect",
          "ExactConstructivePass", -epsilon/Pi /. epsilon -> 1/2,
          -1/(2 Pi), "Exact boxed-star gradient"],
        leanKernelProofGoal["FLUX-D2.RIGIDITY.03", "Dense periods and continuous Cauchy rigidity",
          "Lean checks two-path rigidity under two complete free-probe winner families, separate exact path-KKT contracts, continuity, F(0)=0 and irrational load ratio; it separately checks star rigidity under complete star-winner equality, separate exact star-KKT contracts, continuity, oddness and nonzero load."]
      }
    ],
    makeResultSpecification["FLUX-D3", "Finite-ledger constitutive nonidentification", "FLUX",
      "New exact nonidentification theorem", True,
      "For each finite score ledger at commensurate loads, a nonidentity analytic periodic gauge can preserve every registered score while changing an unregistered one.",
      "Finite edge-difference ledger and strictly increasing quadratic baseline.",
      source, "Finite score and fixed-support probability audits.",
      "No single alternative is claimed invisible to every possible finite ledger.",
      "Exact nullspace construction and unregistered witness.",
      {
        makeProofGoal["FLUX-D3.NULL.01", "Quadratic ledger null vector",
          "ExactConstructivePass",
          quadraticLedgerMatrix[{1/3, 1/4}, 1, 1, 3].{1/3, -2/3, 1},
          {0, 0}, "Exact trigonometric integrals"],
        makeProofGoal["FLUX-D3.MONOTONE.02", "Strict derivative lower bound",
          "ExactSymbolicPass",
          Module[{raw = {1/3, -2/3, 1}, scale},
            scale = 1/(20 Pi Total[Range[3] Abs[raw]]);
            gaugeDerivativeLowerBound[1, scale raw]], 9/10,
          "Triangle-inequality lower bound"],
        makeProofGoal["FLUX-D3.UNREGISTERED.03", "Unregistered score changes",
          "ExactConstructivePass",
          Module[{raw = {1/3, -2/3, 1}, scale},
            scale = 1/(20 Pi Total[Range[3] Abs[raw]]);
            FullSimplify[2 quadraticEdgePerturbation[1/8, 1, 1, scale raw]]],
          1/(280 Pi^2), "Exact held-out edge difference"],
        leanKernelProofGoal["FLUX-D3.GENERAL.04", "Arbitrary-marginal finite-ledger construction",
          "The registered Lean theorem closes the arbitrary-marginal finite-ledger construction under its declared assumptions; Wolfram separately checks the quadratic witness and Lean reference metadata."]
      }
    ],
    makeResultSpecification["FLUX-D4", "Support-boundary contact response", "FLUX",
      "New singular-response theorem", True,
      "Every positive odd contact is realized by the declared analytic fixed-load gauge; conditional on the registered normalized remainder, its support response has the corrected logarithmic balance and canonical Lambert normal form.",
      "Positive gauge period, p>1, positive coefficient, positive odd contact, eventually positive scale tending to zero, and normalized remainder tending to zero.",
      source, "Conditional analytic-gauge response at the registered normalized-remainder interface.",
      "The theorem does not derive the normalized remainder from a KKT contact-germ model; that former derivation is withdrawn from the dissertation theorem set.",
      "Exact scale, coefficient anchors, all-order odd-contact gauge, quotient balance, positive Lambert branch, and normalized-remainder response proofs.",
      {
        makeProofGoal["FLUX-D4.SCALES.01", "Drop and response scales",
          "ExactSymbolicPass", FullSimplify[m/h == p (m/(h p)),
            Assumptions -> h != 0 && p != 0], True, "Exact scale conversion"],
        makeProofGoal["FLUX-D4.COEFFICIENTS.02", "Kazakh regular and cubic contacts",
          "ExactSymbolicPass",
          {contactResponseCoefficient[2, raisedCosineKappa[0, 1/10], 1/10, 4, 1],
            contactResponseCoefficient[2, raisedCosineKappa[1, 1/10], 1/10, 4, 3]},
          {25/2, 8125 Pi^2/12}, "Exact raised-cosine coefficients"],
        makeProofGoal["FLUX-D4.NORMALFORM.03", "Lambert normal-form identity",
          "ExactSymbolicPass",
          Module[{w = ProductLog[gamma c/epsilon], t},
            t = (epsilon w/(gamma c))^(1/gamma);
            FullSimplify[c t^gamma/(-Log[t]) == epsilon,
              Assumptions -> c > 0 && epsilon > 0 && gamma > 0 &&
                gamma c/epsilon > 1]], True,
          "Exact ProductLog defining identity"],
        leanKernelProofGoal["FLUX-D4.PERTURBATION.04", "Normalized-remainder support response",
          "The Wolfram source catalogue does not encode this limit proof; the registered Lean theorem closes the narrowed normalized-remainder conditional."]
      }
    ],
    makeResultSpecification["FLUX-D5", "Finite response fibres and accumulating-response tomography", "FLUX",
      "New exact identification theorem", True,
      "For the declared affine-winner, support-birth, finite-jet, and finite-score audits at explicit raised-cosine baselines, nontrivial periodic analytic perturbations preserve the registered finite data; an accumulating exact response in one connected analytic domain identifies the normalized law.",
      "The declared finite audit and explicit raised-cosine baselines; a connected common analytic domain for accumulating-response tomography.",
      source, "Finite versus accumulating constitutive response queries.",
      "The finite construction is audit-relative; the analytic identity theorem is an external antecedent.",
      "Exact finite perturbation and recurrence; identity-theorem step exposed.",
      {
        makeProofGoal["FLUX-D5.FINITE.01", "Finite audit perturbation witness",
          "ExactConstructivePass",
          Module[{primitive, marginal, z},
            primitive[z_] = Sin[2 Pi z] (1 - Cos[2 Pi z])^3
              (1 - Cos[2 Pi (z - 1/4)])^2;
            marginal[z_] = D[primitive[t], t] /. t -> z;
            {primitive[0], primitive[1/2],
              Table[D[marginal[z], {z, order}] /. z -> 1/4,
                {order, 0, 2}], FullSimplify[primitive[1/8] != 0]}],
          {0, 0, {0, 0, 0}, True}, "Exact periodic analytic construction"],
        makeProofGoal["FLUX-D5.RECURRENCE.02", "Response recurrence value",
          "ExactSymbolicPass",
          Fzi == mu (1 + epsilon) Sum[x[j]^epsilon, {j, i, n}],
          Fzi == mu (1 + epsilon) Sum[x[j]^epsilon, {j, i, n}],
          "Typed recurrence retained exactly"],
        leanKernelProofGoal["FLUX-D5.IDENTITY.03", "Accumulating-set analytic identity theorem",
          "The inherited analytic identity step is explicit and the project-specific consequence is replayed by Lean."]
      }
    ]
  }
];

buildSupportSpecifications[] := Module[{source},
  source = "Mathematical contribution, support and continuation theorems";
  {
    makeResultSpecification["SUP-E1", "Endpoint slope classifies exact support", "SUP",
      "New support theorem", True,
      "Zero endpoint site slope forces every finite winner positive; positive endpoint slope and finite edge slope impose a uniform finite positive-prefix bound.",
      "Printed differentiability, convexity, strict-increase, and endpoint-slope premises, together with an explicit ExactEndpointWinnerKKT contract equating the complete endpoint KKT package with the global-winner predicate for the concrete objective.",
      source, "General local directional edge/site objective.",
      "The theorem does not classify arbitrary nondifferentiable or nonlocal penalties.",
      "Exact perturbation derivative and integer bound; general convex proof exposed.",
      {
        makeProofGoal["SUP-E1.DERIVATIVE.01", "Zero-lifting right derivative",
          "ExactSymbolicPass", -phiPrimeA + phiPrime0 + psiPrime0,
          -phiPrimeA + phiPrime0 + psiPrime0, "Exact local derivative skeleton"],
        makeProofGoal["SUP-E1.BOUND.02", "Strict-prefix integer bound",
          "ExactConstructivePass",
          {Ceiling[10/3] - 1, 3 < 10/3, 4 < 10/3}, {3, True, False},
          "Exact strict-inequality integer conversion"],
        leanKernelProofGoal["SUP-E1.GENERAL.03", "Arbitrary-convex-function support proof",
          "The running-minimum and endpoint-derivative lemmas are checked by the registered Lean declarations; Wolfram verifies their exact reference metadata."]
      }
    ],
    makeResultSpecification["SUP-E2", "All-positive free-end winners are not projective", "SUP",
      "New projectivity theorem", True,
      "Appending a free endpoint changes an all-positive prefix, whereas an attained terminal zero licenses exact zero-extension projectivity.",
      "Strict edge convexity, positive site derivative, unique finite winners.",
      source, "Finite free-end horizons in the local directional family.",
      "Zero-extension projectivity begins only after an exact terminal zero.",
      "Exact contradiction and quadratic/zero-tail witnesses.",
      {
        makeProofGoal["SUP-E2.CONTRADICTION.01", "Terminal/interior equation contradiction",
          "ExactSymbolicPass",
          Resolve[ForAll[{a, b, c, d},
            (a == b && a - c == b && c == d && d > 0) \[Implies] False], Reals],
          True, "Exact scalar elimination"],
        makeProofGoal["SUP-E2.QUADRATIC.02", "One-to-two follower prefix change",
          "ExactConstructivePass",
          Module[{one, two},
            one = x /. First@Solve[D[(1 - x)^2 + x^2, x] == 0, x];
            two = {x1, x2} /. First@Solve[{
              D[(1 - x1)^2 + (x1 - x2)^2 + x1^2 + x2^2, x1] == 0,
              D[(1 - x1)^2 + (x1 - x2)^2 + x1^2 + x2^2, x2] == 0},
              {x1, x2}];
            {{1, one}, Prepend[two, 1]}],
          {{1, 1/2}, {1, 2/5, 1/5}},
          "Exact matched-power free-end witness"],
        makeProofGoal["SUP-E2.ZEROEXTEND.03", "Post-extinction exact prefix stability",
          "ExactConstructivePass",
          {quadraticProfile[5, 1, 4], Take[quadraticProfile[5, 1, 7], 5]},
          {{1, 3/5, 3/10, 1/10, 0}, {1, 3/5, 3/10, 1/10, 0}},
          "Exact extension-stable zero tail"]
      }
    ],
    makeResultSpecification["SUP-E3", "Matched-power geometric persistence", "SUP",
      "New infinite-horizon theorem", True,
      "Matched edge and site powers yield a unique geometric ell-p profile with an exact scalar decay equation and closed continuation energy.",
      "p>1, positive h,m, ell-p admissibility, infinite directional chain.",
      source, "Infinite matched-power directional objective.",
      "The result does not apply to the original linear-site McCollum grammar.",
      "Exact scalar equation, quadratic root, and energy identity; direct-method antecedent exposed.",
      {
        makeProofGoal["SUP-E3.ROOT.01", "Quadratic golden-ratio decay",
          "ExactSymbolicPass",
          FullSimplify[matchedDecayEquation[1, 1, 2, (3 - Sqrt[5])/2]], 0,
          "Exact radical substitution"],
        makeProofGoal["SUP-E3.ENERGY.02", "Continuation energy identity",
          "ExactSymbolicPass",
          FullSimplify[
            ((h (1 - lambda)^p + m lambda^p)/(1 - lambda^p) ==
              h (1 - lambda)^(p - 1)) /.
              m -> h (1 - lambda)^(p - 1)
                (1 - lambda^(p - 1))/lambda^(p - 1),
            Assumptions -> h > 0 && p > 1 && 0 < lambda < 1], True,
          "Exact algebra under the scalar decay equation"],
        leanKernelProofGoal["SUP-E3.EXISTENCE.03", "Infinite-dimensional direct method",
          "The registered Lean theorem checks the declared weak-compactness, lower-semicontinuity, and Bellman-uniqueness dependencies relative to its explicit foundation parameters; Wolfram verifies the reference metadata."]
      }
    ],
    makeResultSpecification["SUP-E4", "Exact continuation and McCollum repair", "SUP",
      "New continuation theorem", True,
      "One terminal coefficient exactly replaces the optimized tail and makes every finite matched-power prefix projective.",
      "Matched-power family and terminal term tau x_N^p.",
      source, "Finite exact continuation of the E3 infinite winner.",
      "Uniqueness is only within the declared monomial terminal family.",
      "Exact coefficient, Euler endpoint, and fixed-profile repair.",
      {
        makeProofGoal["SUP-E4.COEFFICIENT.01", "Continuation coefficient identity",
          "ExactSymbolicPass",
          FullSimplify[
            (h (1 - lambda)^(p - 1)/lambda^(p - 1) - m ==
              matchedContinuationCoefficient[h, p, lambda]) /.
              m -> h (1 - lambda)^(p - 1)
                (1 - lambda^(p - 1))/lambda^(p - 1),
            Assumptions -> h > 0 && p > 1 && 0 < lambda < 1], True,
          "Exact terminal stationarity"],
        makeProofGoal["SUP-E4.REPAIR.02", "Kazakh first-follower repair",
          "ExactConstructivePass",
          {matchedDecayEquation[15/4, 1, 2, 3/5],
            matchedContinuationCoefficient[15/4, 2, 3/5],
            Table[(3/5)^index, {index, 0, 5}]},
          {0, 3/2, {1, 3/5, 9/25, 27/125, 81/625, 243/3125}},
          "Exact repaired profile and continuation"],
        makeProofGoal["SUP-E4.TRILEMMA.03", "Linear-site versus matched-power support",
          "ExactConstructivePass",
          {quadraticProfile[5, 1, 5], Table[(3/5)^index, {index, 0, 5}]},
          {{1, 3/5, 3/10, 1/10, 0, 0},
            {1, 3/5, 9/25, 27/125, 81/625, 243/3125}},
          "Exact phonologically readable contrast"]
      }
    ]
  }
];

(* Embedded canonical decision ledgers.  Each string is a build-time
   Compress[HoldComplete[...]] result; runtime verifies the adjacent
   canonical-expression SHA-256 before using any row. *)

$ptR1Compressed = "1:eJytWU1vGzcQdZMU6Fd8KNBLL3XPQQEOZ0gOz0WBGAiaIuqlp4VirewF1pIhre0gt/6n/oT+hP6IXgv0B3S4shvH3o2G3NiGIK1tPQ0f35s33O9fr18tPzk4ONh+JQ/P1+3ix/X5RVt39fJJupoeXjTbbvatPPllvekuTy/rbX20qE+abbNeHbX14rTeNOktlp++9x+fy5PrZrVYX1fNYvZUXr2erxZVu76uN9XZ2/7K9mS9qaur+aaZr7pZ+gjn9UKeV4u67eazb+TCor6q2/XFeb3qqtN5V1cX8+12+fwu1D3g9MbL5k29qF5YU718Zpp/5ePN0u+Xl227fJT++jN5eDXvpIR5e5yAIco3uhACQ3/BmXdfs8dy4befZjqkr+VyW8+v6mrZzrtVvd1W68tuAPdLeYGG2YP8APav78DO0n/8/DIX9Kw5PUvL/AFQb4AoRutuarXFtT79H/btyWYEsUcAi05qteCxfHn/fryfSALy8p6AweFxegswxVBqJvsdhMSIjmRtdyVaNx1XQWaQrQORASiWk9nDasmEwOyQnXOkJvPwHiQoZeltYBuBAkftoo5BZbHpwUdLngV9aBsNSnM/8IfpbH7/7q9fj794r8rMGjUUpk0ThTtrxO5i2K3znXVVF6eRI6CJGIw4nA8TCMyXo/McQ2TP3oUJBObpsa/YkDPRMDkc8IEsXK0gEQOKUAA9RG2t9zzgB6fToxE9epYCSU3nCFJWm2QgCyT7FQf2ayHsHi6TDp1lS8agjf2nAOdvcfNA1UTa4Jg8OOuHiNRiqoRpPJMRj7td0iImC9qkkc0qXHpf3K8e4mrapEjSB2ORw0NYpULyRGlZFMlis1zM5TOlKkmSK0TjxABKo0euKndrKOGDbDD+xg0KUl2uLPt6mSWuu+AiTMXVsulSGxOXJTHACWyqEqw3SNaT+OxkqDw6wXppXiC5oHgGypVmctkYUPKdgRB2I9E7c88D1XJJGClZnyR1KFlgzBgrDUUv+RU9lygTS8bK3TjrxXesScmggMphXIUyMchU2ZssT15aNZ2eGb34eyyTJuqHS5CmxSFixCLDw5LZspdEMNGjNWTxZltNh9VFWUBLYrVDUTYLVzuYiMFKJ5Ph/aZSRTo4vIeoHS3FZ4wFTtUpE8EYUp7LuiCbyKK/xXUfAVdz6CPhkli2LoI2Qo/hqg8KfJQoaz0OTu/aUlXCBIqENsXnkjETi8dM8skQ0gGF0ae8/cgKPvuNKz9k1Nocw1VHWuFRRmoUTtWHIvf9QJdoLUVn2AThtNhoS+ZMyQTeonitJIP0mgrLy7JZkpkoWmnVgEWTAhbk2WQGkRFkoI/lC6ySpoR0cYEYIpSkSixPsxSBxX34I+JqIhDFAD7JEsojUEai7bepRevASobGAm+njK7pPLAMXsyW9cfrY1hZ0owp5KVjRDNw02JfLxmB1YjTBtm+UczITy9Y3ThdCE6adSCrPa0YgNynzr6L+HQUjBLZB4DUxWWps/nn6PBRc/DHn0+KARTtER3IFM2OTZwgiSwVSvNIp6NoIT64l7dX9qRvjhQiidiBCItucVFJd9ylLGYI7GIYOszf1x+HYTWO6pzkZYBgMzLWCLBWgYGcS6cwId3NK8fUNEj0NhpRoBebmQqVF3YkP8qcLltpd/Di99522ouqYdM4aSBWYlaGoY4Aa5UpWcek8cCZcZf7D0caP2Q=";
$ptR1CanonicalHash = "36a2aa7cc25d5d2ce19f852ee87ac8d4c40848b40926dedbca0874386e3cbd19";
$enSpeakerR1Compressed = "1:eJy03U2v5ud1pfcdIMiASJAA4QdwkHEASmSR4lCwFXQDbrvREpIhobSpjtBqS7DUg3znjDV1qHJO0ee/1wZ4WOs3MfTSupq4rzr7Wee+93rqf/m/fv8ffvPfzMwf//vv/s+/+f3v/uGvf/9f/vC7b//07W/+27/8p3/5P3/72z/+6Zf/63f/4hf/+J9+99s//t9/9cc/fPvr//ztP/1vf/yP3/7jr//pt7//q//87f/zV7/79h/+07f/9Nu/sH7z3736n/4Pf/l3//I/+eaPf/jdb//0y0/+1X/y2394/2//9E+//o///7/9H//y3/7p1//0p29+/5vf/PHbP33zX/74nvHtP/7Dv/pP/ufv/pM//Pq33yH/6x/+8Pvv/h9/9z/503/942+++upf/f/9+Cf5n777F3/993/3v//b//Dvfv6rf/v3f/fN3//N3/zyL//tH37603fv/zF+9cW7zz775v/87Kfvfvv//vM///P7//PLT7/7L/79z3/5y29+/qtv/vYXP//lr7754ptf/Pyv/81H0/9M6d/9R+Pon1D6p4r+Z2r1z9Tqn6nVP1Orf/nHduf+ns7O/T2dnft7uj139tP0CbX6CbX6CbX6CbX6CbX6KbX6KbX6KbX6KbX6KbD6HRzmmQe9bPVBL1t90MtWH3RmVeSZB51ZFXnmQWdW/0ytDpjADzqzOmACP+jM6tAJLNLSg86sirT0oDOrIi19Txdp6UFnVkVaetCZVZiWPv9MpqUXurH6QjdWX+jG6gudWYVp6YXOrMK09EJnVmFa+o4+bgK/0JnVcRP4hc6sDp3AMC290JlVmJZe6MwqTEvf0WFaeqEzqzAtvdCZVZKW6FvZg962St/KHvS2VfpW9j2dpCX6VvagM6skLb2mM6sjJjB9iXvQmdURE5i+xH1PJ2mJvsQ96MwqSUv0Je57OklL9CXuQWdWSVqyL3Hv6N3Sa7qxqu6WXtONVXW39IEO05K6W3pNZ1ZhWlJ3Sx/o4yawult6TWdWx01gdbf0gQ7Tkrpbek1nVmFaUndLH+gwLam7pdd0ZhWmJXS39CXdW3rQy1Yf9LLVB71s9UFnVkVaetCZVZGWHnRmVaSl7+kDJvCDzqwOmMAPOrM6dAKLtPSgM6siLT3ozKpIS9/TRVp60JlVkZYedGa1mpa+eu6QV9NSpresZnrLaqa3rGY6s1pNS5nOrFbTUqYzq9W0tOjTnMCZzqxOcwJnOrM6dAJX01KmM6vVtJTpzGo1LS16NS1lOrNaTUuZzqyKtIQ6cZletoo6cZletoo6cYsu0hLqxGU6syrSEurELfqACYw6cZnOrA6YwKgTt+giLaFOXKYzqyItoU7coou0hDpxmc6sirSEOnGv6e29pUw3Vtt7S5lurLb3lhYdpqX23lKmM6swLbX3lhZ93ARu7y1lOrM6bgK395YWHaal9t5SpjOrMC2195YWHaal9t5SpjOrMC2195Ze6PQlDnXiMr1tlb7EoU7copO0RF/iUCcu05lVkpboSxzqxGU6szpiAtOXONSJy3RmlaQl+hKHOnGLTtISfYlDnbhMZ1ZhWlJ3S6YTl+nGqrpbMp24RYdpSd0tmU5cpjOrMC2puyXTict0ZnXcBFZ3S6YTl+nMKkxL6m7JdOIWHaYldbdkOnGZzqyKtIRaa5lePnfUWlt0kThQryzT2bkPmASom5Xp7GTEJx/qN2U6Oxnx6YE6QpneOpmvn3up1Qmc6a1Pj0WvzshMZydT/b0p09m5VydwprNzr87ITLf/7GwSVH87yHT2J7I637+m+++ZXj53tEOe6exkqjky09m5ixmJtrwzvfyzijalM52djJjAaNs409nJiJSKdmoznf2zwwncfjvIdDMj27f7iw4ncPt2P9PZycAJ3L4hz3T2syoyMNqPzHR27na+V++wM73902T2IzO9bdXsR2Y6O3fyuUpvf9AG46KPmARmTy/T25PA7OktOvlcpXdLaE8v05lV8rlqNuky3Zx7exst083JqN/KzL7YosPPJvU7n9kXW/RxP03trahMN1NM/c5ntqIynVmFn03qdz6zt5Tp7NztZ5P4rQx923aml88d7S1levnPO/q27UUXn6toKyrTmVVxU4u+bXvRB8xItNGV6czqezqzOnQCi8SBttEynVkViQN92/aiizyDNukynVkVd9jm27Y//0nc0ytZPeglqwe9ZPWgl6wedGa1mZYOOrPaTEsHnVltpqVNn+IEPujM6hQn8EFnVodO4GZaOujMajMtHXRmtZmWNr2Zlg46s9pMSwedWRVp6R25WzroZavvyN3SQS9bfUfuljZdpCWzKX3QmVWRlt6Ru6VNHzCBzR72QWdWB0xgs0O+6SItmR3yg86sirT0jtwtbbpIS2b//aAzqyIt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";
$enSpeakerR1CanonicalHash = "207de1eb5828d73ac5a7cde58d757323d9a8aa3dc21316df3f31552f200e5c6e";
$enAggregateR1Compressed = "1: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";
$enAggregateR1CanonicalHash = "623b1176eac74c2d180751283d7876827ac572c8553065ae6e245d30925d2f7f";
$zhR1Compressed = "1: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";
$zhR1CanonicalHash = "4ab03d13b87baba97100f1671c20db0c05af24698a960c3733392abe1006b19c";

(* Selected-output geometry and finite-MaxEnt response algebra *)

ClearAll[
  positiveRayMultipleQ, binaryNetworkHarmony, exactMetricProjection,
  collectIntegerPolynomial, polynomialToUnitMassLedgers,
  compiledPartitionDifference, strictOTWinnerIndex,
  basicSyllableProof, multiIndices, interpolationDegree,
  mixedRadixDirection, primitiveIntegerCoefficientList,
  orderedContactPolynomial, contactPhasePolynomial,
  unbalancedInteriorContactPolynomial, balancedInteriorContactPolynomial,
  probabilityFromMassVector, buildSelectedSpecifications,
  buildMaxEntSpecifications
];

positiveRayMultipleQ[vector_List, reference_List] := Module[{position, ratio},
  If[Length[vector] =!= Length[reference] || reference === ConstantArray[0, Length[reference]],
    Return[False]];
  position = FirstPosition[Boole[# =!= 0] & /@ reference, 1, Missing["Zero"]];
  If[MissingQ[position], Return[False]];
  ratio = vector[[First[position]]]/reference[[First[position]]];
  TrueQ[ratio > 0 && vector === ratio reference]
];

binaryNetworkHarmony[input_List, output_List, faithfulness_, markedness_] :=
  input.faithfulness.output + output.markedness.output;

exactMetricProjection[normals_List, thresholds_List, metric_] := Module[
  {inverseMetric, gram, multipliers, point, distanceSquared},
  inverseMetric = Inverse[metric];
  gram = Simplify[normals.inverseMetric.Transpose[normals]];
  multipliers = Simplify[Inverse[gram].thresholds];
  point = Simplify[inverseMetric.Transpose[normals].multipliers];
  distanceSquared = Simplify[thresholds.multipliers];
  <|"Gram" -> gram, "Multipliers" -> multipliers,
    "Point" -> point, "DistanceSquared" -> distanceSquared|>
];

collectIntegerPolynomial[polynomial_, variables_List] := Module[{rules},
  rules = CoefficientRules[Expand[polynomial], variables];
  If[! AllTrue[Last /@ rules, IntegerQ],
    Failure["NonIntegerCoefficients", <||>], rules]
];

polynomialToUnitMassLedgers[polynomial_, variables_List] := Module[
  {rules, positiveRows, negativeRows},
  rules = collectIntegerPolynomial[polynomial, variables];
  If[FailureQ[rules], Return[rules]];
  positiveRows = Flatten[Table[
    ConstantArray[First[rule], Max[Last[rule], 0]], {rule, rules}], 1];
  negativeRows = Flatten[Table[
    ConstantArray[First[rule], Max[-Last[rule], 0]], {rule, rules}], 1];
  <|"Variables" -> variables, "PositiveRows" -> positiveRows,
    "NegativeRows" -> negativeRows,
    "AlternativeCount" -> Length[positiveRows] + Length[negativeRows]|>
];

compiledPartitionDifference[compilation_Association, variables_List] :=
  Expand[
    Total[(Times @@ (variables^#)) & /@ compilation["PositiveRows"]] -
    Total[(Times @@ (variables^#)) & /@ compilation["NegativeRows"]]
  ];

strictOTWinnerIndex[rows_List, ranking_List] :=
  First@SortBy[Range[Length[rows]], rows[[#, ranking]] &];

basicSyllableProof[] := basicSyllableProof[] = Module[
  {tensor, rankings, winnerMaps, mappingEvents, mappingKeys,
    allPairs, nonreflexivePairs, universalAll, universalNonreflexive,
    emptyMappings, liveImplications},
  tensor = {
    {{0, 0, 0, 0}, {0, 1, 1, 0}, {1, 0, 0, 1}, {1, 1, 1, 1}},
    {{0, 0, 0, 1}, {0, 1, 0, 0}, {1, 0, 0, 2}, {1, 1, 0, 1}},
    {{0, 0, 1, 0}, {0, 1, 2, 0}, {1, 0, 0, 0}, {1, 1, 1, 0}},
    {{0, 0, 1, 1}, {0, 1, 1, 0}, {1, 0, 0, 1}, {1, 1, 0, 0}}
  };
  rankings = Permutations[Range[4]];
  winnerMaps = Table[
    Table[strictOTWinnerIndex[tensor[[input]], ranking], {input, 4}],
    {ranking, rankings}];
  mappingKeys = Flatten[Table[{input, output}, {input, 4}, {output, 4}], 1];
  mappingEvents = Association@Table[
    key -> Select[Range[Length[rankings]],
      winnerMaps[[#, key[[1]]]] == key[[2]] &], {key, mappingKeys}];
  allPairs = Tuples[mappingKeys, 2];
  nonreflexivePairs = Select[allPairs, #[[1]] =!= #[[2]] &];
  universalAll = Select[allPairs,
    SubsetQ[mappingEvents[#[[2]]], mappingEvents[#[[1]]]] &];
  universalNonreflexive = Select[nonreflexivePairs,
    SubsetQ[mappingEvents[#[[2]]], mappingEvents[#[[1]]]] &];
  emptyMappings = Select[mappingKeys, mappingEvents[#] === {} &];
  liveImplications = Select[universalNonreflexive,
    mappingEvents[#[[1]]] =!= {} &];
  <|"Tensor" -> tensor, "RankingCount" -> Length[rankings],
    "DistinctWinnerMaps" -> Sort@DeleteDuplicates[winnerMaps],
    "MappingEvents" -> mappingEvents,
    "UniversalIncludingReflexiveCount" -> Length[universalAll],
    "NonreflexiveUniversalCount" -> Length[universalNonreflexive],
    "EmptyMappingCount" -> Length[emptyMappings],
    "EmptyAntecedentCount" -> Length[universalNonreflexive] - Length[liveImplications],
    "LiveAntecedentCount" -> Length[liveImplications],
    "LiveImplications" -> liveImplications|>
];

multiIndices[dimension_Integer?Positive, degree_Integer?NonNegative] :=
  Select[Tuples[Range[0, degree], dimension], Total[#] <= degree &];

interpolationDegree[support_List] := Module[{degree = 0, matrix},
  While[True,
    matrix = Table[Times @@ MapThread[If[#2 == 0, 1, #1^#2] &,
        {point, alpha}],
      {alpha, multiIndices[Length[First[support]], degree]}, {point, support}];
    If[MatrixRank[matrix] == Length[support], Return[degree]];
    degree++
  ]
];

mixedRadixDirection[bounds_List] :=
  FoldList[Times, 1, Most[bounds + 1]];

primitiveIntegerCoefficientList[polynomial_, variable_] := Module[
  {coefficients, denominatorScale, integers, divisor, sign},
  coefficients = CoefficientList[Expand[polynomial], variable];
  denominatorScale = LCM @@ (Denominator /@ coefficients);
  integers = denominatorScale coefficients;
  divisor = GCD @@ Abs[DeleteCases[integers, 0]];
  integers = integers/divisor;
  sign = Sign[First[DeleteCases[integers, 0]]];
  sign integers
];

orderedContactPolynomial[contactRoots_List, multiplicities_List,
    reversalRoots_List, variable_] := Expand[
  variable Times @@ MapThread[(variable - #1)^#2 &,
    {contactRoots, multiplicities}] Times @@ (variable - # & /@ reversalRoots)
];

contactPhasePolynomial[contact_Integer?NonNegative, reversals_Integer?NonNegative,
    spacing_Integer?Positive, variable_] := Expand[
  (-1)^reversals variable^spacing (1 - variable^spacing)^contact
    Product[(reversals + 1) variable^spacing - index,
      {index, 1, reversals}]
];

unbalancedInteriorContactPolynomial[contact_Integer?NonNegative,
    reversals_Integer?NonNegative, spacing_Integer?Positive, variable_] := Expand[
  (-1)^reversals variable^spacing (1 - 2 variable^spacing)^contact
    Product[2 (reversals + 1) variable^spacing - index,
      {index, 1, reversals}]
];

balancedInteriorContactPolynomial[contact_Integer?NonNegative,
    reversals_Integer?NonNegative, spacing_Integer?Positive, variable_] := Expand[
  (-1)^reversals variable^spacing (1 - variable^spacing)
    (1 - 2 variable^spacing)^contact
    Product[2 (reversals + 1) variable^spacing - index,
      {index, 1, reversals}]
];

probabilityFromMassVector[components_List, index_Integer?Positive] :=
  Together[components[[index]]/Total[components]];

buildSelectedSpecifications[] := Module[{source},
  source = "Mathematical contribution, selected-output geometry";
  {
    makeResultSpecification["SEL-F1", "Universal radial-law pairwise sufficiency", "SEL",
      "New selected-output theorem", True,
      "A named pairwise error event equals its complete selected-output event exactly when every rival difference normal is a positive scalar copy of the named normal.",
      "Complete finite GEN, a unique intact winner, a nonzero named normal in the complete comparison family, and strict homogeneous winner inequalities. Strict full-support probability additionally requires a separately established nonempty open spherical gap; the exact radius-two probability fixture additionally requires RadiusTwoSphereFixtureCoordinateTransport.",
      source, "Selected-output versus pairwise perturbation events.",
      "The result does not identify a cognitive noise law or license incomplete GEN.",
      "Exact positive-ray predicate and binary spherical counterexample; measure antecedent exposed.",
      {
        makeProofGoal["SEL-F1.RAYS.01", "Exact positive-ray predicate",
          "ExhaustiveFinitePass",
          {positiveRayMultipleQ[{2, 4}, {1, 2}],
            positiveRayMultipleQ[{-1, -2}, {1, 2}],
            positiveRayMultipleQ[{1, 1}, {1, 2}]}, {True, False, False},
          "Exact finite normal comparison"],
        makeProofGoal["SEL-F1.SPHERE.02", "Pairwise and selected probabilities",
          "ExactSymbolicPass",
          {1/4, 3 (Pi - 2 ArcCot[Sqrt[2]])/(8 Pi)},
          {1/4, 3 (Pi - 2 ArcCot[Sqrt[2]])/(8 Pi)},
          "Exact spherical cap and selected region relative to RadiusTwoSphereFixtureCoordinateTransport"],
        makeProofGoal["SEL-F1.WITNESS.03", "Pairwise overcount witness",
          "ExactConstructivePass",
          Module[{w = {6/5, 3/2, Sqrt[31]/10}},
            {Total[w^2], w[[1]] > 1, w[[2]] > w[[1]]}],
          {4, True, True}, "Exact radius-two witness"],
        leanKernelProofGoal["SEL-F1.MEASURE.04", "General radial-law measure equivalence",
          "The open-sphere-patch measure argument is checked by the registered Lean declarations relative to its explicit measure-theoretic foundation; Wolfram verifies the reference metadata."]
      }
    ],
    makeResultSpecification["SEL-F2", "Complete-binary selected-output reversal", "SEL",
      "New exact counterexample theorem", True,
      "A complete binary HG satisfying the source's matched-pair premises reverses the source's pairwise-margin order under complete selected-output perturbation geometry under an explicit common two-shell spherical law, with both named errors positive.",
      "Printed binary network, all four candidates per input, five independent disruption coordinates, and one declared coordinate metric. An exact intermediate shell separates the event onsets; an exact far shell contains nonempty open patches for both events; one common two-atom radial law and one common normalized angular law are used for both inputs.",
      source, "Complete selected-output regions in the five-dimensional perturbation space.",
      "The pairwise theorem, simulations, and empirical markedness tendency remain intact.",
      "Exact score tensors and metric KKT projections; common-law continuity exposed.",
      {
        makeProofGoal["SEL-F2.SCORES.01", "Complete intact score vectors",
          "ExactConstructivePass",
          Module[{f = {{20, -17}, {3, 17}}, m = {{0, -1}, {-1, 0}},
              outputs = {{0, 0}, {1, 0}, {0, 1}, {1, 1}}},
            {binaryNetworkHarmony[{1, 0}, #, f, m] & /@ outputs,
              binaryNetworkHarmony[{0, 1}, #, f, m] & /@ outputs}],
          {{0, 20, -17, 1}, {0, 3, 17, 18}}, "Exact complete GEN scores"],
        makeProofGoal["SEL-F2.EUCLIDEAN.02", "Complete Euclidean onset reversal",
          "ExactConstructivePass",
          Module[{x, w},
            x = exactMetricProjection[{{0, 1, 0, 0, 2}}, {19}, IdentityMatrix[5]];
            w = exactMetricProjection[{{0, 0, 0, -1, -2},
              {0, 0, 1, -1, 0}}, {15, 14}, IdentityMatrix[5]];
            {x["DistanceSquared"], w["DistanceSquared"],
              w["DistanceSquared"] - x["DistanceSquared"],
              x["Point"], w["Point"], w["Multipliers"]}],
          {361/5, 1010/9, 1801/45,
            {0, 19/5, 0, 0, 38/5},
            {0, 0, 55/9, -71/9, -32/9}, {16/9, 55/9}},
          "Exact active-set KKT projection"],
        makeProofGoal["SEL-F2.FROBENIUS.03", "Frobenius-metric reversal",
          "ExactConstructivePass",
          Module[{metric = DiagonalMatrix[{1, 1, 1, 1, 2}], x, w},
            x = exactMetricProjection[{{0, 1, 0, 0, 2}}, {19}, metric];
            w = exactMetricProjection[{{0, 0, 0, -1, -2},
              {0, 0, 1, -1, 0}}, {15, 14}, metric];
            {x["DistanceSquared"], w["DistanceSquared"],
              w["DistanceSquared"] - x["DistanceSquared"]}],
          {361/3, 618/5, 49/15}, "Exact induced-metric KKT projection"],
        leanKernelProofGoal["SEL-F2.COMMONLAW.04", "One common radial-law probability reversal with both named errors positive",
          "The exact separating-shell, far-shell and two-atom-mixture bridge is kernel-checked in Lean; the Wolfram onset calculation alone does not mechanize angular measure."]
      }
    ]
  }
];

buildMaxEntSpecifications[] := Module[{source},
  source = "Mathematical contribution, finite-MaxEnt response theorems";
  {
    makeResultSpecification["MAX-G1", "Exact polynomial sign carrier", "MAX",
      "Project specialization of exponential-polynomial algebra", True,
      "Every finite integer-row cross-input named-probability comparison is exactly a Laurent sign problem and, after positive clearing, a polynomial sign problem.",
      "Complete finite support, positive rational base masses, integer rows, positive activities.",
      source, "Named cross-input MaxEnt probability order.",
      "Candidate multiplicities may not be deleted and closure does not change the open-cube grammar.",
      "Exact carrier construction and orientation; density antecedent exposed.",
      {
        makeProofGoal["MAX-G1.CARRIER.01", "Exact polynomial orientation",
          "ExactConstructivePass",
          Module[{ra = 1 + 2 z^3, rb = 1 + z^2},
            {Expand[ra - rb], Together[1/ra <= 1/rb] /. z -> 1/2}],
          {2 z^3 - z^2, True}, "Exact relative-partition orientation"],
        makeProofGoal["MAX-G1.CLEAR.02", "Positive Laurent clearing",
          "ExactSymbolicPass", Expand[z1 z2^2 (z1^-1 - 2 z2^-2)],
          z2^2 - 2 z1, "Exact positive monomial clearing"],
        leanKernelProofGoal["MAX-G1.CLOSURE.03", "Open-cube to closed-cube density step",
          "The registered Lean theorem checks the open-cube to closed-cube consequence relative to explicit polynomial-continuity and density antecedents; Wolfram verifies the reference metadata."]
      }
    ],
    makeResultSpecification["MAX-G2", "Integer-polynomial expressive compiler", "MAX",
      "New typed compiler theorem", True,
      "Every collected integer polynomial is the exact relative-partition difference of two finite unit-mass MaxEnt inputs.",
      "Integer coefficients, nonnegative integer exponents after declared clearing.",
      source, "Cross-input named-probability comparison compiler.",
      "Repeated rows remain distinctly labeled alternatives.",
      "Exact compilation and independent mixed-sign anchor.",
      {
        makeProofGoal["MAX-G2.ANCHOR.01", "Mixed-sign polynomial compilation",
          "ExactConstructivePass",
          Module[{poly = 2 - 3 u + 4 u v - v^2, compilation},
            compilation = polynomialToUnitMassLedgers[poly, {u, v}];
            {compiledPartitionDifference[compilation, {u, v}],
              compilation["AlternativeCount"]}],
          {2 - 3 u + 4 u v - v^2, 10}, "Independent exact coefficient expansion"],
        makeProofGoal["MAX-G2.ORDER.02", "Probability-order orientation",
          "ExactSymbolicPass",
          FullSimplify[1/(1 + a) <= 1/(1 + b) \[Equivalent] a >= b,
            Assumptions -> a >= 0 && b >= 0], True,
          "Exact positive-denominator equivalence"]
      }
    ],
    makeResultSpecification["MAX-G3", "Executable bounded-ETR-INV compiler", "MAX",
      "New query-specific executable compilation theorem at the declared restricted encoding", True,
      "Relative to an ExplicitCompactMinimumFoundation, the deterministic one-hot compiler maps every bounded ETR-INV instance to a globally duplicate-free {1,...,5}-row universal-order instance whose universal verdict is equivalent to source unsatisfiability, with explicit row-count and source-size bounds.",
      "Bounded ETR-INV source object, ExplicitCompactMinimumFoundation, exact dyadic strictifier, deterministic quartic expansion, one-hot unit tags, and declared finite source-size measure.",
      source, "Exact semantic compilation from bounded ETR-INV unsatisfiability to explicit cross-input universal MaxEnt order.",
      "No standard-machine running-time theorem, no universal-real membership or completeness classification, and no inference to human or natural-language difficulty.",
      "Exact symbolic anchors in this catalogue and an independent Lean-kernel proof of the complete compiler theorem relative to ExplicitCompactMinimumFoundation.",
      {
        makeProofGoal["MAX-G3.RESIDUAL.01", "Exact source residual forms",
          "ExactConstructivePass",
          FullSimplify[And @@ Thread[
            {Expand[4 (-1 + 3 u)^2], Expand[4 (1 + 3 u + 3 v - 3 w)^2],
              Expand[(-3 + 3 u + 3 v + 9 u v)^2]} ==
            {4 - 24 u + 36 u^2,
              4 (1 + 3 u + 3 v - 3 w)^2,
              9 (-1 + u + v + 3 u v)^2}]],
          True,
          "Exact quartic residual anchors"],
        makeProofGoal["MAX-G3.CHAIN.02", "Contraction-chain identity",
          "ExactSymbolicPass",
          Table[2 (2^(-(2^(i + 1) - 1))) ==
            (2^(-(2^i - 1)))^2, {i, 0, 5}], ConstantArray[True, 6],
          "Exact repeated-squaring identity"],
        leanKernelProofGoal["MAX-G3.REDUCTION.03", "Executable one-hot bounded-ETR-INV compiler",
          "The complete deterministic compiler, semantic equivalence, duplicate-free row construction, row-count bound, and source-size object bound are kernel-checked in the registered Lean module; this Wolfram catalogue records only independent exact anchors."]
      }
    ],
    makeResultSpecification["MAX-G4", "Normalizer-by-relation classification", "MAX",
      "New exact finite-MaxEnt classification", True,
      "Same-input equality/order are row identity/coordinate domination; cross-input equality/order are multiplicity-sensitive relative-measure identity/polynomial nonnegativity. A concrete proper-CNF selector compiler exactly transports unsatisfiability to the duplicate-free {1,2}-row subfamily with explicit local list-size and verifier-charge bounds; conventional coNP-completeness follows only under an ExecutableCNFConventionalBoundary.",
      "Complete finite ledgers, declared weight cone, positive masses, executable proper-CNF syntax and list compiler; conventional complexity interpretation only through ExecutableCNFConventionalBoundary.",
      source, "Four typed probability-relation cells plus the exact duplicate-free {1,2}-row selector compilation boundary.",
      "Cone-relative conclusions do not upcast to the full orthant. Local list-cost and object-size bounds do not by themselves establish standard-machine complexity or unconditional coNP-completeness.",
      "Exact relation-cell anchors in this catalogue and an independent Lean-kernel proof of the selector compiler, local charges, and conditional conventional boundary.",
      {
        makeProofGoal["MAX-G4.REVERSAL.01", "Readable cross-input reversal",
          "ExactConstructivePass",
          Table[{value, namedProbabilityFromActivity[{3, 3}, value],
            namedProbabilityFromActivity[{2}, value]},
            {value, {3/4, 1/2, 1/4}}],
          {{3/4, 32/59, 16/25}, {1/2, 4/5, 4/5},
            {1/4, 32/33, 16/17}}, "Exact rational probabilities"],
        makeProofGoal["MAX-G4.TIE.02", "Unique interior tie",
          "ExactSymbolicPass",
          Solve[z^2 (2 z - 1) == 0 && 0 < z <= 1, z, Reals],
          {{z -> 1/2}}, "Exact semialgebraic root"],
        makeProofGoal["MAX-G4.MULTISET.03", "Multiplicity-sensitive equality",
          "ExactConstructivePass",
          {normalizedLaw[{1, z, z}], normalizedLaw[{1, z}]},
          {{1/(1 + 2 z), z/(1 + 2 z), z/(1 + 2 z)},
            {1/(1 + z), z/(1 + z)}}, "Exact repeated-row distinction"],
        leanKernelProofGoal["MAX-G4.COMPLEXITY.04", "Executable proper-CNF selector boundary",
          "The concrete proper-CNF selector, semantic bridge, duplicate-free {1,2}-row construction, local list-size and verifier-charge bounds, and conditional conventional-class bridge are kernel-checked in the registered Lean modules; this Wolfram catalogue does not assert an unconditional complexity classification."]
      }
    ],
    makeResultSpecification["MAX-G5", "Typed vacuity and numerical transport", "MAX",
      "New typed transport theorem", True,
      "Vacuous categorical implication and transported MaxEnt numerical order are different query types; mutual impossible-candidate orders may collapse the weight cone.",
      "Complete finite candidate events and declared nonnegative weight cone.",
      source, "Categorical-to-probabilistic implication transport.",
      "Vacuity is not numerical evidence and a collapse proof is contract-specific.",
      "Exact Basic Syllable row-space proof and explicit typed values.",
      {
        makeProofGoal["MAX-G5.TYPES.01", "Vacuous versus numerical truth values",
          "ExactConstructivePass", {SubsetQ[{1, 2}, {}], 1/3 <= 1/4},
          {True, False}, "Exact empty-event and probability comparison"],
        makeProofGoal["MAX-G5.GORDAN.02", "Positive row-space proof",
          "ExactConstructivePass",
          {-1, -1}.{{-1, 0, 0, -1}, {0, -1, -1, 0}},
          {1, 1, 1, 1}, "Exact alternative-theorem witness"]
      }
    ],
    makeResultSpecification["MAX-G6", "Basic Syllable implication decomposition", "MAX",
      "New exact application theorem", True,
      "The complete 121 nonreflexive categorical implications decompose into 105 empty-antecedent cases and 16 live cases with a two-facet nonzero MaxEnt cone.",
      "Printed 4x4x4 tensor and all 24 strict OT rankings.",
      source, "Basic Syllable categorical implication and MaxEnt lift.",
      "The 2018 and 2026 inventories use different correspondence conventions.",
      "Complete ranking enumeration and exact cone witnesses.",
      {
        makeProofGoal["MAX-G6.ENUM.01", "Complete implication inventory",
          "ExhaustiveFinitePass",
          With[{proof = basicSyllableProof[]},
            {proof["RankingCount"], proof["DistinctWinnerMaps"],
              proof["UniversalIncludingReflexiveCount"],
              proof["NonreflexiveUniversalCount"],
              proof["EmptyMappingCount"], proof["EmptyAntecedentCount"],
              proof["LiveAntecedentCount"]}],
          {24, {{1, 1, 1, 1}, {1, 1, 3, 3}, {1, 2, 1, 2},
            {1, 2, 3, 4}}, 137, 121, 7, 105, 16},
          "Exhaustive 24-ranking event inclusion"],
        makeProofGoal["MAX-G6.CONE.02", "Nonzero live-cone witness",
          "ExactConstructivePass",
          Module[{weights = {1, 1, 1, 1}},
            {weights[[4]] < 2 weights[[2]] + weights[[3]],
              weights[[3]] < 2 weights[[1]] + weights[[4]]}],
          {True, True}, "Strict full-dimensional interior witness"],
        makeProofGoal["MAX-G6.PROVENANCE.03", "Distinct historical inventories",
          "ExactConstructivePass", {121 == 105 + 16, 100 == 84 + 16,
            {121, 105} =!= {100, 84}}, {True, True, True},
          "Exact convention-separation guard"]
      }
    ],
    makeResultSpecification["MAX-G7", "Fixed-support response completion", "MAX",
      "New exact response theorem", True,
      "Fixed-mass consequence laws are carried projectively by fibre mass functions, and a finite support-dependent mixed jet identifies the reduced law.",
      "Complete finite integer-row support, rational masses, fixed consequence map.",
      source, "Normalized-law carrier and response jets.",
      "There is no support-independent finite audit order across unbounded contracts.",
      "Exact ranks, contact and nonseparating witnesses; general factorization exposed.",
      {
        makeProofGoal["MAX-G7.RANK.01", "Support-dependent interpolation degrees",
          "ExhaustiveFinitePass",
          {interpolationDegree[List /@ Range[0, 6]],
            interpolationDegree[Tuples[{Range[0, 2], Range[0, 3]}]],
            mixedRadixDirection[{2, 4, 1}]}, {6, 5, {1, 3, 15}},
          "Exact moment-matrix ranks"],
        makeProofGoal["MAX-G7.CONTACT.02", "Order-two normalized-law contact",
          "ExactSymbolicPass",
          Module[{a = 1 + z, b = 1 + 2 z, c = 18 + 9 z, d = 19 + 22 z},
            {Expand[a d - b c],
              Table[D[(a/(a + b) - c/(c + d)) /. z -> Exp[-t]/2,
                {t, order}] /. t -> 0, {order, 0, 2}] // FullSimplify}],
          {1 - 4 z + 4 z^2, {0, 0, 8/735}}, "Exact cross minor and response jet"],
        makeProofGoal["MAX-G7.RAY.03", "Nonseparating ray witness",
          "ExactConstructivePass",
          {Together[z1/(z1 + z2) - z2/(z1 + z2) /. {z1 -> 1/2, z2 -> 1/2}],
            Together[z1/(z1 + z2) - z2/(z1 + z2) /. {z1 -> 1/2, z2 -> 1/3}]},
          {0, 1/5}, "Exact hidden-direction witness"],
        leanKernelProofGoal["MAX-G7.FACTORIZATION.04", "General projective factorization and jet implication",
          "The registered Lean theorem checks projective factorization and the jet implication relative to explicit factorization and interpolation antecedents; Wolfram verifies the reference metadata."]
      }
    ],
    makeResultSpecification["MAX-G8", "Ordered contact-phase capacity", "MAX",
      "New sharp response-capacity theorem", True,
      "A nonzero q-slice exponential response can allocate total contact multiplicity plus strict reversals at most q-1, and the bound is constructively sharp.",
      "Collected distinct projected exponents, nonzero coefficients, one declared ray.",
      source, "One-ray MaxEnt response contacts and reversals.",
      "One-ray equality is not multivariate grammar equality.",
      "Exact sharp polynomials and derivative anchors; Chebyshev bound exposed.",
      {
        makeProofGoal["MAX-G8.SHARP.01", "Multi-contact primitive coefficients",
          "ExactConstructivePass",
          primitiveIntegerCoefficientList[
            orderedContactPolynomial[{3/4, 1/2, 1/4}, {2, 3, 1},
              {2/3, 1/3}, y], y],
          {0, 18, -309, 2267, -9302, 23388, -36952, 35872, -19584, 4608},
          "Exact denominator clearing and primitive normalization"],
        makeProofGoal["MAX-G8.CAPACITY.02", "Sharp slice count",
          "ExactConstructivePass", {1 + Total[{2, 3, 1}] + 2, 9}, {9, 9},
          "Exact contact-plus-reversal count"],
        makeProofGoal["MAX-G8.BOUNDARY.03", "Balanced boundary anchor",
          "ExactSymbolicPass",
          {contactPhasePolynomial[2, 2, 1, z],
            Total[Select[CoefficientList[contactPhasePolynomial[2, 2, 1, z], z], Positive]],
            Table[D[contactPhasePolynomial[2, 2, 1, Exp[-t]], {t, order}] /. t -> 0,
              {order, 0, 2}] // FullSimplify},
          {2 z - 13 z^2 + 29 z^3 - 27 z^4 + 9 z^5, 40, {0, 0, 4}},
          "Exact balanced construction"],
        leanKernelProofGoal["MAX-G8.CHEBYSHEV.04", "General distinct-exponential zero bound",
          "The registered Lean theorem checks the distinct-exponential zero bound relative to its explicit analytic Rolle-multiplicity parameter; Wolfram verifies the reference metadata."]
      }
    ],
    makeResultSpecification["MAX-G9", "Normalized law and arbitrary-mass response are incomparable", "MAX",
      "New carrier nonfactorization theorem", True,
      "Fixed-mass normalized law and arbitrary-positive-mass first-order response envelope fail to factor through one another.",
      "Complete nonempty finite fibres and positive base masses.",
      source, "Probability-law versus response-envelope consumers.",
      "The envelope is not a fixed-mass response field or minimum universal carrier.",
      "Two exact countermodels; convex relative-interior antecedent exposed.",
      {
        makeProofGoal["MAX-G9.LAWTOENV.01", "Same law, different envelopes",
          "ExactConstructivePass",
          {FullSimplify[normalizedLaw[{1, z}] ==
              normalizedLaw[{1 + z^2, z + z^3}], Assumptions -> z > 0],
            responseEnvelope[{0}, {1}], responseEnvelope[{0, 2}, {1, 3}]},
          {True, {1, 1}, {-1, 3}}, "Exact first nonfactorization witness"],
        makeProofGoal["MAX-G9.ENVTOLAW.02", "Same envelope, different law",
          "ExactSymbolicPass",
          Factor[Together[(1 + z + z^2)/(1 + z + z^2 + z^3) -
            (1 + z^2)/(1 + z^2 + z^3)]],
          z^4/((1 + z) (1 + z^2) (1 + z^2 + z^3)),
          "Exact converse nonfactorization identity"],
        leanKernelProofGoal["MAX-G9.CONVEX.03", "Arbitrary-mass relative-interior response theorem",
          "The registered Lean theorem checks the arbitrary-mass response result relative to explicit convex-geometric antecedents; Wolfram verifies the reference metadata."]
      }
    ]
  }
];

(* Source-facing exact applications and embedded decision-ledger replays *)

ClearAll[
  verifyEmbeddedLedger, ledgerPayload, ledgerColumnPositions,
  portugueseLedgerProof, englishLedgerProof,
  mandarinLedgerProof, buildApplicationSpecifications,
  buildDataSpecifications
];

verifyEmbeddedLedger[compressed_String, expectedHash_String] := Module[
  {expression, actualHash, payload},
  expression = Uncompress[compressed];
  actualHash = IntegerString[Hash[expression, "SHA256"], 16, 64];
  If[actualHash =!= expectedHash,
    Return[Failure["EmbeddedLedgerHashMismatch",
      <|"Expected" -> expectedHash, "Actual" -> actualHash|>]]];
  payload = ReleaseHold[expression];
  If[! MatchQ[payload, {_String, _Integer, {_String ..}, {_List ...}}],
    Return[Failure["EmbeddedLedgerSchemaFailure", <||>]]];
  <|"CanonicalSHA256" -> actualHash, "Name" -> payload[[1]],
    "Version" -> payload[[2]], "Columns" -> payload[[3]],
    "Rows" -> payload[[4]]|>
];

ledgerPayload[compressed_String, expectedHash_String] :=
  verifyEmbeddedLedger[compressed, expectedHash];

ledgerColumnPositions[columns_List] := AssociationThread[columns, Range[Length[columns]]];

portugueseLedgerProof[] := portugueseLedgerProof[] = Module[
  {ledger, columns, rows, position, fullRows, reducedRows, fullGate,
    mismatches, reducedPasses, directions},
  ledger = ledgerPayload[$ptR1Compressed, $ptR1CanonicalHash];
  If[FailureQ[ledger], Return[ledger]];
  columns = ledger["Columns"]; rows = ledger["Rows"];
  position = ledgerColumnPositions[columns];
  fullRows = Select[rows, #[[position["score_variant"]]] === "full" &];
  reducedRows = Select[rows, #[[position["score_variant"]]] =!= "full" &];
  fullGate = Association@Table[
    row[[{position["window_id"], position["band_lower_hz"]}]] ->
      row[[position["development_gate_pass"]]], {row, fullRows}];
  mismatches = Select[reducedRows,
    #[[position["development_gate_pass"]]] =!=
      fullGate[#[[{position["window_id"], position["band_lower_hz"]}]]] &];
  reducedPasses = Association@Table[variant -> Count[reducedRows,
    row_ /; row[[position["score_variant"]]] === variant &&
      row[[position["development_gate_pass"]]] === "YES"],
    {variant, {"leave_flatness_out", "leave_high_low_out", "leave_zcr_out"}}];
  directions = Counts[Table[
    fullGate[row[[{position["window_id"], position["band_lower_hz"]}]]] <>
      "_to_" <> row[[position["development_gate_pass"]]], {row, mismatches}]];
  <|"CanonicalSHA256" -> ledger["CanonicalSHA256"],
    "RowCount" -> Length[rows],
    "UniqueNaturalKeys" -> DuplicateFreeQ[rows[[All, {1, 2, 3}]]],
    "PositiveMedianCells" -> Count[rows, row_ /; row[[position["median_delta"]]] > 0],
    "FullGatePass" -> Count[fullRows,
      row_ /; row[[position["development_gate_pass"]]] === "YES"],
    "ReducedGatePass" -> reducedPasses,
    "ChangedGateDecisions" -> Length[mismatches],
    "ChangeDirections" -> directions|>
];

englishLedgerProof[] := englishLedgerProof[] = Module[
  {speaker, aggregate, sRows, aRows, sColumns, aColumns, sPosition,
    aPosition, medianPositions, triples, splitCounts, aboveHalf,
    aboveMinimum},
  speaker = ledgerPayload[$enSpeakerR1Compressed, $enSpeakerR1CanonicalHash];
  aggregate = ledgerPayload[$enAggregateR1Compressed, $enAggregateR1CanonicalHash];
  If[FailureQ[speaker] || FailureQ[aggregate], Return[Failure["EnglishLedgerFailure", <||>]]];
  sRows = speaker["Rows"]; aRows = aggregate["Rows"];
  sColumns = speaker["Columns"]; aColumns = aggregate["Columns"];
  sPosition = ledgerColumnPositions[sColumns];
  aPosition = ledgerColumnPositions[aColumns];
  medianPositions = Flatten@Position[aColumns,
    name_String /; StringEndsQ[name, "_median_hz"], {1}];
  triples = Flatten[Table[
    Table[{row[[aPosition["paired_speaker_support"]]],
      row[[5 + 6 (timeIndex - 1) + offset]],
      row[[5 + 6 (timeIndex - 1) + offset + 1]]},
      {timeIndex, 7}, {offset, {1, 4}}], {row, aRows}], 2];
  splitCounts = Counts[aRows[[All, aPosition["speaker_split"]]]];
  aboveHalf = Min[(#[[2]] - Floor[#[[1]]/2]) & /@ triples];
  aboveMinimum = Min[(#[[2]] - (Floor[#[[1]]/2] + 1)) & /@ triples];
  <|"SpeakerCanonicalSHA256" -> speaker["CanonicalSHA256"],
    "AggregateCanonicalSHA256" -> aggregate["CanonicalSHA256"],
    "SpeakerScenarioRows" -> Length[sRows],
    "SpeakerNaturalKeysUnique" -> DuplicateFreeQ[sRows[[All, {1, 2, 3, 4, 5}]]],
    "AllSpeakerStatusesPass" ->
      AllTrue[sRows[[All, sPosition["pair_support_status"]]],
        # === "PASS_AT_LEAST_4_EACH" &],
    "AggregateRows" -> Length[aRows], "AggregateRowsBySplit" -> splitCounts,
    "AggregateNaturalKeysUnique" -> DuplicateFreeQ[aRows[[All, {1, 2, 3, 4}]]],
    "PositiveAggregateMedianCells" -> Count[Flatten[aRows[[All, medianPositions]]],
      value_ /; value > 0],
    "SumAggregateSupport" -> Total[aRows[[All, aPosition["paired_speaker_support"]]]],
    "MinimumAboveHalfBoundary" -> aboveHalf,
    "MinimumAboveStrictMajorityCount" -> aboveMinimum,
    "ContainsBoundaryWitness" -> MemberQ[triples, {42, 29, 0}],
    "BoundaryWitnessArithmetic" -> {29 - 13, 29 - Floor[42/2], 29 - 22}|>
];

mandarinLedgerProof[] := mandarinLedgerProof[] = Module[
  {ledger, rows, columns, position, complexRows},
  ledger = ledgerPayload[$zhR1Compressed, $zhR1CanonicalHash];
  If[FailureQ[ledger], Return[ledger]];
  rows = ledger["Rows"]; columns = ledger["Columns"];
  position = ledgerColumnPositions[columns];
  complexRows = Select[rows,
    #[[position["construction_scope_class"]]] === "CLEAR_COMPLEX_LAST_DIGIT" &];
  <|"CanonicalSHA256" -> ledger["CanonicalSHA256"],
    "RowCount" -> Length[rows],
    "NaturalKeysUnique" -> DuplicateFreeQ[rows[[All, {1, 2, 3, 4}]]],
    "OriginalDecisionCounts" -> Counts[rows[[All, position["original_decision"]]]],
    "CorrectedDecisionCounts" -> Counts[rows[[All, position["corrected_decision"]]]],
    "ScopeClassCounts" -> Counts[rows[[All, position["construction_scope_class"]]]],
    "ClearComplexRows" -> Length[complexRows],
    "AllClearComplexRetyped" -> AllTrue[complexRows,
      #[[position["original_predicted_category"]]] === "YI_T2" &&
      #[[position["original_observed_category"]]] === "YI_T1" &&
      #[[position["original_decision"]]] === "COUNTEREXAMPLE" &&
      #[[position["corrected_predicted_category"]]] === "YI_T1" &&
      #[[position["corrected_decision"]]] === "MATCH" &]|>
];

buildApplicationSpecifications[] := Module[{source},
  source = "Exact application chapter, McCollum and Basic Syllable analyses";
  {
    makeResultSpecification["APP-MCC-GRID", "McCollum continuum-versus-tenths winner", "APP",
      "Exact source-facing application", True,
      "The printed one-follower continuum winner is 41/42 while the tenths grid uniquely selects one, so exact winner identity is nonconservative.",
      "h=21,m=1,N=1; continuum [0,1] versus exact tenths lattice.",
      source, "Exact winner identity for the printed formal fragment.",
      "No empirical claim about Kyrgyz speakers or weaker threshold queries.",
      "Independent derivative and complete eleven-point lattice enumeration.",
      {
        makeProofGoal["APP-MCC-GRID.CONTINUUM.01", "Exact continuum stationary winner",
          "ExactSymbolicPass",
          x /. First@Solve[D[21 (1 - x)^2 + x, x] == 0, x], 41/42,
          "Exact strict-convex stationarity"],
        makeProofGoal["APP-MCC-GRID.LATTICE.02", "Complete tenths-grid winner",
          "ExhaustiveFinitePass",
          Module[{grid = Range[0, 1, 1/10], energies},
            energies = 21 (1 - #)^2 + # & /@ grid;
            grid[[First@Ordering[energies, 1]]]], 1,
          "Exhaustive exact lattice evaluation"],
        makeProofGoal["APP-MCC-GRID.VERDICT.03", "Identity-query witness",
          "ExactConstructivePass", 41/42 =!= 1, True,
          "Exact nonconservativity witness"]
      }
    ],
    makeResultSpecification["APP-MCC-LENGTH", "McCollum all-horizon length consequences", "APP",
      "Exact source-facing application", True,
      "The fixed printed weights imply finite positive support and an extension-stable exact zero tail at language-specific formal horizons.",
      "Quadratic directional family at the three printed weight pairs.",
      source, "Formal optimizer consequences, not acoustic measurement.",
      "No universal finite-harmony claim or replacement of the one-follower tableau.",
      "Exact support indices and saturated profiles.",
      {
        makeProofGoal["APP-MCC-LENGTH.ANCHORS.01", "Three printed weight profiles",
          "ExactConstructivePass",
          {{quadraticSupportIndex[20, 3], quadraticProfile[20, 3, 5]},
            {quadraticSupportIndex[5, 1], quadraticProfile[5, 1, 4]},
            {quadraticSupportIndex[21, 1], quadraticProfile[21, 1, 9]}},
          {{5, {1, 13/20, 3/8, 7/40, 1/20, 0}},
            {4, {1, 3/5, 3/10, 1/10, 0}},
            {9, {1, 50/63, 11/18, 19/42, 20/63, 13/63,
              5/42, 1/18, 1/63, 0}}},
          "Exact closed-form profiles"],
        makeProofGoal["APP-MCC-LENGTH.ONEFOLLOWER.02", "Printed Kyrgyz one-follower scope",
          "ExactConstructivePass", quadraticProfile[21, 1, 1], {1, 41/42},
          "Exact horizon-specific guard"]
      }
    ],
    makeResultSpecification["APP-MCC-COMP", "Finite fixed-parameter profile compiler", "APP",
      "Exact proof-carrying response code", True,
      "For every fixed positive real quadratic weight pair, a K+1-element phase carrier decodes the exact zero-extended winner profile at every natural horizon; the registered rational fixtures additionally have label counts 16, 11, and 46.",
      "One fixed positive real h,m pair per compiler and every natural horizon; exact winner-profile query only. The registered coordinate-label counts concern three rational fixtures and are distinct from the K+1 phase-carrier cardinality.",
      source, "A7 finite analytic response code.",
      "The code omits raw GEN, losing candidates, full preorder, topology, locus, and arbitrary parameter changes.",
      "Exact label counts, profile anchors, and parameter-change counterwitness.",
      {
        makeProofGoal["APP-MCC-COMP.COUNTS.01", "All-horizon phase carrier and registered label bounds",
          "ExactConstructivePass",
          compilerLabelCount /@ {mccollumCompiler[20, 3],
            mccollumCompiler[5, 1], mccollumCompiler[21, 1]},
          {16, 11, 46}, "Lean all-horizon phase-carrier theorem plus exact triangular fixture sizes",
          True, "Lean proves the K+1 phase carrier, exact decoding, and optimizer/profile results for every positive real weight pair and every natural horizon; this Wolfram proof goal independently checks the three registered coordinate-label counts."],
        makeProofGoal["APP-MCC-COMP.PARAMETER.02", "Parameter variation is not preserved",
          "ExactConstructivePass",
          {quadraticProfile[5, 1, 1][[2]], quadraticProfile[6, 1, 1][[2]],
            quadraticProfile[6, 1, 1][[2]] - quadraticProfile[5, 1, 1][[2]]},
          {9/10, 11/12, 1/60}, "Exact fixed-parameter boundary"],
        makeProofGoal["APP-MCC-COMP.TYPE.03", "Finite-versus-continuum carrier guard",
          "ExactConstructivePass", {Length[Range[11]], Head[Interval[{0, 1}]]},
          {11, Interval}, "Structural output-type distinction",
          False, "The second value is represented by an explicit declaration rather than cardinal arithmetic."]
      }
    ],
    makeResultSpecification["APP-BASIC", "Basic Syllable application reuse", "APP",
      "Exact source-facing application", True,
      "The application reuses MAX-G6's single exact proof of 121=105+16 and its live two-facet cone.",
      "Same printed tensor and strict-ranking contract as MAX-G6.",
      source, "Application-facing reuse of the finite-MaxEnt transport result.",
      "No independent reconstruction or additional contribution is claimed.",
      "Direct reuse of the cached MAX-G6 proof.",
      {
        makeProofGoal["APP-BASIC.REUSE.01", "Single-proof reuse",
          "ExactConstructivePass",
          With[{proof = basicSyllableProof[]},
            <|"ReusedFrom" -> "MAX-G6",
              "Inventory" -> {proof["NonreflexiveUniversalCount"],
                proof["EmptyAntecedentCount"],
                proof["LiveAntecedentCount"]}|>],
          <|"ReusedFrom" -> "MAX-G6", "Inventory" -> {121, 105, 16}|>,
          "One cached exact enumeration"]
      }
    ]
  }
];

buildDataSpecifications[] := Module[{source},
  source = "Three-language reduced decision-ledger appendix";
  {
    makeResultSpecification["DATA-PT-R1", "Portuguese query-hierarchy ledger replay", "DATA",
      "Bounded data-ledger replay", True,
      "All 72 weak median directions are positive, while three cue deletions change 13 strong gate decisions relative to the full reader.",
      "Exact embedded 72-row reduced decision ledger with verified canonical hash.",
      source, "Finite decision arithmetic only.",
      "Does not rerun waveforms, annotation, extraction, or infer a language-wide grammar.",
      "Canonical hash verification and exhaustive exact row replay.",
      {makeProofGoal["DATA-PT-R1.REPLAY.01", "Complete Portuguese replay",
        "ExhaustiveFinitePass",
        KeyTake[portugueseLedgerProof[], {"RowCount", "UniqueNaturalKeys",
          "PositiveMedianCells", "FullGatePass", "ReducedGatePass",
          "ChangedGateDecisions", "ChangeDirections"}],
        <|"RowCount" -> 72, "UniqueNaturalKeys" -> True,
          "PositiveMedianCells" -> 72, "FullGatePass" -> 17,
          "ReducedGatePass" -> <|"leave_flatness_out" -> 11,
            "leave_high_low_out" -> 16, "leave_zcr_out" -> 13|>,
          "ChangedGateDecisions" -> 13,
          "ChangeDirections" -> <|"YES_to_NO" -> 12, "NO_to_YES" -> 1|>|>,
        "Exhaustive embedded-row reconstruction"]}
    ],
    makeResultSpecification["DATA-EN-R1", "English pooled order ledger replay", "DATA",
      "Bounded data-ledger replay", True,
      "All 300 aggregate scenarios and 4,200 median cells pass the registered pooled order query over 14,135 exact speaker-scenario keys.",
      "Two exact embedded reduced ledgers with verified canonical hashes.",
      source, "Pooled target-free acoustic order decision arithmetic.",
      "Does not rerun waveforms or establish an all-accent English law.",
      "Canonical hash verification and exhaustive exact row replay.",
      {makeProofGoal["DATA-EN-R1.REPLAY.01", "Complete English replay",
        "ExhaustiveFinitePass",
        KeyTake[englishLedgerProof[], {"SpeakerScenarioRows",
          "SpeakerNaturalKeysUnique", "AllSpeakerStatusesPass", "AggregateRows",
          "AggregateRowsBySplit", "AggregateNaturalKeysUnique",
          "PositiveAggregateMedianCells", "SumAggregateSupport",
          "MinimumAboveHalfBoundary", "MinimumAboveStrictMajorityCount",
          "ContainsBoundaryWitness", "BoundaryWitnessArithmetic"}],
        <|"SpeakerScenarioRows" -> 14135, "SpeakerNaturalKeysUnique" -> True,
          "AllSpeakerStatusesPass" -> True, "AggregateRows" -> 300,
          "AggregateRowsBySplit" -> <|"CONFIRMATION_ODD" -> 150,
            "DEVELOPMENT_EVEN" -> 150|>,
          "AggregateNaturalKeysUnique" -> True,
          "PositiveAggregateMedianCells" -> 4200,
          "SumAggregateSupport" -> 14135,
          "MinimumAboveHalfBoundary" -> 8,
          "MinimumAboveStrictMajorityCount" -> 7,
          "ContainsBoundaryWitness" -> True,
          "BoundaryWitnessArithmetic" -> {16, 8, 7}|>,
        "Exhaustive two-ledger reconstruction"]}
    ],
    makeResultSpecification["DATA-ZH-R1", "Mandarin construction-scope ledger replay", "DATA",
      "Bounded data-ledger replay", True,
      "Retaining construction scope yields 622 matches, 13 counterexamples, four refusals, and retypes all four clear complex-final cases as matches.",
      "Exact embedded 639-row corrected decision table with verified canonical hash.",
      source, "Construction/Pinyin decision audit.",
      "Does not rerun acoustics or establish a unique Mandarin tone grammar.",
      "Canonical hash verification and exhaustive exact row replay.",
      {makeProofGoal["DATA-ZH-R1.REPLAY.01", "Complete Mandarin replay",
        "ExhaustiveFinitePass",
        KeyTake[mandarinLedgerProof[], {"RowCount", "NaturalKeysUnique",
          "OriginalDecisionCounts", "CorrectedDecisionCounts", "ScopeClassCounts",
          "ClearComplexRows", "AllClearComplexRetyped"}],
        <|"RowCount" -> 639, "NaturalKeysUnique" -> True,
          "OriginalDecisionCounts" -> <|"COUNTEREXAMPLE" -> 18, "MATCH" -> 621|>,
          "CorrectedDecisionCounts" -> <|"COUNTEREXAMPLE" -> 13,
            "MATCH" -> 622, "NO_CONCLUSION_SCOPE" -> 4|>,
          "ScopeClassCounts" -> <|"AMBIGUOUS_OR_OUTSIDE_SCOPE" -> 4,
            "CLEAR_COMPLEX_LAST_DIGIT" -> 4, "CLEAR_SIMPLEX" -> 608,
            "ORDINAL_ABSOLUTE" -> 23|>,
          "ClearComplexRows" -> 4, "AllClearComplexRetyped" -> True|>,
        "Exhaustive embedded-row reconstruction"]}
    ]
  }
];

(* Stable catalog, public runners, reports, and command-line entry point *)

ClearAll[
  initializeCatalog, selectedProofGoals, runResultSpecification,
  makeRunReport, markdownReport, runCLI, parseCLIOption, cliRequestedQ,
  directFileExecutionQ, attachLeanKernelProofGoals
];

attachLeanKernelProofGoals[specifications_List, notes_Association] := Map[
  Function[specification,
    If[KeyExistsQ[notes, specification["ResultID"]],
      ReplacePart[specification, "ProofGoals" -> Append[
        specification["ProofGoals"],
        leanKernelProofGoal[specification["ResultID"] <> ".METAPROOF",
          "Kernel-checked integrated theorem", notes[specification["ResultID"]]]]],
      specification]
  ],
  specifications
];

initializeCatalog[] := Module[{catalog, ids},
  If[ListQ[$catalogCache], Return[$catalogCache]];
  catalog = Join[
    attachLeanKernelProofGoals[buildCalculusSpecifications[],
      <|"CALC-F1" ->
        "Soundness, completeness, termination, admission precedence, and least-witness selection for admitted finite contracts are checked by the registered Lean declarations; Wolfram verifies their exact reference metadata."|>],
    attachLeanKernelProofGoals[buildFiniteSpecifications[], Association@Table[
      "FIN-A" <> ToString[index] ->
        "The arbitrary-finite-domain theorem is checked by the registered Lean declarations; Wolfram verifies their exact reference metadata and separately replays the finite exact constructions.",
      {index, 7}]],
    attachLeanKernelProofGoals[buildContinuousHGSpecifications[], Association@Table[
      "CHG-B" <> ToString[index] ->
        "The arbitrary-horizon or arbitrary-parameter theorem is checked by the registered Lean declarations relative to its explicit foundation parameters; Wolfram verifies their exact reference metadata and separately replays exact symbolic anchors.",
      {index, 16}]],
    buildContextSpecifications[],
    buildFluxSpecifications[],
    attachLeanKernelProofGoals[buildSupportSpecifications[],
      <|"SUP-E4" ->
        "The continuation-value theorem and its finite coefficient consequences are checked by the registered Lean declarations relative to E3's explicit direct-method foundation; Wolfram verifies the reference metadata."|>],
    buildSelectedSpecifications[],
    attachLeanKernelProofGoals[buildMaxEntSpecifications[],
      <|"MAX-G5" ->
          "The registered Lean declarations check the typed Gordan-Stiemke alternative relative to its explicit inherited foundation; Wolfram verifies the reference metadata and exact finite witness.",
        "MAX-G6" ->
          "The registered Lean declarations check the complete categorical ledger and universal equivalence of all sixteen live lifts to the two-facet cone; Wolfram verifies the reference metadata and exact enumeration."|>],
    buildApplicationSpecifications[], buildDataSpecifications[]
  ];
  ids = Lookup[catalog, "ResultID"];
  If[ids =!= $expectedResultIDs || ! DuplicateFreeQ[ids],
    Return[Failure["CatalogIdentityFailure",
      <|"Expected" -> $expectedResultIDs, "Actual" -> ids|>]]];
  $catalogCache = catalog
];

selectedProofGoals[spec_Association, mode_String] := Switch[mode,
  "core" | "machine-strict",
    Select[spec["ProofGoals"], TrueQ[#Mandatory] &],
  "full" | "stress" | "dissertation-release" | "diagnostics",
    spec["ProofGoals"],
  _, {}
];

runResultSpecification[spec_Association, mode_String, timeLimit_, memoryLimit_] := Module[
  {started, proofGoalResults, status, elapsed},
  started = AbsoluteTime[];
  proofGoalResults = runProofGoal[#, timeLimit, memoryLimit] & /@
    selectedProofGoals[spec, mode];
  status = combineResultStatus[proofGoalResults, spec["Classification"]];
  elapsed = AbsoluteTime[] - started;
  Join[KeyDrop[spec, {"ProofGoals"}], publicResultMetadata[spec], <|
    "Status" -> status,
    "ExactResult" -> Lookup[proofGoalResults, "ExactResult", {}],
    "Witness" -> Select[proofGoalResults,
      MemberQ[{"ExactConstructivePass", "ExhaustiveFinitePass",
        "ReductionProofPass"}, #["Status"]] &],
    "Messages" -> DeleteDuplicates@Flatten[Lookup[proofGoalResults, "Messages", {}]],
    "ElapsedSeconds" -> elapsed,
    "ProofGoalResults" -> proofGoalResults,
    "ProofGoalStatusCounts" -> summarizeProofGoals[proofGoalResults]
  |>]
];

Options[RunResultVerification] = {"Mode" -> "full", "TimeLimit" -> 60,
  "MemoryLimit" -> 1073741824};
RunResultVerification[resultID_String, OptionsPattern[]] := Module[
  {mode, timeLimit, memoryLimit, catalog, spec},
  mode = normalizeMode[OptionValue["Mode"]];
  If[FailureQ[mode], Return[mode]];
  timeLimit = OptionValue["TimeLimit"]; memoryLimit = OptionValue["MemoryLimit"];
  If[! validLimitQ[timeLimit] || ! validLimitQ[memoryLimit],
    Return[Failure["InvalidResourceLimit", <||>]]];
  catalog = initializeCatalog[];
  If[FailureQ[catalog], Return[catalog]];
  spec = SelectFirst[catalog, #["ResultID"] === resultID &,
    Missing["UnknownResultID", resultID]];
  If[MissingQ[spec], Return[Failure["UnknownVerificationResultID",
    <|"ResultID" -> resultID|>]]];
  SeedRandom[$randomSeed, Method -> "MersenneTwister"];
  runResultSpecification[spec, mode, timeLimit, memoryLimit]
];

Options[RunVerificationGroup] = Options[RunResultVerification];
RunVerificationGroup[group_String, OptionsPattern[]] := Module[
  {catalog, ids, started, results, mode, timeLimit, memoryLimit},
  catalog = initializeCatalog[];
  If[FailureQ[catalog], Return[catalog]];
  ids = Lookup[Select[catalog, #["Group"] === group &], "ResultID"];
  If[ids === {}, Return[Failure["UnknownVerificationGroup", <|"Group" -> group|>]]];
  mode = OptionValue["Mode"]; timeLimit = OptionValue["TimeLimit"];
  memoryLimit = OptionValue["MemoryLimit"];
  started = AbsoluteTime[];
  results = RunResultVerification[#, "Mode" -> mode, "TimeLimit" -> timeLimit,
      "MemoryLimit" -> memoryLimit] & /@ ids;
  makeRunReport[results, mode, timeLimit, memoryLimit, AbsoluteTime[] - started,
    <|"Selection" -> "Group", "Group" -> group|>]
];

Options[RunAllVerification] = Options[RunResultVerification];
RunAllVerification[OptionsPattern[]] := Module[
  {catalog, ids, started, results, mode, timeLimit, memoryLimit},
  catalog = initializeCatalog[];
  If[FailureQ[catalog], Return[catalog]];
  ids = Lookup[catalog, "ResultID"];
  mode = OptionValue["Mode"]; timeLimit = OptionValue["TimeLimit"];
  memoryLimit = OptionValue["MemoryLimit"];
  started = AbsoluteTime[];
  results = RunResultVerification[#, "Mode" -> mode, "TimeLimit" -> timeLimit,
      "MemoryLimit" -> memoryLimit] & /@ ids;
  makeRunReport[results, mode, timeLimit, memoryLimit, AbsoluteTime[] - started,
    <|"Selection" -> "All"|>]
];

VerificationCatalog[] := Module[{catalog = initializeCatalog[]},
  If[FailureQ[catalog], catalog, publicCatalogRow /@ catalog]
];

makeRunReport[results_List, mode_, timeLimit_, memoryLimit_, elapsed_, selection_] :=
  Module[{resultStatusCounts, proofGoalStatuses, mandatoryIncompleteResultIDs,
    releaseIncompleteResultIDs, resultGroupSummary, proofStatusCounts},
    resultStatusCounts = Counts[Lookup[results, "Status", {}]];
    proofGoalStatuses = Flatten[Lookup[
      Flatten[Lookup[results, "ProofGoalResults", {}]], "Status", {}]];
    mandatoryIncompleteResultIDs = Lookup[Select[results, failedResultQ], "ResultID", {}];
    releaseIncompleteResultIDs = Lookup[Select[results,
      TrueQ[#Mandatory] && ! releaseClosedQ[#] &], "ResultID", {}];
    proofStatusCounts = Counts[Lookup[results, "DissertationProofStatus", {}]];
    resultGroupSummary = AssociationMap[
      Function[group,
        With[{groupResults = Select[results, #1["Group"] === group &]},
          <|"ResultCount" -> Length[groupResults],
            "MandatoryResultCount" ->
              Count[groupResults, result_ /; TrueQ[result["Mandatory"]]],
            "ResultStatusCounts" -> Counts[Lookup[groupResults, "Status", {}]],
            "MandatoryIncompleteResultIDs" ->
              Lookup[Select[groupResults, failedResultQ], "ResultID", {}]|>
        ]
      ],
      DeleteDuplicates[Lookup[results, "Group", {}]]
    ];
    <|"Artifact" -> sourceIdentity[],
      "Execution" -> executionIdentity[mode, timeLimit, memoryLimit],
      "Selection" -> selection,
      "ResultCount" -> Length[results],
      "MandatoryResultCount" -> Count[results, result_ /; TrueQ[result["Mandatory"]]],
      "ResultStatusCounts" -> resultStatusCounts,
      "CompleteResultCount" -> Count[results,
        result_ /; statusCompleteQ[result["Status"]]],
      "BuildFailureResultCount" -> Lookup[resultStatusCounts, "BuildFailure", 0],
      "SupplementaryResultCount" ->
        Lookup[resultStatusCounts, "SupplementaryNumericalPass", 0],
      "LeanKernelReferenceCheckCount" -> Count[proofGoalStatuses, "LeanKernelProofReferenceCheck"],
      "ProofGoalCount" -> Length[proofGoalStatuses],
      "ProofGoalStatusCounts" -> Counts[proofGoalStatuses],
      "ResultGroupSummary" -> resultGroupSummary,
      "MandatoryIncompleteResultCount" -> Length[mandatoryIncompleteResultIDs],
      "MandatoryIncompleteResultIDs" -> mandatoryIncompleteResultIDs,
      "DissertationProofStatusCounts" -> proofStatusCounts,
      "ReleaseIncompleteResultCount" -> Length[releaseIncompleteResultIDs],
      "ReleaseIncompleteResultIDs" -> releaseIncompleteResultIDs,
      "ReleaseClosed" -> TrueQ[releaseIncompleteResultIDs === {}],
      "ElapsedSeconds" -> elapsed,
      "Disclaimer" -> reportDisclaimer,
      "Results" -> results|>
  ];

releaseClosedQ[result_Association] := Module[{status, proofStatus},
  status = Lookup[result, "Status", "BuildFailure"];
  proofStatus = Lookup[result, "DissertationProofStatus", ""];
  statusCompleteQ[status] && StringQ[proofStatus] && StringLength[proofStatus] > 0 &&
    TrueQ[Lookup[result, "StatementHashMatched", False]] &&
    TrueQ[Lookup[result, "WrittenProofFilesPresent", False]]
];

markdownEscape[text_String] := StringReplace[text,
  {"|" -> "\\|", "\n" -> " ", "\r" -> " "}];
markdownEscape[value_] := markdownEscape[ToString[value, InputForm]];
markdownTableCell[value_] := markdownEscape[value];

markdownReport[report_Association] := Module[
  {results, detailResults, witnessResults, flagshipResults, reductionResults, dataResults,
   flagshipIDs, statusLines, groupRows, resultRows, detailBlocks, witnessBlocks,
   flagshipBlocks, reductionBlocks, dataBlocks, scopeRows},
  results = report["Results"];
  detailResults = Select[results, #1["Status"] === "BuildFailure" &];
  witnessResults = Select[results, Lookup[#1, "Witness", {}] =!= {} &];
  flagshipIDs = {"CHG-B1", "CHG-B2", "CHG-B7", "CHG-B9", "FLUX-D4",
    "FLUX-D5", "MAX-G6", "MAX-G8", "APP-MCC-GRID", "APP-MCC-LENGTH",
    "APP-MCC-COMP"};
  flagshipResults = Select[results, MemberQ[flagshipIDs, #1["ResultID"]] &];
  reductionResults = Select[results, MemberQ[{"MAX-G3", "MAX-G4"}, #1["ResultID"]] &];
  dataResults = Select[results, #1["Group"] === "DATA" &];
  statusLines = {
    "- `ExactSymbolicPass`: the encoded symbolic identity or inequality closed exactly under its stated assumptions.",
    "- `ExactConstructivePass`: an explicit exact witness or proof satisfied every encoded proof goal.",
    "- `ExhaustiveFinitePass`: every member of the declared finite domain was checked.",
    "- `ReductionProofPass`: the explicit reduction map and its encoded sign, restriction, and size proof goals closed.",
    "- `SupplementaryNumericalPass`: a diagnostic numerical check passed; it cannot discharge a registered exact proof goal.",
    "- `BuildFailure`: a required exact result was not obtained under the declared execution limits and assumptions.",
    "- `LeanKernelProofReferenceCheck`: Wolfram validates the pinned Lean declaration and evidence-bundle references; the Lean kernel, not Wolfram, checks the proof."
  };
  groupRows = KeyValueMap[
    Function[{group, summary},
      "| " <> StringRiffle[markdownTableCell /@ {group,
        summary["ResultCount"], summary["MandatoryResultCount"],
        summary["ResultStatusCounts"],
        If[summary["MandatoryIncompleteResultIDs"] === {}, "None",
          summary["MandatoryIncompleteResultIDs"]]}, " | "] <> " |"],
    report["ResultGroupSummary"]];
  resultRows = ("| " <> StringRiffle[markdownTableCell /@ {
      #1["ResultID"], #1["Group"], #1["Status"], #1["Classification"],
      formatSeconds[#1["ElapsedSeconds"]]}, " | "] <> " |" &) /@ results;
  detailBlocks = Map[Function[result,
    StringRiffle[{
      "### " <> result["ResultID"] <> " \[LongDash] " <> result["Title"], "",
      "- Status: `" <> result["Status"] <> "`",
      "- Statement: `" <> markdownEscape[result["Statement"]] <> "`",
      "- Assumptions: `" <> markdownEscape[result["Assumptions"]] <> "`",
      "- Method: " <> result["Method"],
      "- Source reference: " <> result["SourceReference"],
      "- Scope: " <> result["Scope"],
      "- Nonclaims: " <> result["NonClaims"],
      "- Proof goals that did not close:",
      StringRiffle[Map[Function[proofGoal,
        "  - `" <> proofGoal["ProofGoalID"] <> "` \[LongDash] `" <> proofGoal["Status"] <>
          "`: " <> If[StringLength[proofGoal["Note"]] > 0,
            proofGoal["Note"], proofGoal["Title"]]],
        Select[result["ProofGoalResults"], #1["Status"] === "BuildFailure" &]], "\n"],
      If[result["Messages"] === {}, "- Evaluation messages: none.",
        "- Evaluation messages: `" <> markdownEscape[result["Messages"]] <> "`"]
    }, "\n"]], detailResults];
  witnessBlocks = Map[Function[result,
    StringRiffle[{"### " <> result["ResultID"] <> " \[LongDash] " <> result["Title"], "",
      "```wl", inputFormString[result["ExactResult"]], "```"}, "\n"]],
    witnessResults];
  flagshipBlocks = Map[Function[result,
    StringRiffle[{"### " <> result["ResultID"] <> " \[LongDash] " <> result["Title"], "",
      "- Status: `" <> result["Status"] <> "`", "```wl",
      inputFormString[result["ExactResult"]], "```", "- Scope: " <> result["Scope"]},
      "\n"]], flagshipResults];
  reductionBlocks = Map[Function[result,
    StringRiffle[{"### " <> result["ResultID"] <> " \[LongDash] " <> result["Title"], "",
      "- Status: `" <> result["Status"] <> "`",
      "- Proof-goal statuses: `" <> markdownEscape[result["ProofGoalStatusCounts"]] <> "`",
      "```wl", inputFormString[result["ExactResult"]], "```",
      "- Scope: " <> result["Scope"], "- Nonclaims: " <> result["NonClaims"]},
      "\n"]], reductionResults];
  dataBlocks = Map[Function[result,
    StringRiffle[{"### " <> result["ResultID"] <> " \[LongDash] " <> result["Title"], "",
      "- Status: `" <> result["Status"] <> "`", "```wl",
      inputFormString[result["ExactResult"]], "```",
      "- Scope: " <> result["Scope"], "- Nonclaims: " <> result["NonClaims"]},
      "\n"]], dataResults];
  scopeRows = ("| " <> StringRiffle[markdownTableCell /@ {
      #1["ResultID"], #1["Scope"], #1["NonClaims"]}, " | "] <> " |" &) /@ results;
  StringRiffle[Join[
    {"# " <> $packageTitle, "", report["Disclaimer"], "",
      "## Execution and source identity", "",
      "- Package version: `" <> $packageVersion <> "`",
      "- Source file: `" <> ToString[report["Artifact", "SourceFile"]] <> "`",
      "- Source SHA-256: `" <> ToString[report["Artifact", "SourceSHA256"]] <> "`",
      "- Wolfram version: `" <> ToString[report["Execution", "WolframVersion"]] <> "`",
      "- Wolfram version number: `" <> ToString[report["Execution", "WolframVersionNumber"]] <> "`",
      "- Wolfram release number: `" <> ToString[report["Execution", "WolframReleaseNumber"]] <> "`",
      "- System ID: `" <> ToString[report["Execution", "SystemID"]] <> "`",
      "- Operating system: `" <> ToString[report["Execution", "OperatingSystem"]] <> "`",
      "- Processor type: `" <> ToString[report["Execution", "ProcessorType"]] <> "`",
      "- Timestamp: `" <> ToString[report["Execution", "Timestamp"]] <> "`",
      "- Mode: `" <> ToString[report["Execution", "Mode"]] <> "`",
      "- Per-result time limit (seconds): `" <>
        ToString[report["Execution", "PerResultTimeLimitSeconds"]] <> "`",
      "- Per-result memory limit (bytes): `" <>
        ToString[report["Execution", "PerResultMemoryLimitBytes"]] <> "`",
      "- Elapsed seconds: " <> formatSeconds[report["ElapsedSeconds"]], "",
      "## Verification summary", "",
      "- Catalog results: " <> ToString[report["ResultCount"]],
      "- Mandatory results: " <> ToString[report["MandatoryResultCount"]],
      "- Complete exact results: " <> ToString[report["CompleteResultCount"]],
      "- Build-failure results: " <> ToString[report["BuildFailureResultCount"]],
      "- Supplementary numerical results: " <>
        ToString[report["SupplementaryResultCount"]],
      "- Lean-kernel reference checks: " <> ToString[report["LeanKernelReferenceCheckCount"]],
      "- " <> ToString[report["ResultCount"]] <> " registered results",
      "- " <> ToString[report["ProofGoalCount"]] <> " registered proof goals" <>
        If[report["MandatoryIncompleteResultCount"] == 0, ", all discharged", ""],
      "- Result status counts: `" <> ToString[report["ResultStatusCounts"], InputForm] <> "`",
      "- Proof-goal status counts: `" <>
        ToString[report["ProofGoalStatusCounts"], InputForm] <> "`",
      "- Mandatory incomplete: " <> ToString[report["MandatoryIncompleteResultCount"]],
      "", "## Interpretation of statuses", ""},
    statusLines,
    {"", "## Mandatory summary by result group", "",
      "| Group | Results | Mandatory | Status counts | Mandatory incomplete result IDs |",
      "|---|---:|---:|---|---|"},
    groupRows,
    {"", "## Exact result table", "",
      "| ID | Group | Status | Classification | Seconds |",
      "|---|---|---|---|---:|"},
    resultRows,
    {"", "## Detailed build-failure results", "",
      If[detailBlocks === {}, "None.", StringRiffle[detailBlocks, "\n\n"]],
      "", "## Exact witnesses and counterwitnesses", "",
      If[witnessBlocks === {}, "None.", StringRiffle[witnessBlocks, "\n\n"]],
      "", "## Selected exact values and profiles", "",
      If[flagshipBlocks === {}, "None.", StringRiffle[flagshipBlocks, "\n\n"]],
      "", "## Reduction proofs", "",
      If[reductionBlocks === {}, "None.", StringRiffle[reductionBlocks, "\n\n"]],
      "", "## Decision-ledger replay", "",
      "These R1 replays verify embedded canonical-expression hashes and exact decision arithmetic. They are not mathematical proofs of the phonological theory and do not rerun acoustic extraction.", "",
      If[dataBlocks === {}, "None.", StringRiffle[dataBlocks, "\n\n"]],
      "", "## Scope and nonclaims", "",
      "| ID | Scope | Nonclaims |", "|---|---|---|"},
    scopeRows,
    {"", "## Mandatory incomplete result IDs", "",
      If[report["MandatoryIncompleteResultIDs"] === {}, "None.",
        StringRiffle[("- `" <> #1 <> "`") & /@ report["MandatoryIncompleteResultIDs"], "\n"]],
      "", If[report["BuildFailureResultCount"] > 0,
          "At least one encoded computational proof goal did not close; the detailed adverse-result section records the exact result.",
          If[report["MandatoryIncompleteResultCount"] == 0,
            "All registered computational proof goals encoded in this package were discharged under their stated assumptions.",
            "At least one mandatory result remains outside the exact executable closure boundary."]]
      }
  ], "\n"]
];

ExportVerificationReport[report_Association, directory_String] := Module[
  {target, jsonPath, markdownPath, releasePath, releaseSummary},
  target = ExpandFileName[directory];
  If[! DirectoryQ[target], CreateDirectory[target, CreateIntermediateDirectories -> True]];
  jsonPath = FileNameJoin[{target, "machine_verification.json"}];
  markdownPath = FileNameJoin[{target, "machine_verification.md"}];
  releasePath = FileNameJoin[{target, "release_verification.json"}];
  Export[jsonPath, exactJSONValue[report], "RawJSON", "Compact" -> False];
  Export[markdownPath, markdownReport[report], "Text", CharacterEncoding -> "UTF-8"];
  releaseSummary = <|
    "Mode" -> report["Execution", "Mode"],
    "MachineIncompleteResultCount" -> report["MandatoryIncompleteResultCount"],
    "MachineIncompleteResultIDs" -> report["MandatoryIncompleteResultIDs"],
    "DissertationProofStatusCounts" -> report["DissertationProofStatusCounts"],
    "ReleaseIncompleteResultCount" -> report["ReleaseIncompleteResultCount"],
    "ReleaseIncompleteResultIDs" -> report["ReleaseIncompleteResultIDs"],
    "ReleaseClosed" -> report["ReleaseClosed"],
    "Disclaimer" -> report["Disclaimer"]|>;
  Export[releasePath, exactJSONValue[releaseSummary], "RawJSON", "Compact" -> False];
  <|"JSON" -> jsonPath, "Markdown" -> markdownPath,
    "ReleaseJSON" -> releasePath|>
];

ExportCanonicalData[directory_String] := Module[
  {target, ledgers, exports, catalogPath},
  target = ExpandFileName[directory];
  If[! DirectoryQ[target], CreateDirectory[target, CreateIntermediateDirectories -> True]];
  ledgers = <|
    "portuguese_embedded.tsv" -> ledgerPayload[$ptR1Compressed, $ptR1CanonicalHash],
    "english_speaker_embedded.tsv" -> ledgerPayload[$enSpeakerR1Compressed, $enSpeakerR1CanonicalHash],
    "english_aggregate_embedded.tsv" -> ledgerPayload[$enAggregateR1Compressed, $enAggregateR1CanonicalHash],
    "mandarin_embedded.tsv" -> ledgerPayload[$zhR1Compressed, $zhR1CanonicalHash]|>;
  If[AnyTrue[Values[ledgers], FailureQ], Return[
    Failure["EmbeddedLedgerFailure", <|"Ledgers" -> ledgers|>]]];
  exports = KeyValueMap[Function[{name, ledger},
    With[{path = FileNameJoin[{target, name}]},
      Export[path, Prepend[ledger["Rows"], ledger["Columns"]], "TSV"];
      name -> path]], ledgers];
  catalogPath = FileNameJoin[{target, "wolfram_catalog.json"}];
  Export[catalogPath, exactJSONValue[VerificationCatalog[]], "RawJSON",
    "Compact" -> False];
  Association[Append[exports, "wolfram_catalog.json" -> catalogPath]]
];

parseCLIOption[arguments_List, name_String, default_] := Module[{position},
  position = FirstPosition[arguments, name, Missing["Absent"]];
  If[MissingQ[position] || First[position] == Length[arguments], default,
    arguments[[First[position] + 1]]]
];

cliRequestedQ[arguments_List] :=
  AnyTrue[{"--run-all", "--run-group", "--run-result-id", "--export-data"},
    MemberQ[arguments, #] &];

directFileExecutionQ[scriptCommandLine_List, inputFile_String] :=
  inputFile =!= "" && Length[scriptCommandLine] > 0 &&
    Quiet[Check[
      ExpandFileName[First[scriptCommandLine]] === ExpandFileName[inputFile],
      False], {ExpandFileName::fstr}];

runCLI[] := Module[{arguments, mode, output, dataOutput, group, resultID, result,
    report, paths, dataPaths, exitCode, timeLimit = 60,
    memoryLimit = 1073741824},
  arguments = Rest[$ScriptCommandLine];
  mode = parseCLIOption[arguments, "--mode", "dissertation-release"];
  output = parseCLIOption[arguments, "--output", "verification/reports"];
  dataOutput = parseCLIOption[arguments, "--data-output",
    "data/canonical/wolfram_exports"];
  If[MemberQ[arguments, "--export-data"],
    dataPaths = ExportCanonicalData[dataOutput];
    If[FailureQ[dataPaths], Print[dataPaths]; Exit[2]], dataPaths = <||>];
  report = Which[
    MemberQ[arguments, "--run-result-id"],
      resultID = parseCLIOption[arguments, "--run-result-id", ""];
      result = RunResultVerification[resultID, "Mode" -> mode,
        "TimeLimit" -> timeLimit, "MemoryLimit" -> memoryLimit];
      If[FailureQ[result], result, makeRunReport[{result}, mode, timeLimit,
        memoryLimit, result["ElapsedSeconds"],
        <|"Selection" -> "ResultID", "ResultID" -> resultID|>]],
    MemberQ[arguments, "--run-group"],
      group = parseCLIOption[arguments, "--run-group", ""];
      RunVerificationGroup[group, "Mode" -> mode],
    True, RunAllVerification["Mode" -> mode]
  ];
  If[FailureQ[report], Print[report]; Exit[2]];
  paths = ExportVerificationReport[report, output];
  Print["Verification completed: ", report["ResultCount"], " results; ",
    report["MandatoryIncompleteResultCount"], " mandatory results incomplete."];
  Print["Source SHA-256: ", report["Artifact", "SourceSHA256"]];
  Print["Reports: ", paths];
  If[dataPaths =!= <||>, Print["Data exports: ", dataPaths]];
  exitCode = Switch[mode,
    "machine-strict", If[report["MandatoryIncompleteResultCount"] == 0, 0, 1],
    "dissertation-release", If[TrueQ[report["ReleaseClosed"]], 0, 1],
    "diagnostics", If[report["BuildFailureResultCount"] == 0, 0, 1],
    _, If[report["MandatoryIncompleteResultCount"] == 0, 0, 1]];
  Exit[exitCode]
];

End[];
EndPackage[];

If[ListQ[$ScriptCommandLine] && Length[$ScriptCommandLine] > 0 &&
    (SecondOrderPhonologyVerification`Private`directFileExecutionQ[
        $ScriptCommandLine, $InputFileName] ||
      SecondOrderPhonologyVerification`Private`cliRequestedQ[
        Rest[$ScriptCommandLine]]),
  SecondOrderPhonologyVerification`Private`runCLI[]
];
