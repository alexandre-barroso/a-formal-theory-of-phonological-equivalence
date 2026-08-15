BeginPackage["SecondOrderProofExporter`"];

HeldExpressionAST::usage =
  "HeldExpressionAST[HoldComplete[expr]] returns a lossless, tagged, JSON-safe syntax tree without releasing expr.";
ExportNeutralProofGoals::usage =
  "ExportNeutralProofGoals[source, output] exports exact held expressions, expected values, evaluated values, dependencies, and independent-checker requirements for every mechanized proof goal.";
ProofMethodFor::usage =
  "ProofMethodFor[resultID, classification] returns the neutral proof method assigned to a proof goal.";

Begin["`Private`"];

System`$HistoryLength = 0;
$NeutralSchema = "second-order-phonology-neutral-proof/1";
$ExpressionSchema = "second-order-phonology-neutral-expression/1";
$PackageContext = "SecondOrderPhonologyVerification`Private`";
$DefinedNameCache =.;
$DependencyGraphCache =.;

ClearAll[
  heldNode, splitHeldCall, heldArguments, heldValue, symbolIdentity,
  symbolNamesInHeld, definitionValues, definitionHeld, definedNameQ,
  definedNames, directPackageDependencies, dependencyGraph,
  transitivePackageDependencies, systemDependencies, checkerRequirements,
  evaluateProofGoal, proofRecord, readTSVAssociations,
  leanKernelReferenceCheck, exportManifest, inputFormString
];

SetAttributes[symbolIdentity, HoldAllComplete];
symbolIdentity[symbol_Symbol] :=
  Context[Unevaluated[symbol]] <> SymbolName[Unevaluated[symbol]];

heldArguments[held_HoldComplete] :=
  Apply[List, Map[HoldComplete, held], {0}];

splitHeldCall[HoldComplete[head_[arguments___]]] :=
  {HoldComplete[head], heldArguments[HoldComplete[arguments]]};

heldNode[HoldComplete[value_Integer]] := <|
  "kind" -> "integer",
  "decimal" -> IntegerString[value, 10]
|>;

heldNode[HoldComplete[value_String]] := <|
  "kind" -> "string",
  "value" -> value
|>;

heldNode[HoldComplete[True]] := <|"kind" -> "boolean", "value" -> True|>;
heldNode[HoldComplete[False]] := <|"kind" -> "boolean", "value" -> False|>;

heldNode[HoldComplete[value_Real]] := <|
  "kind" -> "inexact-real",
  "input_form" -> ToString[Unevaluated[value], InputForm,
    CharacterEncoding -> "UTF-8"],
  "precision_bits" -> ToString[Precision[value], InputForm],
  "exact" -> False
|>;

heldNode[HoldComplete[value_Symbol]] := <|
  "kind" -> "symbol",
  "name" -> symbolIdentity[value]
|>;

heldNode[held_HoldComplete] := Module[{parts},
  parts = Quiet[Check[splitHeldCall[held], $Failed]];
  If[ListQ[parts] && Length[parts] === 2,
    <|
      "kind" -> "call",
      "head" -> heldNode[parts[[1]]],
      "arguments" -> (heldNode /@ parts[[2]])
    |>,
    <|
      "kind" -> "opaque-atom",
      "input_form" -> ToString[held, InputForm,
        CharacterEncoding -> "UTF-8"],
      "exact" -> False
    |>
  ]
];

HeldExpressionAST[held_HoldComplete] := <|
  "schema" -> $ExpressionSchema,
  "root" -> heldNode[held]
|>;

heldValue[value_] := With[{evaluated = value}, HoldComplete[evaluated]];

SetAttributes[inputFormString, HoldAllComplete];
inputFormString[value_] := ToString[Unevaluated[value], InputForm,
  CharacterEncoding -> "UTF-8"];

symbolNamesInHeld[held_HoldComplete] := DeleteDuplicates@Cases[
  held,
  symbol_Symbol :> symbolIdentity[symbol],
  Infinity,
  Heads -> True
];

definitionValues[name_String] := ToExpression[
  name,
  InputForm,
  Function[symbol,
    Join[
      OwnValues[Unevaluated[symbol]],
      DownValues[Unevaluated[symbol]],
      SubValues[Unevaluated[symbol]],
      UpValues[Unevaluated[symbol]]
    ],
    HoldAllComplete
  ]
];

definitionHeld[name_String] := With[
  {definitions = definitionValues[name]},
  HoldComplete[definitions]
];

definedNameQ[name_String] := Length[definitionValues[name]] > 0;

definedNames[] := If[ListQ[$DefinedNameCache],
  $DefinedNameCache,
  $DefinedNameCache = Select[Names[$PackageContext <> "*"], definedNameQ]
];

directPackageDependencies[held_HoldComplete] := Intersection[
  symbolNamesInHeld[held],
  definedNames[]
];

dependencyGraph[] := If[AssociationQ[$DependencyGraphCache],
  $DependencyGraphCache,
  $DependencyGraphCache = AssociationMap[
    directPackageDependencies[definitionHeld[#]] &,
    definedNames[]
  ]
];

transitivePackageDependencies[held_HoldComplete] := Module[
  {graph = dependencyGraph[], initial},
  initial = directPackageDependencies[held];
  FixedPoint[
    Sort@DeleteDuplicates@Join[#, Flatten[Lookup[graph, #, {}]]] &,
    initial
  ]
];

systemDependencies[held_HoldComplete] := Sort@Select[
  symbolNamesInHeld[held],
  StringStartsQ[#, "System`"] &
];

ProofMethodFor[resultID_String, classification_String] := Which[
  StringStartsQ[resultID, "DATA-"], "DatasetReplayProof",
  StringStartsQ[resultID, "APP-"], "ApplicationReplayProof",
  classification === "ReductionProofPass", "FiniteReductionProof",
  classification === "ExhaustiveFinitePass", "FiniteEnumerationProof",
  classification === "ExactSymbolicPass", "ExactSymbolicProof",
  classification === "ExactConstructivePass", "ConstructiveWitnessProof",
  classification === "LeanKernelProofReferenceCheck", "LeanKernelProofReferenceCheck",
  True, Missing["UnrecognizedProofClassification", classification]
];

checkerRequirements[proofMethod_String, dependencies_List] := Module[
  {common, specific},
  common = {
    "Parse the tagged neutral AST without evaluating Wolfram Language text.",
    "Reject opaque atoms and inexact real nodes in a mandatory exact proof record.",
    "Resolve every package dependency through an independently implemented and versioned Python translation registry.",
    "Recompute the proof-goal result from the neutral expression and source-transcribed constants; do not trust the exported Wolfram result or pass flag.",
    "Compare recomputed actual and expected values by typed canonical structural equality."
  };
  specific = Switch[proofMethod,
    "FiniteEnumerationProof", {
      "Reconstruct the declared finite domain and independently visit every member exactly once.",
      "Recompute each predicate, partition, relation, count, or aggregate and verify completeness and duplicate-free coverage."
    },
    "ExactSymbolicProof", {
      "Normalize the exact arithmetic or symbolic identity under the explicitly encoded assumptions.",
      "Verify all denominators, domains, strict boundaries, and branch conditions before accepting the equality or inequality."
    },
    "ConstructiveWitnessProof", {
      "Reconstruct the explicit witness, map, profile, matrix, or counterexample.",
      "Evaluate every defining predicate and verify that the witness has the declared type and lies in the declared domain."
    },
    "FiniteReductionProof", {
      "Verify the explicit reduction map, its totality, restrictions, sign correspondence, uniqueness or tag clauses, and encoded size bound.",
      "Reject a reduction that preserves only the sampled instances or only the final Boolean without its stated side conditions."
    },
    "DatasetReplayProof", {
      "Verify the embedded canonical payload hash, schema, natural-key uniqueness, and exact row count.",
      "Recompute every reported count and decision from all embedded rows; do not treat the acoustic corpus as rerun."
    },
    "ApplicationReplayProof", {
      "Recompute the source-transcribed finite arithmetic and all displayed witness conditions from exact inputs.",
      "Verify the application-specific scope guard; do not upcast the finite arithmetic to a broader empirical claim."
    },
    _, {"Reject the unsupported proof method."}
  ];
  <|
    "algorithm" -> proofMethod,
    "direct_package_dependencies" -> dependencies,
    "must_check" -> Join[common, specific],
    "forbidden_shortcut" ->
      "Acceptance from wolfram_pass, evaluated_actual_ast, source hashes, or matching display strings alone is forbidden."
  |>
];

evaluateProofGoal[proofGoal_Association, timeLimit_Integer,
    memoryLimit_Integer] := Module[{evaluation, actual, expected, comparison},
  evaluation = SecondOrderPhonologyVerification`Private`captureEvaluation[
    proofGoal["Expression"], timeLimit, memoryLimit];
  actual = evaluation["Value"];
  expected = ReleaseHold[proofGoal["Expected"]];
  comparison = SameQ[
    SecondOrderPhonologyVerification`Private`canonicalAnswer[actual],
    SecondOrderPhonologyVerification`Private`canonicalAnswer[expected]
  ];
  <|
    "outcome" -> evaluation["Outcome"],
    "messages" -> (inputFormString /@ evaluation["Messages"]),
    "elapsed_seconds" -> ToString[evaluation["ElapsedSeconds"], InputForm],
    "actual" -> actual,
    "expected" -> expected,
    "comparison" -> comparison
  |>
];

proofRecord[specification_Association, proofGoal_Association,
    timeLimit_Integer, memoryLimit_Integer] := Module[
  {evaluation, proofMethod, directDependencies, transitiveDependencies,
   expressionSystems, expectedSystems},
  evaluation = evaluateProofGoal[proofGoal, timeLimit, memoryLimit];
  proofMethod = ProofMethodFor[
    specification["ResultID"], proofGoal["Classification"]];
  directDependencies = directPackageDependencies[proofGoal["Expression"]];
  transitiveDependencies = transitivePackageDependencies[
    proofGoal["Expression"]];
  expressionSystems = systemDependencies[proofGoal["Expression"]];
  expectedSystems = systemDependencies[proofGoal["Expected"]];
  <|
    "schema" -> $NeutralSchema,
    "proof_id" -> proofGoal["ProofGoalID"] <> ".WOLFRAM-PROOF",
    "result_id" -> specification["ResultID"],
    "proof_goal_id" -> proofGoal["ProofGoalID"],
    "title" -> proofGoal["Title"],
    "declared_classification" -> proofGoal["Classification"],
    "proof_method" -> proofMethod,
    "mandatory" -> proofGoal["Mandatory"],
    "method" -> proofGoal["ProofMethod"],
    "note" -> proofGoal["Note"],
    "held_expression_wolfram_sha256" -> IntegerString[
      Hash[proofGoal["Expression"], "SHA256"], 16, 64],
    "held_expected_wolfram_sha256" -> IntegerString[
      Hash[proofGoal["Expected"], "SHA256"], 16, 64],
    "held_expression_ast" -> HeldExpressionAST[proofGoal["Expression"]],
    "held_expected_ast" -> HeldExpressionAST[proofGoal["Expected"]],
    "evaluated_actual_ast" -> HeldExpressionAST[heldValue[evaluation["actual"]]],
    "evaluated_expected_ast" -> HeldExpressionAST[heldValue[evaluation["expected"]]],
    "wolfram_outcome" -> evaluation["outcome"],
    "wolfram_messages" -> evaluation["messages"],
    "wolfram_pass" -> evaluation["comparison"],
    "direct_package_dependencies" -> directDependencies,
    "transitive_package_dependencies" -> transitiveDependencies,
    "system_symbols_in_expression" -> expressionSystems,
    "system_symbols_in_expected" -> expectedSystems,
    "python_independent_check" ->
      checkerRequirements[proofMethod, directDependencies],
    "trust_boundary" ->
      "The held and evaluated Wolfram trees are evidence inputs only. Independent acceptance requires the Python checks listed above."
  |>
];

readTSVAssociations[path_String] := Module[{rows},
  rows = Quiet[Check[Import[path, "TSV"], $Failed]];
  If[rows === $Failed || ! ListQ[rows] || Length[rows] < 2,
    Return[$Failed]
  ];
  AssociationThread[First[rows], #] & /@ Rest[rows]
];

leanKernelReferenceCheck[specification_Association,
    proofGoal_Association, source_String] := Module[
  {root, coveragePath, buildPath, axiomPath, axiomPolicyPath, forbiddenPath,
   leancheckerPath, toolchainPath, manifestPath, coverage, matches,
   match, declarations, buildText, axiomText,
   forbiddenText, leancheckerText, passed},
  root = Nest[DirectoryName, ExpandFileName[source], 3];
  coveragePath = FileNameJoin[{root, "lean", "reports", "proof_goal_coverage.tsv"}];
  buildPath = FileNameJoin[{root, "lean", "logs", "build.txt"}];
  axiomPath = FileNameJoin[{root, "lean", "logs", "axiom_audit.txt"}];
  axiomPolicyPath = FileNameJoin[{root, "lean", "logs", "axiom_policy.txt"}];
  forbiddenPath = FileNameJoin[{root, "lean", "logs", "forbidden_tokens.txt"}];
  leancheckerPath = FileNameJoin[{root, "lean", "logs", "leanchecker.txt"}];
  toolchainPath = FileNameJoin[{root, "lean", "lean-toolchain"}];
  manifestPath = FileNameJoin[{root, "lean", "lake-manifest.json"}];
  coverage = If[FileExistsQ[coveragePath], readTSVAssociations[coveragePath], $Failed];
  matches = If[ListQ[coverage], Select[
    coverage,
    Lookup[#, "proof_goal_id", ""] === proofGoal["ProofGoalID"] &&
      Lookup[#, "result_id", ""] === specification["ResultID"] &
  ], {}];
  match = If[Length[matches] === 1, First[matches], <||>];
  declarations = If[StringQ[Lookup[match, "lean_declaration", Missing["Declaration"]]],
    StringSplit[Lookup[match, "lean_declaration", ""], ";"], {}];
  buildText = If[FileExistsQ[buildPath], Import[buildPath, "Text"], ""];
  axiomText = If[FileExistsQ[axiomPolicyPath], Import[axiomPolicyPath, "Text"], ""];
  forbiddenText = If[FileExistsQ[forbiddenPath], Import[forbiddenPath, "Text"], ""];
  leancheckerText = If[FileExistsQ[leancheckerPath], Import[leancheckerPath, "Text"], ""];
  passed = And[
    Length[matches] === 1,
    Lookup[match, "formalization_status", ""] === "lean_closed",
    declarations =!= {},
    FileExistsQ[toolchainPath], FileExistsQ[manifestPath],
    FileExistsQ[axiomPath], FileByteCount[axiomPath] > 0,
    StringContainsQ[buildText, "All targets up-to-date"],
    StringContainsQ[axiomText, "PASS: all "],
    StringContainsQ[axiomText, "explicit standard whitelist"],
    StringContainsQ[forbiddenText, "PASS: no sorry, admit, native_decide, unsafe, or project axiom declarations found."],
    StringSplit[StringTrim[leancheckerText], "\n"] === {
      "$ lake env leanchecker --fresh PhonologicalCalculus.All",
      "Independent kernel check completed successfully."
    }
  ];
  <|
    "schema" -> "second-order-phonology-lean-kernel-reference-check/1",
    "check_id" -> proofGoal["ProofGoalID"] <> ".LEAN-KERNEL-REFERENCE.CHECK",
    "check_type" -> "LeanKernelProofReferenceCheck",
    "result_id" -> specification["ResultID"],
    "proof_goal_id" -> proofGoal["ProofGoalID"],
    "lean_declarations" -> declarations,
    "proof_goal_coverage_path" -> FileNameJoin[{"lean", "reports", "proof_goal_coverage.tsv"}],
    "proof_goal_coverage_sha256" -> If[FileExistsQ[coveragePath], IntegerString[FileHash[coveragePath, "SHA256"], 16, 64], ""],
    "lean_toolchain_sha256" -> If[FileExistsQ[toolchainPath], IntegerString[FileHash[toolchainPath, "SHA256"], 16, 64], ""],
    "lake_manifest_sha256" -> If[FileExistsQ[manifestPath], IntegerString[FileHash[manifestPath, "SHA256"], 16, 64], ""],
    "build_log_sha256" -> If[FileExistsQ[buildPath], IntegerString[FileHash[buildPath, "SHA256"], 16, 64], ""],
    "axiom_audit_log_sha256" -> If[FileExistsQ[axiomPath], IntegerString[FileHash[axiomPath, "SHA256"], 16, 64], ""],
    "axiom_policy_log_sha256" -> If[FileExistsQ[axiomPolicyPath], IntegerString[FileHash[axiomPolicyPath, "SHA256"], 16, 64], ""],
    "forbidden_token_log_sha256" -> If[FileExistsQ[forbiddenPath], IntegerString[FileHash[forbiddenPath, "SHA256"], 16, 64], ""],
    "leanchecker_fresh_log_sha256" -> If[FileExistsQ[leancheckerPath], IntegerString[FileHash[leancheckerPath, "SHA256"], 16, 64], ""],
    "status" -> If[TrueQ[passed], "PASS", "FAIL"]
  |>
];

exportManifest[proofs_List, leanReferenceChecks_List,
    source_String, sourceLabel_String] := Module[
  {methods, dependencies, systemSymbols},
  methods = Counts[Lookup[proofs, "proof_method"]];
  dependencies = Sort@DeleteDuplicates@Flatten[
    Lookup[proofs, "transitive_package_dependencies"]];
  systemSymbols = Sort@DeleteDuplicates@Join[
    Flatten[Lookup[proofs, "system_symbols_in_expression"]],
    Flatten[Lookup[proofs, "system_symbols_in_expected"]]
  ];
  <|
    "schema" -> "second-order-phonology-neutral-proof-goal-export/1",
    "source_file" -> sourceLabel,
    "source_sha256" -> IntegerString[FileHash[source, "SHA256"], 16, 64],
    "wolfram_version" -> $Version,
    "wolfram_version_number" -> ToString[$VersionNumber, InputForm],
    "system_id" -> $SystemID,
    "history_length" -> System`$HistoryLength,
    "proof_goal_count" -> Length[proofs] + Length[leanReferenceChecks],
    "wolfram_proof_replay_count" -> Length[proofs],
    "proof_method_counts" -> methods,
    "wolfram_proof_replay_pass_count" -> Count[Lookup[proofs, "wolfram_pass"], True],
    "wolfram_proof_replay_failure_ids" -> Lookup[
      Select[proofs, ! TrueQ[#["wolfram_pass"]] &],
      "proof_goal_id",
      {}
    ],
    "lean_kernel_reference_check_count" -> Length[leanReferenceChecks],
    "lean_kernel_reference_check_pass_count" -> Count[Lookup[leanReferenceChecks, "status"], "PASS"],
    "lean_kernel_reference_check_failure_ids" -> Lookup[
      Select[leanReferenceChecks, Lookup[#, "status", "FAIL"] =!= "PASS" &],
      "check_id",
      {}
    ],
    "transitive_package_dependency_count" -> Length[dependencies],
    "transitive_package_dependencies" -> dependencies,
    "system_symbol_count" -> Length[systemSymbols],
    "system_symbols" -> systemSymbols,
    "acceptance_rule" ->
      "No proof is accepted solely because Wolfram evaluated it to the expected value. Python must replay the proof method independently."
  |>
];

Options[ExportNeutralProofGoals] = {
  "TimeLimit" -> 60,
  "MemoryLimit" -> 1073741824,
  "SourceLabel" -> Automatic
};

ExportNeutralProofGoals[source_String, output_String,
    OptionsPattern[]] := Module[
  {catalog, pairs, proofPairs, leanReferencePairs, timeLimit,
   memoryLimit, sourceLabel, proofs, leanReferenceChecks, payload, result,
   mappingPath, mappingHeader, mappingRows, leanMappingPath,
   leanMappingHeader, leanMappingRows, failureIDs},
  If[! FileExistsQ[source],
    Return[Failure["MissingSource", <|"Source" -> source|>]]];
  Get[source];
  catalog = SecondOrderPhonologyVerification`Private`initializeCatalog[];
  If[FailureQ[catalog], Return[catalog]];
  pairs = Join @@ Table[
    {specification, #} & /@ specification["ProofGoals"],
    {specification, catalog}
  ];
  leanReferencePairs = Select[
    pairs,
    #[[2, "Classification"]] === "LeanKernelProofReferenceCheck" &
  ];
  proofPairs = Select[
    pairs,
    #[[2, "Classification"]] =!= "LeanKernelProofReferenceCheck" &
  ];
  timeLimit = OptionValue["TimeLimit"];
  memoryLimit = OptionValue["MemoryLimit"];
  sourceLabel = Replace[
    OptionValue["SourceLabel"],
    Automatic :> FileNameTake[source]
  ];
  If[! StringQ[sourceLabel],
    Return[Failure["InvalidSourceLabel", <||>]]
  ];
  proofs = proofRecord[#[[1]], #[[2]], timeLimit,
      memoryLimit] & /@ proofPairs;
  leanReferenceChecks = leanKernelReferenceCheck[#[[1]], #[[2]], source] & /@
    leanReferencePairs;
  payload = <|
    "manifest" -> exportManifest[proofs, leanReferenceChecks, source, sourceLabel],
    "proofs" -> proofs,
    "lean_kernel_reference_checks" -> leanReferenceChecks
  |>;
  result = Export[output, payload, "RawJSON", "Compact" -> False];
  mappingPath = FileNameJoin[{
    DirectoryName[ExpandFileName[output]],
    FileBaseName[output] <> "_map.tsv"
  }];
  mappingHeader = {
    "proof_id", "result_id", "proof_goal_id", "declared_classification",
    "proof_method", "direct_package_dependencies",
    "transitive_dependency_count", "system_symbol_count", "wolfram_pass",
    "python_algorithm", "python_must_check"
  };
  mappingRows = ({
      #["proof_id"],
      #["result_id"],
      #["proof_goal_id"],
      #["declared_classification"],
      #["proof_method"],
      StringRiffle[#["direct_package_dependencies"], ";"],
      Length[#["transitive_package_dependencies"]],
      Length@DeleteDuplicates@Join[
        #["system_symbols_in_expression"],
        #["system_symbols_in_expected"]
      ],
      #["wolfram_pass"],
      #["python_independent_check", "algorithm"],
      StringRiffle[#["python_independent_check", "must_check"], " | "]
    } &) /@ proofs;
  Export[mappingPath, Prepend[mappingRows, mappingHeader], "TSV"];
  leanMappingPath = FileNameJoin[{
    DirectoryName[ExpandFileName[output]],
    FileBaseName[output] <> "_lean_reference_checks.tsv"
  }];
  leanMappingHeader = {
    "check_id", "result_id", "proof_goal_id", "check_type",
    "lean_declarations", "status"
  };
  leanMappingRows = ({
      #["check_id"],
      #["result_id"],
      #["proof_goal_id"],
      #["check_type"],
      StringRiffle[#["lean_declarations"], ";"],
      #["status"]
    } &) /@ leanReferenceChecks;
  Export[leanMappingPath, Prepend[leanMappingRows, leanMappingHeader], "TSV"];
  failureIDs = Join[
    Lookup[Select[proofs, ! TrueQ[#["wolfram_pass"]] &], "proof_goal_id", {}],
    Lookup[Select[leanReferenceChecks, Lookup[#, "status", "FAIL"] =!= "PASS" &], "check_id", {}]
  ];
  <|
    "output" -> result,
    "mapping_tsv" -> mappingPath,
    "lean_reference_check_tsv" -> leanMappingPath,
    "proof_goal_count" -> Length[pairs],
    "wolfram_proof_replay_count" -> Length[proofs],
    "wolfram_proof_replay_pass_count" -> Count[Lookup[proofs, "wolfram_pass"], True],
    "lean_kernel_reference_check_count" -> Length[leanReferenceChecks],
    "lean_kernel_reference_check_pass_count" -> Count[Lookup[leanReferenceChecks, "status"], "PASS"],
    "failure_ids" -> failureIDs
  |>
];

End[];
EndPackage[];
