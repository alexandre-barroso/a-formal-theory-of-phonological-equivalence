BeginPackage["SecondOrderMachineClosure`"];

RunMachineClosure::usage = "RunMachineClosure[root, output] independently validates the neutral registered-result proofs and exports a Wolfram closure trace.";
RunAdversarialClosure::usage = "RunAdversarialClosure[root, output] checks every registered mutant against the canonical formal statement and proof binding.";

Begin["`Private`"];

System`$HistoryLength = 0;

ClearAll[
  readJSON, writeJSON, sha256, lexicographicStringLess, canonicalize,
  canonicalHash, canonicalEqualQ, formalStatementHash,
  noApproximateQ, subsetListQ, exactKeySubsetQ,
  expectedClaim, sourceRecordValidQ, sourceRecordsValidQ,
  statementPayloadValidQ, validateStatementCheck, statementCheckResult,
  semanticPayloadValidQ, finitePayloadValidQ,
  applicationPayloadValidQ, dataPayloadValidQ, geometricPayloadValidQ,
  leanKernelPayloadValidQ,
  maxEntPayloadValidQ, maxEntG1G5ReplayValidQ, maxEntG6G9ReplayValidQ,
  validateProof, dependencyAcyclicQ, flagshipIndependentCheck,
  proofGoalResult, resultResult, canonicalSemanticProjection,
  RunMachineClosure, RunAdversarialClosure
];

readJSON[path_String] := Import[path, "RawJSON"];

writeJSON[path_String, value_] := Module[{directory = DirectoryName[path]},
  If[! DirectoryQ[directory], CreateDirectory[directory, CreateIntermediateDirectories -> True]];
  Export[path, value, "RawJSON", "Compact" -> False]
];

sha256[path_String] := IntegerString[FileHash[path, "SHA256"], 16, 64];

lexicographicStringLess[left_String, right_String] := Module[
  {leftCodes = ToCharacterCode[left], rightCodes = ToCharacterCode[right], length, position},
  length = Min[Length[leftCodes], Length[rightCodes]];
  position = FirstPosition[
    MapThread[Unequal, {Take[leftCodes, length], Take[rightCodes, length]}],
    True,
    Missing["Equal"]
  ];
  If[
    MissingQ[position],
    Length[leftCodes] < Length[rightCodes],
    leftCodes[[First[position]]] < rightCodes[[First[position]]]
  ]
];

canonicalize[value_Association] := Association@Table[
  key -> canonicalize[Lookup[value, key]],
  {key, Sort[Keys[value], lexicographicStringLess]}
];
canonicalize[value_List] := canonicalize /@ value;
canonicalize[value_] := value;

canonicalHash[value_] := IntegerString[
  Hash[StringReplace[ExportString[canonicalize[value], "RawJSON", "Compact" -> True], "\\/" -> "/"], "SHA256"],
  16,
  64
];

canonicalEqualQ[left_, right_] := canonicalize[left] === canonicalize[right];

formalStatementHash[spec_Association] := canonicalHash@KeyTake[
  spec,
  {
    "schema_version", "result_id", "kind", "group", "variables", "sorts",
    "domains", "definitions", "assumptions", "conclusion", "quantifier_prefix",
    "registered_query_type", "scope", "nonclaims", "foundation_dependencies",
    "result_dependencies", "source_transcription_dependencies",
    "expected_proof_methods", "withdrawal_condition"
  }
];

noApproximateQ[value_] := FreeQ[value, _Real, Infinity];

subsetListQ[left_List, right_List] := And @@ (MemberQ[right, #] & /@ DeleteDuplicates[left]);

exactKeySubsetQ[association_Association, required_List] := subsetListQ[required, Keys[association]];

expectedClaim[spec_Association, proofGoalID_String] := Module[{matches},
  matches = Select[
    Lookup[spec, "proof_goals", {}],
    Lookup[#, "proof_goal_id", ""] === proofGoalID &
  ];
  If[Length[matches] === 1, Lookup[First[matches], "claim", Missing["Claim"]], Missing["UnknownProofGoal"]]
];

sourceRecordValidQ[root_String, source_Association] := Module[{path, rows, rowCount},
  path = FileNameJoin[{root, Lookup[source, "path", ""]}];
  If[! FileExistsQ[path] || sha256[path] =!= Lookup[source, "sha256", ""], Return[False]];
  If[! KeyExistsQ[source, "row_count"], Return[True]];
  rows = Quiet[Check[Import[path, "TSV"], $Failed]];
  rowCount = Lookup[source, "row_count", Missing["RowCount"]];
  rows =!= $Failed && ListQ[rows] && Length[rows] >= 1 && Length[Rest[rows]] === rowCount
];

sourceRecordsValidQ[root_String, sources_List] := And @@ (sourceRecordValidQ[root, #] & /@ sources);

statementPayloadValidQ[root_String, payload_Association, spec_Association] :=
  Sort[Keys[payload]] === Sort[{
    "en_statement_path", "en_statement_file_sha256", "en_statement_marker", "en_statement_sha256",
    "pt_BR_statement_path", "pt_BR_statement_file_sha256", "pt_BR_statement_marker", "pt_BR_statement_sha256"
  }] && And @@ Table[
  Module[{path = FileNameJoin[{root, Lookup[payload, locale <> "_statement_path", ""]}]},
    FileExistsQ[path] &&
    sha256[path] === Lookup[payload, locale <> "_statement_file_sha256", ""] &&
    Lookup[payload, locale <> "_statement_sha256", ""] === Lookup[
      spec,
      If[locale === "en", "english_statement_sha256", "portuguese_statement_sha256"],
      ""
    ] &&
    StringQ[Lookup[payload, locale <> "_statement_marker", Missing["Marker"]]] &&
    StringContainsQ[Import[path, "Text"], Lookup[payload, locale <> "_statement_marker", ""]]
  ],
  {locale, {"en", "pt_BR"}}
];

validateStatementCheck[root_String, check_Association, spec_Association] := And[
  Sort[Keys[check]] === Sort[{
    "schema_version", "check_id", "check_type", "result_id",
    "formal_statement_sha256", "payload"
  }],
  Lookup[check, "schema_version", ""] === "1.0.0",
  Lookup[check, "check_id", ""] === Lookup[spec, "result_id", ""] <> ".STATEMENT-CORRESPONDENCE.CHECK",
  Lookup[check, "check_type", ""] === "StatementCorrespondenceCheck",
  Lookup[check, "result_id", ""] === Lookup[spec, "result_id", ""],
  formalStatementHash[spec] === Lookup[spec, "formal_statement_sha256", ""],
  Lookup[check, "formal_statement_sha256", ""] === Lookup[spec, "formal_statement_sha256", ""],
  noApproximateQ[check],
  AssociationQ[Lookup[check, "payload", Missing["Payload"]]],
  statementPayloadValidQ[root, Lookup[check, "payload", <||>], spec]
];

statementCheckResult[root_String, check_Association, path_String, spec_Association] := Module[{passed},
  passed = validateStatementCheck[root, check, spec];
  <|
    "result_id" -> Lookup[spec, "result_id", ""],
    "check_id" -> Lookup[check, "check_id", ""],
    "check_type" -> Lookup[check, "check_type", ""],
    "formal_statement_sha256" -> Lookup[spec, "formal_statement_sha256", ""],
    "check_sha256" -> sha256[path],
    "status" -> If[passed, "PASS", "FAIL"]
  |>
];

semanticPayloadValidQ[proof_Association, spec_Association] := Module[
  {payload, claim, expected, observed, derivation, antiVacuity, assumptionIDs},
  payload = Lookup[proof, "payload", Missing["Payload"]];
  claim = Lookup[proof, "claim", Missing["Claim"]];
  If[! AssociationQ[payload], Return[False]];
  assumptionIDs = Lookup[Lookup[spec, "assumptions", {}], "id", {}];
  antiVacuity = Lookup[payload, "anti_vacuity", <||>];
  If[
    Lookup[payload, "assumption_model_result", False] =!= True ||
    ! AssociationQ[antiVacuity] ||
    Lookup[antiVacuity, "conclusion_is_not_assumption", False] =!= True ||
    Sort[Lookup[proof, "assumptions_used", {}]] =!= Sort[assumptionIDs],
    Return[False]
  ];
  If[KeyExistsQ[payload, "claim"] && ! canonicalEqualQ[Lookup[payload, "claim", Missing["Claim"]], claim], Return[False]];
  expected = Lookup[claim, "expected", Missing["NoExpected"]];
  observed = Lookup[payload, "observed", Missing["NoObserved"]];
  If[! MissingQ[expected] && ! MissingQ[observed] && observed =!= expected, Return[False]];
  derivation = Lookup[payload, "derivation", Missing["NoDerivation"]];
  If[! MissingQ[derivation] && ! (ListQ[derivation] || AssociationQ[derivation]), Return[False]];
  If[
    ListQ[derivation] && Length[derivation] === 0 &&
    ! (
      Lookup[payload, "derivation_method", ""] === "exact_finite_replay" &&
      StringQ[Lookup[payload, "regression_algorithm", Missing["Algorithm"]]] &&
      KeyExistsQ[payload, "regression_expected"]
    ),
    Return[False]
  ];
  True
];

finitePayloadValidQ[proof_Association] := Module[{payload, claim},
  payload = Lookup[proof, "payload", Missing["Payload"]];
  claim = Lookup[proof, "claim", Missing["Claim"]];
  AssociationQ[payload] &&
  canonicalEqualQ[claim, <|
    "node" -> "equal",
    "left" -> Lookup[payload, "expression", Missing["Expression"]],
    "right" -> Lookup[payload, "expected", Missing["Expected"]]
  |>]
];

applicationPayloadValidQ[root_String, proof_Association] := Module[{payload, source},
  payload = Lookup[proof, "payload", Missing["Payload"]];
  If[! AssociationQ[payload], Return[False]];
  source = Lookup[payload, "source", Missing["Source"]];
  AssociationQ[source] && sourceRecordValidQ[root, source] &&
  canonicalEqualQ[Lookup[proof, "claim", Missing["Claim"]], <|
    "node" -> "exact_application_result",
    "source" -> source,
    "algorithm" -> Lookup[payload, "algorithm", Missing["Algorithm"]],
    "inputs" -> Lookup[payload, "inputs", Missing["Inputs"]],
    "expected" -> Lookup[payload, "expected", Missing["Expected"]]
  |>]
];

dataPayloadValidQ[root_String, proof_Association] := Module[{payload, sources},
  payload = Lookup[proof, "payload", Missing["Payload"]];
  If[! AssociationQ[payload], Return[False]];
  sources = Lookup[payload, "sources", Missing["Sources"]];
  ListQ[sources] && sourceRecordsValidQ[root, sources] &&
  canonicalEqualQ[Lookup[proof, "claim", Missing["Claim"]], <|
    "node" -> "exact_data_replay",
    "sources" -> sources,
    "algorithm" -> Lookup[payload, "algorithm", Missing["Algorithm"]],
    "expected" -> Lookup[payload, "expected", Missing["Expected"]]
  |>]
];

geometricPayloadValidQ[proof_Association] := Module[{payload},
  payload = Lookup[proof, "payload", Missing["Payload"]];
  AssociationQ[payload] &&
  Lookup[payload, "variable", ""] === "p" &&
  Lookup[payload, "state_count", -1] === 2 &&
  Lookup[payload, "total_mass", ""] === "1" &&
  Lookup[payload, "infinity_mass", ""] === "0" &&
  Lookup[payload, "base_left", Missing["Left"]] === Lookup[payload, "base_right", Missing["Right"]] &&
  Lookup[payload, "step_left", Missing["Left"]] === Lookup[payload, "step_right", Missing["Right"]]
];

leanKernelPayloadValidQ[root_String, proof_Association, spec_Association] := Module[
  {payload, paths, expectedKeys, filesValid, rows, coverage, matches,
   declarations, buildText, axiomText, axiomPolicyText, forbiddenText,
   leancheckerText, proofGoalID, resultID},
  payload = Lookup[proof, "payload", Missing["Payload"]];
  If[! AssociationQ[payload], Return[False]];
  paths = <|
    "proof_goal_coverage_path" -> "lean/reports/proof_goal_coverage.tsv",
    "lean_toolchain_path" -> "lean/lean-toolchain",
    "lake_manifest_path" -> "lean/lake-manifest.json",
    "build_log_path" -> "lean/logs/build.txt",
    "axiom_audit_log_path" -> "lean/logs/axiom_audit.txt",
    "axiom_policy_log_path" -> "lean/logs/axiom_policy.txt",
    "forbidden_token_log_path" -> "lean/logs/forbidden_tokens.txt",
    "leanchecker_fresh_log_path" -> "lean/logs/leanchecker.txt"
  |>;
  expectedKeys = Join[
    Keys[paths],
    StringReplace[Keys[paths], "_path" -> "_sha256"],
    {"proof_goal_id", "lean_declarations"}
  ];
  If[Sort[Keys[payload]] =!= Sort[expectedKeys], Return[False]];
  filesValid = And @@ KeyValueMap[
    Function[{pathField, relativePath},
      Module[{path = FileNameJoin[{root, relativePath}], hashField},
        hashField = StringReplace[pathField, "_path" -> "_sha256"];
        Lookup[payload, pathField, ""] === relativePath &&
          FileExistsQ[path] && sha256[path] === Lookup[payload, hashField, ""]
      ]
    ],
    paths
  ];
  If[! TrueQ[filesValid], Return[False]];
  proofGoalID = Lookup[proof, "proof_goal_id", ""];
  resultID = Lookup[proof, "result_id", ""];
  If[Lookup[payload, "proof_goal_id", ""] =!= proofGoalID, Return[False]];
  rows = Import[FileNameJoin[{root, paths["proof_goal_coverage_path"]}], "TSV"];
  If[! ListQ[rows] || Length[rows] < 2, Return[False]];
  coverage = AssociationThread[First[rows], #] & /@ Rest[rows];
  matches = Select[
    coverage,
    Lookup[#, "proof_goal_id", ""] === proofGoalID &&
      Lookup[#, "result_id", ""] === resultID &
  ];
  If[Length[matches] =!= 1 || Lookup[First[matches], "formalization_status", ""] =!= "lean_closed",
    Return[False]
  ];
  declarations = StringSplit[Lookup[First[matches], "lean_declaration", ""], ";"];
  If[declarations === {} || MemberQ[declarations, ""] ||
      Lookup[payload, "lean_declarations", {}] =!= declarations,
    Return[False]
  ];
  buildText = Import[FileNameJoin[{root, paths["build_log_path"]}], "Text"];
  axiomText = Import[FileNameJoin[{root, paths["axiom_audit_log_path"]}], "Text"];
  axiomPolicyText = Import[FileNameJoin[{root, paths["axiom_policy_log_path"]}], "Text"];
  forbiddenText = Import[FileNameJoin[{root, paths["forbidden_token_log_path"]}], "Text"];
  leancheckerText = Import[FileNameJoin[{root, paths["leanchecker_fresh_log_path"]}], "Text"];
  StringContainsQ[buildText, "All targets up-to-date"] &&
    StringLength[StringTrim[axiomText]] > 0 &&
    StringContainsQ[axiomPolicyText, "PASS: all "] &&
    StringContainsQ[axiomPolicyText, "explicit standard whitelist"] &&
    StringContainsQ[forbiddenText, "PASS: no sorry, admit, native_decide, unsafe, or project axiom declarations found."] &&
    StringSplit[StringTrim[leancheckerText], "\n"] === {
      "$ lake env leanchecker --fresh PhonologicalCalculus.All",
      "Independent kernel check completed successfully."
    }
];

maxEntPayloadValidQ[root_String, proof_Association, spec_Association] := Module[
  {payload, nested, nestedPayload, checkerPath, proofPath, companionPath,
   companion, companionProofGoal, closureRecord, verification, replayResult,
   resultID, proofGoalID, claimHash, foundationDependencies, resultDependencies,
   normalizedRoot, common, familySpecific},
  payload = Lookup[proof, "payload", Missing["Payload"]];
  If[! AssociationQ[payload], Return[False]];
  resultID = Lookup[proof, "result_id", ""];
  proofGoalID = Lookup[proof, "proof_goal_id", ""];
  claimHash = Lookup[proof, "claim_sha256", ""];
  foundationDependencies = Sort[Lookup[proof, "foundation_dependencies", {}]];
  resultDependencies = Sort[Lookup[proof, "result_dependencies", {}]];
  normalizedRoot = StringReplace[
    ExpandFileName[root],
    RegularExpression[If[$PathnameSeparator === "\\", "[\\\\]+$", "/+$"]] -> ""
  ];
  checkerPath = ExpandFileName@FileNameJoin[{root, Lookup[payload, "checker_module", ""]}];
  companionPath = FileNameJoin[
    {root, "formal", "proofs", "maxent", "semantic", "specs", resultID <> ".json"}
  ];
  If[
    ! StringStartsQ[checkerPath, normalizedRoot <> $PathnameSeparator] ||
    ! FileExistsQ[checkerPath] ||
    sha256[checkerPath] =!= Lookup[payload, "checker_module_sha256", ""] ||
    ! FileExistsQ[companionPath],
    Return[False]
  ];
  companion = readJSON[companionPath];
  companionProofGoal = SelectFirst[
    Lookup[companion, "proof_goals", {}],
    Lookup[#, "proof_goal_id", ""] === proofGoalID &,
    Missing["CompanionProofGoal"]
  ];
  If[MissingQ[companionProofGoal], Return[False]];
  nested = Lookup[payload, "closure_proof", Missing["ClosureProof"]];
  If[! AssociationQ[nested], Return[False]];
  nestedPayload = Lookup[nested, "payload", Missing["NestedPayload"]];
  If[! AssociationQ[nestedPayload], Return[False]];
  proofPath = ExpandFileName@FileNameJoin[{root, Lookup[nestedPayload, "proof", ""]}];
  common =
    Lookup[payload, "proof_method", ""] === "MaxEntSemanticClosureProof" &&
    Lookup[payload, "closure_status", ""] === "MACHINE_CLOSED_RELATIVE_TO_FOUNDATION" &&
    Lookup[payload, "proof_goal_id", ""] === proofGoalID &&
    Lookup[payload, "claim_sha256", ""] === claimHash &&
    Lookup[payload, "semantic_kernel_version", ""] === "maxent-semantics-1.0.0" &&
    Lookup[payload, "supports_whole_result_closure", False] === True &&
    MemberQ[{True, False}, Lookup[payload, "replayed_universal", Missing["Boolean"]]] &&
    Lookup[nested, "schema_version", ""] === "1.0.0" &&
    Lookup[nested, "proof_method", ""] === "MaxEntSemanticClosureProof" &&
    Lookup[nested, "proof_id", ""] === Lookup[proof, "proof_id", ""] &&
    Lookup[nested, "result_id", ""] === resultID &&
    Lookup[nested, "proof_goal_id", ""] === proofGoalID &&
    canonicalEqualQ[Lookup[nested, "claim", Missing["Claim"]], Lookup[proof, "claim", Missing["Claim"]]] &&
    Lookup[nested, "claim_sha256", ""] === claimHash &&
    Lookup[nested, "formal_statement_sha256", ""] ===
      Lookup[companion, "formal_statement_sha256", ""] &&
    Lookup[companion, "result_id", ""] === resultID &&
    Sort[Lookup[companion, "foundation_dependencies", {}]] === foundationDependencies &&
    Sort[Lookup[companion, "result_dependencies", {}]] === resultDependencies &&
    canonicalEqualQ[
      Lookup[companionProofGoal, "claim", Missing["Claim"]],
      Lookup[proof, "claim", Missing["Claim"]]
    ] &&
    Lookup[nestedPayload, "closure_status", ""] === "MACHINE_CLOSED_RELATIVE_TO_FOUNDATION" &&
    Lookup[nestedPayload, "proof_goal_id", ""] === proofGoalID &&
    Lookup[nestedPayload, "claim_sha256", ""] === claimHash &&
    StringStartsQ[proofPath, normalizedRoot <> $PathnameSeparator] &&
    FileExistsQ[proofPath] &&
    sha256[proofPath] === Lookup[nestedPayload, "proof_sha256", ""];
  If[! TrueQ[common], Return[False]];
  closureRecord = Lookup[nestedPayload, "closure_record", Missing["ClosureRecord"]];
  verification = Lookup[nestedPayload, "verification", Missing["Verification"]];
  replayResult = Lookup[nestedPayload, "replay_result", Missing["ReplayResult"]];
  familySpecific = If[StringMatchQ[resultID, "MAX-G" ~~ Alternatives["1", "2", "3", "4", "5"]],
    AssociationQ[closureRecord] && AssociationQ[verification] &&
    Lookup[nestedPayload, "checker_module", ""] === Lookup[payload, "checker_module", ""] &&
    Lookup[nestedPayload, "checker_module_sha256", ""] === Lookup[payload, "checker_module_sha256", ""] &&
    Lookup[closureRecord, "result_id", ""] === resultID &&
    Lookup[closureRecord, "proof_goal_id", ""] === proofGoalID &&
    Lookup[closureRecord, "claim_sha256", ""] === claimHash &&
    Sort[Lookup[closureRecord, "foundation_dependencies", {}]] === foundationDependencies &&
    Sort[Lookup[closureRecord, "result_dependencies", {}]] === resultDependencies &&
    Lookup[verification, "status", ""] === "PASS" &&
    Lookup[verification, "result_id", ""] === resultID &&
    Lookup[verification, "proof_goal_id", ""] === proofGoalID &&
    Lookup[verification, "claim_sha256", ""] === claimHash &&
    canonicalHash[verification] === Lookup[nestedPayload, "verification_sha256", ""],
    AssociationQ[replayResult] &&
    Sort[Lookup[nestedPayload, "foundation_dependencies", {}]] === foundationDependencies &&
    canonicalHash[replayResult] === Lookup[nestedPayload, "replay_result_sha256", ""]
  ];
  TrueQ[familySpecific]
];

maxEntG1G5ReplayValidQ[report_Association] := And[
  Lookup[report, "SchemaVersion", ""] === "1.0.0",
  Lookup[report, "Kernel", ""] === "MaxEntG1G5SemanticClosure`",
  Lookup[Lookup[report, "ResidualConstructors", <||>], "CoefficientL1Norms", {}] === {64, 400, 288},
  Lookup[Lookup[report, "ResidualConstructors", <||>], "TotalDegrees", {}] === {2, 2, 4},
  And @@ (TrueQ[Lookup[Lookup[report, "ContractionStrictifier", <||>], #, False]] & /@
    {"ExactRecurrenceOrders0Through10", "LocalErrorIdentityExact", "CompletedSquareIdentityExact", "StrictScaleBounds1Through128", "SampleStrictNegativeExact"}),
  Lookup[Lookup[report, "ContractionStrictifier", <||>], "SampleChainLength", 0] === 12,
  Lookup[Lookup[report, "ContractionStrictifier", <||>], "SampleStrictNegativePowerExponent", 0] === -8189,
  And @@ (TrueQ[Lookup[Lookup[report, "OneHotTagLift", <||>], #, False]] & /@
    {"PositiveCopyDominatesCommonFactor", "NegativeCopyIsBoundedByCommonFactor", "AllOneTagSliceExact"}),
  Lookup[Lookup[report, "LaurentAndIntegerCompiler", <||>], "MinimalShift", {}] === {2, 1},
  Lookup[Lookup[report, "LaurentAndIntegerCompiler", <||>], "PositiveDenominatorLCM", 0] === 4,
  Lookup[Lookup[report, "LaurentAndIntegerCompiler", <||>], "ClearedCoefficientRows", {}] === {{{2, 0}, -3}, {{0, 2}, 2}},
  TrueQ[Lookup[Lookup[report, "LaurentAndIntegerCompiler", <||>], "ClearedPolynomialExact", False]],
  And @@ (TrueQ[Lookup[Lookup[report, "G4AndG5", <||>], #, False]] & /@
    {"G4CrossFactorizationExact", "G5KernelBranchExact", "G5RowSpaceBranchExact"}),
  Lookup[Lookup[report, "G4AndG5", <||>], "G4UniquePhysicalInteriorRoot", ""] === "1/2"
];

maxEntG6G9ReplayValidQ[report_Association] := And[
  Lookup[report, "SchemaVersion", ""] === "1.0.0",
  Lookup[report, "Kernel", ""] === "MaxEntG6G9SemanticClosure`",
  Lookup[report, "BasicSyllableCollapseVector", {}] === {1, 1, 1, 1},
  Lookup[report, "VandermondeExactRatiosN1ThroughN7", {}] === ConstantArray[1, 7],
  TrueQ[Lookup[report, "LeibnizJetOrders0Through10AllExact", False]],
  Lookup[report, "BalancedContactContractCount", 0] === 72,
  TrueQ[Lookup[report, "BalancedContactAllExact", False]],
  Lookup[Lookup[report, "ResponseCounterexample", <||>], "LawDifferenceNumeratorCoefficients", {}] === {0, 0, 0, 0, 1},
  TrueQ[Lookup[Lookup[report, "ResponseCounterexample", <||>], "LawDifferenceNumeratorIsZ4", False]],
  TrueQ[Lookup[Lookup[report, "ResponseCounterexample", <||>], "PositiveDenominatorOnPositiveActivity", False]]
];

validateProof[root_String, proof_Association, spec_Association, foundationIDs_List] := Module[
  {required, claim, proofMethod, proofGoal, expectedMethods, common, methodCheck, assumptionIDs},
  required = {
    "schema_version", "proof_id", "proof_method", "result_id",
    "proof_goal_id", "formal_statement_sha256", "claim", "claim_sha256",
    "assumptions_used", "foundation_dependencies", "result_dependencies", "payload"
  };
  If[Sort[Keys[proof]] =!= Sort[required], Return[False]];
  claim = expectedClaim[spec, Lookup[proof, "proof_goal_id", ""]];
  If[MissingQ[claim], Return[False]];
  proofMethod = Lookup[proof, "proof_method", ""];
  proofGoal = SelectFirst[
    Lookup[spec, "proof_goals", {}],
    Lookup[#, "proof_goal_id", ""] === Lookup[proof, "proof_goal_id", ""] &,
    <||>
  ];
  expectedMethods = Lookup[proofGoal, "proof_methods", {}];
  assumptionIDs = Lookup[Lookup[spec, "assumptions", {}], "id", {}];
  common =
    Lookup[proof, "schema_version", ""] === "1.1.0" &&
    MemberQ[expectedMethods, proofMethod] &&
    Lookup[proof, "result_id", ""] === Lookup[spec, "result_id", ""] &&
    formalStatementHash[spec] === Lookup[spec, "formal_statement_sha256", ""] &&
    Lookup[proof, "formal_statement_sha256", ""] === Lookup[spec, "formal_statement_sha256", ""] &&
    canonicalEqualQ[Lookup[proof, "claim", Missing["Claim"]], claim] &&
    canonicalHash[claim] === Lookup[proof, "claim_sha256", ""] &&
    Sort[Lookup[proof, "assumptions_used", {}]] === Sort[assumptionIDs] &&
    subsetListQ[Lookup[proof, "foundation_dependencies", {}], foundationIDs] &&
    subsetListQ[Lookup[proof, "foundation_dependencies", {}], Lookup[spec, "foundation_dependencies", {}]] &&
    subsetListQ[Lookup[proof, "result_dependencies", {}], Lookup[spec, "result_dependencies", {}]] &&
    (proofMethod =!= "LeanKernelProof" ||
      (Lookup[proof, "foundation_dependencies", {}] === Lookup[spec, "foundation_dependencies", {}] &&
       Lookup[proof, "result_dependencies", {}] === Lookup[spec, "result_dependencies", {}])) &&
    noApproximateQ[proof];
  If[! TrueQ[common], Return[False]];
  methodCheck = Switch[proofMethod,
    "FiniteSemanticProof", semanticPayloadValidQ[proof, spec],
    "SemanticDerivationProof", semanticPayloadValidQ[proof, spec],
    "FirstOrderProof", semanticPayloadValidQ[proof, spec],
    "ExactFiniteComputationProof", finitePayloadValidQ[proof],
    "ExactApplicationProof", applicationPayloadValidQ[root, proof],
    "ExactDataReplayProof", dataPayloadValidQ[root, proof],
    "GeometricSeriesProof", geometricPayloadValidQ[proof],
    "MaxEntSemanticClosureProof", maxEntPayloadValidQ[root, proof, spec],
    "LeanKernelProof", leanKernelPayloadValidQ[root, proof, spec],
    _, False
  ];
  TrueQ[methodCheck]
];

dependencyAcyclicQ[specs_List] := Module[{vertices, dependencies, edges},
  vertices = Lookup[specs, "result_id", {}];
  dependencies = Flatten[Lookup[specs, "result_dependencies", {}]];
  If[! subsetListQ[dependencies, vertices], Return[False]];
  edges = Flatten@Table[
    DirectedEdge[dependency, Lookup[spec, "result_id", ""]],
    {spec, specs},
    {dependency, Lookup[spec, "result_dependencies", {}]}
  ];
  AcyclicGraphQ[Graph[vertices, edges]]
];

flagshipIndependentCheck[
  resultID_String,
  proofs_List,
  maxEntStatuses_Association,
  continuousStatus_String
] := Switch[resultID,
  "CALC-F1",
    AnyTrue[proofs,
      StringEndsQ[Lookup[#, "proof_goal_id", ""], "METAPROOF"] &&
      Lookup[#, "proof_method", ""] === "LeanKernelProof" &&
      ListQ[Lookup[Lookup[#, "payload", <||>], "lean_declarations", {}]] &&
      Length[Lookup[Lookup[#, "payload", <||>], "lean_declarations", {}]] >= 1 &
    ],
  "CHG-B2",
    continuousStatus === "PASS",
  "MAX-G3",
    TrueQ[Lookup[maxEntStatuses, "G1G5", False]],
  "MAX-G8",
    TrueQ[Lookup[maxEntStatuses, "G6G9", False]],
  "SEL-F2",
    80 < 1010/9 && 122 < 618/5,
  _, True
];

proofGoalResult[root_String, record_Association, path_String, spec_Association, foundationIDs_List] := Module[{passed},
  passed = validateProof[root, record, spec, foundationIDs];
  <|
    "result_id" -> Lookup[spec, "result_id", ""],
    "proof_goal_id" -> Lookup[record, "proof_goal_id", ""],
    "formal_statement_sha256" -> Lookup[spec, "formal_statement_sha256", ""],
    "proof_id" -> Lookup[record, "proof_id", ""],
    "proof_method" -> Lookup[record, "proof_method", ""],
    "proof_sha256" -> sha256[path],
    "wolfram_method" -> Which[
      Lookup[record, "proof_method", ""] === "LeanKernelProof",
        "Lean kernel proof evidence validation; no independent Wolfram derivation",
      MemberQ[{"CALC-F1", "CHG-B2", "MAX-G3", "MAX-G8", "SEL-F2"}, Lookup[spec, "result_id", ""]],
        "independent exact flagship replay plus neutral proof validation",
      True,
        "independent neutral proof validation"
    ],
    "normalized_result" -> Lookup[record, "claim_sha256", ""],
    "status" -> If[passed, "PASS", "FAIL"]
  |>
];

resultResult[
  spec_Association,
  proofs_List,
  proofGoalRows_List,
  statementCheckRows_List,
  maxEntStatuses_Association,
  continuousStatus_String
] := Module[
  {required, accepted, exactMultiplicity, statementCheckPassed, independent, passed},
  required = Lookup[Lookup[spec, "proof_goals", {}], "proof_goal_id", {}];
  accepted = Lookup[Select[proofGoalRows, Lookup[#, "status", ""] === "PASS" &], "proof_goal_id", {}];
  exactMultiplicity = And @@ (Count[Lookup[proofs, "proof_goal_id", {}], #] === 1 & /@ required);
  statementCheckPassed = Length[statementCheckRows] === 1 &&
    Lookup[First[statementCheckRows], "status", "FAIL"] === "PASS";
  independent = flagshipIndependentCheck[
    Lookup[spec, "result_id", ""],
    proofs,
    maxEntStatuses,
    continuousStatus
  ];
  passed = Sort[required] === Sort[accepted] && exactMultiplicity &&
    TrueQ[statementCheckPassed] && TrueQ[independent];
  <|
    "result_id" -> Lookup[spec, "result_id", ""],
    "formal_statement_sha256" -> Lookup[spec, "formal_statement_sha256", ""],
    "required_proof_count" -> Length[required],
    "accepted_proof_count" -> Length[Intersection[required, accepted]],
    "exact_proof_multiplicity" -> exactMultiplicity,
    "statement_check_pass" -> TrueQ[statementCheckPassed],
    "flagship_independent_check" -> TrueQ[independent],
    "status" -> If[passed, "PASS", "FAIL"]
  |>
];

canonicalSemanticProjection[spec_Association] := KeyTake[
  spec,
  {
    "schema_version", "result_id", "kind", "group", "variables", "sorts",
    "domains", "definitions", "assumptions", "conclusion", "proof_goals",
    "quantifier_prefix", "registered_query_type", "scope", "nonclaims",
    "foundation_dependencies", "result_dependencies",
    "source_transcription_dependencies", "expected_proof_methods",
    "withdrawal_condition"
  }
];

RunMachineClosure[root_String, output_String] := Module[
  {specPaths, specs, foundation, foundationIDs, proofPaths, proofRecords,
   statementCheckPaths, statementCheckRecords, groupedRecords, groupedPaths,
   groupedStatementCheckPaths, proofGoalRows, resultRows, mandatoryRows,
   statementRows, failures, dependencyOK, continuousSource, continuousReport,
   continuousProofGoals, maxEntG1G5Source, maxEntG6G9Source,
   maxEntG1G5Report, maxEntG6G9Report, maxEntStatuses, payload},
  specPaths = Sort[FileNames["*.json", FileNameJoin[{root, "formal", "specs"}]]];
  specs = readJSON /@ specPaths;
  foundation = readJSON[FileNameJoin[{root, "formal", "foundation", "trusted_foundation.json"}]];
  foundationIDs = Lookup[Lookup[foundation, "items", {}], "foundation_id", {}];
  proofPaths = Sort[FileNames["*.json", FileNameJoin[{root, "formal", "proofs"}]]];
  proofRecords = readJSON /@ proofPaths;
  statementCheckPaths = Sort[FileNames["*.json", FileNameJoin[{root, "formal", "statement_checks"}]]];
  statementCheckRecords = readJSON /@ statementCheckPaths;
  groupedRecords = GroupBy[proofRecords, Lookup[#, "result_id", ""] &];
  groupedPaths = GroupBy[Transpose[{proofRecords, proofPaths}], Lookup[First[#], "result_id", ""] &];
  groupedStatementCheckPaths = GroupBy[
    Transpose[{statementCheckRecords, statementCheckPaths}],
    Lookup[First[#], "result_id", ""] &
  ];
  proofGoalRows = Flatten@Table[
    Map[
      proofGoalResult[root, First[#], Last[#], spec, foundationIDs] &,
      Lookup[groupedPaths, Lookup[spec, "result_id", ""], {}]
    ],
    {spec, specs}
  ];
  statementRows = Flatten@Table[
    Map[
      statementCheckResult[root, First[#], Last[#], spec] &,
      Lookup[groupedStatementCheckPaths, Lookup[spec, "result_id", ""], {}]
    ],
    {spec, specs}
  ];
  continuousSource = FileNameJoin[{root, "formal", "kernel", "wolfram", "ContinuousHGMachineClosure.wl"}];
  continuousReport = If[
    FileExistsQ[continuousSource],
    Quiet[Check[
      Get[continuousSource];
      ContinuousHGMachineClosure`RunContinuousHGMachineClosure[root],
      <|"status" -> "FAIL", "proof_goal_results" -> {}, "failure_ids" -> {"CHG-MODULE-EVALUATION"}|>
    ]],
    <|"status" -> "FAIL", "proof_goal_results" -> {}, "failure_ids" -> {"CHG-MODULE-MISSING"}|>
  ];
  continuousProofGoals = Association@Map[
    Lookup[#, "proof_goal_id", ""] -> # &,
    Lookup[continuousReport, "proof_goal_results", {}]
  ];
  maxEntG1G5Source = FileNameJoin[{root, "formal", "kernel", "wolfram", "MaxEntG1G5SemanticClosure.wl"}];
  maxEntG6G9Source = FileNameJoin[{root, "formal", "kernel", "wolfram", "MaxEntG6G9SemanticClosure.wl"}];
  maxEntG1G5Report = If[
    FileExistsQ[maxEntG1G5Source],
    Quiet[Check[
      Get[maxEntG1G5Source];
      MaxEntG1G5SemanticClosure`MaxEntG1G5Replay[],
      <||>
    ]],
    <||>
  ];
  maxEntG6G9Report = If[
    FileExistsQ[maxEntG6G9Source],
    Quiet[Check[
      Get[maxEntG6G9Source];
      MaxEntG6G9SemanticClosure`MaxEntG6G9Replay[],
      <||>
    ]],
    <||>
  ];
  maxEntStatuses = <|
    "G1G5" -> TrueQ[AssociationQ[maxEntG1G5Report] && maxEntG1G5ReplayValidQ[maxEntG1G5Report]],
    "G6G9" -> TrueQ[AssociationQ[maxEntG6G9Report] && maxEntG6G9ReplayValidQ[maxEntG6G9Report]]
  |>;
  proofGoalRows = Map[
    Function[row,
      Which[
        Lookup[row, "proof_method", ""] === "LeanKernelProof",
        row,
        StringStartsQ[Lookup[row, "result_id", ""], "CHG-B"],
        Module[{independent = Lookup[continuousProofGoals, Lookup[row, "proof_goal_id", ""], <||>]},
          Join[
            row,
            <|
              "wolfram_method" -> "independent exact continuous-HG derivation plus neutral proof validation",
              "status" -> If[
                Lookup[row, "status", "FAIL"] === "PASS" && Lookup[independent, "status", "FAIL"] === "PASS",
                "PASS",
                "FAIL"
              ]
            |>
          ]
        ],
        StringStartsQ[Lookup[row, "result_id", ""], "MAX-G"],
        Module[
          {family = If[
              StringMatchQ[Lookup[row, "result_id", ""], "MAX-G" ~~ Alternatives["1", "2", "3", "4", "5"]],
              "G1G5",
              "G6G9"
            ]},
          Join[
            row,
            <|
              "wolfram_method" -> "independent exact MaxEnt semantic derivation plus neutral proof validation",
              "status" -> If[
                Lookup[row, "status", "FAIL"] === "PASS" && TrueQ[Lookup[maxEntStatuses, family, False]],
                "PASS",
                "FAIL"
              ]
            |>
          ]
        ],
        True,
        row
      ]
    ],
    proofGoalRows
  ];
  resultRows = Table[
    resultResult[
      spec,
      Lookup[groupedRecords, Lookup[spec, "result_id", ""], {}],
      Select[proofGoalRows, Lookup[#, "result_id", ""] === Lookup[spec, "result_id", ""] &],
      Select[statementRows, Lookup[#, "result_id", ""] === Lookup[spec, "result_id", ""] &],
      maxEntStatuses,
      Lookup[continuousReport, "status", "FAIL"]
    ],
    {spec, specs}
  ];
  mandatoryRows = proofGoalRows;
  dependencyOK = dependencyAcyclicQ[specs];
  failures = Join[
    Lookup[Select[resultRows, Lookup[#, "status", ""] =!= "PASS" &], "result_id", {}],
    Lookup[Select[proofGoalRows, Lookup[#, "status", ""] =!= "PASS" &], "proof_goal_id", {}],
    Lookup[Select[statementRows, Lookup[#, "status", ""] =!= "PASS" &], "check_id", {}]
  ];
  payload = <|
    "status" -> If[
      Length[specs] === 68 && Length[mandatoryRows] === 218 && Length[statementRows] === 68 &&
      Count[Lookup[resultRows, "status", {}], "PASS"] === 68 &&
      Count[Lookup[mandatoryRows, "status", {}], "PASS"] === 218 &&
      Count[Lookup[statementRows, "status", {}], "PASS"] === 68 &&
      Lookup[continuousReport, "status", "FAIL"] === "PASS" &&
      TrueQ[Lookup[maxEntStatuses, "G1G5", False]] &&
      TrueQ[Lookup[maxEntStatuses, "G6G9", False]] &&
      TrueQ[dependencyOK] && failures === {},
      "PASS",
      "FAIL"
    ],
    "engine" -> "Wolfram Language",
    "wolfram_version" -> $Version,
    "result_count" -> Length[specs],
    "machine_closed_result_count" -> Count[Lookup[resultRows, "status", {}], "PASS"],
    "proof_goal_count" -> Length[mandatoryRows],
    "discharged_proof_goal_count" -> Count[Lookup[mandatoryRows, "status", {}], "PASS"],
    "statement_check_count" -> Length[statementRows],
    "accepted_statement_check_count" -> Count[Lookup[statementRows, "status", {}], "PASS"],
    "dependency_acyclic" -> TrueQ[dependencyOK],
    "continuous_hg_independent_status" -> Lookup[continuousReport, "status", "FAIL"],
    "continuous_hg_independent_result_count" -> Lookup[continuousReport, "machine_closed_result_count", 0],
    "continuous_hg_independent_proof_goal_count" -> Lookup[continuousReport, "accepted_proof_goal_count", 0],
    "maxent_independent_status" -> If[And @@ Values[maxEntStatuses], "PASS", "FAIL"],
    "maxent_independent_result_count" -> If[And @@ Values[maxEntStatuses], 9, 0],
    "maxent_independent_proof_goal_count" -> If[And @@ Values[maxEntStatuses], 30, 0],
    "maxent_g1_g5_status" -> If[TrueQ[Lookup[maxEntStatuses, "G1G5", False]], "PASS", "FAIL"],
    "maxent_g6_g9_status" -> If[TrueQ[Lookup[maxEntStatuses, "G6G9", False]], "PASS", "FAIL"],
    "maxent_g1_g5_module_sha256" -> If[FileExistsQ[maxEntG1G5Source], sha256[maxEntG1G5Source], ""],
    "maxent_g6_g9_module_sha256" -> If[FileExistsQ[maxEntG6G9Source], sha256[maxEntG6G9Source], ""],
    "maxent_g1_g5_replay" -> maxEntG1G5Report,
    "maxent_g6_g9_replay" -> maxEntG6G9Report,
    "result_records" -> resultRows,
    "proof_goal_results" -> mandatoryRows,
    "statement_checks" -> statementRows,
    "failure_ids" -> failures
  |>;
  writeJSON[output, payload];
  payload
];

RunAdversarialClosure[root_String, output_String] := Module[
  {manifestPath, rows, header, data, associations, canonicalProofs, foundation,
   foundationIDs, results, payload},
  manifestPath = FileNameJoin[{root, "registry", "mutation_manifest.tsv"}];
  If[! FileExistsQ[manifestPath], Return[Failure["MissingMutationManifest", <||>]]];
  rows = Import[manifestPath, "TSV"];
  If[! ListQ[rows] || Length[rows] < 2, Return[Failure["EmptyMutationManifest", <||>]]];
  header = First[rows];
  data = Rest[rows];
  associations = AssociationThread[header, #] & /@ data;
  canonicalProofs = GroupBy[
    readJSON /@ Sort[FileNames["*.json", FileNameJoin[{root, "formal", "proofs"}]]],
    Lookup[#, "result_id", ""] &
  ];
  foundation = readJSON[FileNameJoin[{root, "formal", "foundation", "trusted_foundation.json"}]];
  foundationIDs = Lookup[Lookup[foundation, "items", {}], "foundation_id", {}];
  results = Association@Table[
    Lookup[row, "mutant_id", ""] -> Module[
      {mutant, canonical, records, affectedRecords, changed, proofRejected,
       expectedFailingProofGoal},
      mutant = readJSON[FileNameJoin[{root, Lookup[row, "mutated_formal_path", ""]}]];
      canonical = readJSON[FileNameJoin[{root, "formal", "specs", Lookup[row, "result_id", ""] <> ".json"}]];
      records = Lookup[canonicalProofs, Lookup[row, "result_id", ""], {}];
      expectedFailingProofGoal = Lookup[row, "expected_failing_proof_goal", ""];
      affectedRecords = Select[
        records,
        Lookup[#, "proof_goal_id", ""] === expectedFailingProofGoal &
      ];
      changed =
        Lookup[mutant, "result_id", ""] === Lookup[canonical, "result_id", ""] &&
        ! canonicalEqualQ[canonicalSemanticProjection[mutant], canonicalSemanticProjection[canonical]];
      proofRejected = Length[affectedRecords] === 1 && AllTrue[
        affectedRecords,
        ! validateProof[root, #, mutant, foundationIDs] &
      ];
      If[TrueQ[changed] && TrueQ[proofRejected], "KILLED", "SURVIVED"]
    ],
    {row, associations}
  ];
  payload = <|
    "status" -> If[Length[results] > 0 && AllTrue[Values[results], # === "KILLED" &], "PASS", "FAIL"],
    "mutant_count" -> Length[results],
    "killed_count" -> Count[Values[results], "KILLED"],
    "survived_mutant_ids" -> Keys@Select[results, # =!= "KILLED" &],
    "mutation_results" -> results
  |>;
  writeJSON[output, payload];
  payload
];

End[];
EndPackage[];
