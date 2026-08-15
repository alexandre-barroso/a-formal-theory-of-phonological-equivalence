System`$HistoryLength = 0;

ClearAll[
  $cliSourcePath, $wolframKernelDirectory, $deliverablesRoot,
  $verificationSource, $exporterSource, $machineClosureSource,
  $defaultOutputDirectory, $operationTimeLimitSeconds,
  CliArguments, OptionValueAfter, EnsureDirectory, RunBoundedOperation,
  WriteStatus, HelpText, RunVerificationSelection, LoadMachineClosure,
  RunMachineValidation, RunAdversarialValidation,
  RunCLI, DirectFileExecutionQ
];

$cliSourcePath = If[
  StringQ[$InputFileName] && StringLength[$InputFileName] > 0,
  ExpandFileName[$InputFileName],
  Missing["SourcePathUnavailable"]
];

$wolframKernelDirectory = If[StringQ[$cliSourcePath], DirectoryName[$cliSourcePath], Missing["KernelDirectoryUnavailable"]];
$deliverablesRoot = If[StringQ[$wolframKernelDirectory], Nest[DirectoryName, $wolframKernelDirectory, 3], Missing["DeliverablesRootUnavailable"]];
$verificationSource = If[StringQ[$deliverablesRoot], FileNameJoin[{$deliverablesRoot, "verification", "wolfram", "SecondOrderPhonologyVerification.wl"}], Missing["VerificationSourceUnavailable"]];
$exporterSource = If[StringQ[$wolframKernelDirectory], FileNameJoin[{$wolframKernelDirectory, "SecondOrderProofExporter.wl"}], Missing["ExporterSourceUnavailable"]];
$machineClosureSource = If[StringQ[$wolframKernelDirectory], FileNameJoin[{$wolframKernelDirectory, "SecondOrderMachineClosure.wl"}], Missing["MachineClosureSourceUnavailable"]];
$defaultOutputDirectory = If[StringQ[$deliverablesRoot], FileNameJoin[{$deliverablesRoot, "formal", "traces", "wolfram"}], Missing["OutputDirectoryUnavailable"]];
$operationTimeLimitSeconds = 600;

CliArguments[] := If[ListQ[$ScriptCommandLine] && Length[$ScriptCommandLine] > 0, Rest[$ScriptCommandLine], {}];

OptionValueAfter[arguments_List, option_String, default_] := Module[
  {position = FirstPosition[arguments, option, Missing["Absent"]]},
  If[MissingQ[position] || First[position] >= Length[arguments], default, arguments[[First[position] + 1]]]
];

EnsureDirectory[path_String] := If[DirectoryQ[path], path, CreateDirectory[path, CreateIntermediateDirectories -> True]];

SetAttributes[RunBoundedOperation, HoldRest];
RunBoundedOperation[label_String, operation_] := Module[{started, result},
  started = AbsoluteTime[];
  System`Print["Starting Wolfram operation: ", label, "."];
  result = TimeConstrained[
    operation,
    $operationTimeLimitSeconds,
    Failure[
      "OperationTimedOut",
      <|
        "Operation" -> label,
        "TimeLimitSeconds" -> $operationTimeLimitSeconds
      |>
    ]
  ];
  System`Print[
    "Finished Wolfram operation: ", label, " (",
    ToString[
      NumberForm[N[AbsoluteTime[] - started], {10, 3}],
      OutputForm
    ],
    " s)."
  ];
  result
];

WriteStatus[directory_String, name_String, status_Association] := Module[{target, path},
  target = EnsureDirectory[ExpandFileName[directory]];
  path = FileNameJoin[{target, name}];
  Export[path, status, "RawJSON", "Compact" -> False];
  path
];

HelpText[] := StringRiffle[{
  "Second-order phonological calculus Wolfram proof interface",
  "",
  "Usage:",
  "  wolframscript -script formal/kernel/wolfram/SecondOrderProofCLI.wl [actions] [options]",
  "",
  "Actions:",
  "  --export-proofs        Export the neutral exact trace and validate canonical proofs.",
  "  --run-result <ID>            Run one exact verification result.",
  "  --run-group <GROUP>          Run one verification group.",
  "  --run-all                    Run all exact verification results.",
  "  --machine-closed             Require 68 registered results and 218 registered proof goals, all discharged.",
  "  --adversarial                Run the Wolfram adversarial proof-binding suite.",
  "  --help                       Show this help.",
  "",
  "Options:",
  "  --output <DIRECTORY>         Output directory; defaults to formal/traces/wolfram.",
  "  --mode <MODE>                Verification mode; defaults to machine-strict.",
  "",
  "Exit codes:",
  "  0  every requested operation passed",
  "  1  at least one requested proof or mutation check failed",
  "  2  invalid invocation or unknown result/group",
  "  3  internal evaluation or export failure"
}, "\n"];

RunVerificationSelection[arguments_List, mode_String, output_String] := Module[{report, item, identifier, paths},
  If[! StringQ[$verificationSource] || ! FileExistsQ[$verificationSource], Return[Failure["MissingVerificationSource", <|"Path" -> $verificationSource|>]]];
  Get[$verificationSource];
  report = Which[
    MemberQ[arguments, "--run-result"],
      identifier = OptionValueAfter[arguments, "--run-result", ""];
      If[identifier === "", Return[Failure["MissingResultID", <||>]]];
      item = SecondOrderPhonologyVerification`RunResultVerification[identifier, "Mode" -> mode];
      If[FailureQ[item], item, SecondOrderPhonologyVerification`Private`makeRunReport[{item}, mode, 60, 1073741824, item["ElapsedSeconds"], <|"Selection" -> "ID", "ID" -> identifier|>]],
    MemberQ[arguments, "--run-group"],
      identifier = OptionValueAfter[arguments, "--run-group", ""];
      If[identifier === "", Return[Failure["MissingGroupID", <||>]]];
      SecondOrderPhonologyVerification`RunVerificationGroup[identifier, "Mode" -> mode],
    True,
      SecondOrderPhonologyVerification`RunAllVerification["Mode" -> mode]
  ];
  If[FailureQ[report], Return[report]];
  paths = SecondOrderPhonologyVerification`ExportVerificationReport[report, output];
  <|"Report" -> report, "Paths" -> paths|>
];

LoadMachineClosure[] := Module[{},
  If[! StringQ[$machineClosureSource] || ! FileExistsQ[$machineClosureSource], Return[Failure["MissingMachineClosureSource", <|"Path" -> $machineClosureSource|>]]];
  Get[$machineClosureSource];
  True
];

RunMachineValidation[output_String] := Module[{loaded, result, statusPath},
  loaded = LoadMachineClosure[];
  If[FailureQ[loaded], Return[loaded]];
  EnsureDirectory[output];
  result = SecondOrderMachineClosure`RunMachineClosure[$deliverablesRoot, FileNameJoin[{output, "machine_closure.json"}]];
  statusPath = WriteStatus[output, "machine_closure_status.json", <|
    "status" -> If[Lookup[result, "status", "FAIL"] === "PASS", "MachineClosed", "BuildFailure"],
    "machine_closed" -> (Lookup[result, "status", "FAIL"] === "PASS"),
    "result_count" -> Lookup[result, "result_count", 0],
    "proof_goal_count" -> Lookup[result, "proof_goal_count", 0],
    "wolfram_version" -> $Version
  |>];
  <|"Result" -> result, "StatusPath" -> statusPath|>
];

RunAdversarialValidation[output_String] := Module[{loaded, result, statusPath},
  loaded = LoadMachineClosure[];
  If[FailureQ[loaded], Return[loaded]];
  EnsureDirectory[output];
  result = SecondOrderMachineClosure`RunAdversarialClosure[$deliverablesRoot, FileNameJoin[{output, "adversarial_results.json"}]];
  If[FailureQ[result], Return[result]];
  statusPath = WriteStatus[output, "adversarial_status.json", <|
    "status" -> Lookup[result, "status", "FAIL"],
    "machine_closed" -> (Lookup[result, "status", "FAIL"] === "PASS"),
    "mutant_count" -> Lookup[result, "mutant_count", 0],
    "killed_count" -> Lookup[result, "killed_count", 0]
  |>];
  <|"Result" -> result, "StatusPath" -> statusPath|>
];

RunCLI[] := Module[
  {arguments, output, mode, wantsVerification, wantsExport,
   wantsMachineClosure, wantsAdversarial, result, neutral, failures = {}, invalid},
  arguments = CliArguments[];
  If[arguments === {} || MemberQ[arguments, "--help"], System`Print[HelpText[]]; Return[0]];
  invalid = Count[arguments, "--run-result"] + Count[arguments, "--run-group"] > 1;
  If[invalid, System`Print["--run-result and --run-group are mutually exclusive."]; Return[2]];
  output = OptionValueAfter[arguments, "--output", $defaultOutputDirectory];
  mode = OptionValueAfter[arguments, "--mode", "machine-strict"];
  If[! StringQ[output] || ! StringQ[mode], Return[2]];
  wantsVerification = MemberQ[arguments, "--run-all"] || MemberQ[arguments, "--run-result"] || MemberQ[arguments, "--run-group"];
  wantsExport = MemberQ[arguments, "--export-proofs"];
  wantsMachineClosure = MemberQ[arguments, "--machine-closed"] || wantsExport;
  wantsAdversarial = MemberQ[arguments, "--adversarial"];
  If[! Or[wantsVerification, wantsExport, wantsMachineClosure, wantsAdversarial], System`Print["No recognized action was selected."]; Return[2]];
  EnsureDirectory[output];
  If[wantsVerification,
    result = RunBoundedOperation[
      "verification",
      RunVerificationSelection[arguments, mode, output]
    ];
    If[FailureQ[result], AppendTo[failures, "verification"],
      If[
        Lookup[result["Report"], "ReleaseClosed", False] =!= True ||
        Lookup[result["Report"], "MandatoryIncompleteResultCount", 1] =!= 0 ||
        Lookup[result["Report"], "BuildFailureResultCount", 1] =!= 0,
        AppendTo[failures, "verification"]
      ]
    ]
  ];
  If[wantsExport,
    If[! StringQ[$exporterSource] || ! FileExistsQ[$exporterSource],
      AppendTo[failures, "neutral-export"],
      Get[$exporterSource];
      neutral = RunBoundedOperation[
        "neutral-proof export",
        SecondOrderProofExporter`ExportNeutralProofGoals[
          $verificationSource,
          FileNameJoin[{output, "neutral_proof_goals.json"}],
          "SourceLabel" -> "verification/wolfram/SecondOrderPhonologyVerification.wl"
        ]
      ];
      If[FailureQ[neutral] || Lookup[neutral, "failure_ids", {"failure"}] =!= {}, AppendTo[failures, "neutral-export"]]
    ]
  ];
  If[wantsMachineClosure,
    result = RunBoundedOperation[
      "machine closure",
      RunMachineValidation[output]
    ];
    If[FailureQ[result] || Lookup[result["Result"], "status", "FAIL"] =!= "PASS", AppendTo[failures, "machine-closure"]]
  ];
  If[wantsAdversarial,
    result = RunBoundedOperation[
      "adversarial validation",
      RunAdversarialValidation[output]
    ];
    If[FailureQ[result] || Lookup[result["Result"], "status", "FAIL"] =!= "PASS", AppendTo[failures, "adversarial"]]
  ];
  If[failures === {}, System`Print["All requested Wolfram checks passed."], System`Print["Wolfram checks failed: ", DeleteDuplicates[failures]]];
  If[failures === {}, 0, 1]
];

DirectFileExecutionQ[] := TrueQ[
  StringQ[$cliSourcePath] && ListQ[$ScriptCommandLine] && Length[$ScriptCommandLine] > 0 &&
  Quiet[Check[ExpandFileName[First[$ScriptCommandLine]] === $cliSourcePath, False]]
];

If[DirectFileExecutionQ[], System`Exit[RunCLI[]]];
