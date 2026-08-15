Global`continuousHGSearchRoots = DeleteDuplicates@Flatten[
  ({#, FileNameJoin[{#, "deliverables"}]} &) /@
    NestList[DirectoryName, Directory[], 8]
];
Global`continuousHGDeliverablesRoot = SelectFirst[
  Global`continuousHGSearchRoots,
  FileExistsQ[FileNameJoin[{#, "formal", "specs", "CHG-B1.json"}]] &,
  Missing["DeliverablesRootNotFound"]
];

VerificationTest[
  MissingQ[Global`continuousHGDeliverablesRoot],
  False,
  TestID -> "Continuous-HG-deliverables-root-is-discoverable"
]

If[! MissingQ[Global`continuousHGDeliverablesRoot],
  Get[FileNameJoin[{Global`continuousHGDeliverablesRoot, "formal", "kernel", "wolfram", "ContinuousHGMachineClosure.wl"}]];
  Global`continuousHGReport = ContinuousHGMachineClosure`RunContinuousHGMachineClosure[
    Global`continuousHGDeliverablesRoot
  ],
  Global`continuousHGReport = <|
    "status" -> "FAIL",
    "result_count" -> 0,
    "machine_closed_result_count" -> 0,
    "proof_goal_count" -> 0,
    "accepted_proof_goal_count" -> 0,
    "failure_ids" -> {"DeliverablesRootNotFound"}
  |>
];

VerificationTest[
  Lookup[Global`continuousHGReport, "status"],
  "PASS",
  TestID -> "All-continuous-HG-results-machine-close"
]

VerificationTest[
  Lookup[Global`continuousHGReport, {"result_count", "machine_closed_result_count"}],
  {16, 16},
  TestID -> "Sixteen-continuous-HG-results-covered"
]

VerificationTest[
  Lookup[Global`continuousHGReport, {"proof_goal_count", "accepted_proof_goal_count"}],
  {66, 66},
  TestID -> "Sixty-six-continuous-HG-proof_goals-covered"
]

VerificationTest[
  Lookup[Global`continuousHGReport, "failure_ids"],
  {},
  TestID -> "No-continuous-HG-failure-identifiers"
]

VerificationTest[
  ContinuousHGMachineClosure`ReplayContinuousHGComponent[
    "CHG-B2",
    "equality_boundary",
    <||>,
    {"FOUND-FINITE-001", "FOUND-REAL-001", "FOUND-CONVEX-001", "FOUND-KKT-001", "FOUND-LIMIT-001"}
  ],
  {4, {1, 3/5, 3/10, 1/10, 0, 0, 0}, 3, 0},
  TestID -> "Strict-first-zero-boundary-is-exact"
]

VerificationTest[
  Lookup[
    ContinuousHGMachineClosure`ReplayContinuousHGComponent[
      "CHG-B16",
      "positivity_equivalence",
      <||>,
      {"FOUND-REAL-001", "FOUND-LIMIT-001"}
    ],
    {"finite_p_positivity_iff", "does_not_imply_full_phase_two"}
  ],
  {"p*rho>1", True},
  TestID -> "Finite-p-positivity-does-not-upcast-phase-membership"
]

VerificationTest[
  FailureQ[
    ContinuousHGMachineClosure`ReplayContinuousHGComponent[
      "CHG-B16",
      "universal_result",
      <||>,
      {"FOUND-REAL-001"}
    ]
  ],
  True,
  TestID -> "Missing-foundation-dependency-fails-closed"
]

Clear[
  Global`continuousHGSearchRoots,
  Global`continuousHGDeliverablesRoot,
  Global`continuousHGReport
];
