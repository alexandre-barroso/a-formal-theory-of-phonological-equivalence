(* Exact independent Wolfram replay for MAX-G1--MAX-G5 semantic closure. *)

BeginPackage["MaxEntG1G5SemanticClosure`"];

MaxEntG1G5Replay::usage =
  "MaxEntG1G5Replay[] returns exact cross-engine anchors for the MAX-G1--MAX-G5 semantic proof schemas.";
ExportMaxEntG1G5Replay::usage =
  "ExportMaxEntG1G5Replay[path] exports the exact neutral JSON replay record.";

Begin["`Private`"];

ClearAll[coefficientL1];
coefficientL1[polynomial_, variables_List] :=
  Total[Abs[Last /@ CoefficientRules[Expand[polynomial], variables]]];

ClearAll[totalDegree];
totalDegree[polynomial_, variables_List] :=
  Max[Total /@ First /@ CoefficientRules[Expand[polynomial], variables]];

ClearAll[residualConstructorChecks];
residualConstructorChecks[] := Module[
  {u1, u2, u3, x1, x2, x3, residuals},
  x1 = (1 + 3 u1)/2;
  x2 = (1 + 3 u2)/2;
  x3 = (1 + 3 u3)/2;
  residuals = Expand /@ {
    16 (x1 - 1)^2,
    16 (x1 + x2 - x3)^2,
    16 (x1 x2 - 1)^2
  };
  <|
    "CoefficientL1Norms" ->
      MapThread[coefficientL1, {residuals, {{u1}, {u1, u2, u3}, {u1, u2}}}],
    "TotalDegrees" ->
      MapThread[totalDegree, {residuals, {{u1}, {u1, u2, u3}, {u1, u2}}}]
  |>
];

ClearAll[chainChecks];
chainChecks[] := Module[
  {a, recurrence, localIdentity, completedSquare, strictScales},
  a[index_Integer] := 2^(-(2^index - 1));
  recurrence = And @@ Table[2 a[index + 1] == a[index]^2, {index, 0, 10}];
  localIdentity = Expand[
      (rho + r^2)/2 - a^2/2 -
        (rho/2 + (r + a) (r - a)/2)
    ] === 0;
  completedSquare = Expand[
      t^2 - 2 (a + t/2)^2 + 4 a^2 - (t - 2 a)^2/2
    ] === 0;
  strictScales = And @@ Table[
      With[{m = Ceiling[Log[2, bound + 3]]},
        2^(m + 1) > bound + 3 && 2 a[m]^2 < 2^(-bound)
      ],
      {bound, 1, 128}
    ];
  <|
    "ExactRecurrenceOrders0Through10" -> recurrence,
    "LocalErrorIdentityExact" -> localIdentity,
    "CompletedSquareIdentityExact" -> completedSquare,
    "StrictScaleBounds1Through128" -> strictScales,
    "SampleGapExponent" -> 2176,
    "SampleChainLength" -> Ceiling[Log[2, 2176 + 3]],
    "SampleStrictNegativePowerExponent" ->
      1 - 2 (2^Ceiling[Log[2, 2176 + 3]] - 1),
    "SampleStrictNegativeExact" ->
      -2 a[Ceiling[Log[2, 2176 + 3]]]^2 == -2^-8189
  |>
];

ClearAll[oneHotTagDominationChecks];
oneHotTagDominationChecks[] := <|
  "PositiveCopyDominatesCommonFactor" -> And @@ Table[
    FullSimplify[t^(2 - gamma) >= t^2, Assumptions -> 0 < t <= 1],
    {gamma, 0, 1}
  ],
  "NegativeCopyIsBoundedByCommonFactor" -> And @@ Table[
    FullSimplify[t^(2 + gamma) <= t^2, Assumptions -> 0 < t <= 1],
    {gamma, 0, 1}
  ],
  "AllOneTagSliceExact" -> And @@ Table[
    1^(2 - gamma) == 1^2 && 1^(2 + gamma) == 1^2,
    {gamma, 0, 1}
  ]
|>;

ClearAll[laurentAndCompilerChecks];
laurentAndCompilerChecks[] := Module[
  {z1, z2, source, cleared},
  source = z1^-2 z2/2 - 3 z2^-1/4;
  cleared = Expand[4 z1^2 z2 source];
  <|
    "MinimalShift" -> {2, 1},
    "PositiveDenominatorLCM" -> 4,
    "ClearedCoefficientRows" -> {{{2, 0}, -3}, {{0, 2}, 2}},
    "ClearedPolynomialExact" -> Expand[cleared - (2 z2^2 - 3 z1^2)] === 0,
    "IntegerCompilerCoefficientL1" -> coefficientL1[-z1 + 2 z1^2, {z1}]
  |>
];

ClearAll[g4AndG5Checks];
g4AndG5Checks[] := Module[
  {z, left, right, cross, probabilities},
  left = 1/(1 + 2 z^3);
  right = 1/(1 + z^2);
  cross = Expand[2 z^3 - z^2];
  probabilities = Table[
    <|
      "Activity" -> ToString[activity, InputForm],
      "LeftProbability" -> ToString[Together[left /. z -> activity], InputForm],
      "RightProbability" -> ToString[Together[right /. z -> activity], InputForm]
    |>,
    {activity, {3/4, 1/2, 1/4}}
  ];
  <|
    "G4CrossFactorizationExact" -> Factor[cross] === z^2 (-1 + 2 z),
    "G4ProbabilityTable" -> probabilities,
    "G4UniquePhysicalInteriorRoot" -> ToString[z /. First[Solve[cross == 0 && 0 < z < 1, z, Reals]], InputForm],
    "G5KernelBranchExact" -> {{1, -1}}.{1/2, 1/2} === {0},
    "G5RowSpaceBranchExact" -> Transpose[IdentityMatrix[2]].{1, 1} === {1, 1}
  |>
];

MaxEntG1G5Replay[] := <|
  "SchemaVersion" -> "1.0.0",
  "Kernel" -> "MaxEntG1G5SemanticClosure`",
  "ResidualConstructors" -> residualConstructorChecks[],
  "ContractionStrictifier" -> chainChecks[],
  "OneHotTagLift" -> oneHotTagDominationChecks[],
  "LaurentAndIntegerCompiler" -> laurentAndCompilerChecks[],
  "G4AndG5" -> g4AndG5Checks[]
|>;

ExportMaxEntG1G5Replay[path_String] := Export[path, MaxEntG1G5Replay[], "RawJSON"];

End[];
EndPackage[];
