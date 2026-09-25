ClearAll["Global`*"];
dir = DirectoryName[$InputFileName];
Get[FileNameJoin[{dir,"MaxEntG1G5.wl"}]];
Get[FileNameJoin[{dir,"MaxEntG6G9.wl"}]];
a = MaxEntG1G5Calculations`MaxEntG1G5Results[];
b = MaxEntG6G9Calculations`MaxEntG6G9Results[];
checks = {
  a["ResidualConstructors"]["CoefficientL1Norms"] === {64,400,288},
  a["ResidualConstructors"]["TotalDegrees"] === {2,2,4},
  And @@ Lookup[a["ContractionStrictifier"],{
    "ExactRecurrenceOrders0Through10","LocalErrorIdentityExact",
    "CompletedSquareIdentityExact","StrictScaleBounds1Through128","SampleStrictNegativeExact"}],
  a["ContractionStrictifier"]["SampleChainLength"] === 12,
  a["ContractionStrictifier"]["SampleStrictNegativePowerExponent"] === -8189,
  And @@ Values[a["OneHotTagLift"]],
  a["LaurentAndIntegerCompiler"]["MinimalShift"] === {2,1},
  a["LaurentAndIntegerCompiler"]["PositiveDenominatorLCM"] === 4,
  a["LaurentAndIntegerCompiler"]["ClearedCoefficientRows"] === {{{2,0},-3},{{0,2},2}},
  a["LaurentAndIntegerCompiler"]["ClearedPolynomialExact"],
  a["LaurentAndIntegerCompiler"]["IntegerCompilerCoefficientL1"] === 3,
  And @@ Lookup[a["G4AndG5"],{"G4CrossFactorizationExact","G5KernelBranchExact","G5RowSpaceBranchExact"}],
  a["G4AndG5"]["G4UniquePhysicalInteriorRoot"] === "1/2",
  Lookup[a["G4AndG5"]["G4ProbabilityTable"],"LeftProbability"] === {"32/59","4/5","32/33"},
  Lookup[a["G4AndG5"]["G4ProbabilityTable"],"RightProbability"] === {"16/25","4/5","16/17"},
  b["BasicSyllableCollapseVector"] === {1,1,1,1},
  b["VandermondeExactRatiosN1ThroughN7"] === ConstantArray[1,7],
  b["LeibnizJetOrders0Through10AllExact"],
  b["BalancedContactContractCount"] === 72,
  b["BalancedContactAllExact"],
  b["ResponseCounterexample"]["LawDifferenceNumeratorCoefficients"] === {0,0,0,0,1},
  b["ResponseCounterexample"]["LawDifferenceNumeratorIsZ4"],
  b["ResponseCounterexample"]["PositiveDenominatorOnPositiveActivity"]
};
failures = Select[Range[Length[checks]], checks[[#]] =!= True &];
root = DirectoryName[DirectoryName[dir]];
output = FileNameJoin[{root,"results","maxent","package_checks.json"}];
If[!DirectoryQ[DirectoryName[output]], CreateDirectory[DirectoryName[output],CreateIntermediateDirectories->True]];
Export[output,<|"status"->If[failures==={},"PASS","FAIL_OR_UNRESOLVED"],
  "checks"->Length[checks],"failures"->failures,"G1G5"->a,"G6G9"->b|>,"RawJSON"];
Print[If[failures==={},"PASS","FAIL_OR_UNRESOLVED"]," ",Length[checks]," checks; failures=",failures];
Exit[If[failures==={},0,1]];
