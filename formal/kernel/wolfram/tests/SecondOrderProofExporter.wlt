
VerificationTest[
  SecondOrderProofExporter`HeldExpressionAST[HoldComplete[1/3]]["root", "kind"],
  "call",
  TestID -> "Held-rational-syntax-remains-a-call"
]

VerificationTest[
  SecondOrderProofExporter`HeldExpressionAST[HoldComplete[1/3]]["root", "head", "name"],
  "System`Times",
  TestID -> "Held-rational-head-is-preserved"
]

VerificationTest[
  SecondOrderProofExporter`HeldExpressionAST[
    HoldComplete[Association["x" -> 1, "y" -> 2]]]["root", "head", "name"],
  "System`Association",
  TestID -> "Association-head-is-preserved"
]

VerificationTest[
  SecondOrderProofExporter`ProofMethodFor[
    "MAX-G3", "ReductionProofPass"],
  "FiniteReductionProof",
  TestID -> "Reduction-classification"
]

VerificationTest[
  SecondOrderProofExporter`ProofMethodFor[
    "DATA-PT-R1", "ExhaustiveFinitePass"],
  "DatasetReplayProof",
  TestID -> "Dataset-classification-precedence"
]

VerificationTest[
  SecondOrderProofExporter`ProofMethodFor[
    "CHG-B1", "LeanKernelProofReferenceCheck"],
  "LeanKernelProofReferenceCheck",
  TestID -> "Lean-kernel-proof-is-exported-as-reference-check"
]

Global`heldSentinel = 17;

VerificationTest[
  SecondOrderProofExporter`HeldExpressionAST[
    HoldComplete[Global`heldSentinel]]["root", "name"],
  "Global`heldSentinel",
  TestID -> "Owned-symbol-value-is-not-evaluated"
]

Clear[Global`heldSentinel];
