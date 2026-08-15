import Mathlib.Data.List.Basic

set_option maxRecDepth 10000

/-!
# Exact finite replay proofs for the three corpus demonstrations

This module kernel-checks the arithmetic of compact sufficient statistics
transcribed from the three canonical decision ledgers.  Each transcription is
bound to the published relative path and SHA-256 value of its source ledger.
The Lean proof checks the embedded finite arithmetic; it does not recompute the
file digest, reopen recordings, validate annotations, establish corpus
provenance, or support a language-wide generalization.
-/

namespace PhonologicalCalculus.Demonstration

/-- Public identity and cardinality of a canonical source transcription. -/
structure SourceBinding where
  relativePath : String
  sha256 : String
  rowCount : Nat
  distinctNaturalKeyCount : Nat
deriving DecidableEq, Repr

/-- A compact proof witness for a natural-key multiplicity histogram. -/
structure KeyMultiplicityBin where
  distinctKeys : Nat
  rowsPerKey : Nat
deriving DecidableEq, Repr

def representedRows (bins : List KeyMultiplicityBin) : Nat :=
  (bins.map fun b => b.distinctKeys * b.rowsPerKey).sum

def representedDistinctKeys (bins : List KeyMultiplicityBin) : Nat :=
  (bins.map KeyMultiplicityBin.distinctKeys).sum

def everyKeyOccursOnce (bins : List KeyMultiplicityBin) : Bool :=
  bins.all fun b => b.rowsPerKey == 1

/-- The exact boundary of what the Lean replay verifies. -/
structure ReplayMechanizationBoundary where
  embeddedFiniteArithmetic : Bool
  externalDigestComputation : Bool
  corpusProvenance : Bool
  acousticMeasurements : Bool
  annotationValidity : Bool
  populationGeneralization : Bool
deriving DecidableEq, Repr

def replayMechanizationBoundary : ReplayMechanizationBoundary where
  embeddedFiniteArithmetic := true
  externalDigestComputation := false
  corpusProvenance := false
  acousticMeasurements := false
  annotationValidity := false
  populationGeneralization := false

/-- The finite replay proves arithmetic over the embedded transcription only. -/
theorem empiricalReplay_scope_boundary :
    replayMechanizationBoundary.embeddedFiniteArithmetic = true ∧
    replayMechanizationBoundary.externalDigestComputation = false ∧
    replayMechanizationBoundary.corpusProvenance = false ∧
    replayMechanizationBoundary.acousticMeasurements = false ∧
    replayMechanizationBoundary.annotationValidity = false ∧
    replayMechanizationBoundary.populationGeneralization = false := by
  decide

/-! ## English pooled-order replay -/

inductive EnglishSplit
  | developmentEven
  | confirmationOdd
deriving DecidableEq, Repr

/-- Histogram bin for aggregate scenario support. -/
structure EnglishSupportBin where
  split : EnglishSplit
  support : Nat
  multiplicity : Nat
  queryPass : Bool
deriving DecidableEq, Repr

/-- Exact support histogram of the 300 aggregate rows. -/
def englishSupportBins : List EnglishSupportBin := [
  ⟨.confirmationOdd, 36, 1, true⟩,
  ⟨.confirmationOdd, 40, 3, true⟩,
  ⟨.confirmationOdd, 41, 3, true⟩,
  ⟨.confirmationOdd, 42, 3, true⟩,
  ⟨.confirmationOdd, 43, 2, true⟩,
  ⟨.confirmationOdd, 44, 5, true⟩,
  ⟨.confirmationOdd, 45, 13, true⟩,
  ⟨.confirmationOdd, 46, 19, true⟩,
  ⟨.confirmationOdd, 47, 19, true⟩,
  ⟨.confirmationOdd, 48, 8, true⟩,
  ⟨.confirmationOdd, 49, 33, true⟩,
  ⟨.confirmationOdd, 50, 41, true⟩,
  ⟨.developmentEven, 37, 3, true⟩,
  ⟨.developmentEven, 39, 1, true⟩,
  ⟨.developmentEven, 41, 4, true⟩,
  ⟨.developmentEven, 42, 4, true⟩,
  ⟨.developmentEven, 43, 2, true⟩,
  ⟨.developmentEven, 44, 6, true⟩,
  ⟨.developmentEven, 45, 5, true⟩,
  ⟨.developmentEven, 46, 20, true⟩,
  ⟨.developmentEven, 47, 41, true⟩,
  ⟨.developmentEven, 48, 19, true⟩,
  ⟨.developmentEven, 49, 45, true⟩
]

/-- Histogram bin for one of the fourteen aggregate cells per scenario. -/
structure EnglishCellBin where
  support : Nat
  positiveSpeakers : Nat
  zeroSpeakers : Nat
  medianPositive : Bool
  multiplicity : Nat
deriving DecidableEq, Repr

/-- Exact histogram of the 4,200 aggregate cells. -/
def englishCellBins : List EnglishCellBin := [
  ⟨36, 30, 0, true, 1⟩, ⟨36, 31, 0, true, 2⟩,
  ⟨36, 32, 0, true, 1⟩, ⟨36, 33, 0, true, 1⟩,
  ⟨36, 34, 0, true, 1⟩, ⟨36, 35, 0, true, 1⟩,
  ⟨36, 36, 0, true, 7⟩,
  ⟨37, 32, 0, true, 1⟩, ⟨37, 34, 0, true, 8⟩,
  ⟨37, 35, 0, true, 7⟩, ⟨37, 36, 0, true, 5⟩,
  ⟨37, 37, 0, true, 21⟩,
  ⟨39, 35, 0, true, 1⟩, ⟨39, 36, 0, true, 1⟩,
  ⟨39, 37, 0, true, 1⟩, ⟨39, 38, 0, true, 4⟩,
  ⟨39, 39, 0, true, 7⟩,
  ⟨40, 34, 0, true, 4⟩, ⟨40, 35, 0, true, 3⟩,
  ⟨40, 36, 0, true, 2⟩, ⟨40, 37, 0, true, 3⟩,
  ⟨40, 38, 0, true, 4⟩, ⟨40, 39, 0, true, 1⟩,
  ⟨40, 40, 0, true, 25⟩,
  ⟨41, 31, 0, true, 1⟩, ⟨41, 32, 0, true, 1⟩,
  ⟨41, 33, 0, true, 2⟩, ⟨41, 34, 0, true, 1⟩,
  ⟨41, 35, 0, true, 1⟩, ⟨41, 36, 0, true, 4⟩,
  ⟨41, 37, 0, true, 3⟩, ⟨41, 38, 0, true, 12⟩,
  ⟨41, 39, 0, true, 13⟩, ⟨41, 40, 0, true, 6⟩,
  ⟨41, 41, 0, true, 54⟩,
  ⟨42, 29, 0, true, 2⟩, ⟨42, 33, 0, true, 1⟩,
  ⟨42, 34, 0, true, 2⟩, ⟨42, 35, 0, true, 1⟩,
  ⟨42, 36, 0, true, 1⟩, ⟨42, 37, 0, true, 3⟩,
  ⟨42, 38, 0, true, 9⟩, ⟨42, 39, 0, true, 13⟩,
  ⟨42, 40, 0, true, 8⟩, ⟨42, 41, 0, true, 3⟩,
  ⟨42, 42, 0, true, 55⟩,
  ⟨43, 36, 0, true, 1⟩, ⟨43, 38, 0, true, 5⟩,
  ⟨43, 39, 0, true, 3⟩, ⟨43, 40, 0, true, 4⟩,
  ⟨43, 41, 0, true, 7⟩, ⟨43, 42, 0, true, 4⟩,
  ⟨43, 43, 0, true, 32⟩,
  ⟨44, 37, 0, true, 1⟩, ⟨44, 38, 0, true, 1⟩,
  ⟨44, 39, 0, true, 7⟩, ⟨44, 40, 0, true, 8⟩,
  ⟨44, 41, 0, true, 2⟩, ⟨44, 42, 0, true, 14⟩,
  ⟨44, 43, 0, true, 18⟩, ⟨44, 44, 0, true, 103⟩,
  ⟨45, 36, 0, true, 1⟩, ⟨45, 38, 0, true, 1⟩,
  ⟨45, 39, 0, true, 2⟩, ⟨45, 40, 0, true, 2⟩,
  ⟨45, 41, 0, true, 4⟩, ⟨45, 42, 0, true, 7⟩,
  ⟨45, 43, 0, true, 17⟩, ⟨45, 44, 0, true, 26⟩,
  ⟨45, 45, 0, true, 192⟩,
  ⟨46, 39, 0, true, 2⟩, ⟨46, 40, 0, true, 2⟩,
  ⟨46, 41, 0, true, 9⟩, ⟨46, 42, 0, true, 12⟩,
  ⟨46, 43, 0, true, 21⟩, ⟨46, 44, 0, true, 32⟩,
  ⟨46, 45, 0, true, 32⟩, ⟨46, 46, 0, true, 436⟩,
  ⟨47, 40, 0, true, 1⟩, ⟨47, 41, 0, true, 2⟩,
  ⟨47, 42, 0, true, 7⟩, ⟨47, 43, 0, true, 15⟩,
  ⟨47, 44, 0, true, 20⟩, ⟨47, 45, 0, true, 43⟩,
  ⟨47, 46, 0, true, 88⟩, ⟨47, 47, 0, true, 664⟩,
  ⟨48, 42, 0, true, 2⟩, ⟨48, 43, 0, true, 7⟩,
  ⟨48, 44, 0, true, 4⟩, ⟨48, 45, 0, true, 9⟩,
  ⟨48, 46, 0, true, 16⟩, ⟨48, 47, 0, true, 43⟩,
  ⟨48, 48, 0, true, 297⟩,
  ⟨49, 43, 0, true, 1⟩, ⟨49, 44, 0, true, 5⟩,
  ⟨49, 45, 0, true, 11⟩, ⟨49, 46, 0, true, 15⟩,
  ⟨49, 47, 0, true, 42⟩, ⟨49, 48, 0, true, 127⟩,
  ⟨49, 49, 0, true, 891⟩,
  ⟨50, 45, 0, true, 1⟩, ⟨50, 46, 0, true, 3⟩,
  ⟨50, 47, 0, true, 14⟩, ⟨50, 48, 0, true, 31⟩,
  ⟨50, 49, 0, true, 33⟩, ⟨50, 50, 0, true, 492⟩
]

def englishAggregateBinding : SourceBinding where
  relativePath := "data/source_ledgers/english_aggregate_source.tsv"
  sha256 := "24cf794450a5369c16994af2321ea0312d8b1e05f7f84ef5232c7354485166b3"
  rowCount := 300
  distinctNaturalKeyCount := 300

def englishSpeakerBinding : SourceBinding where
  relativePath := "data/source_ledgers/english_speaker_scenario_source.tsv"
  sha256 := "f8d3f7806dbbbc26b78d3eb606a336ad102d3ccbd991aade39289a65daa81530"
  rowCount := 14135
  distinctNaturalKeyCount := 14135

def englishAggregateKeyBins : List KeyMultiplicityBin := [⟨300, 1⟩]
def englishSpeakerKeyBins : List KeyMultiplicityBin := [⟨14135, 1⟩]

structure EnglishStatusBin where
  passesSupportGate : Bool
  multiplicity : Nat
deriving DecidableEq, Repr

def englishSpeakerStatusBins : List EnglishStatusBin := [⟨true, 14135⟩]

def englishAggregateRows : Nat :=
  (englishSupportBins.map EnglishSupportBin.multiplicity).sum

def englishRowsInSplit (split : EnglishSplit) : Nat :=
  (englishSupportBins.map fun b =>
    if b.split = split then b.multiplicity else 0).sum

def englishAggregateSupport : Nat :=
  (englishSupportBins.map fun b => b.support * b.multiplicity).sum

def englishPassingAggregateRows : Nat :=
  (englishSupportBins.map fun b =>
    if b.queryPass then b.multiplicity else 0).sum

def englishSpeakerRows : Nat :=
  (englishSpeakerStatusBins.map EnglishStatusBin.multiplicity).sum

def englishPassingSpeakerRows : Nat :=
  (englishSpeakerStatusBins.map fun b =>
    if b.passesSupportGate then b.multiplicity else 0).sum

def englishAggregateCells : Nat :=
  (englishCellBins.map EnglishCellBin.multiplicity).sum

def englishPositiveMedianCells : Nat :=
  (englishCellBins.map fun b =>
    if b.medianPositive then b.multiplicity else 0).sum

def EnglishCellBin.negativeSpeakers (b : EnglishCellBin) : Nat :=
  b.support - b.positiveSpeakers - b.zeroSpeakers

def EnglishCellBin.aboveHalf (b : EnglishCellBin) : Nat :=
  b.positiveSpeakers - b.support / 2

def EnglishCellBin.aboveStrictMajority (b : EnglishCellBin) : Nat :=
  b.positiveSpeakers - (b.support / 2 + 1)

def EnglishCellBin.hasStrictMajority (b : EnglishCellBin) : Bool :=
  b.support / 2 < b.positiveSpeakers

def englishMinimumAboveHalf : Nat :=
  englishCellBins.foldl (fun current b => Nat.min current b.aboveHalf) 1000

def englishMinimumAboveStrictMajority : Nat :=
  englishCellBins.foldl
    (fun current b => Nat.min current b.aboveStrictMajority) 1000

def englishContainsBoundaryWitness : Bool :=
  englishCellBins.any fun b =>
    b.support == 42 && b.positiveSpeakers == 29 && b.zeroSpeakers == 0

def englishBoundaryRawSurplus : Nat :=
  let b : EnglishCellBin := ⟨42, 29, 0, true, 2⟩
  b.positiveSpeakers - b.negativeSpeakers

/-- **DATA-EN-R1.REPLAY.01**.  Exact arithmetic of the digest-bound compact
English transcription. -/
theorem data_en_r1_replay :
    englishAggregateBinding.rowCount = 300 ∧
    englishAggregateBinding.distinctNaturalKeyCount = 300 ∧
    englishSpeakerBinding.rowCount = 14135 ∧
    englishSpeakerBinding.distinctNaturalKeyCount = 14135 ∧
    englishAggregateRows = 300 ∧
    englishRowsInSplit .developmentEven = 150 ∧
    englishRowsInSplit .confirmationOdd = 150 ∧
    englishPassingAggregateRows = 300 ∧
    englishAggregateCells = 4200 ∧
    englishPositiveMedianCells = 4200 ∧
    englishCellBins.all EnglishCellBin.hasStrictMajority = true ∧
    englishAggregateSupport = 14135 ∧
    englishSpeakerRows = 14135 ∧
    englishPassingSpeakerRows = 14135 ∧
    representedRows englishAggregateKeyBins = 300 ∧
    representedDistinctKeys englishAggregateKeyBins = 300 ∧
    everyKeyOccursOnce englishAggregateKeyBins = true ∧
    representedRows englishSpeakerKeyBins = 14135 ∧
    representedDistinctKeys englishSpeakerKeyBins = 14135 ∧
    everyKeyOccursOnce englishSpeakerKeyBins = true ∧
    englishMinimumAboveHalf = 8 ∧
    englishMinimumAboveStrictMajority = 7 ∧
    englishContainsBoundaryWitness = true ∧
    englishBoundaryRawSurplus = 16 := by
  decide

/-! ## Portuguese query-hierarchy replay -/

inductive GateDecision
  | yes
  | no
deriving DecidableEq, Repr

/-- One compact frequency bin for the four reader decisions at a cell. -/
structure PortuguesePatternBin where
  full : GateDecision
  leaveFlatnessOut : GateDecision
  leaveHighLowOut : GateDecision
  leaveZcrOut : GateDecision
  positiveMedianRowsPerCell : Nat
  multiplicity : Nat
deriving DecidableEq, Repr

/-- Exact seven-bin compression of the eighteen Portuguese cells. -/
def portuguesePatternBins : List PortuguesePatternBin := [
  ⟨.no, .no, .yes, .no, 4, 1⟩,
  ⟨.yes, .no, .no, .no, 4, 1⟩,
  ⟨.yes, .no, .yes, .no, 4, 2⟩,
  ⟨.yes, .no, .yes, .yes, 4, 3⟩,
  ⟨.yes, .yes, .no, .yes, 4, 1⟩,
  ⟨.yes, .yes, .yes, .no, 4, 1⟩,
  ⟨.yes, .yes, .yes, .yes, 4, 9⟩
]

def portugueseBinding : SourceBinding where
  relativePath := "data/source_ledgers/portuguese_reduced_source.tsv"
  sha256 := "39a9042012f444a0e4e98b06c5b9fc0bdcfe475eac1ca015b430fdc3aedf4a20"
  rowCount := 72
  distinctNaturalKeyCount := 72

def portugueseKeyBins : List KeyMultiplicityBin := [⟨72, 1⟩]

def portugueseCells : Nat :=
  (portuguesePatternBins.map PortuguesePatternBin.multiplicity).sum

def portugueseRows : Nat := portugueseCells * 4

def portuguesePositiveMedianRows : Nat :=
  (portuguesePatternBins.map fun b =>
    b.positiveMedianRowsPerCell * b.multiplicity).sum

def gatePassCount (reader : PortuguesePatternBin → GateDecision) : Nat :=
  (portuguesePatternBins.map fun b =>
    if reader b = .yes then b.multiplicity else 0).sum

def gateChangedCount (reader : PortuguesePatternBin → GateDecision) : Nat :=
  (portuguesePatternBins.map fun b =>
    if reader b = b.full then 0 else b.multiplicity).sum

def gateYesToNoCount (reader : PortuguesePatternBin → GateDecision) : Nat :=
  (portuguesePatternBins.map fun b =>
    if b.full = .yes ∧ reader b = .no then b.multiplicity else 0).sum

def gateNoToYesCount (reader : PortuguesePatternBin → GateDecision) : Nat :=
  (portuguesePatternBins.map fun b =>
    if b.full = .no ∧ reader b = .yes then b.multiplicity else 0).sum

def portugueseChangedDecisions : Nat :=
  gateChangedCount PortuguesePatternBin.leaveFlatnessOut +
  gateChangedCount PortuguesePatternBin.leaveHighLowOut +
  gateChangedCount PortuguesePatternBin.leaveZcrOut

def portugueseYesToNo : Nat :=
  gateYesToNoCount PortuguesePatternBin.leaveFlatnessOut +
  gateYesToNoCount PortuguesePatternBin.leaveHighLowOut +
  gateYesToNoCount PortuguesePatternBin.leaveZcrOut

def portugueseNoToYes : Nat :=
  gateNoToYesCount PortuguesePatternBin.leaveFlatnessOut +
  gateNoToYesCount PortuguesePatternBin.leaveHighLowOut +
  gateNoToYesCount PortuguesePatternBin.leaveZcrOut

def portugueseUniqueChangedCells : Nat :=
  (portuguesePatternBins.map fun b =>
    if b.leaveFlatnessOut ≠ b.full ∨
        b.leaveHighLowOut ≠ b.full ∨
        b.leaveZcrOut ≠ b.full then b.multiplicity else 0).sum

/-- **DATA-PT-R1.REPLAY.01**.  Exact arithmetic of the digest-bound compact
Portuguese transcription. -/
theorem data_pt_r1_replay :
    portugueseBinding.rowCount = 72 ∧
    portugueseBinding.distinctNaturalKeyCount = 72 ∧
    portugueseCells = 18 ∧
    portugueseRows = 72 ∧
    portuguesePositiveMedianRows = 72 ∧
    gatePassCount PortuguesePatternBin.full = 17 ∧
    gatePassCount PortuguesePatternBin.leaveFlatnessOut = 11 ∧
    gatePassCount PortuguesePatternBin.leaveHighLowOut = 16 ∧
    gatePassCount PortuguesePatternBin.leaveZcrOut = 13 ∧
    gateChangedCount PortuguesePatternBin.leaveFlatnessOut = 6 ∧
    gateChangedCount PortuguesePatternBin.leaveHighLowOut = 3 ∧
    gateChangedCount PortuguesePatternBin.leaveZcrOut = 4 ∧
    portugueseChangedDecisions = 13 ∧
    portugueseYesToNo = 12 ∧
    portugueseNoToYes = 1 ∧
    portugueseUniqueChangedCells = 9 ∧
    representedRows portugueseKeyBins = 72 ∧
    representedDistinctKeys portugueseKeyBins = 72 ∧
    everyKeyOccursOnce portugueseKeyBins = true := by
  decide

/-! ## Mandarin construction-scope replay -/

inductive MandarinScope
  | ambiguousOrOutsideScope
  | clearComplexLastDigit
  | clearSimplex
  | ordinalAbsolute
deriving DecidableEq, Repr

inductive MandarinDecision
  | match
  | counterexample
  | noConclusionScope
deriving DecidableEq, Repr

/-- Frequency bin for one scope/original/corrected decision triple. -/
structure MandarinDecisionBin where
  scope : MandarinScope
  original : MandarinDecision
  corrected : MandarinDecision
  multiplicity : Nat
deriving DecidableEq, Repr

/-- Exact seven-bin compression of the 639 Mandarin rows. -/
def mandarinDecisionBins : List MandarinDecisionBin := [
  ⟨.ambiguousOrOutsideScope, .counterexample, .noConclusionScope, 1⟩,
  ⟨.ambiguousOrOutsideScope, .match, .noConclusionScope, 3⟩,
  ⟨.clearComplexLastDigit, .counterexample, .match, 4⟩,
  ⟨.clearSimplex, .counterexample, .counterexample, 7⟩,
  ⟨.clearSimplex, .match, .match, 601⟩,
  ⟨.ordinalAbsolute, .counterexample, .counterexample, 6⟩,
  ⟨.ordinalAbsolute, .match, .match, 17⟩
]

def mandarinBinding : SourceBinding where
  relativePath := "data/source_ledgers/mandarin_corrected_source.tsv"
  sha256 := "8e010db5245c9436fb4bdd5d5f3791a2f4553915cb877c1218dcd70e1bf3c67c"
  rowCount := 639
  distinctNaturalKeyCount := 639

def mandarinKeyBins : List KeyMultiplicityBin := [⟨639, 1⟩]

def mandarinRows : Nat :=
  (mandarinDecisionBins.map MandarinDecisionBin.multiplicity).sum

def mandarinScopeCount (scope : MandarinScope) : Nat :=
  (mandarinDecisionBins.map fun b =>
    if b.scope = scope then b.multiplicity else 0).sum

def mandarinOriginalCount (decision : MandarinDecision) : Nat :=
  (mandarinDecisionBins.map fun b =>
    if b.original = decision then b.multiplicity else 0).sum

def mandarinCorrectedCount (decision : MandarinDecision) : Nat :=
  (mandarinDecisionBins.map fun b =>
    if b.corrected = decision then b.multiplicity else 0).sum

def mandarinClearComplexRetyped : Nat :=
  (mandarinDecisionBins.map fun b =>
    if b.scope = .clearComplexLastDigit ∧
        b.original = .counterexample ∧ b.corrected = .match
    then b.multiplicity else 0).sum

def mandarinAllClearComplexRetyped : Bool :=
  mandarinDecisionBins.all fun b =>
    if b.scope = .clearComplexLastDigit then
      decide (b.original = .counterexample ∧ b.corrected = .match)
    else true

/-- **DATA-ZH-R1.REPLAY.01**.  Exact arithmetic of the digest-bound compact
Mandarin transcription. -/
theorem data_zh_r1_replay :
    mandarinBinding.rowCount = 639 ∧
    mandarinBinding.distinctNaturalKeyCount = 639 ∧
    mandarinRows = 639 ∧
    mandarinOriginalCount .match = 621 ∧
    mandarinOriginalCount .counterexample = 18 ∧
    mandarinOriginalCount .noConclusionScope = 0 ∧
    mandarinCorrectedCount .match = 622 ∧
    mandarinCorrectedCount .counterexample = 13 ∧
    mandarinCorrectedCount .noConclusionScope = 4 ∧
    mandarinScopeCount .clearSimplex = 608 ∧
    mandarinScopeCount .clearComplexLastDigit = 4 ∧
    mandarinScopeCount .ambiguousOrOutsideScope = 4 ∧
    mandarinScopeCount .ordinalAbsolute = 23 ∧
    mandarinClearComplexRetyped = 4 ∧
    mandarinAllClearComplexRetyped = true ∧
    representedRows mandarinKeyBins = 639 ∧
    representedDistinctKeys mandarinKeyBins = 639 ∧
    everyKeyOccursOnce mandarinKeyBins = true := by
  decide

/-- The three source bindings carry the exact canonical digest strings used by
the public replay specifications. -/
theorem empiricalReplay_source_bindings :
    englishAggregateBinding.relativePath =
      "data/source_ledgers/english_aggregate_source.tsv" ∧
    englishAggregateBinding.sha256 =
      "24cf794450a5369c16994af2321ea0312d8b1e05f7f84ef5232c7354485166b3" ∧
    englishSpeakerBinding.relativePath =
      "data/source_ledgers/english_speaker_scenario_source.tsv" ∧
    englishSpeakerBinding.sha256 =
      "f8d3f7806dbbbc26b78d3eb606a336ad102d3ccbd991aade39289a65daa81530" ∧
    portugueseBinding.relativePath =
      "data/source_ledgers/portuguese_reduced_source.tsv" ∧
    portugueseBinding.sha256 =
      "39a9042012f444a0e4e98b06c5b9fc0bdcfe475eac1ca015b430fdc3aedf4a20" ∧
    mandarinBinding.relativePath =
      "data/source_ledgers/mandarin_corrected_source.tsv" ∧
    mandarinBinding.sha256 =
      "8e010db5245c9436fb4bdd5d5f3791a2f4553915cb877c1218dcd70e1bf3c67c" := by
  decide

end PhonologicalCalculus.Demonstration
