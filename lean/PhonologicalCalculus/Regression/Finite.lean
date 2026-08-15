import PhonologicalCalculus.Contract.FiniteDecision
import PhonologicalCalculus.Foundation.Finite
import Mathlib.Data.Finset.Prod

/-!
Kernel-checked reconstructions of the exact finite regression models registered
as `CALC-R01`--`CALC-R08`, `CALC-R13`, and `CALC-R15`.

The declarations prove propositions about the modelled maps, relations, and
decision procedure.  They do not turn an externally computed Boolean into a
proof and they do not claim to formalize the surrounding phonological prose.
-/

namespace PhonologicalCalculus.Regression

inductive ScientificStatus where
  | complete | incomplete
  deriving DecidableEq, Repr

inductive FailureReason where
  | querySemanticsNotComparable
  deriving DecidableEq, Repr

structure DecisionRecord where
  verdict : Verdict
  failureReason : Option FailureReason
  scientificStatus : ScientificStatus
  deriving DecidableEq, Repr

section DirectAndContextualCarriers

inductive ABC where
  | a | b | c
  deriving DecidableEq, Repr

def abcDomain : Finset ABC := {ABC.a, ABC.b, ABC.c}

def directQuery : ABC → Bool
  | ABC.a | ABC.b => false
  | ABC.c => true

def retainedOperation : ABC → ABC
  | ABC.a => ABC.a
  | ABC.b | ABC.c => ABC.c

def contextualQuery (x : ABC) : Bool × Bool :=
  (directQuery x, directQuery (retainedOperation x))

/-- Exact `CALC-R01.PARTITION.01`: the direct query merges `a,b`, whereas the
identity-plus-retained-operation query distinguishes every point. -/
theorem CALC_R01_PARTITION_01 :
    directQuery ABC.a = directQuery ABC.b ∧
      directQuery ABC.a ≠ directQuery ABC.c ∧
      Function.Injective contextualQuery := by
  constructor
  · rfl
  constructor
  · decide
  · intro x y h
    cases x <;> cases y <;> simp [contextualQuery, directQuery, retainedOperation] at h ⊢

inductive SortName where
  | segment | feature | unregistered
  deriving DecidableEq, Repr

structure UnarySignature where
  input : SortName
  output : SortName
  deriving DecidableEq, Repr

def registeredSorts : Finset SortName :=
  {SortName.segment, SortName.feature}

def manySortedValid (signature : UnarySignature) : Prop :=
  signature.input ∈ registeredSorts ∧ signature.output ∈ registeredSorts

def goodSignature : UnarySignature :=
  ⟨SortName.segment, SortName.feature⟩

def badSignature : UnarySignature :=
  ⟨SortName.unregistered, SortName.feature⟩

/-- Exact `CALC-R01.SORTS.02`. -/
theorem CALC_R01_SORTS_02 :
    manySortedValid goodSignature ∧ ¬manySortedValid badSignature := by
  simp [manySortedValid, goodSignature, badSignature, registeredSorts]

def partialObserver : ABC → Option Bool
  | ABC.a | ABC.b => some false
  | ABC.c => none

/-- Exact `CALC-R01.PARTIAL.03`: undefined observations remain a typed value;
removing the observer altogether collapses all three inputs, and an incomplete
observer is not accepted as complete evidence. -/
theorem CALC_R01_PARTIAL_03 :
    partialObserver ABC.a = partialObserver ABC.b ∧
      partialObserver ABC.a ≠ partialObserver ABC.c ∧
      (∀ x y : ABC, (fun _ : ABC => ()) x = (fun _ : ABC => ()) y) ∧
      ¬(∀ x : ABC, (partialObserver x).isSome) := by
  constructor
  · rfl
  constructor
  · decide
  constructor
  · simp
  · intro h
    have := h ABC.c
    simp [partialObserver] at this

end DirectAndContextualCarriers

section OptimizerCoimage

inductive OptInput where
  | one | two | three | four
  deriving DecidableEq, Repr

inductive OptOutput where
  | A | B | C
  deriving DecidableEq, Repr

def optDomain : Finset OptInput :=
  {OptInput.one, OptInput.two, OptInput.three, OptInput.four}

def optimizer : OptInput → OptOutput
  | OptInput.one | OptInput.two => OptOutput.A
  | OptInput.three => OptOutput.B
  | OptInput.four => OptOutput.C

def optimizerImage : Finset OptOutput := optDomain.image optimizer

def optimizerKernel : Finset (OptInput × OptInput) :=
  (optDomain ×ˢ optDomain).filter (fun xy => optimizer xy.1 = optimizer xy.2)

def expectedOptimizerKernel : Finset (OptInput × OptInput) :=
  {(OptInput.one, OptInput.one), (OptInput.one, OptInput.two),
   (OptInput.two, OptInput.one), (OptInput.two, OptInput.two),
   (OptInput.three, OptInput.three), (OptInput.four, OptInput.four)}

/-- Exact `CALC-R02.COIMAGE.01`. -/
theorem CALC_R02_COIMAGE_01 :
    optimizerImage.card = 3 ∧
      optimizerKernel = expectedOptimizerKernel := by
  decide

def partialOptimizer : OptInput → Option OptOutput
  | OptInput.one | OptInput.two => some OptOutput.A
  | OptInput.three | OptInput.four => none

def partialOptimizerImage : Finset (Option OptOutput) :=
  optDomain.image partialOptimizer

/-- Exact `CALC-R02.PARTIAL.02`: the two defined rows share one value and the
two undefined rows share the explicit `none` value. -/
theorem CALC_R02_PARTIAL_02 :
    partialOptimizer OptInput.one = partialOptimizer OptInput.two ∧
      partialOptimizer OptInput.three = partialOptimizer OptInput.four ∧
      partialOptimizer OptInput.one ≠ partialOptimizer OptInput.three ∧
      partialOptimizerImage.card = 2 := by
  decide

end OptimizerCoimage

section AdmissionRefusal

def r03Request : FiniteRequest Unit Unit Unit where
  rows := ∅
  formed := True
  admitted := False
  formedDecision := inferInstance
  admittedDecision := inferInstance
  sourceAnswer := id
  targetAnswer := id
  transport := id

def r03Record : DecisionRecord where
  verdict := r03Request.evaluate
  failureReason := some FailureReason.querySemanticsNotComparable
  scientificStatus := ScientificStatus.complete

/-- Exact decision component of `CALC-R03.REFUSAL.01`: an empty licensed-pair
family fails admission and cannot receive a vacuous conservativity verdict. -/
theorem CALC_R03_REFUSAL_01 :
    r03Request.formed ∧ ¬r03Request.admitted ∧
      r03Request.rows = ∅ ∧
      r03Record =
        ⟨Verdict.notEvaluated,
          some FailureReason.querySemanticsNotComparable,
          ScientificStatus.complete⟩ ∧
      r03Request.evaluate ≠ Verdict.conservative := by
  simp [r03Record, r03Request, FiniteRequest.evaluate]

end AdmissionRefusal

section FrontierCoverage

inductive Level where
  | B1 | B2 | B3
  deriving DecidableEq, Repr

def levelDomain : Finset Level := {Level.B1, Level.B2, Level.B3}

def strictEdge : Level → Level → Bool
  | Level.B3, Level.B1 | Level.B3, Level.B2 => true
  | _, _ => false

def lowerFrontier : Finset Level :=
  levelDomain.filter (fun x => ¬∃ y ∈ levelDomain, strictEdge x y = true)

def comparisonImage : Finset Level := {Level.B1}

/-- Exact `CALC-R04.SURJECTIVITY.01`. -/
theorem CALC_R04_SURJECTIVITY_01 :
    ({Level.B1, Level.B2} : Finset Level) \ comparisonImage = {Level.B2} := by
  decide

/-- Exact `CALC-R04.FRONTIER.02`. -/
theorem CALC_R04_FRONTIER_02 :
    lowerFrontier = {Level.B1, Level.B2} ∧
      lowerFrontier \ comparisonImage = {Level.B2} := by
  constructor
  · ext x
    cases x <;> simp [lowerFrontier, levelDomain, strictEdge]
  · ext x
    cases x <;> simp [lowerFrontier, levelDomain, strictEdge, comparisonImage]

end FrontierCoverage

section OrbitAndRepresentativeRecovery

inductive World where
  | w1 | w2
  deriving DecidableEq, Repr

def swapWorld : World → World
  | World.w1 => World.w2
  | World.w2 => World.w1

def worldOrbit : Finset World := {World.w1, World.w2}

/-- Exact `CALC-R05.ORBIT.01`: the orbit is invariant even though neither
representative is fixed. -/
theorem CALC_R05_ORBIT_01 :
    worldOrbit.image swapWorld = worldOrbit ∧
      swapWorld World.w1 ≠ World.w1 ∧
      swapWorld World.w2 ≠ World.w2 := by
  decide

inductive Representative where
  | a | b
  deriving DecidableEq, Repr

inductive SemanticOrbit where
  | ab
  deriving DecidableEq, Repr

inductive RecoveryOutput where
  | c
  deriving DecidableEq, Repr

def semanticRecovery : SemanticOrbit → RecoveryOutput
  | SemanticOrbit.ab => RecoveryOutput.c

def representativeRecovery : Representative → RecoveryOutput
  | Representative.a | Representative.b => RecoveryOutput.c

def representativeDomain : Finset Representative :=
  {Representative.a, Representative.b}

def unorderedRepresentativeCollisions : Finset (Representative × Representative) :=
  ({(Representative.a, Representative.b)} :
      Finset (Representative × Representative)).filter
    (fun xy => representativeRecovery xy.1 = representativeRecovery xy.2)

/-- Exact `CALC-R06.ORBITS.01`: semantic-orbit recovery is injective, while
representative recovery has the explicit `a,b` collision. -/
theorem CALC_R06_ORBITS_01 :
    Function.Injective semanticRecovery ∧
      unorderedRepresentativeCollisions = {(Representative.a, Representative.b)} ∧
      Representative.a ≠ Representative.b ∧
      representativeRecovery Representative.a =
        representativeRecovery Representative.b ∧
      ¬Function.Injective representativeRecovery := by
  constructor
  · intro x y _
    cases x
    cases y
    rfl
  constructor
  · simp [unorderedRepresentativeCollisions, representativeRecovery]
  constructor
  · decide
  constructor
  · rfl
  · intro h
    exact Representative.noConfusion
      (h (show representativeRecovery Representative.a =
        representativeRecovery Representative.b from rfl))

end OrbitAndRepresentativeRecovery

section OutboundEdges

inductive CarrierNode where
  | c | d
  deriving DecidableEq, Repr

inductive OperationLabel where
  | k
  deriving DecidableEq, Repr

structure LabeledEdge where
  label : OperationLabel
  source : CarrierNode
  target : CarrierNode
  deriving DecidableEq, Repr

def retainedImage : Finset CarrierNode := {CarrierNode.c}

def registeredEdges : Finset LabeledEdge :=
  {⟨OperationLabel.k, CarrierNode.c, CarrierNode.d⟩}

def outboundEdges : Finset LabeledEdge :=
  registeredEdges.filter
    (fun e => e.source ∈ retainedImage ∧ e.target ∉ retainedImage)

/-- Exact `CALC-R07.OUTBOUND.01`. -/
theorem CALC_R07_OUTBOUND_01 :
    outboundEdges = {⟨OperationLabel.k, CarrierNode.c, CarrierNode.d⟩} := by
  decide

end OutboundEdges

section TypedVacuity

inductive VacuityStatus where
  | semanticInverseVacuousEmptyLicensedSourceImage
  | representativeInverseVacuousEmptyLicensedSourceImage
  | recoveryTested
  deriving DecidableEq, Repr

def semanticEmptyStatus (_ : Finset Unit) : VacuityStatus :=
  VacuityStatus.semanticInverseVacuousEmptyLicensedSourceImage

def representativeEmptyStatus (_ : Finset Unit) : VacuityStatus :=
  VacuityStatus.representativeInverseVacuousEmptyLicensedSourceImage

/-- Exact typed content of `CALC-R08.STATUS.01`. -/
theorem CALC_R08_STATUS_01 :
    semanticEmptyStatus ∅ =
        VacuityStatus.semanticInverseVacuousEmptyLicensedSourceImage ∧
      representativeEmptyStatus ∅ =
        VacuityStatus.representativeInverseVacuousEmptyLicensedSourceImage ∧
      semanticEmptyStatus ∅ ≠ representativeEmptyStatus ∅ ∧
      semanticEmptyStatus ∅ ≠ VacuityStatus.recoveryTested ∧
      representativeEmptyStatus ∅ ≠ VacuityStatus.recoveryTested := by
  decide

end TypedVacuity

section MismatchSelection

inductive ComparisonOutcome where
  | loss | tie | win
  deriving DecidableEq, Repr

def comparisonOutcome : Int → ComparisonOutcome
  | -1 => ComparisonOutcome.loss
  | 0 => ComparisonOutcome.tie
  | _ => ComparisonOutcome.win

def comparisonDomain : List Int := [-1, 0, 1]

def selectedMismatches : List Int :=
  comparisonDomain.filter
    (fun x => x > 0 ∧ comparisonOutcome x ≠ ComparisonOutcome.tie)

/-- Exact `CALC-R13.MISMATCH.01`. -/
theorem CALC_R13_MISMATCH_01 : selectedMismatches = [1] := by
  decide

end MismatchSelection

section ExternalScientificStatus

inductive Answer where
  | A
  deriving DecidableEq, Repr

def r15Request : FiniteRequest Unit Answer Answer where
  rows := {()}
  formed := True
  admitted := True
  formedDecision := inferInstance
  admittedDecision := inferInstance
  sourceAnswer := fun _ => Answer.A
  targetAnswer := fun _ => Answer.A
  transport := id

def r15Record : DecisionRecord where
  verdict := r15Request.evaluate
  failureReason := none
  scientificStatus := ScientificStatus.incomplete

/-- Exact `CALC-R15.EXTERNAL.01`: contract-relative conservativity and external
scientific incompleteness coexist without changing either type of verdict. -/
theorem CALC_R15_EXTERNAL_01 :
    r15Record =
      ⟨Verdict.conservative, none, ScientificStatus.incomplete⟩ ∧
      r15Request.evaluate = Verdict.conservative ∧
      ScientificStatus.incomplete ≠ ScientificStatus.complete := by
  decide

end ExternalScientificStatus

end PhonologicalCalculus.Regression
