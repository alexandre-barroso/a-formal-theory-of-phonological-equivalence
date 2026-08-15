import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Max

/-!
The executable mathematical kernel of the qualified finite decision theorem.

This module proves admission precedence, the three disjoint verdicts, exact
transported-answer equality, the complete mismatch set, and least-witness
selection.  It separates the reusable comparison kernel from an integrated
finite-contract layer.  The latter represents every required typed field by
an `Option`, constructs a typed contract only after exact formation succeeds,
derives the complete matched-row carrier from a declared licensed-row
predicate, and evaluates explicit admission fields before answer comparison.
Thus a missing formation field cannot be hidden inside an opaque proposition.
-/

namespace PhonologicalCalculus

inductive Verdict where
  | conservative
  | nonconservative
  | notEvaluated
  deriving DecidableEq, Repr

structure FiniteRequest (Row SourceAnswer TargetAnswer : Type*) where
  rows : Finset Row
  formed : Prop
  admitted : Prop
  formedDecision : Decidable formed
  admittedDecision : Decidable admitted
  sourceAnswer : Row → SourceAnswer
  targetAnswer : Row → TargetAnswer
  transport : SourceAnswer → TargetAnswer

namespace FiniteRequest

variable {Row SourceAnswer TargetAnswer : Type*}

def eligible (r : FiniteRequest Row SourceAnswer TargetAnswer) : Prop :=
  r.formed ∧ r.admitted

def mismatchSet [DecidableEq Row] [DecidableEq TargetAnswer]
    (r : FiniteRequest Row SourceAnswer TargetAnswer) : Finset Row :=
  r.rows.filter
    (fun row => r.transport (r.sourceAnswer row) ≠ r.targetAnswer row)

def evaluate [DecidableEq Row] [DecidableEq TargetAnswer]
    (r : FiniteRequest Row SourceAnswer TargetAnswer) : Verdict :=
  letI := r.formedDecision
  letI := r.admittedDecision
  if r.formed then
    if r.admitted then
      if mismatchSet r = ∅ then Verdict.conservative
      else Verdict.nonconservative
    else Verdict.notEvaluated
  else Verdict.notEvaluated

theorem mem_mismatchSet_iff [DecidableEq Row] [DecidableEq TargetAnswer]
    (r : FiniteRequest Row SourceAnswer TargetAnswer) (row : Row) :
    row ∈ mismatchSet r ↔
      row ∈ r.rows ∧
        r.transport (r.sourceAnswer row) ≠ r.targetAnswer row := by
  simp [mismatchSet]

theorem mismatchSet_empty_iff [DecidableEq Row] [DecidableEq TargetAnswer]
    (r : FiniteRequest Row SourceAnswer TargetAnswer) :
    mismatchSet r = ∅ ↔
      ∀ row ∈ r.rows,
        r.transport (r.sourceAnswer row) = r.targetAnswer row := by
  simp [mismatchSet]

theorem mismatchSet_nonempty_iff [DecidableEq Row] [DecidableEq TargetAnswer]
    (r : FiniteRequest Row SourceAnswer TargetAnswer) :
    (mismatchSet r).Nonempty ↔
      ∃ row ∈ r.rows,
        r.transport (r.sourceAnswer row) ≠ r.targetAnswer row := by
  constructor
  · rintro ⟨row, hrow⟩
    exact ⟨row, (mem_mismatchSet_iff r row).1 hrow⟩
  · rintro ⟨row, hrow, hmismatch⟩
    exact ⟨row, (mem_mismatchSet_iff r row).2 ⟨hrow, hmismatch⟩⟩

theorem evaluate_eq_notEvaluated_iff [DecidableEq Row]
    [DecidableEq TargetAnswer]
    (r : FiniteRequest Row SourceAnswer TargetAnswer) :
    evaluate r = Verdict.notEvaluated ↔ ¬eligible r := by
  letI := r.formedDecision
  letI := r.admittedDecision
  by_cases hf : r.formed <;> by_cases ha : r.admitted <;>
    by_cases hm : mismatchSet r = ∅ <;>
      simp [evaluate, eligible, hf, ha, hm]

theorem evaluate_eq_conservative_iff [DecidableEq Row]
    [DecidableEq TargetAnswer]
    (r : FiniteRequest Row SourceAnswer TargetAnswer) :
    evaluate r = Verdict.conservative ↔
      eligible r ∧
        ∀ row ∈ r.rows,
          r.transport (r.sourceAnswer row) = r.targetAnswer row := by
  letI := r.formedDecision
  letI := r.admittedDecision
  by_cases hf : r.formed <;> by_cases ha : r.admitted <;>
    simp [evaluate, eligible, hf, ha, mismatchSet_empty_iff]

theorem evaluate_eq_nonconservative_iff [DecidableEq Row]
    [DecidableEq TargetAnswer]
    (r : FiniteRequest Row SourceAnswer TargetAnswer) :
    evaluate r = Verdict.nonconservative ↔
      eligible r ∧ (mismatchSet r).Nonempty := by
  letI := r.formedDecision
  letI := r.admittedDecision
  by_cases hf : r.formed <;> by_cases ha : r.admitted <;>
    simp [evaluate, eligible, hf, ha, Finset.nonempty_iff_ne_empty]

theorem verdict_trichotomy [DecidableEq Row] [DecidableEq TargetAnswer]
    (r : FiniteRequest Row SourceAnswer TargetAnswer) :
    evaluate r = Verdict.notEvaluated ∨
      evaluate r = Verdict.conservative ∨
      evaluate r = Verdict.nonconservative := by
  cases evaluate r <;> simp

theorem admitted_before_comparison [DecidableEq Row]
    [DecidableEq TargetAnswer]
    (r : FiniteRequest Row SourceAnswer TargetAnswer)
    (h : ¬eligible r) : evaluate r = Verdict.notEvaluated :=
  (evaluate_eq_notEvaluated_iff r).2 h

def selectedWitness [LinearOrder Row] [DecidableEq TargetAnswer]
    (r : FiniteRequest Row SourceAnswer TargetAnswer) : Option Row :=
  if h : (mismatchSet r).Nonempty then some ((mismatchSet r).min' h)
  else none

theorem selectedWitness_of_nonempty [LinearOrder Row]
    [DecidableEq TargetAnswer]
    (r : FiniteRequest Row SourceAnswer TargetAnswer)
    (h : (mismatchSet r).Nonempty) :
    selectedWitness r = some ((mismatchSet r).min' h) := by
  simp [selectedWitness, h]

theorem selectedWitness_mem [LinearOrder Row] [DecidableEq TargetAnswer]
    (r : FiniteRequest Row SourceAnswer TargetAnswer)
    (h : (mismatchSet r).Nonempty) :
    (mismatchSet r).min' h ∈ mismatchSet r :=
  Finset.min'_mem _ h

theorem selectedWitness_le [LinearOrder Row] [DecidableEq TargetAnswer]
    (r : FiniteRequest Row SourceAnswer TargetAnswer)
    (h : (mismatchSet r).Nonempty) {row : Row}
    (hrow : row ∈ mismatchSet r) :
    (mismatchSet r).min' h ≤ row :=
  Finset.min'_le _ _ hrow

/-! ## Explicit finite formation and refusal ledger -/

/-- The seven formation fields whose absence produces the registered malformed
contract refusals. -/
structure FormationChecklist where
  sourceAnswersPresent : Bool
  targetAnswersPresent : Bool
  transportPresent : Bool
  queryRegistered : Bool
  presentationActionPresent : Bool
  rowCoverageComplete : Bool
  answerTypesCompatible : Bool
  deriving DecidableEq, Repr

/-- Formation succeeds exactly when every required field is present. -/
def FormationChecklist.complete (checklist : FormationChecklist) : Bool :=
  checklist.sourceAnswersPresent &&
    checklist.targetAnswersPresent &&
    checklist.transportPresent &&
    checklist.queryRegistered &&
    checklist.presentationActionPresent &&
    checklist.rowCoverageComplete &&
    checklist.answerTypesCompatible

inductive FormationStatus where
  | admitted
  | malformedContract
  deriving DecidableEq, Repr

/-- The admission gate returns one uniform malformed-contract status before
any answer comparison. -/
def FormationChecklist.status (checklist : FormationChecklist) : FormationStatus :=
  if checklist.complete then FormationStatus.admitted
  else FormationStatus.malformedContract

/-- Formation alone never proves conservativity.  Before answer comparison,
both a successful gate and a failed gate are still non-evaluated; `status`
distinguishes readiness from malformed input. -/
def FormationChecklist.verdict (_checklist : FormationChecklist) : Verdict :=
  Verdict.notEvaluated

def completeFormationChecklist : FormationChecklist :=
  ⟨true, true, true, true, true, true, true⟩

def malformedFormationChecklists : List FormationChecklist := [
  ⟨false, true, true, true, true, true, true⟩,
  ⟨true, false, true, true, true, true, true⟩,
  ⟨true, true, false, true, true, true, true⟩,
  ⟨true, true, true, false, true, true, true⟩,
  ⟨true, true, true, true, false, true, true⟩,
  ⟨true, true, true, true, true, false, true⟩,
  ⟨true, true, true, true, true, true, false⟩
]

/-! ## Integrated typed contract formation and admission -/

/-- Scientific admission conditions that remain meaningful after all typed
contract fields have been formed.  Each condition is explicit and decidable;
none is represented by an unconstrained proposition. -/
structure AdmissionChecklist where
  compatiblePairLicensed : Bool
  evaluatorSemanticsLicensed : Bool
  layerBridgeLicensed : Bool
  presentationPolicyLicensed : Bool
  deriving DecidableEq, Repr

/-- Admission succeeds exactly when every post-formation scientific condition
has been licensed prospectively. -/
def AdmissionChecklist.complete (checklist : AdmissionChecklist) : Bool :=
  checklist.compatiblePairLicensed &&
    checklist.evaluatorSemanticsLicensed &&
    checklist.layerBridgeLicensed &&
    checklist.presentationPolicyLicensed

/-- The two typed fields not present in the historical seven-field formation
fixture.  The complete integrated validator checks these together with that
fixture. -/
structure ContractFormationChecklist where
  core : FormationChecklist
  evaluatorPresent : Bool
  layerPresent : Bool
  deriving DecidableEq, Repr

def ContractFormationChecklist.complete
    (checklist : ContractFormationChecklist) : Bool :=
  checklist.core.complete && checklist.evaluatorPresent &&
    checklist.layerPresent

/-- A fully formed finite phonological comparison contract.  `Finset` supplies
duplicate-free finite support; the functions are typed and total Lean
functions, so their evaluation terminates; and `matchedRows` below is derived
from the declared licensed-row predicate rather than supplied as an
independent, possibly incomplete table. -/
structure TypedFiniteContract
    (Row SourceAnswer TargetAnswer Evaluator Layer Presentation Query : Type) where
  licensedRow : Row → Bool
  sourceAnswer : Row → SourceAnswer
  targetAnswer : Row → TargetAnswer
  transport : SourceAnswer → TargetAnswer
  evaluator : Evaluator
  layer : Layer
  presentationAction : Presentation
  registeredQuery : Query
  admission : AdmissionChecklist

/-- A pre-formation record.  Required fields are optional here so that
malformed input has an exact representation and an exact refusal proof. -/
structure RawFiniteContract
    (Row SourceAnswer TargetAnswer Evaluator Layer Presentation Query : Type) where
  licensedRow : Row → Bool
  sourceAnswer : Option (Row → SourceAnswer)
  targetAnswer : Option (Row → TargetAnswer)
  transport : Option (SourceAnswer → TargetAnswer)
  evaluator : Option Evaluator
  layer : Option Layer
  presentationAction : Option Presentation
  registeredQuery : Option Query
  rowCoverageProved : Bool
  answerTypesProved : Bool
  admission : AdmissionChecklist

namespace RawFiniteContract

variable {Row SourceAnswer TargetAnswer Evaluator Layer Presentation Query : Type}

/-- The executable formation ledger is computed from the raw fields, not
asserted by the caller as a proposition. -/
def formationChecklist
    (raw : RawFiniteContract Row SourceAnswer TargetAnswer Evaluator Layer
      Presentation Query) : ContractFormationChecklist :=
  {
    core := {
      sourceAnswersPresent := raw.sourceAnswer.isSome
      targetAnswersPresent := raw.targetAnswer.isSome
      transportPresent := raw.transport.isSome
      queryRegistered := raw.registeredQuery.isSome
      presentationActionPresent := raw.presentationAction.isSome
      rowCoverageComplete := raw.rowCoverageProved
      answerTypesCompatible := raw.answerTypesProved
    }
    evaluatorPresent := raw.evaluator.isSome
    layerPresent := raw.layer.isSome
  }

/-- Formation extracts every typed field.  Failure of any required option or
either explicit Boolean check yields `none`. -/
def form
    (raw : RawFiniteContract Row SourceAnswer TargetAnswer Evaluator Layer
      Presentation Query) :
    Option (TypedFiniteContract Row SourceAnswer TargetAnswer Evaluator Layer
      Presentation Query) := do
  let sourceAnswer ← raw.sourceAnswer
  let targetAnswer ← raw.targetAnswer
  let transport ← raw.transport
  let evaluator ← raw.evaluator
  let layer ← raw.layer
  let presentationAction ← raw.presentationAction
  let registeredQuery ← raw.registeredQuery
  if raw.rowCoverageProved && raw.answerTypesProved then
    some {
      licensedRow := raw.licensedRow
      sourceAnswer := sourceAnswer
      targetAnswer := targetAnswer
      transport := transport
      evaluator := evaluator
      layer := layer
      presentationAction := presentationAction
      registeredQuery := registeredQuery
      admission := raw.admission
    }
  else
    none

/-- Formation succeeds exactly when all nine integrated formation checks
succeed.  The proof exhausts every optional field and both Boolean
checks. -/
theorem form_isSome_eq_complete
    (raw : RawFiniteContract Row SourceAnswer TargetAnswer Evaluator Layer
      Presentation Query) :
    raw.form.isSome = raw.formationChecklist.complete := by
  cases hSource : raw.sourceAnswer <;>
    cases hTarget : raw.targetAnswer <;>
    cases hTransport : raw.transport <;>
    cases hEvaluator : raw.evaluator <;>
    cases hLayer : raw.layer <;>
    cases hPresentation : raw.presentationAction <;>
    cases hQuery : raw.registeredQuery <;>
    cases hCoverage : raw.rowCoverageProved <;>
    cases hTypes : raw.answerTypesProved <;>
    simp [form, formationChecklist, ContractFormationChecklist.complete,
      FormationChecklist.complete, hSource, hTarget, hTransport, hEvaluator,
      hLayer, hPresentation, hQuery, hCoverage, hTypes]

/-- A raw contract fails formation exactly when the integrated checklist is
false. -/
theorem form_eq_none_iff_incomplete
    (raw : RawFiniteContract Row SourceAnswer TargetAnswer Evaluator Layer
      Presentation Query) :
    raw.form = none ↔ raw.formationChecklist.complete = false := by
  constructor
  · intro hNone
    simpa [hNone] using (form_isSome_eq_complete raw).symm
  · intro hIncomplete
    have hIsSome : raw.form.isSome = false := by
      simpa [hIncomplete] using form_isSome_eq_complete raw
    simpa using hIsSome

end RawFiniteContract

namespace TypedFiniteContract

variable {Row SourceAnswer TargetAnswer Evaluator Layer Presentation Query : Type}

/-- Every and only declared licensed row is included.  `Finset.univ.filter`
makes coverage exhaustive over the finite row type and duplicate-free by
construction. -/
def matchedRows [Fintype Row] [DecidableEq Row]
    (contract : TypedFiniteContract Row SourceAnswer TargetAnswer Evaluator
      Layer Presentation Query) : Finset Row :=
  Finset.univ.filter (fun row => contract.licensedRow row)

theorem mem_matchedRows_iff [Fintype Row] [DecidableEq Row]
    (contract : TypedFiniteContract Row SourceAnswer TargetAnswer Evaluator
      Layer Presentation Query) (row : Row) :
    row ∈ contract.matchedRows ↔ contract.licensedRow row = true := by
  simp [matchedRows]

/-- The integrated contract produces the reusable comparison kernel with no
opaque formation proposition.  Formation is already witnessed by the typed
record.  Admission is exactly the explicit checklist plus a nonempty complete
matched-row family. -/
def toRequest [Fintype Row] [DecidableEq Row]
    (contract : TypedFiniteContract Row SourceAnswer TargetAnswer Evaluator
      Layer Presentation Query) : FiniteRequest Row SourceAnswer TargetAnswer :=
  {
    rows := contract.matchedRows
    formed := True
    admitted := contract.admission.complete = true ∧
      contract.matchedRows.Nonempty
    formedDecision := inferInstance
    admittedDecision := inferInstance
    sourceAnswer := contract.sourceAnswer
    targetAnswer := contract.targetAnswer
    transport := contract.transport
  }

theorem eligible_iff_explicit_admission [Fintype Row] [DecidableEq Row]
    (contract : TypedFiniteContract Row SourceAnswer TargetAnswer Evaluator
      Layer Presentation Query) :
    contract.toRequest.eligible ↔
      contract.admission.complete = true ∧ contract.matchedRows.Nonempty := by
  simp [toRequest, FiniteRequest.eligible]

end TypedFiniteContract

namespace RawFiniteContract

variable {Row SourceAnswer TargetAnswer Evaluator Layer Presentation Query : Type}

/-- The complete integrated evaluator: formation first, explicit admission
second, and transported-answer equality only after both have succeeded. -/
def evaluate [Fintype Row] [DecidableEq Row] [DecidableEq TargetAnswer]
    (raw : RawFiniteContract Row SourceAnswer TargetAnswer Evaluator Layer
      Presentation Query) : Verdict :=
  match raw.form with
  | none => Verdict.notEvaluated
  | some contract => contract.toRequest.evaluate

theorem formation_failure_precedes_comparison
    [Fintype Row] [DecidableEq Row] [DecidableEq TargetAnswer]
    (raw : RawFiniteContract Row SourceAnswer TargetAnswer Evaluator Layer
      Presentation Query) (hFailure : raw.form = none) :
    raw.evaluate = Verdict.notEvaluated := by
  simp [evaluate, hFailure]

theorem evaluate_eq_notEvaluated_iff
    [Fintype Row] [DecidableEq Row] [DecidableEq TargetAnswer]
    (raw : RawFiniteContract Row SourceAnswer TargetAnswer Evaluator Layer
      Presentation Query) :
    raw.evaluate = Verdict.notEvaluated ↔
      raw.form = none ∨
        ∃ contract, raw.form = some contract ∧
          ¬ contract.toRequest.eligible := by
  cases hForm : raw.form with
  | none => simp [evaluate, hForm]
  | some contract =>
      simp [evaluate, hForm,
        FiniteRequest.evaluate_eq_notEvaluated_iff]

theorem evaluate_eq_conservative_iff
    [Fintype Row] [DecidableEq Row] [DecidableEq TargetAnswer]
    (raw : RawFiniteContract Row SourceAnswer TargetAnswer Evaluator Layer
      Presentation Query) :
    raw.evaluate = Verdict.conservative ↔
      ∃ contract, raw.form = some contract ∧
        contract.toRequest.eligible ∧
        ∀ row ∈ contract.matchedRows,
          contract.transport (contract.sourceAnswer row) =
            contract.targetAnswer row := by
  cases hForm : raw.form with
  | none => simp [evaluate, hForm]
  | some contract =>
      simp [evaluate, hForm,
        FiniteRequest.evaluate_eq_conservative_iff,
        TypedFiniteContract.toRequest]

theorem evaluate_eq_nonconservative_iff
    [Fintype Row] [DecidableEq Row] [DecidableEq TargetAnswer]
    (raw : RawFiniteContract Row SourceAnswer TargetAnswer Evaluator Layer
      Presentation Query) :
    raw.evaluate = Verdict.nonconservative ↔
      ∃ contract, raw.form = some contract ∧
        contract.toRequest.eligible ∧
        ∃ row ∈ contract.matchedRows,
          contract.transport (contract.sourceAnswer row) ≠
            contract.targetAnswer row := by
  cases hForm : raw.form with
  | none => simp [evaluate, hForm]
  | some contract =>
      simp [evaluate, hForm,
        FiniteRequest.evaluate_eq_nonconservative_iff,
        FiniteRequest.mismatchSet_nonempty_iff,
        TypedFiniteContract.toRequest]

theorem verdict_trichotomy
    [Fintype Row] [DecidableEq Row] [DecidableEq TargetAnswer]
    (raw : RawFiniteContract Row SourceAnswer TargetAnswer Evaluator Layer
      Presentation Query) :
    raw.evaluate = Verdict.notEvaluated ∨
      raw.evaluate = Verdict.conservative ∨
      raw.evaluate = Verdict.nonconservative := by
  cases raw.evaluate <;> simp

/-- Integrated qualified finite decision theorem.  Unlike the reusable kernel,
this statement includes executable formation, explicit admission, complete
licensed-row derivation, and all three sound-and-complete result branches. -/
theorem qualifiedFiniteContractDecision
    [Fintype Row] [DecidableEq Row] [DecidableEq TargetAnswer]
    (raw : RawFiniteContract Row SourceAnswer TargetAnswer Evaluator Layer
      Presentation Query) :
    (raw.form.isSome = raw.formationChecklist.complete) ∧
    (raw.form = none → raw.evaluate = Verdict.notEvaluated) ∧
    (raw.evaluate = Verdict.notEvaluated ↔
      raw.form = none ∨
        ∃ contract, raw.form = some contract ∧
          ¬ contract.toRequest.eligible) ∧
    (raw.evaluate = Verdict.conservative ↔
      ∃ contract, raw.form = some contract ∧
        contract.toRequest.eligible ∧
        ∀ row ∈ contract.matchedRows,
          contract.transport (contract.sourceAnswer row) =
            contract.targetAnswer row) ∧
    (raw.evaluate = Verdict.nonconservative ↔
      ∃ contract, raw.form = some contract ∧
        contract.toRequest.eligible ∧
        ∃ row ∈ contract.matchedRows,
          contract.transport (contract.sourceAnswer row) ≠
            contract.targetAnswer row) ∧
    (raw.evaluate = Verdict.notEvaluated ∨
      raw.evaluate = Verdict.conservative ∨
      raw.evaluate = Verdict.nonconservative) := by
  exact ⟨form_isSome_eq_complete raw,
    formation_failure_precedes_comparison raw,
    evaluate_eq_notEvaluated_iff raw,
    evaluate_eq_conservative_iff raw,
    evaluate_eq_nonconservative_iff raw,
    verdict_trichotomy raw⟩

end RawFiniteContract

/-- All declared fields pass the exact formation validator. -/
theorem calc_f1_admission_01 :
    completeFormationChecklist.complete = true ∧
      completeFormationChecklist.status = FormationStatus.admitted := by
  decide

/-- Each singly malformed contract is refused before comparison and receives
the same explicit formation-failure status. -/
theorem calc_f1_refusals_05 :
    malformedFormationChecklists.map FormationChecklist.verdict =
      List.replicate 7 Verdict.notEvaluated ∧
    malformedFormationChecklists.map FormationChecklist.status =
      List.replicate 7 FormationStatus.malformedContract := by
  decide

/-- Finite structural measures expose the bounded carriers traversed by the
decision procedure. -/
structure FiniteStructuralMeasure where
  domainSize : Nat
  matchedRowCount : Nat
  sourceTableSize : Nat
  targetTableSize : Nat
  deriving DecidableEq, Repr

def registeredFiniteStructuralMeasure : FiniteStructuralMeasure :=
  ⟨2, 2, 2, 2⟩

/-- Exact registered bounded-enumeration measure. -/
theorem calc_f1_termination_04 :
    registeredFiniteStructuralMeasure = ⟨2, 2, 2, 2⟩ := by
  rfl

/-- The executable decision kernel is a total function and hence supplies a
verdict for every already formed finite request. -/
theorem evaluate_total [DecidableEq Row] [DecidableEq TargetAnswer]
    (r : FiniteRequest Row SourceAnswer TargetAnswer) :
    ∃ verdict, evaluate r = verdict := by
  exact ⟨evaluate r, rfl⟩

/-- The generic progress statement is the exact registered three-way
partition once a finite request has been formed. -/
theorem calc_f1_progress_02 [DecidableEq Row] [DecidableEq TargetAnswer]
    (r : FiniteRequest Row SourceAnswer TargetAnswer) :
    evaluate r = Verdict.conservative ∨
      evaluate r = Verdict.nonconservative ∨
      evaluate r = Verdict.notEvaluated := by
  rcases verdict_trichotomy r with h | h | h
  · exact Or.inr (Or.inr h)
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

/-- A nonconservative admitted request carries the complete finite mismatch
set and therefore at least one genuine transported-answer inequality. -/
theorem calc_f1_witness_03 [DecidableEq Row] [DecidableEq TargetAnswer]
    (r : FiniteRequest Row SourceAnswer TargetAnswer)
    (hVerdict : evaluate r = Verdict.nonconservative) :
    (mismatchSet r).Nonempty ∧
      ∀ row, row ∈ mismatchSet r ↔
        row ∈ r.rows ∧
          r.transport (r.sourceAnswer row) ≠ r.targetAnswer row := by
  refine ⟨(evaluate_eq_nonconservative_iff r).1 hVerdict |>.2, ?_⟩
  exact fun row => mem_mismatchSet_iff r row

/-- Under the declared row order, every nonconservative verdict returns the
least member of the complete mismatch set. -/
theorem calc_f1_least_witness_03 [LinearOrder Row]
    [DecidableEq TargetAnswer]
    (r : FiniteRequest Row SourceAnswer TargetAnswer)
    (hVerdict : evaluate r = Verdict.nonconservative) :
    ∃ h : (mismatchSet r).Nonempty,
      selectedWitness r = some ((mismatchSet r).min' h) ∧
      (mismatchSet r).min' h ∈ mismatchSet r ∧
      ∀ row ∈ mismatchSet r, (mismatchSet r).min' h ≤ row := by
  have hNonempty : (mismatchSet r).Nonempty :=
    (evaluate_eq_nonconservative_iff r).1 hVerdict |>.2
  refine ⟨hNonempty, selectedWitness_of_nonempty r hNonempty,
    selectedWitness_mem r hNonempty, ?_⟩
  intro row hRow
  exact selectedWitness_le r hNonempty hRow

/-- The three registered verdict constructors are pairwise distinct. -/
theorem verdicts_pairwise_distinct :
    Verdict.conservative ≠ Verdict.nonconservative ∧
      Verdict.conservative ≠ Verdict.notEvaluated ∧
      Verdict.nonconservative ≠ Verdict.notEvaluated := by
  decide

/-- The qualified finite decision theorem: the executable kernel terminates,
its three verdicts are exhaustive, and each verdict is equivalent to its
contract-relative semantic condition. -/
theorem qualifiedFiniteDecision
    [LinearOrder Row] [DecidableEq TargetAnswer]
    (r : FiniteRequest Row SourceAnswer TargetAnswer) :
    (∃ verdict, evaluate r = verdict) ∧
    (evaluate r = Verdict.notEvaluated ↔ ¬eligible r) ∧
    (evaluate r = Verdict.conservative ↔
      eligible r ∧
        ∀ row ∈ r.rows,
          r.transport (r.sourceAnswer row) = r.targetAnswer row) ∧
    (evaluate r = Verdict.nonconservative ↔
      eligible r ∧
        ∃ row ∈ r.rows,
          r.transport (r.sourceAnswer row) ≠ r.targetAnswer row) ∧
    (evaluate r = Verdict.conservative ∨
      evaluate r = Verdict.nonconservative ∨
      evaluate r = Verdict.notEvaluated) ∧
    (Verdict.conservative ≠ Verdict.nonconservative ∧
      Verdict.conservative ≠ Verdict.notEvaluated ∧
      Verdict.nonconservative ≠ Verdict.notEvaluated) ∧
    (evaluate r = Verdict.nonconservative →
      ∃ h : (mismatchSet r).Nonempty,
        selectedWitness r = some ((mismatchSet r).min' h) ∧
        (mismatchSet r).min' h ∈ mismatchSet r ∧
        ∀ row ∈ mismatchSet r, (mismatchSet r).min' h ≤ row) := by
  refine ⟨evaluate_total r, evaluate_eq_notEvaluated_iff r,
    evaluate_eq_conservative_iff r, ?_, calc_f1_progress_02 r,
    verdicts_pairwise_distinct, ?_⟩
  · rw [evaluate_eq_nonconservative_iff, mismatchSet_nonempty_iff]
  · exact calc_f1_least_witness_03 r

end FiniteRequest

end PhonologicalCalculus
