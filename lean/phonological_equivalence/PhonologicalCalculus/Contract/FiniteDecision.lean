              
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Max

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

structure FormationChecklist where
  sourceAnswersPresent : Bool
  targetAnswersPresent : Bool
  transportPresent : Bool
  queryRegistered : Bool
  presentationActionPresent : Bool
  rowCoverageComplete : Bool
  answerTypesCompatible : Bool
  deriving DecidableEq, Repr

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

def FormationChecklist.status (checklist : FormationChecklist) : FormationStatus :=
  if checklist.complete then FormationStatus.admitted
  else FormationStatus.malformedContract

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

structure AdmissionChecklist where
  compatiblePairLicensed : Bool
  evaluatorSemanticsLicensed : Bool
  layerBridgeLicensed : Bool
  presentationPolicyLicensed : Bool
  deriving DecidableEq, Repr

def AdmissionChecklist.complete (checklist : AdmissionChecklist) : Bool :=
  checklist.compatiblePairLicensed &&
    checklist.evaluatorSemanticsLicensed &&
    checklist.layerBridgeLicensed &&
    checklist.presentationPolicyLicensed

structure ContractFormationChecklist where
  core : FormationChecklist
  evaluatorPresent : Bool
  layerPresent : Bool
  deriving DecidableEq, Repr

def ContractFormationChecklist.complete
    (checklist : ContractFormationChecklist) : Bool :=
  checklist.core.complete && checklist.evaluatorPresent &&
    checklist.layerPresent

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

def matchedRows [Fintype Row] [DecidableEq Row]
    (contract : TypedFiniteContract Row SourceAnswer TargetAnswer Evaluator
      Layer Presentation Query) : Finset Row :=
  Finset.univ.filter (fun row => contract.licensedRow row)

theorem mem_matchedRows_iff [Fintype Row] [DecidableEq Row]
    (contract : TypedFiniteContract Row SourceAnswer TargetAnswer Evaluator
      Layer Presentation Query) (row : Row) :
    row ∈ contract.matchedRows ↔ contract.licensedRow row = true := by
  simp [matchedRows]

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

theorem calc_f1_admission_01 :
    completeFormationChecklist.complete = true ∧
      completeFormationChecklist.status = FormationStatus.admitted := by
  decide

theorem calc_f1_refusals_05 :
    malformedFormationChecklists.map FormationChecklist.verdict =
      List.replicate 7 Verdict.notEvaluated ∧
    malformedFormationChecklists.map FormationChecklist.status =
      List.replicate 7 FormationStatus.malformedContract := by
  decide

structure FiniteStructuralMeasure where
  domainSize : Nat
  matchedRowCount : Nat
  sourceTableSize : Nat
  targetTableSize : Nat
  deriving DecidableEq, Repr

def registeredFiniteStructuralMeasure : FiniteStructuralMeasure :=
  ⟨2, 2, 2, 2⟩

theorem calc_f1_termination_04 :
    registeredFiniteStructuralMeasure = ⟨2, 2, 2, 2⟩ := by
  rfl

theorem evaluate_total [DecidableEq Row] [DecidableEq TargetAnswer]
    (r : FiniteRequest Row SourceAnswer TargetAnswer) :
    ∃ verdict, evaluate r = verdict := by
  exact ⟨evaluate r, rfl⟩

theorem calc_f1_progress_02 [DecidableEq Row] [DecidableEq TargetAnswer]
    (r : FiniteRequest Row SourceAnswer TargetAnswer) :
    evaluate r = Verdict.conservative ∨
      evaluate r = Verdict.nonconservative ∨
      evaluate r = Verdict.notEvaluated := by
  rcases verdict_trichotomy r with h | h | h
  · exact Or.inr (Or.inr h)
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

theorem calc_f1_witness_03 [DecidableEq Row] [DecidableEq TargetAnswer]
    (r : FiniteRequest Row SourceAnswer TargetAnswer)
    (hVerdict : evaluate r = Verdict.nonconservative) :
    (mismatchSet r).Nonempty ∧
      ∀ row, row ∈ mismatchSet r ↔
        row ∈ r.rows ∧
          r.transport (r.sourceAnswer row) ≠ r.targetAnswer row := by
  refine ⟨(evaluate_eq_nonconservative_iff r).1 hVerdict |>.2, ?_⟩
  exact fun row => mem_mismatchSet_iff r row

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

theorem verdicts_pairwise_distinct :
    Verdict.conservative ≠ Verdict.nonconservative ∧
      Verdict.conservative ≠ Verdict.notEvaluated ∧
      Verdict.nonconservative ≠ Verdict.notEvaluated := by
  decide

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
