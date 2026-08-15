import PhonologicalCalculus.MaxEnt.ExecutableQuarticCompiler
import Mathlib.Tactic

/-!
# Executable one-hot compilation to duplicate-free phonological rows

This module converts the deterministic integer-monomial list into a finite
`{1,...,5}` row table without enumerating an `MvPolynomial` support.  Each
unit of coefficient magnitude receives a rectangular slot and its own tag
coordinate.  Inactive rectangular slots are filtered out.  The resulting
one-hot tag distinguishes rows even when the source list contains repeated
exponent vectors.

The construction is intentionally larger than the binary-tag presentation.
Its purpose is an entirely explicit compiler whose row identity, evaluation,
and size can be checked directly from the source list.
-/

namespace PhonologicalCalculus.MaxEnt

open Finset Set
open scoped BigOperators

/-! ## Proof-carrying executable quartics -/

structure ExecutableQuarticCode where
  coordinateCount : ℕ
  terms : List (ExecutableIntegerMonomial coordinateCount)
  exponent_lt_five : ∀ term ∈ terms, ∀ coordinate,
    term.exponent coordinate < 5

def ExecutableQuarticCode.coefficientL1
    (source : ExecutableQuarticCode) : ℕ :=
  executableCoefficientL1 source.terms

abbrev ExecutableQuarticCode.Slot
    (source : ExecutableQuarticCode) :=
  Fin source.terms.length × Fin source.coefficientL1

def ExecutableQuarticCode.termAt
    (source : ExecutableQuarticCode) (slot : source.Slot) :
    ExecutableIntegerMonomial source.coordinateCount :=
  source.terms.get slot.1

def ExecutableQuarticCode.active
    (source : ExecutableQuarticCode) (slot : source.Slot) : Prop :=
  slot.2.val < (source.termAt slot).coefficient.natAbs

def ExecutableQuarticCode.positive
    (source : ExecutableQuarticCode) (slot : source.Slot) : Prop :=
  source.active slot ∧ 0 < (source.termAt slot).coefficient

def ExecutableQuarticCode.negative
    (source : ExecutableQuarticCode) (slot : source.Slot) : Prop :=
  source.active slot ∧ (source.termAt slot).coefficient < 0

def ExecutableQuarticCode.activeSlots
    (source : ExecutableQuarticCode) : Finset source.Slot :=
  Finset.univ.filter fun slot =>
    slot.2.val < (source.termAt slot).coefficient.natAbs

def ExecutableQuarticCode.positiveSlots
    (source : ExecutableQuarticCode) : Finset source.Slot :=
  Finset.univ.filter fun slot =>
    slot.2.val < (source.termAt slot).coefficient.natAbs ∧
      0 < (source.termAt slot).coefficient

def ExecutableQuarticCode.negativeSlots
    (source : ExecutableQuarticCode) : Finset source.Slot :=
  Finset.univ.filter fun slot =>
    slot.2.val < (source.termAt slot).coefficient.natAbs ∧
      (source.termAt slot).coefficient < 0

def ExecutableQuarticCode.tagDimension
    (source : ExecutableQuarticCode) : ℕ :=
  source.terms.length * source.coefficientL1

def ExecutableQuarticCode.slotTagCoordinate
    (source : ExecutableQuarticCode) (slot : source.Slot) :
    Fin source.tagDimension :=
  finProdFinEquiv slot

def ExecutableQuarticCode.coordinateTagSlot
    (source : ExecutableQuarticCode)
    (coordinate : Fin source.tagDimension) : source.Slot :=
  finProdFinEquiv.symm coordinate

@[simp]
theorem ExecutableQuarticCode.coordinateTagSlot_slotTagCoordinate
    (source : ExecutableQuarticCode) (slot : source.Slot) :
    source.coordinateTagSlot (source.slotTagCoordinate slot) = slot := by
  simp [ExecutableQuarticCode.coordinateTagSlot,
    ExecutableQuarticCode.slotTagCoordinate]

/-! ## Deterministic one-hot rows -/

def ExecutableQuarticCode.sourceResidualExponent
    (source : ExecutableQuarticCode) (slot : source.Slot)
    (coordinate : Fin source.coordinateCount) : Fin 5 :=
  ⟨(source.termAt slot).exponent coordinate,
    source.exponent_lt_five (source.termAt slot)
      (List.get_mem source.terms slot.1) coordinate⟩

def ExecutableQuarticCode.tagResidualExponent
    (source : ExecutableQuarticCode) (slot : source.Slot)
    (coordinate : Fin source.tagDimension) : Fin 5 :=
  if source.coordinateTagSlot coordinate = slot then
    if 0 < (source.termAt slot).coefficient then
      ⟨0, by omega⟩
    else
      ⟨2, by omega⟩
  else
    ⟨1, by omega⟩

def ExecutableQuarticCode.taggedResidualRow
    (source : ExecutableQuarticCode) (slot : source.Slot) :
    Fin (source.coordinateCount + source.tagDimension) → Fin 5 :=
  fun coordinate =>
    match finSumFinEquiv.symm coordinate with
    | .inl oldCoordinate => source.sourceResidualExponent slot oldCoordinate
    | .inr tagCoordinate => source.tagResidualExponent slot tagCoordinate

theorem ExecutableQuarticCode.rectangularOneHotTaggedResidualRow_injective
    (source : ExecutableQuarticCode) :
    Function.Injective source.taggedResidualRow := by
  intro first second hRows
  by_contra hDifferent
  have hCoordinate := congrFun hRows
    (finSumFinEquiv (Sum.inr (source.slotTagCoordinate first)))
  simp only [ExecutableQuarticCode.taggedResidualRow,
    Equiv.symm_apply_apply] at hCoordinate
  unfold ExecutableQuarticCode.tagResidualExponent at hCoordinate
  rw [source.coordinateTagSlot_slotTagCoordinate] at hCoordinate
  simp [hDifferent] at hCoordinate
  split at hCoordinate <;> simp_all

def ExecutableQuarticCode.positiveRows
    (source : ExecutableQuarticCode) :
    Finset (Fin (source.coordinateCount + source.tagDimension) → Fin 5) :=
  source.positiveSlots.image source.taggedResidualRow

def ExecutableQuarticCode.negativeRows
    (source : ExecutableQuarticCode) :
    Finset (Fin (source.coordinateCount + source.tagDimension) → Fin 5) :=
  source.negativeSlots.image source.taggedResidualRow

theorem ExecutableQuarticCode.slots_disjoint
    (source : ExecutableQuarticCode) :
    Disjoint source.positiveSlots source.negativeSlots := by
  rw [Finset.disjoint_left]
  intro slot hPositive hNegative
  have hPositiveCoefficient : 0 < (source.termAt slot).coefficient :=
    (Finset.mem_filter.mp hPositive).2.2
  have hNegativeCoefficient : (source.termAt slot).coefficient < 0 :=
    (Finset.mem_filter.mp hNegative).2.2
  omega

theorem ExecutableQuarticCode.rectangularOneHotRows_disjoint
    (source : ExecutableQuarticCode) :
    Disjoint source.positiveRows source.negativeRows := by
  rw [Finset.disjoint_left]
  intro row hPositive hNegative
  rw [ExecutableQuarticCode.positiveRows, Finset.mem_image] at hPositive
  rw [ExecutableQuarticCode.negativeRows, Finset.mem_image] at hNegative
  obtain ⟨positiveSlot, hPositiveSlot, rfl⟩ := hPositive
  obtain ⟨negativeSlot, hNegativeSlot, hRows⟩ := hNegative
  have hSlots : positiveSlot = negativeSlot :=
    source.rectangularOneHotTaggedResidualRow_injective hRows.symm
  subst negativeSlot
  exact Finset.disjoint_left.mp source.slots_disjoint
    hPositiveSlot hNegativeSlot

def ExecutableQuarticCode.toOneToFiveOrderCode
    (source : ExecutableQuarticCode) : DuplicateFreeOneToFiveOrderCode where
  coordinateCount := source.coordinateCount + source.tagDimension
  positiveRows := source.positiveRows
  negativeRows := source.negativeRows
  rows_disjoint := source.rectangularOneHotRows_disjoint

theorem ExecutableQuarticCode.rectangularOneHotCard_positiveRows
    (source : ExecutableQuarticCode) :
    source.positiveRows.card = source.positiveSlots.card := by
  exact Finset.card_image_of_injective _
    source.rectangularOneHotTaggedResidualRow_injective

theorem ExecutableQuarticCode.rectangularOneHotCard_negativeRows
    (source : ExecutableQuarticCode) :
    source.negativeRows.card = source.negativeSlots.card := by
  exact Finset.card_image_of_injective _
    source.rectangularOneHotTaggedResidualRow_injective

theorem ExecutableQuarticCode.rectangularOneHotTagResidualExponent_le_two
    (source : ExecutableQuarticCode) (slot : source.Slot)
    (coordinate : Fin source.tagDimension) :
    (source.tagResidualExponent slot coordinate).val ≤ 2 := by
  unfold ExecutableQuarticCode.tagResidualExponent
  by_cases hOwn : source.coordinateTagSlot coordinate = slot
  · rw [if_pos hOwn]
    split <;> simp
  · rw [if_neg hOwn]
    simp

theorem ExecutableQuarticCode.rectangularOneHotTarget_row_bounds
    (source : ExecutableQuarticCode) (slot : source.Slot) :
    (∀ coordinate : Fin source.coordinateCount,
      1 ≤ (source.taggedResidualRow slot
        (finSumFinEquiv (Sum.inl coordinate))).val + 1 ∧
      (source.taggedResidualRow slot
        (finSumFinEquiv (Sum.inl coordinate))).val + 1 ≤ 5) ∧
    (∀ coordinate : Fin source.tagDimension,
      1 ≤ (source.taggedResidualRow slot
        (finSumFinEquiv (Sum.inr coordinate))).val + 1 ∧
      (source.taggedResidualRow slot
        (finSumFinEquiv (Sum.inr coordinate))).val + 1 ≤ 3) := by
  constructor
  · intro coordinate
    simp only [ExecutableQuarticCode.taggedResidualRow,
      Equiv.symm_apply_apply]
    exact ⟨Nat.succ_pos _,
      (source.sourceResidualExponent slot coordinate).isLt⟩
  · intro coordinate
    simp only [ExecutableQuarticCode.taggedResidualRow,
      Equiv.symm_apply_apply]
    exact ⟨Nat.succ_pos _, Nat.succ_le_succ
      (source.rectangularOneHotTagResidualExponent_le_two slot coordinate)⟩

/-! ## Strictifier code -/

def executableStrictifierQuarticCode
    (problem : BoundedETRINVInstance) (tailLength : ℕ) :
    ExecutableQuarticCode where
  coordinateCount := problem.variableCount + tailLength
  terms := executableStrictifierPolynomial problem tailLength
  exponent_lt_five := by
    intro term hTerm coordinate
    have hDegree := executableStrictifierPolynomial_degreeAtMostFour
      problem tailLength term hTerm
    have hCoordinate : term.exponent coordinate ≤ term.totalDegree := by
      unfold ExecutableIntegerMonomial.totalDegree
      exact Finset.single_le_sum
        (fun index _ => Nat.zero_le (term.exponent index))
        (Finset.mem_univ coordinate)
    omega

/-! ## Compact deterministic unit expansion -/

structure ExecutableSignedUnit (coordinateCount : ℕ) where
  exponent : Fin coordinateCount → ℕ
  positive : Bool

def expandExecutableMonomialUnits {coordinateCount : ℕ}
    (term : ExecutableIntegerMonomial coordinateCount) :
    List (ExecutableSignedUnit coordinateCount) :=
  List.replicate term.coefficient.natAbs
    ⟨term.exponent, decide (0 < term.coefficient)⟩

def expandExecutablePolynomialUnits {coordinateCount : ℕ}
    (terms : List (ExecutableIntegerMonomial coordinateCount)) :
    List (ExecutableSignedUnit coordinateCount) :=
  terms.flatMap expandExecutableMonomialUnits

def ExecutableSignedUnit.monomial
    {coordinateCount : ℕ} (unit : ExecutableSignedUnit coordinateCount)
    (point : Fin coordinateCount → ℝ) : ℝ :=
  ∏ coordinate, point coordinate ^ unit.exponent coordinate

def ExecutableSignedUnit.value
    {coordinateCount : ℕ} (unit : ExecutableSignedUnit coordinateCount)
    (point : Fin coordinateCount → ℝ) : ℝ :=
  if unit.positive then unit.monomial point else -unit.monomial point

def evaluateExecutableUnitPolynomial {coordinateCount : ℕ}
    (units : List (ExecutableSignedUnit coordinateCount))
    (point : Fin coordinateCount → ℝ) : ℝ :=
  (units.map fun unit => unit.value point).sum

theorem evaluate_expandExecutableMonomialUnits
    {coordinateCount : ℕ}
    (term : ExecutableIntegerMonomial coordinateCount)
    (point : Fin coordinateCount → ℝ) :
    evaluateExecutableUnitPolynomial
        (expandExecutableMonomialUnits term) point =
      term.evaluate point := by
  by_cases hPositive : 0 < term.coefficient
  · have hNonnegative : 0 ≤ term.coefficient := hPositive.le
    have hAbsInteger : (term.coefficient.natAbs : ℤ) = term.coefficient :=
      Int.natAbs_of_nonneg hNonnegative
    have hAbsReal : (term.coefficient.natAbs : ℝ) = term.coefficient := by
      calc
        (term.coefficient.natAbs : ℝ) =
            ((term.coefficient.natAbs : ℤ) : ℝ) := rfl
        _ = (term.coefficient : ℝ) :=
          congrArg (fun value : ℤ => (value : ℝ)) hAbsInteger
    simp only [evaluateExecutableUnitPolynomial,
      expandExecutableMonomialUnits, List.map_replicate,
      List.sum_replicate, ExecutableSignedUnit.value,
      decide_eq_true_eq, hPositive, ↓reduceIte,
      ExecutableSignedUnit.monomial,
      ExecutableIntegerMonomial.evaluate]
    rw [nsmul_eq_mul]
    rw [hAbsReal]
  · by_cases hZero : term.coefficient = 0
    · simp [evaluateExecutableUnitPolynomial,
        expandExecutableMonomialUnits, ExecutableIntegerMonomial.evaluate,
        hZero]
    · have hNegative : term.coefficient < 0 := by omega
      have hAbsInteger :
          term.coefficient = -(term.coefficient.natAbs : ℤ) :=
        (Int.natAbs_eq term.coefficient).resolve_left (by omega)
      have hAbsReal :
          (term.coefficient : ℝ) = -(term.coefficient.natAbs : ℝ) := by
        have hCast := congrArg (fun value : ℤ => (value : ℝ)) hAbsInteger
        simpa only [Int.cast_neg, Int.cast_natCast] using hCast
      simp only [evaluateExecutableUnitPolynomial,
        expandExecutableMonomialUnits, List.map_replicate,
        List.sum_replicate, ExecutableSignedUnit.value,
        decide_eq_true_eq, hPositive, ↓reduceIte,
        ExecutableSignedUnit.monomial,
        ExecutableIntegerMonomial.evaluate]
      rw [nsmul_eq_mul]
      rw [hAbsReal]
      ring

theorem evaluate_expandExecutablePolynomialUnits
    {coordinateCount : ℕ}
    (terms : List (ExecutableIntegerMonomial coordinateCount))
    (point : Fin coordinateCount → ℝ) :
    evaluateExecutableUnitPolynomial
        (expandExecutablePolynomialUnits terms) point =
      evaluateExecutablePolynomial terms point := by
  induction terms with
  | nil => simp [evaluateExecutableUnitPolynomial,
      evaluateExecutablePolynomial, expandExecutablePolynomialUnits]
  | cons term rest ih =>
      rw [expandExecutablePolynomialUnits, List.flatMap_cons]
      simp only [evaluateExecutableUnitPolynomial, List.map_append,
        List.sum_append]
      change evaluateExecutableUnitPolynomial
          (expandExecutableMonomialUnits term) point +
          evaluateExecutableUnitPolynomial
            (expandExecutablePolynomialUnits rest) point = _
      rw [evaluate_expandExecutableMonomialUnits]
      rw [ih]
      simp [evaluateExecutablePolynomial]

theorem expandExecutablePolynomialUnits_length
    {coordinateCount : ℕ}
    (terms : List (ExecutableIntegerMonomial coordinateCount)) :
    (expandExecutablePolynomialUnits terms).length =
      executableCoefficientL1 terms := by
  induction terms with
  | nil => simp [expandExecutablePolynomialUnits,
      executableCoefficientL1]
  | cons term rest ih =>
      simp [expandExecutablePolynomialUnits,
        expandExecutableMonomialUnits, executableCoefficientL1, ih]

def ExecutableQuarticCode.unitCopies
    (source : ExecutableQuarticCode) :
    List (ExecutableSignedUnit source.coordinateCount) :=
  expandExecutablePolynomialUnits source.terms

abbrev ExecutableQuarticCode.UnitSlot
    (source : ExecutableQuarticCode) :=
  Fin source.unitCopies.length

def ExecutableQuarticCode.unitAt
    (source : ExecutableQuarticCode) (slot : source.UnitSlot) :
    ExecutableSignedUnit source.coordinateCount :=
  source.unitCopies.get slot

theorem ExecutableQuarticCode.unitAt_exponent_lt_five
    (source : ExecutableQuarticCode) (slot : source.UnitSlot)
    (coordinate : Fin source.coordinateCount) :
    (source.unitAt slot).exponent coordinate < 5 := by
  have hUnit : source.unitAt slot ∈ source.unitCopies :=
    List.get_mem source.unitCopies slot
  rw [ExecutableQuarticCode.unitCopies,
    expandExecutablePolynomialUnits, List.mem_flatMap] at hUnit
  obtain ⟨term, hTerm, hUnit⟩ := hUnit
  rw [expandExecutableMonomialUnits, List.mem_replicate] at hUnit
  rw [hUnit.2]
  exact source.exponent_lt_five term hTerm coordinate

abbrev ExecutableQuarticCode.unitTagDimension
    (source : ExecutableQuarticCode) : ℕ :=
  source.unitCopies.length

def ExecutableQuarticCode.unitTagResidualExponent
    (source : ExecutableQuarticCode) (slot : source.UnitSlot)
    (coordinate : Fin source.unitTagDimension) : Fin 5 :=
  if coordinate = slot then
    if (source.unitAt slot).positive then ⟨0, by omega⟩
    else ⟨2, by omega⟩
  else ⟨1, by omega⟩

def ExecutableQuarticCode.unitTaggedResidualRow
    (source : ExecutableQuarticCode) (slot : source.UnitSlot) :
    Fin (source.coordinateCount + source.unitTagDimension) → Fin 5 :=
  fun coordinate =>
    match finSumFinEquiv.symm coordinate with
    | .inl oldCoordinate =>
        ⟨(source.unitAt slot).exponent oldCoordinate,
          source.unitAt_exponent_lt_five slot oldCoordinate⟩
    | .inr tagCoordinate =>
        source.unitTagResidualExponent slot tagCoordinate

theorem ExecutableQuarticCode.unitTaggedResidualRow_injective
    (source : ExecutableQuarticCode) :
    Function.Injective source.unitTaggedResidualRow := by
  intro first second hRows
  by_contra hDifferent
  have hCoordinate := congrFun hRows
    (finSumFinEquiv (Sum.inr first))
  simp only [ExecutableQuarticCode.unitTaggedResidualRow,
    Equiv.symm_apply_apply] at hCoordinate
  unfold ExecutableQuarticCode.unitTagResidualExponent at hCoordinate
  rw [if_pos rfl, if_neg hDifferent] at hCoordinate
  cases hSign : (source.unitAt first).positive <;>
    simp [hSign] at hCoordinate

def ExecutableQuarticCode.unitPositiveSlots
    (source : ExecutableQuarticCode) : Finset source.UnitSlot :=
  Finset.univ.filter fun slot => (source.unitAt slot).positive = true

def ExecutableQuarticCode.unitNegativeSlots
    (source : ExecutableQuarticCode) : Finset source.UnitSlot :=
  Finset.univ.filter fun slot => (source.unitAt slot).positive = false

def ExecutableQuarticCode.unitPositiveRows
    (source : ExecutableQuarticCode) :
    Finset (Fin (source.coordinateCount + source.unitTagDimension) → Fin 5) :=
  source.unitPositiveSlots.image source.unitTaggedResidualRow

def ExecutableQuarticCode.unitNegativeRows
    (source : ExecutableQuarticCode) :
    Finset (Fin (source.coordinateCount + source.unitTagDimension) → Fin 5) :=
  source.unitNegativeSlots.image source.unitTaggedResidualRow

theorem ExecutableQuarticCode.unitSlots_disjoint
    (source : ExecutableQuarticCode) :
    Disjoint source.unitPositiveSlots source.unitNegativeSlots := by
  rw [Finset.disjoint_left]
  intro slot hPositive hNegative
  have hp := (Finset.mem_filter.mp hPositive).2
  have hn := (Finset.mem_filter.mp hNegative).2
  exact Bool.noConfusion (hp.symm.trans hn)

theorem ExecutableQuarticCode.unitRows_disjoint
    (source : ExecutableQuarticCode) :
    Disjoint source.unitPositiveRows source.unitNegativeRows := by
  rw [Finset.disjoint_left]
  intro row hPositive hNegative
  rw [ExecutableQuarticCode.unitPositiveRows,
    Finset.mem_image] at hPositive
  rw [ExecutableQuarticCode.unitNegativeRows,
    Finset.mem_image] at hNegative
  obtain ⟨positiveSlot, hPositiveSlot, rfl⟩ := hPositive
  obtain ⟨negativeSlot, hNegativeSlot, hRows⟩ := hNegative
  have hSlots : positiveSlot = negativeSlot :=
    source.unitTaggedResidualRow_injective hRows.symm
  subst negativeSlot
  exact Finset.disjoint_left.mp source.unitSlots_disjoint
    hPositiveSlot hNegativeSlot

theorem ExecutableQuarticCode.unitSlot_partition
    (source : ExecutableQuarticCode) :
    source.unitPositiveSlots ∪ source.unitNegativeSlots = Finset.univ := by
  ext slot
  cases hSign : (source.unitAt slot).positive <;>
    simp [ExecutableQuarticCode.unitPositiveSlots,
      ExecutableQuarticCode.unitNegativeSlots, hSign]

theorem ExecutableQuarticCode.card_unitPositiveRows
    (source : ExecutableQuarticCode) :
    source.unitPositiveRows.card = source.unitPositiveSlots.card := by
  exact Finset.card_image_of_injective _
    source.unitTaggedResidualRow_injective

theorem ExecutableQuarticCode.card_unitNegativeRows
    (source : ExecutableQuarticCode) :
    source.unitNegativeRows.card = source.unitNegativeSlots.card := by
  exact Finset.card_image_of_injective _
    source.unitTaggedResidualRow_injective

theorem ExecutableQuarticCode.unitTarget_row_count
    (source : ExecutableQuarticCode) :
    source.unitPositiveRows.card + source.unitNegativeRows.card =
      source.coefficientL1 := by
  rw [source.card_unitPositiveRows, source.card_unitNegativeRows,
    ← Finset.card_union_of_disjoint source.unitSlots_disjoint,
    source.unitSlot_partition, Finset.card_univ]
  simp [ExecutableQuarticCode.UnitSlot,
    ExecutableQuarticCode.unitCopies,
    ExecutableQuarticCode.coefficientL1,
    expandExecutablePolynomialUnits_length]

def ExecutableQuarticCode.toExecutableOneHotOrderCode
    (source : ExecutableQuarticCode) : DuplicateFreeOneToFiveOrderCode where
  coordinateCount := source.coordinateCount + source.unitTagDimension
  positiveRows := source.unitPositiveRows
  negativeRows := source.unitNegativeRows
  rows_disjoint := source.unitRows_disjoint

theorem ExecutableQuarticCode.unitTagDimension_eq_coefficientL1
    (source : ExecutableQuarticCode) :
    source.unitTagDimension = source.coefficientL1 := by
  simp [ExecutableQuarticCode.unitTagDimension,
    ExecutableQuarticCode.unitCopies,
    ExecutableQuarticCode.coefficientL1,
    expandExecutablePolynomialUnits_length]

theorem ExecutableQuarticCode.executableOneHotOrderCode_size_eq
    (source : ExecutableQuarticCode) :
    duplicateFreeOneToFiveOrderCodeSize
        source.toExecutableOneHotOrderCode =
      (source.coordinateCount + source.coefficientL1 + 1) *
        (source.coefficientL1 + 1) := by
  change
    (source.coordinateCount + source.unitTagDimension + 1) *
        (source.unitPositiveRows.card + source.unitNegativeRows.card + 1) =
      (source.coordinateCount + source.coefficientL1 + 1) *
        (source.coefficientL1 + 1)
  rw [source.unitTarget_row_count]
  have hTags := source.unitTagDimension_eq_coefficientL1
  exact congrArg
    (fun tagDimension =>
      (source.coordinateCount + tagDimension + 1) *
        (source.coefficientL1 + 1)) hTags

theorem ExecutableQuarticCode.unitTarget_row_bounds
    (source : ExecutableQuarticCode) (slot : source.UnitSlot) :
    (∀ coordinate : Fin source.coordinateCount,
      1 ≤ (source.unitTaggedResidualRow slot
        (finSumFinEquiv (Sum.inl coordinate))).val + 1 ∧
      (source.unitTaggedResidualRow slot
        (finSumFinEquiv (Sum.inl coordinate))).val + 1 ≤ 5) ∧
    (∀ coordinate : Fin source.unitTagDimension,
      1 ≤ (source.unitTaggedResidualRow slot
        (finSumFinEquiv (Sum.inr coordinate))).val + 1 ∧
      (source.unitTaggedResidualRow slot
        (finSumFinEquiv (Sum.inr coordinate))).val + 1 ≤ 3) := by
  constructor
  · intro coordinate
    simp only [ExecutableQuarticCode.unitTaggedResidualRow,
      Equiv.symm_apply_apply]
    exact ⟨Nat.succ_pos _,
      source.unitAt_exponent_lt_five slot coordinate⟩
  · intro coordinate
    simp only [ExecutableQuarticCode.unitTaggedResidualRow,
      Equiv.symm_apply_apply]
    unfold ExecutableQuarticCode.unitTagResidualExponent
    by_cases hOwn : coordinate = slot
    · rw [if_pos hOwn]
      split <;> simp
    · rw [if_neg hOwn]
      simp

/-! ## Exact semantics of the executable one-hot compiler -/

def ExecutableQuarticCode.unitJoinActivity
    (source : ExecutableQuarticCode)
    (oldActivity : Fin source.coordinateCount → ℝ)
    (tagActivity : Fin source.unitTagDimension → ℝ) :
    Fin (source.coordinateCount + source.unitTagDimension) → ℝ :=
  fun coordinate =>
    match finSumFinEquiv.symm coordinate with
    | .inl oldCoordinate => oldActivity oldCoordinate
    | .inr tagCoordinate => tagActivity tagCoordinate

def ExecutableQuarticCode.unitOldActivityPart
    (source : ExecutableQuarticCode)
    (point : Fin (source.coordinateCount + source.unitTagDimension) → ℝ) :
    Fin source.coordinateCount → ℝ :=
  fun coordinate => point (finSumFinEquiv (Sum.inl coordinate))

def ExecutableQuarticCode.unitTagActivityPart
    (source : ExecutableQuarticCode)
    (point : Fin (source.coordinateCount + source.unitTagDimension) → ℝ) :
    Fin source.unitTagDimension → ℝ :=
  fun coordinate => point (finSumFinEquiv (Sum.inr coordinate))

theorem ExecutableQuarticCode.unitJoinActivity_parts
    (source : ExecutableQuarticCode)
    (point : Fin (source.coordinateCount + source.unitTagDimension) → ℝ) :
    source.unitJoinActivity (source.unitOldActivityPart point)
      (source.unitTagActivityPart point) = point := by
  funext coordinate
  obtain ⟨coordinate, rfl⟩ := finSumFinEquiv.surjective coordinate
  cases coordinate <;>
    simp [ExecutableQuarticCode.unitJoinActivity,
      ExecutableQuarticCode.unitOldActivityPart,
      ExecutableQuarticCode.unitTagActivityPart]

def ExecutableQuarticCode.unitSourceMonomial
    (source : ExecutableQuarticCode) (slot : source.UnitSlot)
    (oldActivity : Fin source.coordinateCount → ℝ) : ℝ :=
  (source.unitAt slot).monomial oldActivity

def ExecutableQuarticCode.unitSourceValue
    (source : ExecutableQuarticCode)
    (oldActivity : Fin source.coordinateCount → ℝ) : ℝ :=
  ∑ slot, (source.unitAt slot).value oldActivity

theorem ExecutableQuarticCode.unitSourceValue_eq_executablePolynomial
    (source : ExecutableQuarticCode)
    (oldActivity : Fin source.coordinateCount → ℝ) :
    source.unitSourceValue oldActivity =
      evaluateExecutablePolynomial source.terms oldActivity := by
  calc
    source.unitSourceValue oldActivity =
        evaluateExecutableUnitPolynomial source.unitCopies oldActivity := by
      unfold ExecutableQuarticCode.unitSourceValue
        evaluateExecutableUnitPolynomial ExecutableQuarticCode.unitAt
      rw [← List.sum_ofFn]
      exact congrArg List.sum
        (List.ofFn_comp'
          source.unitCopies.get
          (fun unit => unit.value oldActivity) |>.trans
            (congrArg
              (List.map (fun unit => unit.value oldActivity))
              (List.ofFn_get source.unitCopies)))
    _ = evaluateExecutablePolynomial source.terms oldActivity := by
      exact evaluate_expandExecutablePolynomialUnits source.terms oldActivity

def ExecutableQuarticCode.unitTagResidualMonomial
    (source : ExecutableQuarticCode) (slot : source.UnitSlot)
    (tagActivity : Fin source.unitTagDimension → ℝ) : ℝ :=
  ∏ coordinate,
    tagActivity coordinate ^
      (source.unitTagResidualExponent slot coordinate).val

def ExecutableQuarticCode.unitCommonTagMonomial
    (source : ExecutableQuarticCode)
    (tagActivity : Fin source.unitTagDimension → ℝ) : ℝ :=
  ∏ coordinate, tagActivity coordinate

theorem ExecutableQuarticCode.unitTagResidualMonomial_one
    (source : ExecutableQuarticCode) (slot : source.UnitSlot) :
    source.unitTagResidualMonomial slot (fun _ => 1) = 1 := by
  simp [ExecutableQuarticCode.unitTagResidualMonomial]

theorem ExecutableQuarticCode.unitTagResidualMonomial_ge_common_of_positive
    (source : ExecutableQuarticCode) (slot : source.UnitSlot)
    (hPositive : (source.unitAt slot).positive = true)
    (tagActivity : Fin source.unitTagDimension → ℝ)
    (hTag : ∀ coordinate, 0 < tagActivity coordinate ∧
      tagActivity coordinate ≤ 1) :
    source.unitCommonTagMonomial tagActivity ≤
      source.unitTagResidualMonomial slot tagActivity := by
  unfold ExecutableQuarticCode.unitCommonTagMonomial
    ExecutableQuarticCode.unitTagResidualMonomial
  apply Finset.prod_le_prod
  · intro coordinate _
    exact (hTag coordinate).1.le
  · intro coordinate _
    unfold ExecutableQuarticCode.unitTagResidualExponent
    by_cases hOwn : coordinate = slot
    · subst coordinate
      simpa [hPositive] using (hTag slot).2
    · simp [hOwn]

theorem ExecutableQuarticCode.unitTagResidualMonomial_le_common_of_negative
    (source : ExecutableQuarticCode) (slot : source.UnitSlot)
    (hNegative : (source.unitAt slot).positive = false)
    (tagActivity : Fin source.unitTagDimension → ℝ)
    (hTag : ∀ coordinate, 0 < tagActivity coordinate ∧
      tagActivity coordinate ≤ 1) :
    source.unitTagResidualMonomial slot tagActivity ≤
      source.unitCommonTagMonomial tagActivity := by
  unfold ExecutableQuarticCode.unitCommonTagMonomial
    ExecutableQuarticCode.unitTagResidualMonomial
  apply Finset.prod_le_prod
  · intro coordinate _
    exact pow_nonneg (hTag coordinate).1.le _
  · intro coordinate _
    unfold ExecutableQuarticCode.unitTagResidualExponent
    by_cases hOwn : coordinate = slot
    · subst coordinate
      simp only [if_pos rfl, hNegative, Bool.false_eq_true, ↓reduceIte,
        pow_two]
      exact mul_le_of_le_one_right (hTag slot).1.le
        (hTag slot).2
    · simp [hOwn]

def ExecutableQuarticCode.unitTaggedValue
    (source : ExecutableQuarticCode) (slot : source.UnitSlot)
    (oldActivity : Fin source.coordinateCount → ℝ)
    (tagActivity : Fin source.unitTagDimension → ℝ) : ℝ :=
  if (source.unitAt slot).positive then
    source.unitSourceMonomial slot oldActivity *
      source.unitTagResidualMonomial slot tagActivity
  else
    -(source.unitSourceMonomial slot oldActivity *
      source.unitTagResidualMonomial slot tagActivity)

def ExecutableQuarticCode.unitTagLiftValue
    (source : ExecutableQuarticCode)
    (oldActivity : Fin source.coordinateCount → ℝ)
    (tagActivity : Fin source.unitTagDimension → ℝ) : ℝ :=
  ∑ slot, source.unitTaggedValue slot oldActivity tagActivity

theorem ExecutableQuarticCode.unitTagLiftValue_allOne
    (source : ExecutableQuarticCode)
    (oldActivity : Fin source.coordinateCount → ℝ) :
    source.unitTagLiftValue oldActivity (fun _ => 1) =
      source.unitSourceValue oldActivity := by
  unfold ExecutableQuarticCode.unitTagLiftValue
    ExecutableQuarticCode.unitSourceValue
    ExecutableQuarticCode.unitTaggedValue
    ExecutableSignedUnit.value
  apply Finset.sum_congr rfl
  intro slot _
  rw [source.unitTagResidualMonomial_one]
  unfold ExecutableQuarticCode.unitSourceMonomial
  simp

theorem ExecutableQuarticCode.unitCommon_mul_sourceValue_le_tagLift
    (source : ExecutableQuarticCode)
    (oldActivity : Fin source.coordinateCount → ℝ)
    (hOld : ∀ coordinate, 0 ≤ oldActivity coordinate)
    (tagActivity : Fin source.unitTagDimension → ℝ)
    (hTag : ∀ coordinate, 0 < tagActivity coordinate ∧
      tagActivity coordinate ≤ 1) :
    source.unitCommonTagMonomial tagActivity *
        source.unitSourceValue oldActivity ≤
      source.unitTagLiftValue oldActivity tagActivity := by
  unfold ExecutableQuarticCode.unitSourceValue
    ExecutableQuarticCode.unitTagLiftValue
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro slot _
  have hMonomial : 0 ≤ source.unitSourceMonomial slot oldActivity := by
    unfold ExecutableQuarticCode.unitSourceMonomial
      ExecutableSignedUnit.monomial
    exact Finset.prod_nonneg fun coordinate _ =>
      pow_nonneg (hOld coordinate) _
  cases hSign : (source.unitAt slot).positive
  · unfold ExecutableSignedUnit.value
      ExecutableQuarticCode.unitTaggedValue
    rw [hSign]
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hTagLe :=
      source.unitTagResidualMonomial_le_common_of_negative
        slot hSign tagActivity hTag
    have hScaled := mul_le_mul_of_nonneg_left hTagLe hMonomial
    simpa [ExecutableQuarticCode.unitSourceMonomial, mul_comm] using
      neg_le_neg hScaled
  · unfold ExecutableSignedUnit.value
      ExecutableQuarticCode.unitTaggedValue
    rw [hSign]
    simp only [↓reduceIte]
    have hTagGe :=
      source.unitTagResidualMonomial_ge_common_of_positive
        slot hSign tagActivity hTag
    simpa [ExecutableQuarticCode.unitSourceMonomial, mul_comm] using
      (mul_le_mul_of_nonneg_left hTagGe hMonomial)

theorem ExecutableQuarticCode.unitTaggedResidualMonomial_factorization
    (source : ExecutableQuarticCode) (slot : source.UnitSlot)
    (oldActivity : Fin source.coordinateCount → ℝ)
    (tagActivity : Fin source.unitTagDimension → ℝ) :
    boundedQuarticResidualMonomial (source.unitTaggedResidualRow slot)
        (source.unitJoinActivity oldActivity tagActivity) =
      source.unitSourceMonomial slot oldActivity *
        source.unitTagResidualMonomial slot tagActivity := by
  unfold boundedQuarticResidualMonomial
    ExecutableQuarticCode.unitSourceMonomial
    ExecutableSignedUnit.monomial
    ExecutableQuarticCode.unitTagResidualMonomial
  rw [Fin.prod_univ_add]
  congr 1
  · apply Finset.prod_congr rfl
    intro coordinate _
    simp [ExecutableQuarticCode.unitTaggedResidualRow,
      ExecutableQuarticCode.unitJoinActivity]
  · apply Finset.prod_congr rfl
    intro coordinate _
    simp [ExecutableQuarticCode.unitTaggedResidualRow,
      ExecutableQuarticCode.unitJoinActivity]

theorem ExecutableQuarticCode.signedDistinctMargin_unitJoinActivity
    (source : ExecutableQuarticCode)
    (oldActivity : Fin source.coordinateCount → ℝ)
    (tagActivity : Fin source.unitTagDimension → ℝ) :
    signedDistinctQuarticMargin source.unitPositiveRows source.unitNegativeRows
        (source.unitJoinActivity oldActivity tagActivity) =
      source.unitTagLiftValue oldActivity tagActivity := by
  classical
  unfold signedDistinctQuarticMargin
    ExecutableQuarticCode.unitPositiveRows
    ExecutableQuarticCode.unitNegativeRows
  rw [Finset.sum_image, Finset.sum_image]
  · simp_rw [source.unitTaggedResidualMonomial_factorization]
    simpa [ExecutableQuarticCode.unitPositiveSlots,
      ExecutableQuarticCode.unitNegativeSlots,
      ExecutableQuarticCode.unitTagLiftValue,
      ExecutableQuarticCode.unitTaggedValue] using
      (sum_bool_true_sub_false
        (items := (Finset.univ : Finset source.UnitSlot))
        (predicate := fun slot => (source.unitAt slot).positive)
        (value := fun slot => source.unitSourceMonomial slot oldActivity *
          source.unitTagResidualMonomial slot tagActivity))
  · intro first _ second _ hRows
    exact source.unitTaggedResidualRow_injective hRows
  · intro first _ second _ hRows
    exact source.unitTaggedResidualRow_injective hRows

theorem ExecutableQuarticCode.oneToFiveMargin_unitJoinActivity
    (source : ExecutableQuarticCode)
    (oldActivity : Fin source.coordinateCount → ℝ)
    (tagActivity : Fin source.unitTagDimension → ℝ) :
    duplicateFreeOneToFiveOrderMargin source.unitPositiveRows
        source.unitNegativeRows
        (source.unitJoinActivity oldActivity tagActivity) =
      commonAllOneMonomial
          (source.unitJoinActivity oldActivity tagActivity) *
        source.unitTagLiftValue oldActivity tagActivity := by
  rw [duplicateFreeOneToFiveOrderMargin_factorization,
    source.signedDistinctMargin_unitJoinActivity]

theorem ExecutableQuarticCode.unitOldActivityPart_positiveUnitCube
    (source : ExecutableQuarticCode)
    {point : Fin (source.coordinateCount + source.unitTagDimension) → ℝ}
    (hPoint : IsPositiveUnitCubePoint point) :
    IsPositiveUnitCubePoint (source.unitOldActivityPart point) := by
  intro coordinate
  exact hPoint (finSumFinEquiv (Sum.inl coordinate))

theorem ExecutableQuarticCode.unitTagActivityPart_positiveUnitCube
    (source : ExecutableQuarticCode)
    {point : Fin (source.coordinateCount + source.unitTagDimension) → ℝ}
    (hPoint : IsPositiveUnitCubePoint point) :
    IsPositiveUnitCubePoint (source.unitTagActivityPart point) := by
  intro coordinate
  exact hPoint (finSumFinEquiv (Sum.inr coordinate))

theorem ExecutableQuarticCode.unitJoinActivity_positiveUnitCube
    (source : ExecutableQuarticCode)
    {oldActivity : Fin source.coordinateCount → ℝ}
    {tagActivity : Fin source.unitTagDimension → ℝ}
    (hOld : IsPositiveUnitCubePoint oldActivity)
    (hTag : IsPositiveUnitCubePoint tagActivity) :
    IsPositiveUnitCubePoint
      (source.unitJoinActivity oldActivity tagActivity) := by
  intro coordinate
  obtain ⟨coordinate, rfl⟩ := finSumFinEquiv.surjective coordinate
  cases coordinate with
  | inl oldCoordinate =>
      simpa [ExecutableQuarticCode.unitJoinActivity] using
        hOld oldCoordinate
  | inr tagCoordinate =>
      simpa [ExecutableQuarticCode.unitJoinActivity] using
        hTag tagCoordinate

def ExecutableQuarticCode.universallyNonnegative
    (source : ExecutableQuarticCode) : Prop :=
  ∀ oldActivity : Fin source.coordinateCount → ℝ,
    IsPositiveUnitCubePoint oldActivity →
      0 ≤ evaluateExecutablePolynomial source.terms oldActivity

theorem ExecutableQuarticCode.executableOneHot_universalOrder_iff
    (source : ExecutableQuarticCode) :
    source.toExecutableOneHotOrderCode.universalOrder ↔
      source.universallyNonnegative := by
  change
    (∀ point : Fin (source.coordinateCount + source.unitTagDimension) → ℝ,
      IsPositiveUnitCubePoint point →
        0 ≤ duplicateFreeOneToFiveOrderMargin source.unitPositiveRows
          source.unitNegativeRows point) ↔
      source.universallyNonnegative
  constructor
  · intro hTarget oldActivity hOld
    have hTag : IsPositiveUnitCubePoint
        (fun _ : Fin source.unitTagDimension => (1 : ℝ)) := by
      intro coordinate
      exact ⟨by norm_num, by norm_num⟩
    have hMargin := hTarget
      (source.unitJoinActivity oldActivity (fun _ => 1))
      (source.unitJoinActivity_positiveUnitCube hOld hTag)
    rw [source.oneToFiveMargin_unitJoinActivity,
      source.unitTagLiftValue_allOne,
      source.unitSourceValue_eq_executablePolynomial] at hMargin
    exact nonneg_of_mul_nonneg_right hMargin
      (commonAllOneMonomial_pos
        (source.unitJoinActivity_positiveUnitCube hOld hTag))
  · intro hSource point hPoint
    let oldActivity := source.unitOldActivityPart point
    let tagActivity := source.unitTagActivityPart point
    have hOld : IsPositiveUnitCubePoint oldActivity :=
      source.unitOldActivityPart_positiveUnitCube hPoint
    have hTag : IsPositiveUnitCubePoint tagActivity :=
      source.unitTagActivityPart_positiveUnitCube hPoint
    have hSourceValue : 0 ≤ source.unitSourceValue oldActivity := by
      rw [source.unitSourceValue_eq_executablePolynomial]
      exact hSource oldActivity hOld
    have hCommonTag : 0 ≤ source.unitCommonTagMonomial tagActivity := by
      unfold ExecutableQuarticCode.unitCommonTagMonomial
      exact Finset.prod_nonneg fun coordinate _ => (hTag coordinate).1.le
    have hLift : 0 ≤ source.unitTagLiftValue oldActivity tagActivity :=
      le_trans (mul_nonneg hCommonTag hSourceValue)
        (source.unitCommon_mul_sourceValue_le_tagLift oldActivity
          (fun coordinate => (hOld coordinate).1.le) tagActivity hTag)
    rw [← source.unitJoinActivity_parts point]
    rw [source.oneToFiveMargin_unitJoinActivity]
    exact mul_nonneg
      (commonAllOneMonomial_pos
        (source.unitJoinActivity_positiveUnitCube hOld hTag)).le hLift

def compileExplicitBoundedETRINVOneHot
    (problem : BoundedETRINVInstance) : DuplicateFreeOneToFiveOrderCode :=
  (executableStrictifierQuarticCode problem
    (explicitChainLength problem)).toExecutableOneHotOrderCode

theorem compileExplicitBoundedETRINVOneHot_correct
    (foundation : ExplicitCompactMinimumFoundation)
    (problem : BoundedETRINVInstance) :
    (compileExplicitBoundedETRINVOneHot problem).universalOrder ↔
      ¬ problem.Satisfiable := by
  rw [compileExplicitBoundedETRINVOneHot,
    ExecutableQuarticCode.executableOneHot_universalOrder_iff]
  let m := explicitChainLength problem
  have hLength : explicitGapExponent problem + 3 < 2 ^ (m + 1) := by
    have hCanonical :=
      (explicitCompactGapFoundation foundation).chainLength_condition problem
    change
      explicitGapExponent problem + 3 <
        2 ^ ((explicitCompactGapFoundation foundation).chainLength problem + 1)
      at hCanonical
    rw [explicitCompactGapFoundation_chainLength] at hCanonical
    exact hCanonical
  have hStrictifier :=
    boundedETRINV_satisfiable_iff_strictifier_negative_positiveCube
      problem m (dyadicCompactGap (explicitGapExponent problem))
      (foundation.lowerBound problem)
      (exactContractionChain_terminal_lt_dyadicGap
        m (explicitGapExponent problem) hLength)
  change
    (∀ point : Fin (problem.variableCount + m) → ℝ,
      IsPositiveUnitCubePoint point →
        0 ≤ evaluateExecutablePolynomial
          (executableStrictifierPolynomial problem m) point) ↔
      ¬ problem.Satisfiable
  constructor
  · intro hNonnegative hSatisfiable
    obtain ⟨point, hPoint, hNegative⟩ :=
      hStrictifier.mp hSatisfiable
    have hExecutable := hNonnegative point hPoint
    rw [evaluate_executableStrictifierPolynomial,
      ← eval_etrStrictifierPolynomialFin] at hExecutable
    exact (not_lt_of_ge hExecutable) hNegative
  · intro hUnsatisfiable point hPoint
    apply le_of_not_gt
    intro hNegative
    apply hUnsatisfiable
    apply hStrictifier.mpr
    refine ⟨point, hPoint, ?_⟩
    rw [eval_etrStrictifierPolynomialFin,
      ← evaluate_executableStrictifierPolynomial]
    exact hNegative

theorem compileExplicitBoundedETRINVOneHot_row_count_le
    (problem : BoundedETRINVInstance) :
    (compileExplicitBoundedETRINVOneHot problem).positiveRows.card +
        (compileExplicitBoundedETRINVOneHot problem).negativeRows.card ≤
      800 * problem.equationCount +
        9 * explicitChainLength problem ^ 2 + 2 := by
  rw [compileExplicitBoundedETRINVOneHot]
  change
    (executableStrictifierQuarticCode problem
      (explicitChainLength problem)).unitPositiveRows.card +
        (executableStrictifierQuarticCode problem
          (explicitChainLength problem)).unitNegativeRows.card ≤ _
  rw [ExecutableQuarticCode.unitTarget_row_count]
  exact executableStrictifierPolynomial_coefficientL1_le problem
    (explicitChainLength problem)

theorem compileExplicitBoundedETRINVOneHot_size_polynomial
    (problem : BoundedETRINVInstance) :
    duplicateFreeOneToFiveOrderCodeSize
        (compileExplicitBoundedETRINVOneHot problem) ≤
      3000000000000 * boundedETRINVCodeSize problem ^ 4 := by
  let sourceSize := boundedETRINVCodeSize problem
  let chainLength := explicitChainLength problem
  let coefficientMass := executableCoefficientL1
    (executableStrictifierPolynomial problem chainLength)
  have hSourceSize : 1 ≤ sourceSize := by
    dsimp [sourceSize, boundedETRINVCodeSize]
    omega
  have hVariables : problem.variableCount ≤ sourceSize := by
    dsimp [sourceSize, boundedETRINVCodeSize]
    omega
  have hEquations : problem.equationCount ≤ sourceSize := by
    dsimp [sourceSize, boundedETRINVCodeSize]
    omega
  have hChain : chainLength ≤ 412 * sourceSize := by
    simpa [chainLength, sourceSize] using
      explicitChainLength_sourceSize_bound problem
  have hMassRaw : coefficientMass ≤
      800 * problem.equationCount + 9 * chainLength ^ 2 + 2 := by
    simpa [coefficientMass, chainLength] using
      executableStrictifierPolynomial_coefficientL1_le problem chainLength
  have hMass : coefficientMass ≤ 1528500 * sourceSize ^ 2 := by
    nlinarith [sq_nonneg (chainLength : ℤ), sq_nonneg (sourceSize : ℤ)]
  have hSourceSquared : sourceSize ≤ sourceSize ^ 2 := by
    calc
      sourceSize = sourceSize * 1 := by omega
      _ ≤ sourceSize * sourceSize := Nat.mul_le_mul_left sourceSize hSourceSize
      _ = sourceSize ^ 2 := by ring
  have hOneSquared : 1 ≤ sourceSize ^ 2 :=
    hSourceSize.trans hSourceSquared
  have hFirstFactor :
      problem.variableCount + chainLength + coefficientMass + 1 ≤
        1600000 * sourceSize ^ 2 := by
    omega
  have hSecondFactor : coefficientMass + 1 ≤
      1600000 * sourceSize ^ 2 := by
    omega
  rw [compileExplicitBoundedETRINVOneHot]
  rw [ExecutableQuarticCode.executableOneHotOrderCode_size_eq]
  change
    (problem.variableCount + chainLength + coefficientMass + 1) *
        (coefficientMass + 1) ≤ 3000000000000 * sourceSize ^ 4
  calc
    (problem.variableCount + chainLength + coefficientMass + 1) *
          (coefficientMass + 1) ≤
        (1600000 * sourceSize ^ 2) *
          (1600000 * sourceSize ^ 2) :=
      Nat.mul_le_mul hFirstFactor hSecondFactor
    _ = 2560000000000 * sourceSize ^ 4 := by ring
    _ ≤ 3000000000000 * sourceSize ^ 4 := by
      exact Nat.mul_le_mul_right (sourceSize ^ 4) (by norm_num)

end PhonologicalCalculus.MaxEnt
