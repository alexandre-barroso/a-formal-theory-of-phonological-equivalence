import PhonologicalCalculus.MaxEnt.NormalizerRelation
import PhonologicalCalculus.MaxEnt.ETRResidualComplete
import PhonologicalCalculus.MaxEnt.ContractionStrictifierComplete
import PhonologicalCalculus.MaxEnt.ETRStrictifierPolynomialComplete
import Mathlib.Data.Nat.Size
import Mathlib.Tactic

/-!
# Duplicate-free sign-oriented finite-MaxEnt compilation

This module retains the earlier sign-oriented binary-tag construction as
supporting semantic-size material.  It is not the registered closure of
`MAX-G3.REDUCTION.03`, which uses the deterministic one-hot compiler in
`ExecutableOneHotTagCompiler`, and it supplies no registered universal-real
branch of `MAX-G4.COMPLEXITY.04`.  A collected bounded-quartic integer
polynomial is represented by distinct residual exponent rows, a sign, and a
positive multiplicity.  The compiler replaces every coefficient unit by one
binary-tagged row.  It proves row injectivity, unit signed coefficients, exact
all-one-tag recovery, pointwise sign dominance, equivalence of universal
nonnegativity, and explicit finite output bounds.

The preceding bounded-ETR-INV strictifier production and conventional
complexity interpretation are isolated in typed theorem parameters.  They are
not added to Lean's trusted base.  Every binary-tag, row, sign, and finite-size
requirement is proved locally.
-/

namespace PhonologicalCalculus.MaxEnt

open Finset Set
open scoped BigOperators

noncomputable section

theorem sum_bool_true_sub_false {α : Type*} [DecidableEq α]
    (items : Finset α) (predicate : α → Bool) (value : α → ℝ) :
    (∑ item ∈ items.filter (fun item => predicate item = true), value item) -
        (∑ item ∈ items.filter (fun item => predicate item = false), value item) =
      ∑ item ∈ items,
        if predicate item = true then value item else -value item := by
  have hDisjoint : Disjoint
      (items.filter (fun item => predicate item = true))
      (items.filter (fun item => predicate item = false)) := by
    rw [Finset.disjoint_left]
    intro item hTrue hFalse
    simp only [Finset.mem_filter] at hTrue hFalse
    exact Bool.noConfusion (hTrue.2.symm.trans hFalse.2)
  have hUnion :
      items.filter (fun item => predicate item = true) ∪
          items.filter (fun item => predicate item = false) = items := by
    ext item
    cases hPredicate : predicate item <;> simp [hPredicate]
  rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
  calc
    (∑ item ∈ items.filter (fun item => predicate item = true), value item) +
          ∑ item ∈ items.filter (fun item => predicate item = false),
            -value item =
        (∑ item ∈ items.filter (fun item => predicate item = true),
          if predicate item = true then value item else -value item) +
        ∑ item ∈ items.filter (fun item => predicate item = false),
          if predicate item = true then value item else -value item := by
      congr 1
      · apply Finset.sum_congr rfl
        intro item hItem
        simp only [Finset.mem_filter] at hItem
        simp [hItem.2]
      · apply Finset.sum_congr rfl
        intro item hItem
        simp only [Finset.mem_filter] at hItem
        simp [hItem.2]
    _ = ∑ item ∈
          (items.filter (fun item => predicate item = true) ∪
            items.filter (fun item => predicate item = false)),
          if predicate item = true then value item else -value item :=
      (Finset.sum_union hDisjoint).symm
    _ = _ := by rw [hUnion]

/-! ## Collected signed quartic source -/

/-- Canonically collected bounded-quartic integer data.  `positive term`
selects the sign and `multiplicity term` is the nonzero coefficient magnitude.
Distinct terms have distinct residual exponent rows. -/
structure CollectedSignedQuarticCode where
  coordinateCount : ℕ
  termCount : ℕ
  exponent : Fin termCount → Fin coordinateCount → Fin 5
  positive : Fin termCount → Bool
  multiplicity : Fin termCount → ℕ
  multiplicity_pos : ∀ term, 0 < multiplicity term
  exponent_injective : Function.Injective exponent

/-- The signed integer coefficient represented by one collected term. -/
def CollectedSignedQuarticCode.coefficient
    (source : CollectedSignedQuarticCode) (term : Fin source.termCount) : ℤ :=
  if source.positive term then source.multiplicity term
  else -(source.multiplicity term : ℤ)

theorem CollectedSignedQuarticCode.coefficient_ne_zero
    (source : CollectedSignedQuarticCode) (term : Fin source.termCount) :
    source.coefficient term ≠ 0 := by
  unfold CollectedSignedQuarticCode.coefficient
  split
  · exact_mod_cast (ne_of_gt (source.multiplicity_pos term))
  · exact neg_ne_zero.mpr (by
      exact_mod_cast (ne_of_gt (source.multiplicity_pos term)))

theorem CollectedSignedQuarticCode.coefficient_natAbs
    (source : CollectedSignedQuarticCode) (term : Fin source.termCount) :
    Int.natAbs (source.coefficient term) = source.multiplicity term := by
  unfold CollectedSignedQuarticCode.coefficient
  split <;> simp

/-- Exact collected coefficient mass. -/
def CollectedSignedQuarticCode.coefficientL1
    (source : CollectedSignedQuarticCode) : ℕ :=
  ∑ term, source.multiplicity term

/-- One explicit unit copy of one collected coefficient. -/
abbrev CollectedSignedQuarticCode.Copy
    (source : CollectedSignedQuarticCode) :=
  Σ term : Fin source.termCount, Fin (source.multiplicity term)

theorem CollectedSignedQuarticCode.card_copy
    (source : CollectedSignedQuarticCode) :
    Fintype.card source.Copy = source.coefficientL1 := by
  simp [CollectedSignedQuarticCode.coefficientL1, Fintype.card_sigma]

/-! ## Finite binary codebook -/

/-- Number of fresh binary-tag coordinates.  The bit length of the explicit
copy population is at most that population, hence polynomial whenever the
coefficient mass is polynomial. -/
def CollectedSignedQuarticCode.tagDimension
    (source : CollectedSignedQuarticCode) : ℕ :=
  Nat.size (Fintype.card source.Copy)

/-- Canonical enumeration index of a coefficient copy. -/
def CollectedSignedQuarticCode.copyIndex
    (source : CollectedSignedQuarticCode) (copy : source.Copy) :
    Fin (Fintype.card source.Copy) :=
  Fintype.equivFin source.Copy copy

/-- Binary tag attached to a coefficient copy. -/
def CollectedSignedQuarticCode.tagBit
    (source : CollectedSignedQuarticCode) (copy : source.Copy)
    (coordinate : Fin source.tagDimension) : Bool :=
  Nat.testBit (source.copyIndex copy).val coordinate.val

theorem CollectedSignedQuarticCode.tagBit_injective
    (source : CollectedSignedQuarticCode) :
    Function.Injective source.tagBit := by
  intro first second hCode
  have hIndex : source.copyIndex first = source.copyIndex second := by
    apply Fin.ext
    apply Nat.eq_of_testBit_eq
    intro coordinate
    by_cases hCoordinate : coordinate < source.tagDimension
    · exact congrFun hCode ⟨coordinate, hCoordinate⟩
    · have hDimensionLe : source.tagDimension ≤ coordinate :=
        Nat.le_of_not_gt hCoordinate
      have hCardBound : Fintype.card source.Copy <
          2 ^ source.tagDimension := Nat.lt_size_self _
      have hPowerBound : 2 ^ source.tagDimension ≤ 2 ^ coordinate :=
        Nat.pow_le_pow_right (by norm_num) hDimensionLe
      have hFirst : (source.copyIndex first).val < 2 ^ coordinate :=
        lt_of_lt_of_le (lt_of_lt_of_le (source.copyIndex first).isLt
          hCardBound.le) hPowerBound
      have hSecond : (source.copyIndex second).val < 2 ^ coordinate :=
        lt_of_lt_of_le (lt_of_lt_of_le (source.copyIndex second).isLt
          hCardBound.le) hPowerBound
      rw [Nat.testBit_eq_false_of_lt hFirst,
        Nat.testBit_eq_false_of_lt hSecond]
  exact (Fintype.equivFin source.Copy).injective hIndex

theorem CollectedSignedQuarticCode.tagDimension_le_coefficientL1
    (source : CollectedSignedQuarticCode) :
    source.tagDimension ≤ source.coefficientL1 := by
  rw [CollectedSignedQuarticCode.tagDimension, source.card_copy]
  apply Nat.size_le.mpr
  exact Nat.lt_two_pow_self

/-! ## Tagged residual rows -/

/-- Residual tag exponent.  Actual MaxEnt violations add one: positive copies
use tag entries one or two, and negative copies use two or three. -/
def CollectedSignedQuarticCode.tagResidualExponent
    (source : CollectedSignedQuarticCode) (copy : source.Copy)
    (coordinate : Fin source.tagDimension) : Fin 5 :=
  if source.positive copy.1 then
    if source.tagBit copy coordinate then ⟨0, by omega⟩ else ⟨1, by omega⟩
  else
    if source.tagBit copy coordinate then ⟨2, by omega⟩ else ⟨1, by omega⟩

/-- Complete residual row after adjoining the binary tag block. -/
def CollectedSignedQuarticCode.taggedResidualRow
    (source : CollectedSignedQuarticCode) (copy : source.Copy) :
    Fin (source.coordinateCount + source.tagDimension) → Fin 5 :=
  fun coordinate =>
    match finSumFinEquiv.symm coordinate with
    | .inl oldCoordinate => source.exponent copy.1 oldCoordinate
    | .inr tagCoordinate => source.tagResidualExponent copy tagCoordinate

theorem CollectedSignedQuarticCode.tagResidualExponent_injective_of_sameTerm
    (source : CollectedSignedQuarticCode)
    {first second : source.Copy} (hTerm : first.1 = second.1)
    (hRow : source.taggedResidualRow first =
      source.taggedResidualRow second) :
    source.tagBit first = source.tagBit second := by
  funext coordinate
  have hCoordinate := congrFun hRow
    (finSumFinEquiv (Sum.inr coordinate))
  simp only [CollectedSignedQuarticCode.taggedResidualRow,
    Equiv.symm_apply_apply] at hCoordinate
  unfold CollectedSignedQuarticCode.tagResidualExponent at hCoordinate
  rw [hTerm] at hCoordinate
  cases hSign : source.positive second.1 <;>
    cases hFirst : source.tagBit first coordinate <;>
    cases hSecond : source.tagBit second coordinate <;>
    simp_all

theorem CollectedSignedQuarticCode.taggedResidualRow_injective
    (source : CollectedSignedQuarticCode) :
    Function.Injective source.taggedResidualRow := by
  intro first second hRow
  have hOld : source.exponent first.1 = source.exponent second.1 := by
    funext coordinate
    have hCoordinate := congrFun hRow
      (finSumFinEquiv (Sum.inl coordinate))
    simpa [CollectedSignedQuarticCode.taggedResidualRow] using hCoordinate
  have hTerm : first.1 = second.1 := source.exponent_injective hOld
  exact source.tagBit_injective
    (source.tagResidualExponent_injective_of_sameTerm hTerm hRow)

/-- Positive coefficient copies. -/
def CollectedSignedQuarticCode.positiveCopies
    (source : CollectedSignedQuarticCode) : Finset source.Copy :=
  Finset.univ.filter fun copy => source.positive copy.1 = true

/-- Negative coefficient copies. -/
def CollectedSignedQuarticCode.negativeCopies
    (source : CollectedSignedQuarticCode) : Finset source.Copy :=
  Finset.univ.filter fun copy => source.positive copy.1 = false

/-- Globally distinct target rows carrying coefficient `+1`. -/
def CollectedSignedQuarticCode.positiveRows
    (source : CollectedSignedQuarticCode) :
    Finset (Fin (source.coordinateCount + source.tagDimension) → Fin 5) :=
  source.positiveCopies.image source.taggedResidualRow

/-- Globally distinct target rows carrying coefficient `-1`. -/
def CollectedSignedQuarticCode.negativeRows
    (source : CollectedSignedQuarticCode) :
    Finset (Fin (source.coordinateCount + source.tagDimension) → Fin 5) :=
  source.negativeCopies.image source.taggedResidualRow

theorem CollectedSignedQuarticCode.rows_disjoint
    (source : CollectedSignedQuarticCode) :
    Disjoint source.positiveRows source.negativeRows := by
  rw [Finset.disjoint_left]
  intro row hPositive hNegative
  rw [CollectedSignedQuarticCode.positiveRows, Finset.mem_image] at hPositive
  rw [CollectedSignedQuarticCode.negativeRows, Finset.mem_image] at hNegative
  obtain ⟨positiveCopy, hPositiveCopy, rfl⟩ := hPositive
  obtain ⟨negativeCopy, hNegativeCopy, hRows⟩ := hNegative
  have hCopies : positiveCopy = negativeCopy :=
    source.taggedResidualRow_injective hRows.symm
  subst negativeCopy
  simp [CollectedSignedQuarticCode.positiveCopies,
    CollectedSignedQuarticCode.negativeCopies] at hPositiveCopy hNegativeCopy
  exact Bool.noConfusion (hPositiveCopy.symm.trans hNegativeCopy)

/-- The compiled duplicate-free unit-coefficient target. -/
def CollectedSignedQuarticCode.toOneToFiveOrderCode
    (source : CollectedSignedQuarticCode) :
    DuplicateFreeOneToFiveOrderCode where
  coordinateCount := source.coordinateCount + source.tagDimension
  positiveRows := source.positiveRows
  negativeRows := source.negativeRows
  rows_disjoint := source.rows_disjoint

/-! ## Exact unit-coefficient and object-size proofs -/

theorem CollectedSignedQuarticCode.card_positiveRows
    (source : CollectedSignedQuarticCode) :
    source.positiveRows.card = source.positiveCopies.card := by
  unfold CollectedSignedQuarticCode.positiveRows
  exact Finset.card_image_of_injective _ source.taggedResidualRow_injective

theorem CollectedSignedQuarticCode.card_negativeRows
    (source : CollectedSignedQuarticCode) :
    source.negativeRows.card = source.negativeCopies.card := by
  unfold CollectedSignedQuarticCode.negativeRows
  exact Finset.card_image_of_injective _ source.taggedResidualRow_injective

theorem CollectedSignedQuarticCode.copy_partition
    (source : CollectedSignedQuarticCode) :
    source.positiveCopies ∪ source.negativeCopies = Finset.univ := by
  ext copy
  cases hSign : source.positive copy.1 <;>
    simp [CollectedSignedQuarticCode.positiveCopies,
      CollectedSignedQuarticCode.negativeCopies, hSign]

theorem CollectedSignedQuarticCode.copy_partition_disjoint
    (source : CollectedSignedQuarticCode) :
    Disjoint source.positiveCopies source.negativeCopies := by
  rw [Finset.disjoint_left]
  intro copy hPositive hNegative
  simp [CollectedSignedQuarticCode.positiveCopies,
    CollectedSignedQuarticCode.negativeCopies] at hPositive hNegative
  exact Bool.noConfusion (hPositive.symm.trans hNegative)

/-- The target has exactly one alternative row per source coefficient unit. -/
theorem CollectedSignedQuarticCode.target_row_count
    (source : CollectedSignedQuarticCode) :
    source.positiveRows.card + source.negativeRows.card =
      source.coefficientL1 := by
  rw [source.card_positiveRows, source.card_negativeRows,
    ← Finset.card_union_of_disjoint source.copy_partition_disjoint,
    source.copy_partition, Finset.card_univ, source.card_copy]

/-- Signed coefficient of a compiled residual row. -/
def CollectedSignedQuarticCode.targetCoefficient
    (source : CollectedSignedQuarticCode)
    (row : Fin (source.coordinateCount + source.tagDimension) → Fin 5) : ℤ :=
  if row ∈ source.positiveRows then 1
  else if row ∈ source.negativeRows then -1 else 0

theorem CollectedSignedQuarticCode.targetCoefficient_copy
    (source : CollectedSignedQuarticCode) (copy : source.Copy) :
    source.targetCoefficient (source.taggedResidualRow copy) =
      if source.positive copy.1 then 1 else -1 := by
  cases hSign : source.positive copy.1
  · have hNegative : source.taggedResidualRow copy ∈ source.negativeRows := by
      unfold CollectedSignedQuarticCode.negativeRows
      rw [Finset.mem_image]
      exact ⟨copy, by simp [CollectedSignedQuarticCode.negativeCopies, hSign], rfl⟩
    have hNotPositive : source.taggedResidualRow copy ∉ source.positiveRows := by
      intro hPositive
      exact Finset.disjoint_left.mp source.rows_disjoint hPositive hNegative
    simp [CollectedSignedQuarticCode.targetCoefficient,
      hNegative, hNotPositive]
  · have hPositive : source.taggedResidualRow copy ∈ source.positiveRows := by
      unfold CollectedSignedQuarticCode.positiveRows
      rw [Finset.mem_image]
      exact ⟨copy, by simp [CollectedSignedQuarticCode.positiveCopies, hSign], rfl⟩
    simp [CollectedSignedQuarticCode.targetCoefficient, hPositive]

/-- Every nonzero compiled coefficient is exactly `+1` or `-1`. -/
theorem CollectedSignedQuarticCode.targetCoefficient_unit
    (source : CollectedSignedQuarticCode)
    (row : Fin (source.coordinateCount + source.tagDimension) → Fin 5) :
    source.targetCoefficient row = 0 ∨
      source.targetCoefficient row = 1 ∨
      source.targetCoefficient row = -1 := by
  by_cases hPositive : row ∈ source.positiveRows
  · exact Or.inr (Or.inl (by
      simp [CollectedSignedQuarticCode.targetCoefficient, hPositive]))
  · by_cases hNegative : row ∈ source.negativeRows
    · exact Or.inr (Or.inr (by
        simp [CollectedSignedQuarticCode.targetCoefficient,
          hPositive, hNegative]))
    · exact Or.inl (by
        simp [CollectedSignedQuarticCode.targetCoefficient,
          hPositive, hNegative])

theorem CollectedSignedQuarticCode.tagResidualExponent_le_two
    (source : CollectedSignedQuarticCode) (copy : source.Copy)
    (coordinate : Fin source.tagDimension) :
    (source.tagResidualExponent copy coordinate).val ≤ 2 := by
  unfold CollectedSignedQuarticCode.tagResidualExponent
  split <;> split <;> simp

/-- Every old-coordinate actual violation lies in `1,...,5`; every tag-
coordinate actual violation lies in `1,...,3`. -/
theorem CollectedSignedQuarticCode.target_row_bounds
    (source : CollectedSignedQuarticCode) (copy : source.Copy) :
    (∀ coordinate : Fin source.coordinateCount,
      1 ≤ (source.taggedResidualRow copy
        (finSumFinEquiv (Sum.inl coordinate))).val + 1 ∧
      (source.taggedResidualRow copy
        (finSumFinEquiv (Sum.inl coordinate))).val + 1 ≤ 5) ∧
    (∀ coordinate : Fin source.tagDimension,
      1 ≤ (source.taggedResidualRow copy
        (finSumFinEquiv (Sum.inr coordinate))).val + 1 ∧
      (source.taggedResidualRow copy
        (finSumFinEquiv (Sum.inr coordinate))).val + 1 ≤ 3) := by
  constructor
  · intro coordinate
    simp only [CollectedSignedQuarticCode.taggedResidualRow,
      Equiv.symm_apply_apply]
    exact ⟨Nat.succ_pos _, (source.exponent copy.1 coordinate).isLt⟩
  · intro coordinate
    simp only [CollectedSignedQuarticCode.taggedResidualRow,
      Equiv.symm_apply_apply]
    exact ⟨Nat.succ_pos _, Nat.succ_le_succ
      (source.tagResidualExponent_le_two copy coordinate)⟩

/-- The row-range proof applies to every emitted row, independently of
its coefficient sign. -/
theorem CollectedSignedQuarticCode.every_target_row_bounds
    (source : CollectedSignedQuarticCode)
    {row : Fin (source.coordinateCount + source.tagDimension) → Fin 5}
    (hRow : row ∈ source.positiveRows ∪ source.negativeRows) :
    (∀ coordinate : Fin source.coordinateCount,
      1 ≤ (row (finSumFinEquiv (Sum.inl coordinate))).val + 1 ∧
      (row (finSumFinEquiv (Sum.inl coordinate))).val + 1 ≤ 5) ∧
    (∀ coordinate : Fin source.tagDimension,
      1 ≤ (row (finSumFinEquiv (Sum.inr coordinate))).val + 1 ∧
      (row (finSumFinEquiv (Sum.inr coordinate))).val + 1 ≤ 3) := by
  rw [Finset.mem_union] at hRow
  rcases hRow with hPositive | hNegative
  · rw [CollectedSignedQuarticCode.positiveRows,
      Finset.mem_image] at hPositive
    obtain ⟨copy, _, rfl⟩ := hPositive
    exact source.target_row_bounds copy
  · rw [CollectedSignedQuarticCode.negativeRows,
      Finset.mem_image] at hNegative
    obtain ⟨copy, _, rfl⟩ := hNegative
    exact source.target_row_bounds copy

/-- The explicit target-table size used by the local object-size audit. -/
def CollectedSignedQuarticCode.targetObjectSize
    (source : CollectedSignedQuarticCode) : ℕ :=
  (source.coordinateCount + source.tagDimension + 1) *
    (source.positiveRows.card + source.negativeRows.card + 1)

/-- Exact target-size identity in terms of source coefficient mass. -/
theorem CollectedSignedQuarticCode.targetObjectSize_eq
    (source : CollectedSignedQuarticCode) :
    source.targetObjectSize =
      (source.coordinateCount + source.tagDimension + 1) *
        (source.coefficientL1 + 1) := by
  unfold CollectedSignedQuarticCode.targetObjectSize
  rw [source.target_row_count]

/-- Coarse polynomial envelope: binary-tag dimension never exceeds the
explicit coefficient population. -/
theorem CollectedSignedQuarticCode.targetObjectSize_le
    (source : CollectedSignedQuarticCode) :
    source.targetObjectSize ≤
      (source.coordinateCount + source.coefficientL1 + 1) *
        (source.coefficientL1 + 1) := by
  rw [source.targetObjectSize_eq]
  exact Nat.mul_le_mul_right _
    (Nat.add_le_add_right
      (Nat.add_le_add_left source.tagDimension_le_coefficientL1 _) 1)

/-! ## Evaluation and sign transport -/

/-- Join old and tag activities into the compiled coordinate block. -/
def CollectedSignedQuarticCode.joinActivity
    (source : CollectedSignedQuarticCode)
    (oldActivity : Fin source.coordinateCount → ℝ)
    (tagActivity : Fin source.tagDimension → ℝ) :
    Fin (source.coordinateCount + source.tagDimension) → ℝ :=
  fun coordinate =>
    match finSumFinEquiv.symm coordinate with
    | .inl oldCoordinate => oldActivity oldCoordinate
    | .inr tagCoordinate => tagActivity tagCoordinate

/-- Restrict a compiled activity point to its old coordinates. -/
def CollectedSignedQuarticCode.oldActivityPart
    (source : CollectedSignedQuarticCode)
    (point : Fin (source.coordinateCount + source.tagDimension) → ℝ) :
    Fin source.coordinateCount → ℝ :=
  fun coordinate => point (finSumFinEquiv (Sum.inl coordinate))

/-- Restrict a compiled activity point to its tag coordinates. -/
def CollectedSignedQuarticCode.tagActivityPart
    (source : CollectedSignedQuarticCode)
    (point : Fin (source.coordinateCount + source.tagDimension) → ℝ) :
    Fin source.tagDimension → ℝ :=
  fun coordinate => point (finSumFinEquiv (Sum.inr coordinate))

theorem CollectedSignedQuarticCode.joinActivity_parts
    (source : CollectedSignedQuarticCode)
    (point : Fin (source.coordinateCount + source.tagDimension) → ℝ) :
    source.joinActivity (source.oldActivityPart point)
      (source.tagActivityPart point) = point := by
  funext coordinate
  obtain ⟨coordinate, rfl⟩ := finSumFinEquiv.surjective coordinate
  cases coordinate <;>
    simp [CollectedSignedQuarticCode.joinActivity,
      CollectedSignedQuarticCode.oldActivityPart,
      CollectedSignedQuarticCode.tagActivityPart]

/-- One old residual monomial. -/
def CollectedSignedQuarticCode.sourceMonomial
    (source : CollectedSignedQuarticCode)
    (term : Fin source.termCount)
    (oldActivity : Fin source.coordinateCount → ℝ) : ℝ :=
  boundedQuarticResidualMonomial (source.exponent term) oldActivity

/-- Exact value of the collected integer source polynomial. -/
def CollectedSignedQuarticCode.sourceValue
    (source : CollectedSignedQuarticCode)
    (oldActivity : Fin source.coordinateCount → ℝ) : ℝ :=
  ∑ term, if source.positive term then
      (source.multiplicity term : ℝ) * source.sourceMonomial term oldActivity
    else -((source.multiplicity term : ℝ) *
      source.sourceMonomial term oldActivity)

/-- Tag residual monomial attached to one coefficient copy. -/
def CollectedSignedQuarticCode.tagResidualMonomial
    (source : CollectedSignedQuarticCode) (copy : source.Copy)
    (tagActivity : Fin source.tagDimension → ℝ) : ℝ :=
  ∏ coordinate,
    tagActivity coordinate ^ (source.tagResidualExponent copy coordinate).val

/-- Common tag monomial removed by the sign-oriented comparison. -/
def CollectedSignedQuarticCode.commonTagMonomial
    (source : CollectedSignedQuarticCode)
    (tagActivity : Fin source.tagDimension → ℝ) : ℝ :=
  ∏ coordinate, tagActivity coordinate

theorem CollectedSignedQuarticCode.tagResidualMonomial_one
    (source : CollectedSignedQuarticCode) (copy : source.Copy) :
    source.tagResidualMonomial copy (fun _ => 1) = 1 := by
  simp [CollectedSignedQuarticCode.tagResidualMonomial]

theorem CollectedSignedQuarticCode.tagResidualMonomial_ge_common_of_positive
    (source : CollectedSignedQuarticCode) (copy : source.Copy)
    (hPositive : source.positive copy.1 = true)
    (tagActivity : Fin source.tagDimension → ℝ)
    (hTag : ∀ coordinate, 0 < tagActivity coordinate ∧
      tagActivity coordinate ≤ 1) :
    source.commonTagMonomial tagActivity ≤
      source.tagResidualMonomial copy tagActivity := by
  unfold CollectedSignedQuarticCode.commonTagMonomial
    CollectedSignedQuarticCode.tagResidualMonomial
  apply Finset.prod_le_prod
  · intro coordinate _
    exact (hTag coordinate).1.le
  · intro coordinate _
    unfold CollectedSignedQuarticCode.tagResidualExponent
    rw [hPositive]
    cases hBit : source.tagBit copy coordinate
    · simp
    · simp [(hTag coordinate).2]

theorem CollectedSignedQuarticCode.tagResidualMonomial_le_common_of_negative
    (source : CollectedSignedQuarticCode) (copy : source.Copy)
    (hNegative : source.positive copy.1 = false)
    (tagActivity : Fin source.tagDimension → ℝ)
    (hTag : ∀ coordinate, 0 < tagActivity coordinate ∧
      tagActivity coordinate ≤ 1) :
    source.tagResidualMonomial copy tagActivity ≤
      source.commonTagMonomial tagActivity := by
  unfold CollectedSignedQuarticCode.commonTagMonomial
    CollectedSignedQuarticCode.tagResidualMonomial
  apply Finset.prod_le_prod
  · intro coordinate _
    exact pow_nonneg (hTag coordinate).1.le _
  · intro coordinate _
    unfold CollectedSignedQuarticCode.tagResidualExponent
    simp only [hNegative, Bool.false_eq_true, ↓reduceIte]
    cases hBit : source.tagBit copy coordinate
    · simp
    · simp only [↓reduceIte, pow_two]
      exact mul_le_of_le_one_right (hTag coordinate).1.le
        (hTag coordinate).2

/-- One signed unit contribution after binary tagging. -/
def CollectedSignedQuarticCode.copyValue
    (source : CollectedSignedQuarticCode) (copy : source.Copy)
    (oldActivity : Fin source.coordinateCount → ℝ)
    (tagActivity : Fin source.tagDimension → ℝ) : ℝ :=
  if source.positive copy.1 then
    source.sourceMonomial copy.1 oldActivity *
      source.tagResidualMonomial copy tagActivity
  else
    -(source.sourceMonomial copy.1 oldActivity *
      source.tagResidualMonomial copy tagActivity)

/-- Residual value of the unit-coefficient tagged expansion. -/
def CollectedSignedQuarticCode.tagLiftResidualValue
    (source : CollectedSignedQuarticCode)
    (oldActivity : Fin source.coordinateCount → ℝ)
    (tagActivity : Fin source.tagDimension → ℝ) : ℝ :=
  ∑ copy : source.Copy, source.copyValue copy oldActivity tagActivity

theorem CollectedSignedQuarticCode.tagLiftResidualValue_allOne
    (source : CollectedSignedQuarticCode)
    (oldActivity : Fin source.coordinateCount → ℝ) :
    source.tagLiftResidualValue oldActivity (fun _ => 1) =
      source.sourceValue oldActivity := by
  rw [CollectedSignedQuarticCode.tagLiftResidualValue,
    Fintype.sum_sigma]
  unfold CollectedSignedQuarticCode.sourceValue
  apply Finset.sum_congr rfl
  intro term _
  cases hSign : source.positive term <;>
    simp [CollectedSignedQuarticCode.copyValue, hSign,
      source.tagResidualMonomial_one]

/-- Pointwise majorization by the normalized sign-oriented tag bracket. -/
theorem CollectedSignedQuarticCode.common_mul_sourceValue_le_tagLift
    (source : CollectedSignedQuarticCode)
    (oldActivity : Fin source.coordinateCount → ℝ)
    (hOld : ∀ coordinate, 0 ≤ oldActivity coordinate)
    (tagActivity : Fin source.tagDimension → ℝ)
    (hTag : ∀ coordinate, 0 < tagActivity coordinate ∧
      tagActivity coordinate ≤ 1) :
    source.commonTagMonomial tagActivity * source.sourceValue oldActivity ≤
      source.tagLiftResidualValue oldActivity tagActivity := by
  rw [CollectedSignedQuarticCode.tagLiftResidualValue,
    Fintype.sum_sigma]
  unfold CollectedSignedQuarticCode.sourceValue
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro term _
  have hMonomial : 0 ≤ source.sourceMonomial term oldActivity := by
    unfold CollectedSignedQuarticCode.sourceMonomial
      boundedQuarticResidualMonomial
    exact Finset.prod_nonneg fun coordinate _ =>
      pow_nonneg (hOld coordinate) _
  cases hSign : source.positive term
  · simp only [Bool.false_eq_true, ↓reduceIte]
    calc
      source.commonTagMonomial tagActivity *
          -((source.multiplicity term : ℝ) *
            source.sourceMonomial term oldActivity) =
          ∑ copy : Fin (source.multiplicity term),
            -(source.sourceMonomial term oldActivity *
              source.commonTagMonomial tagActivity) := by
            simp
            ring
      _ ≤ ∑ copy : Fin (source.multiplicity term),
          source.copyValue ⟨term, copy⟩ oldActivity tagActivity := by
        apply Finset.sum_le_sum
        intro copy _
        unfold CollectedSignedQuarticCode.copyValue
        rw [hSign]
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact neg_le_neg (mul_le_mul_of_nonneg_left
          (source.tagResidualMonomial_le_common_of_negative
            ⟨term, copy⟩ hSign tagActivity hTag) hMonomial)
  · simp only [↓reduceIte]
    calc
      source.commonTagMonomial tagActivity *
          ((source.multiplicity term : ℝ) *
            source.sourceMonomial term oldActivity) =
          ∑ copy : Fin (source.multiplicity term),
            source.sourceMonomial term oldActivity *
              source.commonTagMonomial tagActivity := by
            simp
            ring
      _ ≤ ∑ copy : Fin (source.multiplicity term),
          source.copyValue ⟨term, copy⟩ oldActivity tagActivity := by
        apply Finset.sum_le_sum
        intro copy _
        unfold CollectedSignedQuarticCode.copyValue
        rw [hSign]
        simp only [↓reduceIte]
        exact mul_le_mul_of_nonneg_left
          (source.tagResidualMonomial_ge_common_of_positive
            ⟨term, copy⟩ hSign tagActivity hTag) hMonomial

theorem CollectedSignedQuarticCode.taggedResidualMonomial_factorization
    (source : CollectedSignedQuarticCode) (copy : source.Copy)
    (oldActivity : Fin source.coordinateCount → ℝ)
    (tagActivity : Fin source.tagDimension → ℝ) :
    boundedQuarticResidualMonomial (source.taggedResidualRow copy)
        (source.joinActivity oldActivity tagActivity) =
      source.sourceMonomial copy.1 oldActivity *
        source.tagResidualMonomial copy tagActivity := by
  unfold boundedQuarticResidualMonomial
    CollectedSignedQuarticCode.sourceMonomial
    CollectedSignedQuarticCode.tagResidualMonomial
  rw [Fin.prod_univ_add]
  congr 1
  · apply Finset.prod_congr rfl
    intro coordinate _
    simp [CollectedSignedQuarticCode.taggedResidualRow,
      CollectedSignedQuarticCode.joinActivity]
  · apply Finset.prod_congr rfl
    intro coordinate _
    simp [CollectedSignedQuarticCode.taggedResidualRow,
      CollectedSignedQuarticCode.joinActivity]

/-- The finite target row ledger evaluates exactly to the signed unit-copy
sum.  This is the coefficient-`±1` realization theorem, not merely a support
count. -/
theorem CollectedSignedQuarticCode.signedDistinctMargin_joinActivity
    (source : CollectedSignedQuarticCode)
    (oldActivity : Fin source.coordinateCount → ℝ)
    (tagActivity : Fin source.tagDimension → ℝ) :
    signedDistinctQuarticMargin source.positiveRows source.negativeRows
        (source.joinActivity oldActivity tagActivity) =
      source.tagLiftResidualValue oldActivity tagActivity := by
  classical
  unfold signedDistinctQuarticMargin
    CollectedSignedQuarticCode.positiveRows
    CollectedSignedQuarticCode.negativeRows
  rw [Finset.sum_image, Finset.sum_image]
  · simp_rw [source.taggedResidualMonomial_factorization]
    simpa [CollectedSignedQuarticCode.positiveCopies,
      CollectedSignedQuarticCode.negativeCopies,
      CollectedSignedQuarticCode.tagLiftResidualValue,
      CollectedSignedQuarticCode.copyValue] using
      (sum_bool_true_sub_false
        (items := (Finset.univ : Finset source.Copy))
        (predicate := fun copy => source.positive copy.1)
        (value := fun copy => source.sourceMonomial copy.1 oldActivity *
          source.tagResidualMonomial copy tagActivity))
  · intro first _ second _ hRows
    exact source.taggedResidualRow_injective hRows
  · intro first _ second _ hRows
    exact source.taggedResidualRow_injective hRows

/-! ## Exact sign and universal-order transport -/

/-- Universal nonnegativity of the collected source polynomial on the
positive unit cube. -/
def CollectedSignedQuarticCode.universallyNonnegative
    (source : CollectedSignedQuarticCode) : Prop :=
  ∀ oldActivity : Fin source.coordinateCount → ℝ,
    IsPositiveUnitCubePoint oldActivity →
      0 ≤ source.sourceValue oldActivity

theorem CollectedSignedQuarticCode.oldActivityPart_positiveUnitCube
    (source : CollectedSignedQuarticCode)
    {point : Fin (source.coordinateCount + source.tagDimension) → ℝ}
    (hPoint : IsPositiveUnitCubePoint point) :
    IsPositiveUnitCubePoint (source.oldActivityPart point) := by
  intro coordinate
  exact hPoint (finSumFinEquiv (Sum.inl coordinate))

theorem CollectedSignedQuarticCode.tagActivityPart_positiveUnitCube
    (source : CollectedSignedQuarticCode)
    {point : Fin (source.coordinateCount + source.tagDimension) → ℝ}
    (hPoint : IsPositiveUnitCubePoint point) :
    IsPositiveUnitCubePoint (source.tagActivityPart point) := by
  intro coordinate
  exact hPoint (finSumFinEquiv (Sum.inr coordinate))

theorem CollectedSignedQuarticCode.joinActivity_positiveUnitCube
    (source : CollectedSignedQuarticCode)
    {oldActivity : Fin source.coordinateCount → ℝ}
    {tagActivity : Fin source.tagDimension → ℝ}
    (hOld : IsPositiveUnitCubePoint oldActivity)
    (hTag : IsPositiveUnitCubePoint tagActivity) :
    IsPositiveUnitCubePoint
      (source.joinActivity oldActivity tagActivity) := by
  intro coordinate
  obtain ⟨coordinate, rfl⟩ := finSumFinEquiv.surjective coordinate
  cases coordinate with
  | inl oldCoordinate =>
      simpa [CollectedSignedQuarticCode.joinActivity] using
        hOld oldCoordinate
  | inr tagCoordinate =>
      simpa [CollectedSignedQuarticCode.joinActivity] using
        hTag tagCoordinate

/-- Exact target margin after adjoining the tag block.  The first factor is
strictly positive on the physical cube, so this factorization preserves the
sign of the tagged residual. -/
theorem CollectedSignedQuarticCode.oneToFiveMargin_joinActivity
    (source : CollectedSignedQuarticCode)
    (oldActivity : Fin source.coordinateCount → ℝ)
    (tagActivity : Fin source.tagDimension → ℝ) :
    duplicateFreeOneToFiveOrderMargin source.positiveRows source.negativeRows
        (source.joinActivity oldActivity tagActivity) =
      commonAllOneMonomial (source.joinActivity oldActivity tagActivity) *
        source.tagLiftResidualValue oldActivity tagActivity := by
  rw [duplicateFreeOneToFiveOrderMargin_factorization,
    source.signedDistinctMargin_joinActivity]

/-- Setting every tag activity to one is the exact forward embedding of an
old point into the compiled cube. -/
theorem CollectedSignedQuarticCode.oneToFiveMargin_allOne
    (source : CollectedSignedQuarticCode)
    (oldActivity : Fin source.coordinateCount → ℝ) :
    duplicateFreeOneToFiveOrderMargin source.positiveRows source.negativeRows
        (source.joinActivity oldActivity (fun _ => 1)) =
      commonAllOneMonomial
          (source.joinActivity oldActivity (fun _ => 1)) *
        source.sourceValue oldActivity := by
  rw [source.oneToFiveMargin_joinActivity,
    source.tagLiftResidualValue_allOne]

/-- **Sign-oriented binary-tag theorem.**  The compiled duplicate-free
`{1,…,5}` target has the universal named-candidate order exactly when the
collected source quartic is nonnegative throughout its positive unit cube. -/
theorem CollectedSignedQuarticCode.binaryTag_universalOrder_iff
    (source : CollectedSignedQuarticCode) :
    source.toOneToFiveOrderCode.universalOrder ↔
      source.universallyNonnegative := by
  change
    (∀ point : Fin (source.coordinateCount + source.tagDimension) → ℝ,
      IsPositiveUnitCubePoint point →
        0 ≤ duplicateFreeOneToFiveOrderMargin source.positiveRows
          source.negativeRows point) ↔
      source.universallyNonnegative
  constructor
  · intro hTarget oldActivity hOld
    have hTag : IsPositiveUnitCubePoint
        (fun _ : Fin source.tagDimension => (1 : ℝ)) := by
      intro coordinate
      exact ⟨by norm_num, by norm_num⟩
    have hMargin := hTarget
      (source.joinActivity oldActivity (fun _ => 1))
      (source.joinActivity_positiveUnitCube hOld hTag)
    rw [source.oneToFiveMargin_allOne] at hMargin
    exact nonneg_of_mul_nonneg_right hMargin
      (commonAllOneMonomial_pos
        (source.joinActivity_positiveUnitCube hOld hTag))
  · intro hSource point hPoint
    let oldActivity := source.oldActivityPart point
    let tagActivity := source.tagActivityPart point
    have hOld : IsPositiveUnitCubePoint oldActivity :=
      source.oldActivityPart_positiveUnitCube hPoint
    have hTag : IsPositiveUnitCubePoint tagActivity :=
      source.tagActivityPart_positiveUnitCube hPoint
    have hSourceValue : 0 ≤ source.sourceValue oldActivity :=
      hSource oldActivity hOld
    have hCommonTag : 0 ≤ source.commonTagMonomial tagActivity := by
      unfold CollectedSignedQuarticCode.commonTagMonomial
      exact Finset.prod_nonneg fun coordinate _ => (hTag coordinate).1.le
    have hLift : 0 ≤ source.tagLiftResidualValue oldActivity tagActivity :=
      le_trans (mul_nonneg hCommonTag hSourceValue)
        (source.common_mul_sourceValue_le_tagLift oldActivity
          (fun coordinate => (hOld coordinate).1.le) tagActivity hTag)
    rw [← source.joinActivity_parts point]
    rw [source.oneToFiveMargin_joinActivity]
    exact mul_nonneg
      (commonAllOneMonomial_pos
        (source.joinActivity_positiveUnitCube hOld hTag)).le hLift

/-- A negative source point maps to an explicit negative target point by
setting every tag activity to one. -/
theorem CollectedSignedQuarticCode.negativeSourceWitness_to_target
    (source : CollectedSignedQuarticCode)
    {oldActivity : Fin source.coordinateCount → ℝ}
    (hOld : IsPositiveUnitCubePoint oldActivity)
    (hNegative : source.sourceValue oldActivity < 0) :
    ∃ point : Fin (source.coordinateCount + source.tagDimension) → ℝ,
      IsPositiveUnitCubePoint point ∧
      duplicateFreeOneToFiveOrderMargin source.positiveRows
        source.negativeRows point < 0 := by
  let point := source.joinActivity oldActivity (fun _ => 1)
  have hTag : IsPositiveUnitCubePoint
      (fun _ : Fin source.tagDimension => (1 : ℝ)) := by
    intro coordinate
    exact ⟨by norm_num, by norm_num⟩
  refine ⟨point, source.joinActivity_positiveUnitCube hOld hTag, ?_⟩
  rw [source.oneToFiveMargin_allOne]
  exact mul_neg_of_pos_of_neg
    (commonAllOneMonomial_pos
      (source.joinActivity_positiveUnitCube hOld hTag)) hNegative

/-- Every negative compiled target point projects to a genuinely negative
old source point.  Thus the fresh tag coordinates cannot manufacture a false
counterexample. -/
theorem CollectedSignedQuarticCode.negativeTargetWitness_to_source
    (source : CollectedSignedQuarticCode)
    {point : Fin (source.coordinateCount + source.tagDimension) → ℝ}
    (hPoint : IsPositiveUnitCubePoint point)
    (hNegative : duplicateFreeOneToFiveOrderMargin source.positiveRows
      source.negativeRows point < 0) :
    source.sourceValue (source.oldActivityPart point) < 0 := by
  let oldActivity := source.oldActivityPart point
  let tagActivity := source.tagActivityPart point
  have hOld : IsPositiveUnitCubePoint oldActivity :=
    source.oldActivityPart_positiveUnitCube hPoint
  have hTag : IsPositiveUnitCubePoint tagActivity :=
    source.tagActivityPart_positiveUnitCube hPoint
  have hPointJoin : source.joinActivity oldActivity tagActivity = point :=
    source.joinActivity_parts point
  have hLiftNegative : source.tagLiftResidualValue oldActivity tagActivity < 0 := by
    have hFactorPositive :
        0 < commonAllOneMonomial
          (source.joinActivity oldActivity tagActivity) := by
      rw [hPointJoin]
      exact commonAllOneMonomial_pos hPoint
    rw [← hPointJoin, source.oneToFiveMargin_joinActivity] at hNegative
    exact (mul_neg_iff.mp hNegative).resolve_right
      (fun hImpossible => (not_lt_of_ge hFactorPositive.le hImpossible.1)) |>.2
  have hDominance := source.common_mul_sourceValue_le_tagLift oldActivity
    (fun coordinate => (hOld coordinate).1.le) tagActivity hTag
  have hCommonPositive : 0 < source.commonTagMonomial tagActivity := by
    unfold CollectedSignedQuarticCode.commonTagMonomial
    exact Finset.prod_pos fun coordinate _ => (hTag coordinate).1
  by_contra hNotNegative
  have hSourceNonnegative : 0 ≤ source.sourceValue oldActivity :=
    le_of_not_gt hNotNegative
  have hProductNonnegative :
      0 ≤ source.commonTagMonomial tagActivity *
        source.sourceValue oldActivity :=
    mul_nonneg hCommonPositive.le hSourceNonnegative
  linarith

/-- Counterexample existence is preserved in both directions, with explicit
witness maps. -/
theorem CollectedSignedQuarticCode.negativeWitness_iff
    (source : CollectedSignedQuarticCode) :
    (∃ point : Fin (source.coordinateCount + source.tagDimension) → ℝ,
      IsPositiveUnitCubePoint point ∧
      duplicateFreeOneToFiveOrderMargin source.positiveRows
        source.negativeRows point < 0) ↔
    (∃ oldActivity : Fin source.coordinateCount → ℝ,
      IsPositiveUnitCubePoint oldActivity ∧
      source.sourceValue oldActivity < 0) := by
  constructor
  · rintro ⟨point, hPoint, hNegative⟩
    exact ⟨source.oldActivityPart point,
      source.oldActivityPart_positiveUnitCube hPoint,
      source.negativeTargetWitness_to_source hPoint hNegative⟩
  · rintro ⟨oldActivity, hOld, hNegative⟩
    exact source.negativeSourceWitness_to_target hOld hNegative

/-! ## Concrete finite-MaxEnt realization -/

abbrev CollectedSignedQuarticCode.PositiveCandidate
    (source : CollectedSignedQuarticCode) :=
  Option {row // row ∈ source.positiveRows}

abbrev CollectedSignedQuarticCode.NegativeCandidate
    (source : CollectedSignedQuarticCode) :=
  Option {row // row ∈ source.negativeRows}

/-- First complete ledger.  `none` is the named zero-row candidate and every
other candidate has unit base mass and one of the globally distinct positive
actual rows. -/
def CollectedSignedQuarticCode.positiveLedger
    (source : CollectedSignedQuarticCode) :
    CompleteFiniteLedger
      (Fin (source.coordinateCount + source.tagDimension))
      source.PositiveCandidate where
  baseMass := fun _ => 1
  row
    | none => fun _ => 0
    | some alternative => fun coordinate =>
        (alternative.1 coordinate).val + 1
  baseMass_pos := by
    intro candidate
    norm_num

/-- Second complete ledger, with the same named zero row and the globally
distinct negative actual rows. -/
def CollectedSignedQuarticCode.negativeLedger
    (source : CollectedSignedQuarticCode) :
    CompleteFiniteLedger
      (Fin (source.coordinateCount + source.tagDimension))
      source.NegativeCandidate where
  baseMass := fun _ => 1
  row
    | none => fun _ => 0
    | some alternative => fun coordinate =>
        (alternative.1 coordinate).val + 1
  baseMass_pos := by
    intro candidate
    norm_num

theorem CollectedSignedQuarticCode.compiledLedgers_unitMass_zeroNamed
    (source : CollectedSignedQuarticCode) :
    ((∀ candidate, source.positiveLedger.baseMass candidate = 1) ∧
      source.positiveLedger.row none = 0) ∧
    ((∀ candidate, source.negativeLedger.baseMass candidate = 1) ∧
      source.negativeLedger.row none = 0) := by
  refine ⟨⟨fun candidate => rfl, ?_⟩, ⟨fun candidate => rfl, ?_⟩⟩
  · funext coordinate
    rfl
  · funext coordinate
    rfl

/-- All nonnamed actual violations in both ledgers lie in `{1,…,5}`. -/
theorem CollectedSignedQuarticCode.compiledLedgers_rowBounds
    (source : CollectedSignedQuarticCode) :
    (∀ alternative : {row // row ∈ source.positiveRows},
      ∀ coordinate,
        1 ≤ source.positiveLedger.row (some alternative) coordinate ∧
        source.positiveLedger.row (some alternative) coordinate ≤ 5) ∧
    (∀ alternative : {row // row ∈ source.negativeRows},
      ∀ coordinate,
        1 ≤ source.negativeLedger.row (some alternative) coordinate ∧
        source.negativeLedger.row (some alternative) coordinate ≤ 5) := by
  constructor <;> intro alternative coordinate <;>
    simp [CollectedSignedQuarticCode.positiveLedger,
      CollectedSignedQuarticCode.negativeLedger]

/-- No nonnamed row is repeated within or across the two ledgers. -/
theorem CollectedSignedQuarticCode.compiledLedgers_globalDistinctness
    (source : CollectedSignedQuarticCode) :
    (Function.Injective
      (fun alternative : {row // row ∈ source.positiveRows} =>
        source.positiveLedger.row (some alternative))) ∧
    (Function.Injective
      (fun alternative : {row // row ∈ source.negativeRows} =>
        source.negativeLedger.row (some alternative))) ∧
    (∀ positive : {row // row ∈ source.positiveRows},
      ∀ negative : {row // row ∈ source.negativeRows},
        source.positiveLedger.row (some positive) ≠
          source.negativeLedger.row (some negative)) := by
  constructor
  · intro first second hRows
    apply Subtype.ext
    funext coordinate
    have hCoordinate := congrFun hRows coordinate
    apply Fin.ext
    change (first.1 coordinate).val = (second.1 coordinate).val
    change (first.1 coordinate).val + 1 =
      (second.1 coordinate).val + 1 at hCoordinate
    omega
  constructor
  · intro first second hRows
    apply Subtype.ext
    funext coordinate
    have hCoordinate := congrFun hRows coordinate
    apply Fin.ext
    change (first.1 coordinate).val = (second.1 coordinate).val
    change (first.1 coordinate).val + 1 =
      (second.1 coordinate).val + 1 at hCoordinate
    omega
  · intro positive negative hRows
    have hResidual : positive.1 = negative.1 := by
      funext coordinate
      have hCoordinate := congrFun hRows coordinate
      apply Fin.ext
      change (positive.1 coordinate).val + 1 =
        (negative.1 coordinate).val + 1 at hCoordinate
      omega
    have hPositive : negative.1 ∈ source.positiveRows := by
      rw [← hResidual]
      exact positive.2
    exact Finset.disjoint_left.mp source.rows_disjoint hPositive negative.2

theorem oneToFiveViolationMonomial_eq_laurentMonomial
    {J : Type*} [Fintype J]
    (row : J → Fin 5) (activity : J → ℝ) :
    oneToFiveViolationMonomial row activity =
      laurentMonomial
        (fun coordinate => ((row coordinate).val + 1 : ℤ)) activity := by
  unfold oneToFiveViolationMonomial laurentMonomial
  apply Finset.prod_congr rfl
  intro coordinate _
  norm_cast

@[simp] theorem CollectedSignedQuarticCode.positiveRelativeRow_named
    (source : CollectedSignedQuarticCode) :
    relativeViolationRow source.positiveLedger none none = 0 := by
  funext coordinate
  rfl

@[simp] theorem CollectedSignedQuarticCode.positiveRelativeRow_alternative
    (source : CollectedSignedQuarticCode)
    (alternative : {row // row ∈ source.positiveRows}) :
    relativeViolationRow source.positiveLedger none (some alternative) =
      fun coordinate => ((alternative.1 coordinate).val + 1 : ℤ) := by
  funext coordinate
  simp [relativeViolationRow, CollectedSignedQuarticCode.positiveLedger]

@[simp] theorem CollectedSignedQuarticCode.negativeRelativeRow_named
    (source : CollectedSignedQuarticCode) :
    relativeViolationRow source.negativeLedger none none = 0 := by
  funext coordinate
  rfl

@[simp] theorem CollectedSignedQuarticCode.negativeRelativeRow_alternative
    (source : CollectedSignedQuarticCode)
    (alternative : {row // row ∈ source.negativeRows}) :
    relativeViolationRow source.negativeLedger none (some alternative) =
      fun coordinate => ((alternative.1 coordinate).val + 1 : ℤ) := by
  funext coordinate
  simp [relativeViolationRow, CollectedSignedQuarticCode.negativeLedger]

theorem CollectedSignedQuarticCode.positiveRelativePartition
    (source : CollectedSignedQuarticCode)
    (activity : Fin (source.coordinateCount + source.tagDimension) → ℝ) :
    relativePartitionEvaluation source.positiveLedger none activity =
      1 + ∑ row ∈ source.positiveRows,
        oneToFiveViolationMonomial row activity := by
  classical
  rw [relativePartitionEvaluation_eq_sum, Fintype.sum_option]
  rw [source.positiveRelativeRow_named]
  simp_rw [source.positiveRelativeRow_alternative]
  simp only [CollectedSignedQuarticCode.positiveLedger, Rat.cast_one,
    one_div, inv_one, one_mul]
  simp only [laurentMonomial, Pi.zero_apply, zpow_zero,
    Finset.prod_const_one]
  rw [show (∑ alternative : {row // row ∈ source.positiveRows},
      ∏ coordinate, activity coordinate ^
        ((alternative.1 coordinate).val + 1 : ℤ)) =
      ∑ row ∈ source.positiveRows,
        oneToFiveViolationMonomial row activity by
    rw [Finset.sum_subtype source.positiveRows (fun _ => Iff.rfl)]
    apply Fintype.sum_congr
    intro alternative
    rw [oneToFiveViolationMonomial_eq_laurentMonomial]
    rfl]

theorem CollectedSignedQuarticCode.negativeRelativePartition
    (source : CollectedSignedQuarticCode)
    (activity : Fin (source.coordinateCount + source.tagDimension) → ℝ) :
    relativePartitionEvaluation source.negativeLedger none activity =
      1 + ∑ row ∈ source.negativeRows,
        oneToFiveViolationMonomial row activity := by
  classical
  rw [relativePartitionEvaluation_eq_sum, Fintype.sum_option]
  rw [source.negativeRelativeRow_named]
  simp_rw [source.negativeRelativeRow_alternative]
  simp only [CollectedSignedQuarticCode.negativeLedger, Rat.cast_one,
    one_div, inv_one, one_mul]
  simp only [laurentMonomial, Pi.zero_apply, zpow_zero,
    Finset.prod_const_one]
  rw [show (∑ alternative : {row // row ∈ source.negativeRows},
      ∏ coordinate, activity coordinate ^
        ((alternative.1 coordinate).val + 1 : ℤ)) =
      ∑ row ∈ source.negativeRows,
        oneToFiveViolationMonomial row activity by
    rw [Finset.sum_subtype source.negativeRows (fun _ => Iff.rfl)]
    apply Fintype.sum_congr
    intro alternative
    rw [oneToFiveViolationMonomial_eq_laurentMonomial]
    rfl]

/-- The finite-table margin is exactly the reverse relative-partition
difference induced by the two named candidates. -/
theorem CollectedSignedQuarticCode.oneToFiveMargin_eq_relativePartitions
    (source : CollectedSignedQuarticCode)
    (activity : Fin (source.coordinateCount + source.tagDimension) → ℝ) :
    duplicateFreeOneToFiveOrderMargin source.positiveRows source.negativeRows
        activity =
      relativePartitionEvaluation source.positiveLedger none activity -
        relativePartitionEvaluation source.negativeLedger none activity := by
  rw [source.positiveRelativePartition, source.negativeRelativePartition]
  unfold duplicateFreeOneToFiveOrderMargin
  ring

/-- The row-language order is the actual named-candidate probability order
in the two complete unit-mass MaxEnt ledgers. -/
theorem CollectedSignedQuarticCode.probabilityOrder_iff_margin_nonnegative
    (source : CollectedSignedQuarticCode)
    (activity : Fin (source.coordinateCount + source.tagDimension) → ℝ)
    (hActivity : ∀ coordinate, 0 < activity coordinate) :
    rationalNamedCandidateProbability source.positiveLedger.baseMass
        (fun candidate coordinate =>
          (source.positiveLedger.row candidate coordinate : ℤ))
        none activity ≤
      rationalNamedCandidateProbability source.negativeLedger.baseMass
        (fun candidate coordinate =>
          (source.negativeLedger.row candidate coordinate : ℤ))
        none activity ↔
      0 ≤ duplicateFreeOneToFiveOrderMargin source.positiveRows
        source.negativeRows activity := by
  rw [candidateProbability_eq_inv_relativePartition
      source.positiveLedger none activity hActivity,
    candidateProbability_eq_inv_relativePartition
      source.negativeLedger none activity hActivity]
  have hPositive := relativePartitionEvaluation_pos
    source.positiveLedger none activity hActivity
  have hNegative := relativePartitionEvaluation_pos
    source.negativeLedger none activity hActivity
  rw [div_le_div_iff_of_pos_left (by norm_num : (0 : ℝ) < 1)
    hPositive hNegative]
  constructor
  · intro hPartitions
    rw [source.oneToFiveMargin_eq_relativePartitions]
    linarith
  · intro hMargin
    rw [source.oneToFiveMargin_eq_relativePartitions] at hMargin
    linarith

/-- Universal target order is exactly universal named-probability order over
the full nonnegative MaxEnt weight orthant. -/
theorem CollectedSignedQuarticCode.universalOrder_iff_allWeightProbabilityOrder
    (source : CollectedSignedQuarticCode) :
    source.toOneToFiveOrderCode.universalOrder ↔
      ∀ weight : Fin (source.coordinateCount + source.tagDimension) → ℝ,
        IsNonnegativeWeight weight →
        exponentialCandidateProbability source.positiveLedger weight none ≤
          exponentialCandidateProbability source.negativeLedger weight none := by
  change
    (∀ activity : Fin (source.coordinateCount + source.tagDimension) → ℝ,
      IsPositiveUnitCubePoint activity →
        0 ≤ duplicateFreeOneToFiveOrderMargin source.positiveRows
          source.negativeRows activity) ↔ _
  constructor
  · intro hOrder weight hWeight
    have hActivity : IsPositiveUnitCubePoint (activityOfWeight weight) :=
      fun coordinate => ⟨activityOfWeight_pos weight coordinate,
        activityOfWeight_le_one weight hWeight coordinate⟩
    rw [← activityProbability_eq_exponentialProbability,
      ← activityProbability_eq_exponentialProbability]
    exact (source.probabilityOrder_iff_margin_nonnegative
      (activityOfWeight weight)
      (fun coordinate => (hActivity coordinate).1)).2
      (hOrder (activityOfWeight weight) hActivity)
  · intro hOrder activity hActivity
    let weight := weightOfActivity activity
    have hWeight : IsNonnegativeWeight weight :=
      weightOfActivity_nonnegative activity hActivity
    have hInverse : activityOfWeight weight = activity :=
      activityOfWeight_weightOfActivity activity
        (fun coordinate => (hActivity coordinate).1)
    have hProbability := hOrder weight hWeight
    rw [← activityProbability_eq_exponentialProbability,
      ← activityProbability_eq_exponentialProbability] at hProbability
    rw [hInverse] at hProbability
    exact (source.probabilityOrder_iff_margin_nonnegative activity
      (fun coordinate => (hActivity coordinate).1)).1 hProbability

/-! ## Canonical collection of bounded integer quartics -/

/-- An integer polynomial together with the degree proof needed to
encode every collected exponent in `Fin 5`. -/
structure BoundedQuarticIntegerPolynomialCode where
  coordinateCount : ℕ
  polynomial : MvPolynomial (Fin coordinateCount) ℤ
  totalDegree_le_four : polynomial.totalDegree ≤ 4

/-- Nonzero collected monomials of a polynomial. -/
abbrev BoundedQuarticIntegerPolynomialCode.SupportTerm
    (input : BoundedQuarticIntegerPolynomialCode) :=
  {monomial // monomial ∈ input.polynomial.support}

/-- Canonical finite enumeration of the nonzero collected monomials. -/
def BoundedQuarticIntegerPolynomialCode.supportTerm
    (input : BoundedQuarticIntegerPolynomialCode)
    (term : Fin (Fintype.card input.SupportTerm)) : input.SupportTerm :=
  (Fintype.equivFin input.SupportTerm).symm term

theorem BoundedQuarticIntegerPolynomialCode.supportExponent_le_four
    (input : BoundedQuarticIntegerPolynomialCode)
    (term : Fin (Fintype.card input.SupportTerm))
    (coordinate : Fin input.coordinateCount) :
    (input.supportTerm term).1 coordinate ≤ 4 := by
  have hCoordinate :
      (input.supportTerm term).1 coordinate ≤
        (input.supportTerm term).1.sum (fun _ exponent => exponent) := by
    exact Finsupp.single_eval_le_sum (input.supportTerm term).1
      (g := fun exponent : ℕ => exponent) rfl
      (fun exponent => Nat.zero_le exponent) coordinate
  exact hCoordinate.trans
    ((MvPolynomial.le_totalDegree (input.supportTerm term).2).trans
      input.totalDegree_le_four)

/-- Canonical collection map: support removes zero coefficients, the support
enumeration removes duplicate exponent rows, and coefficient magnitude is
recorded before binary expansion. -/
def BoundedQuarticIntegerPolynomialCode.toCollected
    (input : BoundedQuarticIntegerPolynomialCode) :
    CollectedSignedQuarticCode where
  coordinateCount := input.coordinateCount
  termCount := Fintype.card input.SupportTerm
  exponent := fun term coordinate =>
    ⟨(input.supportTerm term).1 coordinate,
      Nat.lt_succ_iff.mpr (input.supportExponent_le_four term coordinate)⟩
  positive := fun term => decide
    (0 < input.polynomial.coeff (input.supportTerm term).1)
  multiplicity := fun term =>
    Int.natAbs (input.polynomial.coeff (input.supportTerm term).1)
  multiplicity_pos := by
    intro term
    rw [Int.natAbs_pos]
    exact MvPolynomial.mem_support_iff.mp (input.supportTerm term).2
  exponent_injective := by
    intro first second hExponent
    apply (Fintype.equivFin input.SupportTerm).symm.injective
    apply Subtype.ext
    apply Finsupp.ext
    intro coordinate
    have hCoordinate := congrFun hExponent coordinate
    exact congrArg Fin.val hCoordinate

/-- The sign-and-magnitude representation recovers each original nonzero
integer coefficient exactly. -/
theorem BoundedQuarticIntegerPolynomialCode.toCollected_coefficient
    (input : BoundedQuarticIntegerPolynomialCode)
    (term : Fin (Fintype.card input.SupportTerm)) :
    input.toCollected.coefficient term =
      input.polynomial.coeff (input.supportTerm term).1 := by
  let coefficient := input.polynomial.coeff (input.supportTerm term).1
  have hNonzero : coefficient ≠ 0 :=
    MvPolynomial.mem_support_iff.mp (input.supportTerm term).2
  by_cases hPositive : 0 < coefficient
  · simp [BoundedQuarticIntegerPolynomialCode.toCollected,
      CollectedSignedQuarticCode.coefficient, coefficient, hPositive,
      Int.natAbs_of_nonneg hPositive.le]
  · have hNonpositive : coefficient ≤ 0 := le_of_not_gt hPositive
    have hIdentity : -(Int.natAbs coefficient : ℤ) = coefficient :=
      (Int.eq_neg_natAbs_of_nonpos hNonpositive).symm
    simp only [BoundedQuarticIntegerPolynomialCode.toCollected,
      CollectedSignedQuarticCode.coefficient, decide_eq_true_eq]
    rw [if_neg hPositive]
    exact hIdentity

theorem BoundedQuarticIntegerPolynomialCode.toCollected_exponent
    (input : BoundedQuarticIntegerPolynomialCode)
    (term : Fin (Fintype.card input.SupportTerm))
    (coordinate : Fin input.coordinateCount) :
    (input.toCollected.exponent term coordinate).val =
      (input.supportTerm term).1 coordinate := rfl

theorem BoundedQuarticIntegerPolynomialCode.toCollected_termCount
    (input : BoundedQuarticIntegerPolynomialCode) :
    input.toCollected.termCount = input.polynomial.support.card := by
  change Fintype.card input.SupportTerm = input.polynomial.support.card
  exact Fintype.card_coe input.polynomial.support

/-- The collected representation retains the exact coefficient `ℓ1` mass;
this is the emitted alternative-row count after binary expansion. -/
theorem BoundedQuarticIntegerPolynomialCode.toCollected_coefficientL1
    (input : BoundedQuarticIntegerPolynomialCode) :
    input.toCollected.coefficientL1 = coefficientL1 input.polynomial := by
  classical
  unfold CollectedSignedQuarticCode.coefficientL1 coefficientL1
  change
    (∑ term : Fin (Fintype.card input.SupportTerm),
      Int.natAbs
        (input.polynomial.coeff (input.supportTerm term).1)) = _
  calc
    (∑ term : Fin (Fintype.card input.SupportTerm),
      Int.natAbs
        (input.polynomial.coeff (input.supportTerm term).1)) =
        ∑ term : input.SupportTerm,
          Int.natAbs (input.polynomial.coeff term.1) := by
      apply Fintype.sum_equiv
        (Fintype.equivFin input.SupportTerm).symm
      intro term
      rfl
    _ = ∑ monomial ∈ input.polynomial.support,
          Int.natAbs (input.polynomial.coeff monomial) := by
      rw [Finset.univ_eq_attach input.polynomial.support]
      conv_rhs => rw [← Finset.sum_attach]

/-- Collection preserves real evaluation exactly. -/
theorem BoundedQuarticIntegerPolynomialCode.toCollected_sourceValue
    (input : BoundedQuarticIntegerPolynomialCode)
    (point : Fin input.coordinateCount → ℝ) :
    input.toCollected.sourceValue point =
      MvPolynomial.eval₂ (Int.castRingHom ℝ) point input.polynomial := by
  classical
  rw [input.polynomial.as_sum, MvPolynomial.eval₂_sum]
  have hCoefficientForm :
      input.toCollected.sourceValue point =
        ∑ term : Fin input.toCollected.termCount,
          (input.toCollected.coefficient term : ℝ) *
            input.toCollected.sourceMonomial term point := by
    unfold CollectedSignedQuarticCode.sourceValue
    apply Finset.sum_congr rfl
    intro term _
    unfold CollectedSignedQuarticCode.coefficient
    split <;> simp
  rw [hCoefficientForm]
  change
    (∑ term : Fin (Fintype.card input.SupportTerm),
      (input.toCollected.coefficient term : ℝ) *
        input.toCollected.sourceMonomial term point) = _
  calc
    (∑ term : Fin (Fintype.card input.SupportTerm),
        (input.toCollected.coefficient term : ℝ) *
          input.toCollected.sourceMonomial term point) =
        ∑ term : input.SupportTerm,
          ((MvPolynomial.coeff term.1 input.polynomial : ℤ) : ℝ) *
            term.1.prod (fun coordinate exponent =>
              point coordinate ^ exponent) := by
      apply Fintype.sum_equiv
        (Fintype.equivFin input.SupportTerm).symm
      intro term
      rw [input.toCollected_coefficient]
      unfold CollectedSignedQuarticCode.sourceMonomial
        boundedQuarticResidualMonomial
      rw [Finsupp.prod_fintype]
      · rfl
      · intro coordinate
        simp
    _ = ∑ monomial ∈ input.polynomial.support,
          MvPolynomial.eval₂ (Int.castRingHom ℝ) point
            (MvPolynomial.monomial monomial
              (input.polynomial.coeff monomial)) := by
      rw [Finset.univ_eq_attach input.polynomial.support]
      conv_rhs => rw [← Finset.sum_attach]
      apply Finset.sum_congr rfl
      intro term _
      rw [MvPolynomial.eval₂_monomial]
      rfl

/-! ## Explicit polynomial output-size reduction -/

/-- Explicit-size collected quartic language.  Coefficients are measured in
expanded unary mass because the compiler emits one target row per coefficient
unit. -/
def collectedSignedQuarticCodeSize
    (source : CollectedSignedQuarticCode) : ℕ :=
  source.coordinateCount + source.coefficientL1 + 1

def collectedSignedQuarticUniversalNonnegativity : EncodedDecisionProblem where
  Instance := CollectedSignedQuarticCode
  accepts := CollectedSignedQuarticCode.universallyNonnegative
  size := collectedSignedQuarticCodeSize
  size_positive := by
    intro source
    unfold collectedSignedQuarticCodeSize
    omega

theorem CollectedSignedQuarticCode.compiledDecisionSize_eq
    (source : CollectedSignedQuarticCode) :
    duplicateFreeOneToFiveUniversalOrder.size source.toOneToFiveOrderCode =
      source.targetObjectSize := rfl

theorem CollectedSignedQuarticCode.targetObjectSize_le_sourceSize_sq
    (source : CollectedSignedQuarticCode) :
    source.targetObjectSize ≤ collectedSignedQuarticCodeSize source ^ 2 := by
  have hLeft := source.targetObjectSize_le
  have hRight : source.coefficientL1 + 1 ≤
      collectedSignedQuarticCodeSize source := by
    unfold collectedSignedQuarticCodeSize
    omega
  calc
    source.targetObjectSize ≤
        (source.coordinateCount + source.coefficientL1 + 1) *
          (source.coefficientL1 + 1) := hLeft
    _ ≤ collectedSignedQuarticCodeSize source *
          collectedSignedQuarticCodeSize source := by
      exact Nat.mul_le_mul_left _ hRight
    _ = collectedSignedQuarticCodeSize source ^ 2 := by ring

/-- Every project-specific step of the sign-oriented binary-tag compiler,
including correctness and output size, is packaged in this reduction object. -/
def collectedQuarticToDuplicateFreeOneToFiveReduction :
    PolynomialSizeManyOneReduction
      collectedSignedQuarticUniversalNonnegativity
      duplicateFreeOneToFiveUniversalOrder where
  map := CollectedSignedQuarticCode.toOneToFiveOrderCode
  correct := CollectedSignedQuarticCode.binaryTag_universalOrder_iff
  coefficient := 1
  degree := 2
  coefficient_positive := by norm_num
  size_bound := by
    intro source
    rw [source.compiledDecisionSize_eq]
    change source.targetObjectSize ≤
      1 * collectedSignedQuarticCodeSize source ^ 2
    simpa using source.targetObjectSize_le_sourceSize_sq

/-! ## Polynomial-source interface for the ETR strictifier -/

def BoundedQuarticIntegerPolynomialCode.universallyNonnegative
    (input : BoundedQuarticIntegerPolynomialCode) : Prop :=
  ∀ point : Fin input.coordinateCount → ℝ,
    IsPositiveUnitCubePoint point →
      0 ≤ MvPolynomial.eval₂ (Int.castRingHom ℝ) point input.polynomial

def boundedQuarticIntegerPolynomialCodeSize
    (input : BoundedQuarticIntegerPolynomialCode) : ℕ :=
  input.coordinateCount + coefficientL1 input.polynomial + 1

def boundedQuarticIntegerUniversalNonnegativity : EncodedDecisionProblem where
  Instance := BoundedQuarticIntegerPolynomialCode
  accepts := BoundedQuarticIntegerPolynomialCode.universallyNonnegative
  size := boundedQuarticIntegerPolynomialCodeSize
  size_positive := by
    intro input
    unfold boundedQuarticIntegerPolynomialCodeSize
    omega

theorem BoundedQuarticIntegerPolynomialCode.toCollected_universal_iff
    (input : BoundedQuarticIntegerPolynomialCode) :
    input.toCollected.universallyNonnegative ↔
      input.universallyNonnegative := by
  unfold CollectedSignedQuarticCode.universallyNonnegative
    BoundedQuarticIntegerPolynomialCode.universallyNonnegative
  apply forall_congr'
  intro point
  apply forall_congr'
  intro hPoint
  rw [input.toCollected_sourceValue]

theorem BoundedQuarticIntegerPolynomialCode.toCollected_size_eq
    (input : BoundedQuarticIntegerPolynomialCode) :
    collectedSignedQuarticUniversalNonnegativity.size input.toCollected =
      boundedQuarticIntegerUniversalNonnegativity.size input := by
  change collectedSignedQuarticCodeSize input.toCollected =
    boundedQuarticIntegerPolynomialCodeSize input
  unfold collectedSignedQuarticCodeSize
    boundedQuarticIntegerPolynomialCodeSize
  rw [input.toCollected_coefficientL1]
  rfl

def boundedQuarticIntegerToCollectedReduction :
    PolynomialSizeManyOneReduction
      boundedQuarticIntegerUniversalNonnegativity
      collectedSignedQuarticUniversalNonnegativity where
  map := BoundedQuarticIntegerPolynomialCode.toCollected
  correct := BoundedQuarticIntegerPolynomialCode.toCollected_universal_iff
  coefficient := 1
  degree := 1
  coefficient_positive := by norm_num
  size_bound := by
    intro input
    rw [input.toCollected_size_eq]
    simp

/-- Complete local semantic/output-size reduction from a bounded integer
quartic to the concrete duplicate-free `{1,…,5}` MaxEnt named-order
instance. -/
def boundedQuarticIntegerToDuplicateFreeOneToFiveReduction :
    PolynomialSizeManyOneReduction
      boundedQuarticIntegerUniversalNonnegativity
      duplicateFreeOneToFiveUniversalOrder :=
  boundedQuarticIntegerToCollectedReduction.trans
    collectedQuarticToDuplicateFreeOneToFiveReduction

/-! ## Constructive bounded-ETR strictifier composition -/

/-- The canonical bounded-ETR strictifier as a polynomial source with a proved
degree bound for collection and binary tagging. -/
def boundedETRStrictifierQuarticCode
    (problem : BoundedETRINVInstance) (m : ℕ) :
    BoundedQuarticIntegerPolynomialCode where
  coordinateCount := problem.variableCount + m
  polynomial := etrStrictifierPolynomialFin problem m
  totalDegree_le_four :=
    etrStrictifierPolynomialFin_totalDegree_le_four problem m

/-- Final duplicate-free `{1,…,5}` row-language target compiled directly
from a bounded-ETR instance and a declared contraction length. -/
def compileBoundedETRINVToDuplicateFreeOneToFive
    (problem : BoundedETRINVInstance) (m : ℕ) :
    DuplicateFreeOneToFiveOrderCode :=
  (boundedETRStrictifierQuarticCode problem m).toCollected.toOneToFiveOrderCode

theorem boundedETRStrictifierQuarticCode_sourceValue
    (problem : BoundedETRINVInstance) (m : ℕ)
    (point : Fin (problem.variableCount + m) → ℝ) :
    (boundedETRStrictifierQuarticCode problem m).toCollected.sourceValue point =
      contractionStrictifier problem.sourceResidualSum m
        (strictifierSourceActivity problem m
          (strictifierSumPointOfFin problem m point))
        (strictifierChainFromTail
          (strictifierTailActivity problem m
            (strictifierSumPointOfFin problem m point))) := by
  rw [BoundedQuarticIntegerPolynomialCode.toCollected_sourceValue]
  exact eval_etrStrictifierPolynomialFin problem m point

/-- Exact inherited coefficient-mass bound before the tag stage. -/
theorem boundedETRStrictifierQuarticCode_coefficientL1_le
    (problem : BoundedETRINVInstance) (m : ℕ) :
    (boundedETRStrictifierQuarticCode problem m).toCollected.coefficientL1 ≤
      800 * problem.equationCount + 9 * m ^ 2 + 2 := by
  rw [BoundedQuarticIntegerPolynomialCode.toCollected_coefficientL1]
  exact etrStrictifierPolynomialFin_coefficientL1_le problem m

/-- The compiled target emits no more rows than the exact strictifier
coefficient-mass envelope. -/
theorem compileBoundedETRINV_targetRowCount_le
    (problem : BoundedETRINVInstance) (m : ℕ) :
    (compileBoundedETRINVToDuplicateFreeOneToFive problem m).positiveRows.card +
        (compileBoundedETRINVToDuplicateFreeOneToFive problem m).negativeRows.card ≤
      800 * problem.equationCount + 9 * m ^ 2 + 2 := by
  change
    (boundedETRStrictifierQuarticCode problem m).toCollected.positiveRows.card +
        (boundedETRStrictifierQuarticCode problem m).toCollected.negativeRows.card ≤ _
  rw [CollectedSignedQuarticCode.target_row_count]
  exact boundedETRStrictifierQuarticCode_coefficientL1_le problem m

/-- The fresh binary-tag block is bounded by the same polynomial envelope. -/
theorem compileBoundedETRINV_tagDimension_le
    (problem : BoundedETRINVInstance) (m : ℕ) :
    (boundedETRStrictifierQuarticCode problem m).toCollected.tagDimension ≤
      800 * problem.equationCount + 9 * m ^ 2 + 2 := by
  exact (CollectedSignedQuarticCode.tagDimension_le_coefficientL1 _).trans
    (boundedETRStrictifierQuarticCode_coefficientL1_le problem m)

/-- Exact end-to-end strict-witness transport.  The forward direction uses
the strictifier witness and the all-one tag embedding; the reverse direction
projects an arbitrary target counterexample through sign dominance and then
uses the compact-gap theorem. -/
theorem boundedETRINV_satisfiable_iff_compiled_negativeWitness
    (problem : BoundedETRINVInstance) (m : ℕ) (gap : ℝ)
    (hGapIfNoZero :
      (¬ ∃ source, problem.IsCubePoint source ∧
          problem.sourceResidualSum source = 0) →
        ∀ source, problem.IsCubePoint source →
          gap ≤ problem.sourceResidualSum source)
    (hTerminal : 2 * exactContractionChain m ^ 2 < gap) :
    problem.Satisfiable ↔
      ∃ targetPoint : Fin
          ((problem.variableCount + m) +
            (boundedETRStrictifierQuarticCode problem m).toCollected.tagDimension) → ℝ,
        IsPositiveUnitCubePoint targetPoint ∧
        duplicateFreeOneToFiveOrderMargin
          (boundedETRStrictifierQuarticCode problem m).toCollected.positiveRows
          (boundedETRStrictifierQuarticCode problem m).toCollected.negativeRows
          targetPoint < 0 := by
  let polynomialCode := boundedETRStrictifierQuarticCode problem m
  let collected := polynomialCode.toCollected
  have hStrictifier :=
    boundedETRINV_satisfiable_iff_strictifier_negative_positiveCube
      problem m gap hGapIfNoZero hTerminal
  constructor
  · intro hSatisfiable
    obtain ⟨point, hPoint, hNegative⟩ := hStrictifier.mp hSatisfiable
    have hCollectedNegative : collected.sourceValue point < 0 := by
      rw [BoundedQuarticIntegerPolynomialCode.toCollected_sourceValue]
      exact hNegative
    exact collected.negativeSourceWitness_to_target hPoint hCollectedNegative
  · rintro ⟨targetPoint, hTargetPoint, hTargetNegative⟩
    let oldPoint : Fin (problem.variableCount + m) → ℝ :=
      collected.oldActivityPart targetPoint
    have hOldPoint : IsPositiveUnitCubePoint oldPoint :=
      collected.oldActivityPart_positiveUnitCube hTargetPoint
    have hCollectedNegative : collected.sourceValue oldPoint < 0 :=
      collected.negativeTargetWitness_to_source
        hTargetPoint hTargetNegative
    apply hStrictifier.mpr
    refine ⟨oldPoint, hOldPoint, ?_⟩
    have hEvaluation :
        (etrStrictifierPolynomialFin problem m).eval₂
            (Int.castRingHom ℝ) oldPoint =
          collected.sourceValue oldPoint := by
      symm
      exact BoundedQuarticIntegerPolynomialCode.toCollected_sourceValue
        polynomialCode oldPoint
    rw [hEvaluation]
    exact hCollectedNegative

/-- Universal named order in the compiled target is exactly source
unsatisfiability. -/
theorem boundedETRINV_compiled_universalOrder_iff_not_satisfiable
    (problem : BoundedETRINVInstance) (m : ℕ) (gap : ℝ)
    (hGapIfNoZero :
      (¬ ∃ source, problem.IsCubePoint source ∧
          problem.sourceResidualSum source = 0) →
        ∀ source, problem.IsCubePoint source →
          gap ≤ problem.sourceResidualSum source)
    (hTerminal : 2 * exactContractionChain m ^ 2 < gap) :
    (compileBoundedETRINVToDuplicateFreeOneToFive problem m).universalOrder ↔
      ¬ problem.Satisfiable := by
  let collected := (boundedETRStrictifierQuarticCode problem m).toCollected
  have hWitness := boundedETRINV_satisfiable_iff_compiled_negativeWitness
    problem m gap hGapIfNoZero hTerminal
  change
    (∀ targetPoint : Fin
        ((problem.variableCount + m) + collected.tagDimension) → ℝ,
      IsPositiveUnitCubePoint targetPoint →
        0 ≤ duplicateFreeOneToFiveOrderMargin collected.positiveRows
          collected.negativeRows targetPoint) ↔
      ¬ problem.Satisfiable
  constructor
  · intro hUniversal hSatisfiable
    obtain ⟨targetPoint, hPoint, hNegative⟩ := hWitness.mp hSatisfiable
    exact (not_lt_of_ge (hUniversal targetPoint hPoint)) hNegative
  · intro hUnsatisfiable targetPoint hPoint
    apply le_of_not_gt
    intro hNegative
    exact hUnsatisfiable (hWitness.mpr ⟨targetPoint, hPoint, hNegative⟩)

/-- Phonological reading of the end-to-end reduction: source
unsatisfiability is equivalent to the all-weight named-candidate probability
order in the two concrete complete MaxEnt ledgers. -/
theorem boundedETRINV_allWeightProbabilityOrder_iff_not_satisfiable
    (problem : BoundedETRINVInstance) (m : ℕ) (gap : ℝ)
    (hGapIfNoZero :
      (¬ ∃ source, problem.IsCubePoint source ∧
          problem.sourceResidualSum source = 0) →
        ∀ source, problem.IsCubePoint source →
          gap ≤ problem.sourceResidualSum source)
    (hTerminal : 2 * exactContractionChain m ^ 2 < gap) :
    (∀ weight : Fin
        ((boundedETRStrictifierQuarticCode problem m).toCollected.coordinateCount +
          (boundedETRStrictifierQuarticCode problem m).toCollected.tagDimension) → ℝ,
      IsNonnegativeWeight weight →
      exponentialCandidateProbability
          (boundedETRStrictifierQuarticCode problem m).toCollected.positiveLedger
          weight none ≤
        exponentialCandidateProbability
          (boundedETRStrictifierQuarticCode problem m).toCollected.negativeLedger
          weight none) ↔
      ¬ problem.Satisfiable := by
  rw [← CollectedSignedQuarticCode.universalOrder_iff_allWeightProbabilityOrder]
  exact boundedETRINV_compiled_universalOrder_iff_not_satisfiable
    problem m gap hGapIfNoZero hTerminal

/-- Explicit target-table size bound before conversion to a monomial bound in
the source encoding size. -/
theorem compileBoundedETRINV_targetObjectSize_le
    (problem : BoundedETRINVInstance) (m : ℕ) :
    (boundedETRStrictifierQuarticCode problem m).toCollected.targetObjectSize ≤
      (problem.variableCount + m +
          (800 * problem.equationCount + 9 * m ^ 2 + 2) + 1) *
        ((800 * problem.equationCount + 9 * m ^ 2 + 2) + 1) := by
  let collected := (boundedETRStrictifierQuarticCode problem m).toCollected
  let bound := 800 * problem.equationCount + 9 * m ^ 2 + 2
  have hMass : collected.coefficientL1 ≤ bound :=
    boundedETRStrictifierQuarticCode_coefficientL1_le problem m
  calc
    collected.targetObjectSize ≤
        (collected.coordinateCount + collected.coefficientL1 + 1) *
          (collected.coefficientL1 + 1) :=
      collected.targetObjectSize_le
    _ ≤ (problem.variableCount + m + bound + 1) * (bound + 1) := by
      apply Nat.mul_le_mul
      · exact Nat.add_le_add_right
          (Nat.add_le_add_left hMass (problem.variableCount + m)) 1
      · exact Nat.add_le_add_right hMass 1

/-! ## Ordinary bounded-ETR source and canonical compact-gap compiler -/

/-- Abstract size used for ordinary bounded ETR-INV instances.  The equations
and variables are counted explicitly.  A conventional machine-complexity
interpretation additionally requires an effective encoding/runtime bridge;
that bridge is not represented by this definition. -/
def boundedETRINVCodeSize (problem : BoundedETRINVInstance) : ℕ :=
  problem.variableCount + problem.equationCount + 1

/-- The ordinary bounded ETR-INV unsatisfiability language. -/
def boundedETRINVUnsatisfiability : EncodedDecisionProblem where
  Instance := BoundedETRINVInstance
  accepts := fun problem => ¬ problem.Satisfiable
  size := boundedETRINVCodeSize
  size_positive := by
    intro problem
    unfold boundedETRINVCodeSize
    omega

/-- Exact compact-gap interface used by the compiler.  `gapExponent` is the
binary integer `B` in the lower bound `2⁻ᴮ`; only its bit length controls the
contraction-chain length.  The proof payload is logical evidence, not input
data.  `chainLength_bound` records the conventional polynomial bit bound in
the ordinary bounded-ETR encoding size. -/
structure CompactGapFoundation where
  gapExponent : BoundedETRINVInstance → ℕ
  gapIfNoZero : ∀ problem,
    (¬ ∃ source, problem.IsCubePoint source ∧
        problem.sourceResidualSum source = 0) →
      ∀ source, problem.IsCubePoint source →
        dyadicCompactGap (gapExponent problem) ≤
          problem.sourceResidualSum source
  chainLengthCoefficient : ℕ
  chainLengthDegree : ℕ
  chainLengthCoefficient_positive : 0 < chainLengthCoefficient
  chainLength_bound : ∀ problem,
    Nat.size (gapExponent problem + 3) ≤
      chainLengthCoefficient *
        boundedETRINVCodeSize problem ^ chainLengthDegree

/-- Canonical contraction length: the binary length of `B + 3`, never the
numeric value of the gap exponent. -/
def CompactGapFoundation.chainLength
    (foundation : CompactGapFoundation)
    (problem : BoundedETRINVInstance) : ℕ :=
  Nat.size (foundation.gapExponent problem + 3)

/-- The canonical bit-length choice is sufficient for the strictifier's
terminal inequality. -/
theorem CompactGapFoundation.chainLength_condition
    (foundation : CompactGapFoundation)
    (problem : BoundedETRINVInstance) :
    foundation.gapExponent problem + 3 <
      2 ^ (foundation.chainLength problem + 1) := by
  let exponent := foundation.gapExponent problem + 3
  have hStrict : exponent < 2 ^ Nat.size exponent :=
    Nat.lt_size_self exponent
  have hMonotone : 2 ^ Nat.size exponent ≤
      2 ^ (Nat.size exponent + 1) := by
    rw [pow_succ]
    have hPositive : 0 < 2 ^ Nat.size exponent := by positivity
    omega
  simpa [CompactGapFoundation.chainLength, exponent] using
    hStrict.trans_le hMonotone

/-- Collected strictifier polynomial selected by the compact-gap interface. -/
def CompactGapFoundation.collectedCode
    (foundation : CompactGapFoundation)
    (problem : BoundedETRINVInstance) : CollectedSignedQuarticCode :=
  (boundedETRStrictifierQuarticCode problem
    (foundation.chainLength problem)).toCollected

/-- Canonical compiler on ordinary bounded-ETR instances. -/
def compileGapProvedBoundedETRINV
    (foundation : CompactGapFoundation)
    (problem : BoundedETRINVInstance) :
    DuplicateFreeOneToFiveOrderCode :=
  (foundation.collectedCode problem).toOneToFiveOrderCode

/-- Exact semantic correctness of the canonical ordinary-source compiler. -/
theorem compileGapProvedBoundedETRINV_correct
    (foundation : CompactGapFoundation)
    (problem : BoundedETRINVInstance) :
    duplicateFreeOneToFiveUniversalOrder.accepts
        (compileGapProvedBoundedETRINV foundation problem) ↔
      boundedETRINVUnsatisfiability.accepts problem := by
  simpa [compileGapProvedBoundedETRINV,
    CompactGapFoundation.collectedCode,
    compileBoundedETRINVToDuplicateFreeOneToFive,
    duplicateFreeOneToFiveUniversalOrder,
    boundedETRINVUnsatisfiability] using
    boundedETRINV_compiled_universalOrder_iff_not_satisfiable
      problem (foundation.chainLength problem)
        (dyadicCompactGap (foundation.gapExponent problem))
        (foundation.gapIfNoZero problem)
        (exactContractionChain_terminal_lt_dyadicGap
          (foundation.chainLength problem)
          (foundation.gapExponent problem)
          (foundation.chainLength_condition problem))

/-- Exact transport of strict counterexamples for the canonical compiler. -/
theorem compileGapProvedBoundedETRINV_negativeWitness_iff
    (foundation : CompactGapFoundation)
    (problem : BoundedETRINVInstance) :
    problem.Satisfiable ↔
      ∃ targetPoint : Fin
          ((problem.variableCount + foundation.chainLength problem) +
            (boundedETRStrictifierQuarticCode problem
              (foundation.chainLength problem)).toCollected.tagDimension) → ℝ,
        IsPositiveUnitCubePoint targetPoint ∧
        duplicateFreeOneToFiveOrderMargin
          (boundedETRStrictifierQuarticCode problem
            (foundation.chainLength problem)).toCollected.positiveRows
          (boundedETRStrictifierQuarticCode problem
            (foundation.chainLength problem)).toCollected.negativeRows
          targetPoint < 0 := by
  exact boundedETRINV_satisfiable_iff_compiled_negativeWitness
    problem (foundation.chainLength problem)
      (dyadicCompactGap (foundation.gapExponent problem))
      (foundation.gapIfNoZero problem)
      (exactContractionChain_terminal_lt_dyadicGap
        (foundation.chainLength problem)
        (foundation.gapExponent problem)
        (foundation.chainLength_condition problem))

/-- Canonical phonological reading: at every nonnegative real weight vector,
the named candidate in the positive ledger is no more probable than the named
candidate in the negative ledger exactly when the source is unsatisfiable. -/
theorem compileGapProvedBoundedETRINV_allWeightProbabilityOrder_iff
    (foundation : CompactGapFoundation)
    (problem : BoundedETRINVInstance) :
    (∀ weight : Fin
        ((boundedETRStrictifierQuarticCode problem
            (foundation.chainLength problem)).toCollected.coordinateCount +
          (boundedETRStrictifierQuarticCode problem
            (foundation.chainLength problem)).toCollected.tagDimension) → ℝ,
      IsNonnegativeWeight weight →
      exponentialCandidateProbability
          (boundedETRStrictifierQuarticCode problem
            (foundation.chainLength problem)).toCollected.positiveLedger
          weight none ≤
        exponentialCandidateProbability
          (boundedETRStrictifierQuarticCode problem
            (foundation.chainLength problem)).toCollected.negativeLedger
          weight none) ↔
      ¬ problem.Satisfiable := by
  exact boundedETRINV_allWeightProbabilityOrder_iff_not_satisfiable
    problem (foundation.chainLength problem)
      (dyadicCompactGap (foundation.gapExponent problem))
      (foundation.gapIfNoZero problem)
      (exactContractionChain_terminal_lt_dyadicGap
        (foundation.chainLength problem)
        (foundation.gapExponent problem)
        (foundation.chainLength_condition problem))

/-- Coefficient in the explicit monomial output-size bound. -/
def CompactGapFoundation.outputCoefficient
    (foundation : CompactGapFoundation) : ℕ :=
  (804 + foundation.chainLengthCoefficient +
      9 * foundation.chainLengthCoefficient ^ 2) *
    (803 + 9 * foundation.chainLengthCoefficient ^ 2)

/-- Degree in the explicit monomial output-size bound. -/
def CompactGapFoundation.outputDegree
    (foundation : CompactGapFoundation) : ℕ :=
  (foundation.chainLengthDegree * 2 + 2) * 2

theorem CompactGapFoundation.outputCoefficient_positive
    (foundation : CompactGapFoundation) :
    0 < foundation.outputCoefficient := by
  unfold CompactGapFoundation.outputCoefficient
  positivity

/-- Full target-table size is polynomial in the ordinary bounded-ETR source
size.  This proof counts the strictifier coordinates, coefficient copies, and
binary tags; the gap exponent enters only through its polynomially bounded
binary length. -/
theorem compileGapProvedBoundedETRINV_size_le
    (foundation : CompactGapFoundation)
    (problem : BoundedETRINVInstance) :
    duplicateFreeOneToFiveUniversalOrder.size
        (compileGapProvedBoundedETRINV foundation problem) ≤
      foundation.outputCoefficient *
        boundedETRINVCodeSize problem ^ foundation.outputDegree := by
  let sourceSize := boundedETRINVCodeSize problem
  let chainLength := foundation.chainLength problem
  let coefficient := foundation.chainLengthCoefficient
  let degree := foundation.chainLengthDegree
  let power := sourceSize ^ (degree * 2 + 2)
  let massBound := 800 * problem.equationCount +
    9 * chainLength ^ 2 + 2
  have hSourcePositive : 0 < sourceSize := by
    dsimp [sourceSize, boundedETRINVCodeSize]
    omega
  have hSourceOne : 1 ≤ sourceSize := hSourcePositive
  have hVariable : problem.variableCount ≤ sourceSize := by
    dsimp [sourceSize, boundedETRINVCodeSize]
    omega
  have hEquation : problem.equationCount ≤ sourceSize := by
    dsimp [sourceSize, boundedETRINVCodeSize]
    omega
  have hPowerOne : 1 ≤ power := by
    dsimp [power]
    exact one_le_pow₀ hSourceOne
  have hSourcePower : sourceSize ≤ power := by
    calc
      sourceSize = sourceSize ^ 1 := by simp
      _ ≤ sourceSize ^ (degree * 2 + 2) := by
        exact pow_le_pow_right' hSourceOne (by omega)
      _ = power := rfl
  have hDegreePower : sourceSize ^ degree ≤ power := by
    dsimp [power]
    exact pow_le_pow_right' hSourceOne (by omega)
  have hChain : chainLength ≤ coefficient * sourceSize ^ degree := by
    simpa only [CompactGapFoundation.chainLength, chainLength,
      coefficient, degree, sourceSize] using
      foundation.chainLength_bound problem
  have hChainPower : chainLength ≤ coefficient * power :=
    hChain.trans (Nat.mul_le_mul_left coefficient hDegreePower)
  have hChainSquare : chainLength ^ 2 ≤ coefficient ^ 2 * power := by
    calc
      chainLength ^ 2 ≤
          (coefficient * sourceSize ^ degree) ^ 2 :=
        pow_le_pow_left' hChain 2
      _ = coefficient ^ 2 * sourceSize ^ (degree * 2) := by
        rw [mul_pow, pow_mul]
      _ ≤ coefficient ^ 2 * power := by
        apply Nat.mul_le_mul_left
        dsimp [power]
        exact pow_le_pow_right' hSourceOne (by omega)
  have hMass : massBound ≤
      (802 + 9 * coefficient ^ 2) * power := by
    calc
      massBound ≤
          800 * power + 9 * (coefficient ^ 2 * power) + 2 * power := by
        dsimp [massBound]
        exact Nat.add_le_add
          (Nat.add_le_add
            (Nat.mul_le_mul_left 800 (hEquation.trans hSourcePower))
            (Nat.mul_le_mul_left 9 hChainSquare))
          (by omega)
      _ = (802 + 9 * coefficient ^ 2) * power := by ring
  have hLeft : problem.variableCount + chainLength + massBound + 1 ≤
      (804 + coefficient + 9 * coefficient ^ 2) * power := by
    calc
      problem.variableCount + chainLength + massBound + 1 ≤
          power + coefficient * power +
            (802 + 9 * coefficient ^ 2) * power + power := by
        exact Nat.add_le_add
          (Nat.add_le_add
            (Nat.add_le_add (hVariable.trans hSourcePower) hChainPower)
            hMass)
          hPowerOne
      _ = (804 + coefficient + 9 * coefficient ^ 2) * power := by ring
  have hRight : massBound + 1 ≤
      (803 + 9 * coefficient ^ 2) * power := by
    calc
      massBound + 1 ≤
          (802 + 9 * coefficient ^ 2) * power + power :=
        Nat.add_le_add hMass hPowerOne
      _ = (803 + 9 * coefficient ^ 2) * power := by ring
  calc
    duplicateFreeOneToFiveUniversalOrder.size
        (compileGapProvedBoundedETRINV foundation problem) =
        ((boundedETRStrictifierQuarticCode problem
          chainLength).toCollected).targetObjectSize := by
      rfl
    _ ≤ (problem.variableCount + chainLength + massBound + 1) *
          (massBound + 1) := by
      exact compileBoundedETRINV_targetObjectSize_le problem chainLength
    _ ≤ ((804 + coefficient + 9 * coefficient ^ 2) * power) *
          ((803 + 9 * coefficient ^ 2) * power) :=
      Nat.mul_le_mul hLeft hRight
    _ = foundation.outputCoefficient *
          boundedETRINVCodeSize problem ^ foundation.outputDegree := by
      simp only [CompactGapFoundation.outputCoefficient,
        CompactGapFoundation.outputDegree]
      dsimp [coefficient, degree, sourceSize, power]
      rw [pow_mul]
      ring

/-- The exact semantic ordinary-source compiler packaged as a proof-bearing
polynomial-size many-one reduction. -/
def boundedETRINVToDuplicateFreeOneToFiveReduction
    (foundation : CompactGapFoundation) :
    PolynomialSizeManyOneReduction
      boundedETRINVUnsatisfiability
      duplicateFreeOneToFiveUniversalOrder where
  map := compileGapProvedBoundedETRINV foundation
  correct := compileGapProvedBoundedETRINV_correct foundation
  coefficient := foundation.outputCoefficient
  degree := foundation.outputDegree
  coefficient_positive := foundation.outputCoefficient_positive
  size_bound := compileGapProvedBoundedETRINV_size_le foundation

/-- Predicate form of the concrete unit-mass and named-zero guarantees. -/
def CollectedSignedQuarticCode.compiledLedgersUnitMassZeroNamed
    (source : CollectedSignedQuarticCode) : Prop :=
  ((∀ candidate, source.positiveLedger.baseMass candidate = 1) ∧
      source.positiveLedger.row none = 0) ∧
    ((∀ candidate, source.negativeLedger.baseMass candidate = 1) ∧
      source.negativeLedger.row none = 0)

/-- Predicate form of the actual-violation row bounds. -/
def CollectedSignedQuarticCode.compiledLedgersRowBounded
    (source : CollectedSignedQuarticCode) : Prop :=
  (∀ alternative : {row // row ∈ source.positiveRows},
      ∀ coordinate,
        1 ≤ source.positiveLedger.row (some alternative) coordinate ∧
        source.positiveLedger.row (some alternative) coordinate ≤ 5) ∧
    (∀ alternative : {row // row ∈ source.negativeRows},
      ∀ coordinate,
        1 ≤ source.negativeLedger.row (some alternative) coordinate ∧
        source.negativeLedger.row (some alternative) coordinate ≤ 5)

/-- Predicate form of within-ledger and cross-ledger row distinctness. -/
def CollectedSignedQuarticCode.compiledLedgersGloballyDistinct
    (source : CollectedSignedQuarticCode) : Prop :=
  Function.Injective
      (fun alternative : {row // row ∈ source.positiveRows} =>
        source.positiveLedger.row (some alternative)) ∧
    Function.Injective
      (fun alternative : {row // row ∈ source.negativeRows} =>
        source.negativeLedger.row (some alternative)) ∧
    (∀ positive : {row // row ∈ source.positiveRows},
      ∀ negative : {row // row ∈ source.negativeRows},
        source.positiveLedger.row (some positive) ≠
          source.negativeLedger.row (some negative))

/-- Machine-checkable record of every project-specific guarantee supplied by
the canonical compiler: source semantics, counterexample transport, concrete
ledger form, row bounds, global duplicate-freedom, and polynomial size. -/
structure BoundedETRINVCompilationProof
    (foundation : CompactGapFoundation)
    (problem : BoundedETRINVInstance) : Prop where
  universalOrder_iff_unsatisfiable :
    (compileGapProvedBoundedETRINV foundation problem).universalOrder ↔
      ¬ problem.Satisfiable
  negativeWitness_iff_satisfiable :
    problem.Satisfiable ↔
      ∃ point : Fin
          ((problem.variableCount + foundation.chainLength problem) +
            (boundedETRStrictifierQuarticCode problem
              (foundation.chainLength problem)).toCollected.tagDimension) → ℝ,
        IsPositiveUnitCubePoint point ∧
        duplicateFreeOneToFiveOrderMargin
          (boundedETRStrictifierQuarticCode problem
            (foundation.chainLength problem)).toCollected.positiveRows
          (boundedETRStrictifierQuarticCode problem
            (foundation.chainLength problem)).toCollected.negativeRows
          point < 0
  unitMass_zeroNamed :
    (foundation.collectedCode problem).compiledLedgersUnitMassZeroNamed
  ledgerRowBounds :
    (foundation.collectedCode problem).compiledLedgersRowBounded
  globalDistinctness :
    (foundation.collectedCode problem).compiledLedgersGloballyDistinct
  oldAndTagRowBounds :
    ∀ {row}, row ∈
        (foundation.collectedCode problem).positiveRows ∪
          (foundation.collectedCode problem).negativeRows →
      (∀ coordinate : Fin
          (foundation.collectedCode problem).coordinateCount,
        1 ≤ (row (finSumFinEquiv (Sum.inl coordinate))).val + 1 ∧
        (row (finSumFinEquiv (Sum.inl coordinate))).val + 1 ≤ 5) ∧
      (∀ coordinate : Fin
          (foundation.collectedCode problem).tagDimension,
        1 ≤ (row (finSumFinEquiv (Sum.inr coordinate))).val + 1 ∧
        (row (finSumFinEquiv (Sum.inr coordinate))).val + 1 ≤ 3)
  targetRowCount_bound :
    (boundedETRStrictifierQuarticCode problem
        (foundation.chainLength problem)).toCollected.positiveRows.card +
      (boundedETRStrictifierQuarticCode problem
        (foundation.chainLength problem)).toCollected.negativeRows.card ≤
      800 * problem.equationCount +
        9 * foundation.chainLength problem ^ 2 + 2
  tagDimension_bound :
    (boundedETRStrictifierQuarticCode problem
        (foundation.chainLength problem)).toCollected.tagDimension ≤
      800 * problem.equationCount +
        9 * foundation.chainLength problem ^ 2 + 2
  targetSize_bound :
    duplicateFreeOneToFiveUniversalOrder.size
        (compileGapProvedBoundedETRINV foundation problem) ≤
      foundation.outputCoefficient *
        boundedETRINVCodeSize problem ^ foundation.outputDegree

/-- Earlier binary-tag semantic compiler content retained as a supporting
comparison object.  The ordinary bounded-ETR compiler is exact, explicit,
duplicate-free, bounded to actual violations `{1,…,5}`, and polynomial in the
ordinary source size under the declared compact-gap foundation.  The
registered `MAX-G3.REDUCTION.03` instead points to the deterministic one-hot
compiler.  This result does not by itself assert an executable polynomial-time
realization in a named machine model. -/
theorem max_g3_reduction_03_semanticCompiler
    (foundation : CompactGapFoundation)
    (problem : BoundedETRINVInstance) :
    BoundedETRINVCompilationProof foundation problem := by
  refine ⟨?_, ?_,
    (foundation.collectedCode problem).compiledLedgers_unitMass_zeroNamed,
    (foundation.collectedCode problem).compiledLedgers_rowBounds,
    (foundation.collectedCode problem).compiledLedgers_globalDistinctness,
    ?_, compileBoundedETRINV_targetRowCount_le problem
      (foundation.chainLength problem),
    compileBoundedETRINV_tagDimension_le problem
      (foundation.chainLength problem),
    compileGapProvedBoundedETRINV_size_le foundation problem⟩
  · simpa [duplicateFreeOneToFiveUniversalOrder,
      boundedETRINVUnsatisfiability] using
      compileGapProvedBoundedETRINV_correct foundation problem
  · exact compileGapProvedBoundedETRINV_negativeWitness_iff
      foundation problem
  · intro row hRow
    exact (foundation.collectedCode problem).every_target_row_bounds hRow

/-! ## Conditional class transfer under the local semantic-size relation -/

/-- Premises consumed by the local class-transfer result: ordinary bounded
ETR-INV unsatisfiability is complete for the selected class under the imported
semantic-size reduction relation, and the explicitly typed target language
belongs to that class.  This structure does not assert standard Turing-machine
computability or running-time bounds. -/
structure UniversalRealSemanticSizeFoundation
    (universalReal : EncodedDecisionClass) where
  boundedETRINVUnsatisfiability_complete :
    CompleteFor universalReal boundedETRINVUnsatisfiability
  duplicateFreeOneToFive_mem :
    universalReal duplicateFreeOneToFiveUniversalOrder

/-- Conditional class transfer for duplicate-free `{1,…,5}` named order under
the local semantic-size reduction relation.  A standard universal-real
completeness claim additionally requires an executable polynomial-time
realization theorem for the compiler and effective gap constructor. -/
theorem duplicateFreeOneToFive_semanticSize_complete
    {universalReal : EncodedDecisionClass}
    (complexity : UniversalRealSemanticSizeFoundation universalReal)
    (compactGap : CompactGapFoundation) :
    CompleteFor universalReal duplicateFreeOneToFiveUniversalOrder := by
  exact complete_of_complete_source
    complexity.boundedETRINVUnsatisfiability_complete
    complexity.duplicateFreeOneToFive_mem
    (boundedETRINVToDuplicateFreeOneToFiveReduction compactGap)

/-- Current-scope conditional conjunction under the semantic-size relation.
The `{1,2}` branch invokes its separately declared conventional foundation;
the `{1,…,5}` branch remains conditional on a standard executable complexity
bridge.  The registered `MAX-G4.COMPLEXITY.04` instead uses the proper-CNF
selector and `ExecutableCNFConventionalBoundary`. -/
theorem duplicateFreeSemanticSizeConditional
    {coNP universalReal : EncodedDecisionClass}
    (coNPFoundation : ConventionalCoNPFoundation coNP)
    (universalRealFoundation :
      UniversalRealSemanticSizeFoundation universalReal)
    (compactGap : CompactGapFoundation) :
    CompleteFor coNP duplicateFreeOneTwoUniversalOrder ∧
      CompleteFor universalReal duplicateFreeOneToFiveUniversalOrder := by
  exact ⟨duplicateFreeOneTwo_semanticSize_complete
      coNPFoundation,
    duplicateFreeOneToFive_semanticSize_complete
      universalRealFoundation compactGap⟩

end

end PhonologicalCalculus.MaxEnt
