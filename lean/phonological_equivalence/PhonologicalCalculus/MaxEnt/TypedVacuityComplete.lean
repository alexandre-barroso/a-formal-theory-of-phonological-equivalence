import PhonologicalCalculus.MaxEnt.ExactCore
import Mathlib

         

namespace PhonologicalCalculus.MaxEnt

open scoped Matrix

universe u v

noncomputable section

def NonnegativeVector {K : Type*} [Fintype K] (w : K → ℚ) : Prop :=
  ∀ k, 0 ≤ w k

def RawNonnegativeKernel {I K : Type*} [Fintype I] [Fintype K]
    (D : Matrix I K ℚ) : Prop :=
  ∃ w : K → ℚ, NonnegativeVector w ∧ w ≠ 0 ∧ D *ᵥ w = 0

def NormalizedNonnegativeKernel {I K : Type*} [Fintype I] [Fintype K]
    (D : Matrix I K ℚ) : Prop :=
  ∃ w : K → ℚ, NonnegativeVector w ∧ (∑ k, w k) = 1 ∧ D *ᵥ w = 0

def StrictlyPositiveRowSpace {I K : Type*} [Fintype I] [Fintype K]
    (D : Matrix I K ℚ) : Prop :=
  ∃ lam : I → ℚ, ∀ k, 0 < (D.transpose *ᵥ lam) k

def GordanStiemkeFoundation : Prop :=
  ∀ (I : Type u) (K : Type v) [Fintype I] [Fintype K] [Nonempty K]
    (D : Matrix I K ℚ),
    RawNonnegativeKernel D ∨ StrictlyPositiveRowSpace D

lemma exists_pos_coordinate_of_nonnegative_ne_zero
    {K : Type*} [Fintype K] {w : K → ℚ}
    (hw : NonnegativeVector w) (hne : w ≠ 0) :
    ∃ k, 0 < w k := by
  by_contra h
  push Not at h
  apply hne
  funext k
  exact le_antisymm (h k) (hw k)

theorem rawNonnegativeKernel_iff_normalized
    {I K : Type*} [Fintype I] [Fintype K] [Nonempty K]
    (D : Matrix I K ℚ) :
    RawNonnegativeKernel D ↔ NormalizedNonnegativeKernel D := by
  constructor
  · rintro ⟨w, hw, hne, hDw⟩
    obtain ⟨k0, hk0⟩ := exists_pos_coordinate_of_nonnegative_ne_zero hw hne
    let s : ℚ := ∑ k, w k
    have hs : 0 < s := by
      apply Finset.sum_pos'
      · intro k _
        exact hw k
      · exact ⟨k0, Finset.mem_univ k0, hk0⟩
    refine ⟨fun k => w k / s, ?_, ?_, ?_⟩
    · intro k
      exact div_nonneg (hw k) hs.le
    · rw [← Finset.sum_div]
      exact div_self hs.ne'
    · funext i
      have hi : (∑ x, D i x * w x) = 0 := by
        simpa [Matrix.mulVec, dotProduct] using congrFun hDw i
      simp only [Matrix.mulVec, dotProduct]
      calc
        ∑ x, D i x * (w x / s) = (∑ x, D i x * w x) / s := by
          simp only [div_eq_mul_inv, mul_assoc, Finset.sum_mul]
        _ = 0 := by rw [hi, zero_div]
  · rintro ⟨w, hw, hsum, hDw⟩
    refine ⟨w, hw, ?_, hDw⟩
    intro hw0
    subst w
    simpa using hsum

theorem normalizedKernel_disjoint_positiveRowSpace
    {I K : Type*} [Fintype I] [Fintype K]
    (D : Matrix I K ℚ) :
    ¬ (NormalizedNonnegativeKernel D ∧ StrictlyPositiveRowSpace D) := by
  rintro ⟨⟨w, hw, hsum, hDw⟩, ⟨lam, hlam⟩⟩
  have hwne : w ≠ 0 := by
    intro hw0
    subst w
    simpa using hsum
  obtain ⟨k0, hk0⟩ := exists_pos_coordinate_of_nonnegative_ne_zero hw hwne
  have hdotpos : 0 < w ⬝ᵥ (D.transpose *ᵥ lam) := by
    apply Finset.sum_pos'
    · intro k _
      exact mul_nonneg (hw k) (hlam k).le
    · exact ⟨k0, Finset.mem_univ k0, mul_pos hk0 (hlam k0)⟩
  have hdotzero : w ⬝ᵥ (D.transpose *ᵥ lam) = 0 := by
    rw [Matrix.dotProduct_transpose_mulVec D w lam, hDw]
    simp
  linarith

                   
theorem max_g5_gordan_02
    (foundation : GordanStiemkeFoundation.{u, v})
    {I : Type u} {K : Type v} [Fintype I] [Fintype K] [Nonempty K]
    (D : Matrix I K ℚ) :
    Xor (NormalizedNonnegativeKernel D) (StrictlyPositiveRowSpace D) := by
  have hdisjoint := normalizedKernel_disjoint_positiveRowSpace D
  rcases foundation I K D with hraw | hpos
  · left
    exact ⟨(rawNonnegativeKernel_iff_normalized D).1 hraw,
      fun hp => hdisjoint ⟨(rawNonnegativeKernel_iff_normalized D).1 hraw, hp⟩⟩
  · right
    exact ⟨hpos, fun hnorm => hdisjoint ⟨hnorm, hpos⟩⟩

def rationalHarmonic {I K : Type*} [Fintype K]
    (v : Matrix I K ℚ) (w : K → ℚ) (i : I) : ℚ :=
  ∑ k, w k * v i k

def differenceMatrix {I K : Type*}
    (v : Matrix I K ℚ) (base : I) : Matrix I K ℚ :=
  fun i k => v i k - v base k

lemma differenceMatrix_mulVec_apply {I K : Type*} [Fintype K]
    (v : Matrix I K ℚ) (base : I) (w : K → ℚ) (i : I) :
    (differenceMatrix v base *ᵥ w) i =
      rationalHarmonic v w i - rationalHarmonic v w base := by
  simp only [differenceMatrix, rationalHarmonic, Matrix.mulVec, dotProduct]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

def finiteMaxEntNumerator {I K : Type*} [Fintype K]
    (v : Matrix I K ℚ) (w : K → ℚ) (i : I) : ℝ :=
  Real.exp (-((rationalHarmonic v w i : ℚ) : ℝ))

def finiteMaxEntNormalizer {I K : Type*} [Fintype I] [Fintype K]
    (v : Matrix I K ℚ) (w : K → ℚ) : ℝ :=
  ∑ i, finiteMaxEntNumerator v w i

def finiteMaxEntProbability {I K : Type*} [Fintype I] [Fintype K]
    (v : Matrix I K ℚ) (w : K → ℚ) (i : I) : ℝ :=
  finiteMaxEntNumerator v w i / finiteMaxEntNormalizer v w

lemma finiteMaxEntNormalizer_pos {I K : Type*} [Fintype I] [Nonempty I]
    [Fintype K] (v : Matrix I K ℚ) (w : K → ℚ) :
    0 < finiteMaxEntNormalizer v w := by
  apply Finset.sum_pos
  · intro i _
    exact Real.exp_pos _
  · exact Finset.univ_nonempty

lemma finiteMaxEntProbability_le_iff_harmonic_ge
    {I K : Type*} [Fintype I] [Nonempty I] [Fintype K]
    (v : Matrix I K ℚ) (w : K → ℚ) (i j : I) :
    finiteMaxEntProbability v w i ≤ finiteMaxEntProbability v w j ↔
      rationalHarmonic v w j ≤ rationalHarmonic v w i := by
  rw [finiteMaxEntProbability, finiteMaxEntProbability,
    div_le_div_iff_of_pos_right (finiteMaxEntNormalizer_pos v w)]
  simp only [finiteMaxEntNumerator, Real.exp_le_exp]
  norm_cast
  exact neg_le_neg_iff

def AllMutualProbabilityOrders {I K : Type*} [Fintype I] [Fintype K]
    (v : Matrix I K ℚ) (w : K → ℚ) : Prop :=
  ∀ i j, finiteMaxEntProbability v w i ≤ finiteMaxEntProbability v w j

def AllCategoricalEventsEmpty {I A : Type*} [Fintype I] [DecidableEq A]
    (events : I → Finset A) : Prop :=
  ∀ i, events i = ∅

def AllMutualCategoricalImplications
    {I A : Type*} [Fintype I] [DecidableEq A]
    (events : I → Finset A) : Prop :=
  ∀ i j, categoricalEventImplication (events i) (events j)

theorem allCategoricalEventsEmpty_implies_allMutualImplications
    {I A : Type*} [Fintype I] [DecidableEq A]
    (events : I → Finset A) :
    AllCategoricalEventsEmpty events →
      AllMutualCategoricalImplications events := by
  intro hempty i j
  rw [hempty i, hempty j]
  simp [categoricalEventImplication]

theorem allMutualProbabilityOrders_iff_differenceKernel
    {I K : Type*} [Fintype I] [Nonempty I] [Fintype K]
    (v : Matrix I K ℚ) (base : I) (w : K → ℚ) :
    AllMutualProbabilityOrders v w ↔
      differenceMatrix v base *ᵥ w = 0 := by
  constructor
  · intro hall
    funext i
    rw [differenceMatrix_mulVec_apply]
    have hib := (finiteMaxEntProbability_le_iff_harmonic_ge v w i base).1
      (hall i base)
    have hbi := (finiteMaxEntProbability_le_iff_harmonic_ge v w base i).1
      (hall base i)
    exact sub_eq_zero.mpr (le_antisymm hbi hib)
  · intro hkernel i j
    apply (finiteMaxEntProbability_le_iff_harmonic_ge v w i j).2
    have hi := congrFun hkernel i
    have hj := congrFun hkernel j
    rw [differenceMatrix_mulVec_apply] at hi hj
    have hieq : rationalHarmonic v w i = rationalHarmonic v w base :=
      sub_eq_zero.mp hi
    have hjeq : rationalHarmonic v w j = rationalHarmonic v w base :=
      sub_eq_zero.mp hj
    rw [hieq, hjeq]

def MutualTransportWeightRegion {I K : Type*} [Fintype I] [Fintype K]
    (v : Matrix I K ℚ) : Set (K → ℚ) :=
  {w | NonnegativeVector w ∧ AllMutualProbabilityOrders v w}

def NonnegativeKernelRegion {I K : Type*} [Fintype I] [Fintype K]
    (D : Matrix I K ℚ) : Set (K → ℚ) :=
  {w | NonnegativeVector w ∧ D *ᵥ w = 0}

theorem mutualTransportWeightRegion_eq_nonnegativeKernel
    {I K : Type*} [Fintype I] [Nonempty I] [Fintype K]
    (v : Matrix I K ℚ) (base : I) :
    MutualTransportWeightRegion v =
      NonnegativeKernelRegion (differenceMatrix v base) := by
  ext w
  exact and_congr_right fun _ =>
    allMutualProbabilityOrders_iff_differenceKernel v base w

theorem nonnegativeKernelRegion_eq_singleton_zero_iff
    {I K : Type*} [Fintype I] [Fintype K] [Nonempty K]
    (D : Matrix I K ℚ) :
    NonnegativeKernelRegion D = {0} ↔
      ¬ NormalizedNonnegativeKernel D := by
  constructor
  · intro hsingle hnorm
    rcases hnorm with ⟨w, hw, hsum, hDw⟩
    have hwmem : w ∈ NonnegativeKernelRegion D := ⟨hw, hDw⟩
    rw [hsingle] at hwmem
    have hw0 : w = 0 := by simpa using hwmem
    subst w
    simpa using hsum
  · intro hnorm
    ext w
    constructor
    · rintro ⟨hw, hDw⟩
      have hw0 : w = 0 := by
        by_contra hwne
        apply hnorm
        exact (rawNonnegativeKernel_iff_normalized D).1 ⟨w, hw, hwne, hDw⟩
      simpa [hw0]
    · intro hwmem
      have hw0 : w = 0 := by simpa using hwmem
      subst w
      constructor
      · intro k
        simp
      · simp

theorem max_g5_collapse_iff_positiveRowSpace
    (foundation : GordanStiemkeFoundation.{u, v})
    {I : Type u} {K : Type v} [Fintype I] [Fintype K] [Nonempty K]
    (D : Matrix I K ℚ) :
    NonnegativeKernelRegion D = {0} ↔ StrictlyPositiveRowSpace D := by
  have hxor := max_g5_gordan_02 foundation D
  rw [nonnegativeKernelRegion_eq_singleton_zero_iff]
  rcases hxor with ⟨hnorm, hnpos⟩ | ⟨hpos, hnnorm⟩
  · simp [hnorm, hnpos]
  · simp [hpos, hnnorm]

                   
theorem max_g5_completeTypedVacuityCollapse
    (foundation : GordanStiemkeFoundation.{u, v})
    {I : Type u} {K : Type v} [Fintype I] [Nonempty I]
    [Fintype K] [Nonempty K]
    {A : Type*} [DecidableEq A]
    (events : I → Finset A) (v : Matrix I K ℚ) (base : I)
    (hempty : AllCategoricalEventsEmpty events) :
    AllMutualCategoricalImplications events ∧
      MaxEntAnswerSort.booleanEventInclusion ≠
        MaxEntAnswerSort.orderedRealProbability ∧
      MutualTransportWeightRegion v =
        NonnegativeKernelRegion (differenceMatrix v base) ∧
      (MutualTransportWeightRegion v = {0} ↔
        StrictlyPositiveRowSpace (differenceMatrix v base)) := by
  refine ⟨allCategoricalEventsEmpty_implies_allMutualImplications events hempty,
    by decide, mutualTransportWeightRegion_eq_nonnegativeKernel v base, ?_⟩
  rw [mutualTransportWeightRegion_eq_nonnegativeKernel]
  exact max_g5_collapse_iff_positiveRowSpace foundation _

end

end PhonologicalCalculus.MaxEnt
