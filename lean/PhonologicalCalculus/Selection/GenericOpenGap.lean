import PhonologicalCalculus.Selection.SphericalMeasure
import Mathlib.Tactic

/-!
# The generic finite-comparison open-gap converse

For a complete finite homogeneous comparison family containing a nonzero
target normal, failure of the positive-ray condition is not merely a set-level
counterexample.  It produces a nonempty relatively open part of the unit
sphere on which the target comparison succeeds while the complete selected
output fails.  Every normalized Haar-induced full-support spherical law
therefore assigns the complete event strictly less mass than the pairwise
event.

The probability conclusion is deliberately one-way.  Equality under one
arbitrary measure is not used to infer event identity.  The converse premise
is the distribution-independent failure of the positive-ray/event-identity
condition.
-/

namespace PhonologicalCalculus.Selection

open MeasureTheory Metric Set
open scoped NNReal ENNReal

noncomputable section

/-! ## Directional events and their topology -/

/-- The named strict comparison restricted to the unit sphere of the ambient
finite coordinate space.  The theorem below is norm-independent; the ambient
function space carries its standard finite-product norm. -/
def sphericalPairwiseEvent {ι : Type*} [Fintype ι]
    (target : ι → ℝ) : Set (sphere (0 : ι → ℝ) 1) :=
  {direction | 0 < coordinateDot (direction : ι → ℝ) target}

/-- The complete finite strict-comparison event restricted to the same unit
sphere. -/
def sphericalSelectedEvent {ι : Type*} [Fintype ι]
    (normals : List (ι → ℝ)) : Set (sphere (0 : ι → ℝ) 1) :=
  {direction | ∀ normal ∈ normals,
    0 < coordinateDot (direction : ι → ℝ) normal}

/-- A strict pairwise-only sector determined by one excluded comparison. -/
def sphericalStrictGap {ι : Type*} [Fintype ι]
    (target normal : ι → ℝ) : Set (sphere (0 : ι → ℝ) 1) :=
  {direction | 0 < coordinateDot (direction : ι → ℝ) target ∧
    coordinateDot (direction : ι → ℝ) normal < 0}

lemma coordinateDot_direction_continuous {ι : Type*} [Fintype ι]
    (normal : ι → ℝ) :
    Continuous fun direction : sphere (0 : ι → ℝ) 1 =>
      coordinateDot (direction : ι → ℝ) normal := by
  unfold coordinateDot
  exact continuous_finsetSum Finset.univ fun i _ =>
    ((continuous_apply i).comp continuous_subtype_val).mul continuous_const

theorem sphericalPairwiseEvent_isOpen {ι : Type*} [Fintype ι]
    (target : ι → ℝ) : IsOpen (sphericalPairwiseEvent target) := by
  exact isOpen_lt continuous_const (coordinateDot_direction_continuous target)

theorem sphericalSelectedEvent_isOpen {ι : Type*} [Fintype ι]
    (normals : List (ι → ℝ)) : IsOpen (sphericalSelectedEvent normals) := by
  induction normals with
  | nil => simp [sphericalSelectedEvent]
  | cons normal rest ih =>
      have hnormalOpen :
          IsOpen {direction : sphere (0 : ι → ℝ) 1 |
            0 < coordinateDot (direction : ι → ℝ) normal} :=
        isOpen_lt continuous_const
          (coordinateDot_direction_continuous normal)
      have hevent : sphericalSelectedEvent (normal :: rest) =
          {direction : sphere (0 : ι → ℝ) 1 |
            0 < coordinateDot (direction : ι → ℝ) normal} ∩
            sphericalSelectedEvent rest := by
        ext direction
        constructor
        · intro hselected
          exact ⟨hselected normal (by simp), fun other hother =>
            hselected other (by simp [hother])⟩
        · rintro ⟨hhead, htail⟩ other hother
          rcases List.mem_cons.mp hother with heq | hrest
          · subst other
            exact hhead
          · exact htail other hrest
      rw [hevent]
      exact hnormalOpen.inter ih

theorem sphericalStrictGap_isOpen {ι : Type*} [Fintype ι]
    (target normal : ι → ℝ) : IsOpen (sphericalStrictGap target normal) := by
  unfold sphericalStrictGap
  exact (isOpen_lt continuous_const
    (coordinateDot_direction_continuous target)).inter
      (isOpen_lt (coordinateDot_direction_continuous normal) continuous_const)

theorem sphericalSelectedEvent_subset_pairwise {ι : Type*} [Fintype ι]
    {target : ι → ℝ} {normals : List (ι → ℝ)}
    (htargetMember : target ∈ normals) :
    sphericalSelectedEvent normals ⊆ sphericalPairwiseEvent target := by
  intro direction hselected
  exact hselected target htargetMember

/-! ## Strict witnesses and normalization -/

/-- If one nonzero comparison normal is not a positive multiple of the target,
there is a parameter that satisfies the target comparison strictly and fails
the other comparison strictly.  A boundary witness is pushed into the strict
side by an explicit norm-controlled perturbation. -/
theorem exists_strict_pairwise_exclusion_of_not_positiveRay
    {ι : Type*} [Fintype ι]
    {target normal : ι → ℝ} (htarget : target ≠ 0)
    (hnormal : normal ≠ 0)
    (hnotray : ¬ ∃ scale : ℝ, 0 < scale ∧
      normal = fun i => scale * target i) :
    ∃ parameter : ι → ℝ,
      0 < coordinateDot parameter target ∧
        coordinateDot parameter normal < 0 := by
  have hnotSubset : ¬ pairwiseEvent target ⊆ pairwiseEvent normal := by
    intro hsubset
    exact hnotray (positiveRay_of_pairwiseEvent_subset htarget hsubset)
  obtain ⟨parameter, htargetScore, hnormalScore⟩ :=
    Set.not_subset.mp hnotSubset
  change 0 < coordinateDot parameter target at htargetScore
  change ¬ 0 < coordinateDot parameter normal at hnormalScore
  have hnormalLe : coordinateDot parameter normal ≤ 0 :=
    le_of_not_gt hnormalScore
  by_cases hnormalLt : coordinateDot parameter normal < 0
  · exact ⟨parameter, htargetScore, hnormalLt⟩
  · have hnormalEq : coordinateDot parameter normal = 0 :=
      le_antisymm hnormalLe (not_lt.mp hnormalLt)
    let cross := coordinateDot normal target
    let epsilon := coordinateDot parameter target /
      (2 * (|cross| + 1))
    have hdenominatorPos : 0 < 2 * (|cross| + 1) := by
      have := abs_nonneg cross
      positivity
    have hepsilonPos : 0 < epsilon :=
      div_pos htargetScore hdenominatorPos
    have hepsilonIdentity : epsilon * (|cross| + 1) =
        coordinateDot parameter target / 2 := by
      dsimp [epsilon]
      field_simp
    have hepsilonCross : epsilon * cross <
        coordinateDot parameter target := by
      have hcrossLe : cross ≤ |cross| := le_abs_self cross
      have hmulLe : epsilon * cross ≤ epsilon * |cross| :=
        mul_le_mul_of_nonneg_left hcrossLe hepsilonPos.le
      have hstrict : epsilon * |cross| <
          epsilon * (|cross| + 1) := by
        nlinarith
      rw [hepsilonIdentity] at hstrict
      linarith
    let repaired : ι → ℝ := fun i =>
      parameter i - epsilon * normal i
    refine ⟨repaired, ?_, ?_⟩
    · rw [coordinateDot_sub_left, coordinateDot_scale_left]
      change 0 < coordinateDot parameter target - epsilon * cross
      linarith
    · rw [coordinateDot_sub_left, coordinateDot_scale_left, hnormalEq,
        zero_sub]
      exact neg_neg_of_pos (mul_pos hepsilonPos
        (coordinateDot_self_pos hnormal))

/-- Positive and negative homogeneous scores survive normalization to the unit
sphere. -/
theorem exists_spherical_strict_exclusion_of_ambient
    {ι : Type*} [Fintype ι]
    {target normal parameter : ι → ℝ}
    (htargetScore : 0 < coordinateDot parameter target)
    (hnormalScore : coordinateDot parameter normal < 0) :
    ∃ direction : sphere (0 : ι → ℝ) 1,
      0 < coordinateDot (direction : ι → ℝ) target ∧
        coordinateDot (direction : ι → ℝ) normal < 0 := by
  have hparameterNonzero : parameter ≠ 0 := by
    intro hzero
    subst parameter
    simp [coordinateDot] at htargetScore
  have hparameterNorm : 0 < ‖parameter‖ :=
    norm_pos_iff.mpr hparameterNonzero
  let scale : ℝ := ‖parameter‖⁻¹
  have hscale : 0 < scale := inv_pos.mpr hparameterNorm
  let direction : sphere (0 : ι → ℝ) 1 :=
    ⟨scale • parameter, by
      simp only [mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs]
      rw [abs_of_pos hscale]
      exact inv_mul_cancel₀ hparameterNorm.ne'⟩
  refine ⟨direction, ?_, ?_⟩
  · change 0 < coordinateDot (fun i => scale * parameter i) target
    rw [coordinateDot_scale_left]
    exact mul_pos hscale htargetScore
  · change coordinateDot (fun i => scale * parameter i) normal < 0
    rw [coordinateDot_scale_left]
    exact mul_neg_of_pos_of_neg hscale hnormalScore

/-- A nonzero normal determines at least one direction in its own strict
comparison halfspace. -/
theorem sphericalPairwiseEvent_nonempty {ι : Type*} [Fintype ι]
    {target : ι → ℝ} (htarget : target ≠ 0) :
    (sphericalPairwiseEvent target).Nonempty := by
  have hscore : 0 < coordinateDot target target :=
    coordinateDot_self_pos htarget
  have htargetNorm : 0 < ‖target‖ := norm_pos_iff.mpr htarget
  let scale : ℝ := ‖target‖⁻¹
  have hscale : 0 < scale := inv_pos.mpr htargetNorm
  let direction : sphere (0 : ι → ℝ) 1 :=
    ⟨scale • target, by
      simp only [mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs]
      rw [abs_of_pos hscale]
      exact inv_mul_cancel₀ htargetNorm.ne'⟩
  refine ⟨direction, ?_⟩
  change 0 < coordinateDot (fun i => scale * target i) target
  rw [coordinateDot_scale_left]
  exact mul_pos hscale hscore

/-! ## Generic open-gap and strict-probability theorems -/

/-- Failed positive-ray completion yields a nonempty relatively open spherical
patch inside the pairwise-only region.  The zero-normal case is kept explicit:
then the whole pairwise event is excluded by that comparison. -/
theorem exists_open_spherical_gap_of_not_positiveRayFamily
    {ι : Type*} [Fintype ι]
    {target : ι → ℝ} {normals : List (ι → ℝ)}
    (htargetNonzero : target ≠ 0)
    (hnotrays : ¬ PositiveRayFamily target normals) :
    ∃ gap : Set (sphere (0 : ι → ℝ) 1),
      IsOpen gap ∧ gap.Nonempty ∧
        gap ⊆ sphericalPairwiseEvent target \ sphericalSelectedEvent normals := by
  classical
  simp only [PositiveRayFamily, not_forall] at hnotrays
  obtain ⟨normal, hnormalMember, hnotray⟩ := hnotrays
  by_cases hnormalZero : normal = 0
  · refine ⟨sphericalPairwiseEvent target,
      sphericalPairwiseEvent_isOpen target,
      sphericalPairwiseEvent_nonempty htargetNonzero, ?_⟩
    intro direction hpairwise
    refine ⟨hpairwise, ?_⟩
    intro hselected
    have hzeroScore := hselected normal hnormalMember
    rw [hnormalZero] at hzeroScore
    simp [coordinateDot] at hzeroScore
  · obtain ⟨parameter, htargetScore, hnormalScore⟩ :=
      exists_strict_pairwise_exclusion_of_not_positiveRay
        htargetNonzero hnormalZero hnotray
    obtain ⟨direction, hdirectionTarget, hdirectionNormal⟩ :=
      exists_spherical_strict_exclusion_of_ambient
        htargetScore hnormalScore
    refine ⟨sphericalStrictGap target normal,
      sphericalStrictGap_isOpen target normal,
      ⟨direction, hdirectionTarget, hdirectionNormal⟩, ?_⟩
    intro candidate hgap
    refine ⟨hgap.1, ?_⟩
    intro hselected
    exact (not_lt_of_ge hgap.2.le) (hselected normal hnormalMember)

/-- The generic full-support converse for complete finite comparison families:
failed positive-ray/event identity forces a strict probability overcount under
the normalized Haar-induced spherical law.  This is not a converse from
equality under one arbitrary measure. -/
theorem haarSphereProbability_selected_lt_pairwise_of_not_positiveRayFamily
    {ι : Type*} [Fintype ι]
    [MeasurableSpace (ι → ℝ)] [BorelSpace (ι → ℝ)]
    [Nontrivial (ι → ℝ)] [Nonempty (sphere (0 : ι → ℝ) 1)]
    (ambient : Measure (ι → ℝ)) [ambient.IsAddHaarMeasure]
    {target : ι → ℝ} {normals : List (ι → ℝ)}
    (htargetMember : target ∈ normals) (htargetNonzero : target ≠ 0)
    (hnotrays : ¬ PositiveRayFamily target normals) :
    (haarSphereProbability ambient :
        Measure (sphere (0 : ι → ℝ) 1))
          (sphericalSelectedEvent normals) <
      (haarSphereProbability ambient :
        Measure (sphere (0 : ι → ℝ) 1))
          (sphericalPairwiseEvent target) := by
  obtain ⟨gap, hgapOpen, hgapNonempty, hgapSubset⟩ :=
    exists_open_spherical_gap_of_not_positiveRayFamily
      htargetNonzero hnotrays
  exact haarSphereProbability_strict_of_open_gap
    ambient
    (sphericalSelectedEvent_subset_pairwise htargetMember)
    (sphericalSelectedEvent_isOpen normals).measurableSet
    hgapOpen hgapNonempty hgapSubset

end

end PhonologicalCalculus.Selection
