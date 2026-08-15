import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

/-!
# Pairwise and complete selected-output regions

A named selected-output event is the intersection of every strict comparison
halfspace needed for the candidate to beat the complete finite rival set.  A
single pairwise event is therefore always an upper bound.  If all comparison
normals are positive scalar copies of the named normal, every halfspace is
identical and the bound is exact.

The finite fixtures below check the registered positive-ray predicate and an
exact radius-two point that lies in the pairwise event but outside the
selected event.  No probability law is defined in this module.
-/

namespace PhonologicalCalculus.Selection

open Set

/-- Euclidean coordinate pairing on a finite real coordinate type. -/
noncomputable def coordinateDot {ι : Type*} [Fintype ι]
    (x y : ι → ℝ) : ℝ :=
  ∑ i, x i * y i

theorem coordinateDot_scale_right {ι : Type*} [Fintype ι]
    (x y : ι → ℝ) (scale : ℝ) :
    coordinateDot x (fun i => scale * y i) =
      scale * coordinateDot x y := by
  simp only [coordinateDot, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Strict comparison halfspace determined by one target--competitor normal. -/
def pairwiseEvent {ι : Type*} [Fintype ι] (normal : ι → ℝ) :
    Set (ι → ℝ) :=
  {parameter | 0 < coordinateDot parameter normal}

/-- Complete selected-output event for a finite list of comparison normals. -/
def selectedEvent {ι : Type*} [Fintype ι] (normals : List (ι → ℝ)) :
    Set (ι → ℝ) :=
  {parameter | ∀ normal ∈ normals, 0 < coordinateDot parameter normal}

/-- Every complete selected-output event is contained in each of its named
pairwise comparison events. -/
theorem selectedEvent_subset_pairwise {ι : Type*} [Fintype ι]
    {target : ι → ℝ} {normals : List (ι → ℝ)}
    (htarget : target ∈ normals) :
    selectedEvent normals ⊆ pairwiseEvent target := by
  intro parameter hselected
  exact hselected target htarget

/-- Every comparison normal belongs to the positive ray of the target normal. -/
def PositiveRayFamily {ι : Type*} (target : ι → ℝ)
    (normals : List (ι → ℝ)) : Prop :=
  ∀ normal ∈ normals,
    ∃ scale : ℝ, 0 < scale ∧ normal = fun i => scale * target i

/-- Positive-ray duplication makes the pairwise and complete events equal. -/
theorem selectedEvent_eq_pairwise_of_positiveRays
    {ι : Type*} [Fintype ι]
    {target : ι → ℝ} {normals : List (ι → ℝ)}
    (htarget : target ∈ normals)
    (hrays : PositiveRayFamily target normals) :
    selectedEvent normals = pairwiseEvent target := by
  apply Set.Subset.antisymm
  · exact selectedEvent_subset_pairwise htarget
  · intro parameter hpair normal hnormal
    rcases hrays normal hnormal with ⟨scale, hscale, rfl⟩
    rw [coordinateDot_scale_right]
    exact mul_pos hscale hpair

/-- A positive scalar multiple relation between two two-dimensional normals. -/
def PositiveRayMultiple2 (vector reference : Fin 2 → ℝ) : Prop :=
  ∃ scale : ℝ, 0 < scale ∧
    vector = fun i => scale * reference i

noncomputable def rayReference : Fin 2 → ℝ := ![1, 2]
noncomputable def rayPositiveFixture : Fin 2 → ℝ := ![2, 4]
noncomputable def rayNegativeFixture : Fin 2 → ℝ := ![-1, -2]
noncomputable def rayNonparallelFixture : Fin 2 → ℝ := ![1, 1]

/-- `SEL-F1.RAYS.01`: the registered comparison is respectively a positive
copy, a negative copy, and a nonparallel vector. -/
theorem sel_f1_rays_01 :
    PositiveRayMultiple2 rayPositiveFixture rayReference ∧
      ¬ PositiveRayMultiple2 rayNegativeFixture rayReference ∧
      ¬ PositiveRayMultiple2 rayNonparallelFixture rayReference := by
  constructor
  · refine ⟨2, by norm_num, ?_⟩
    funext i
    fin_cases i <;> norm_num [rayPositiveFixture, rayReference]
  constructor
  · rintro ⟨scale, hscale, heq⟩
    have hzero := congrFun heq 0
    norm_num [rayNegativeFixture, rayReference] at hzero
    linarith
  · rintro ⟨scale, hscale, heq⟩
    have hzero := congrFun heq 0
    have hone := congrFun heq 1
    norm_num [rayNonparallelFixture, rayReference] at hzero hone
    linarith

/-- The exact radius-two pairwise-overcount witness. -/
noncomputable def pairwiseOvercountWitness : Fin 3 → ℝ :=
  ![6 / 5, 3 / 2, Real.sqrt 31 / 10]

noncomputable def squaredRadius3 (point : Fin 3 → ℝ) : ℝ :=
  point 0 ^ 2 + point 1 ^ 2 + point 2 ^ 2

/-- `SEL-F1.WITNESS.03`: the witness has squared radius four, crosses the
named pairwise boundary, and is blocked by the additional comparison. -/
theorem sel_f1_witness_03 :
    squaredRadius3 pairwiseOvercountWitness = 4 ∧
      1 < pairwiseOvercountWitness 0 ∧
      pairwiseOvercountWitness 0 < pairwiseOvercountWitness 1 := by
  have hsqrt : (Real.sqrt 31) ^ 2 = 31 := by
    norm_num
  change (6 / 5 : ℝ) ^ 2 + (3 / 2 : ℝ) ^ 2 +
      (Real.sqrt 31 / 10) ^ 2 = 4 ∧
    (1 : ℝ) < 6 / 5 ∧ (6 / 5 : ℝ) < 3 / 2
  simp only [div_pow]
  rw [hsqrt]
  norm_num

/-- Exact two-dimensional normals for a finite failure-of-equality witness. -/
noncomputable def patchTargetNormal : Fin 2 → ℝ := ![1, 2]
noncomputable def patchExcludedNormal : Fin 2 → ℝ := ![1, 1]
noncomputable def patchCenter : Fin 2 → ℝ := ![-3, 2]

def coordinateClose2 (radius : ℝ) (x y : Fin 2 → ℝ) : Prop :=
  |x 0 - y 0| < radius ∧ |x 1 - y 1| < radius

/-- An algebraic proof witness for an open coordinate patch in a pairwise event
and outside one additional halfspace.  It records an exact interior point,
strict slacks, and a rational coordinate-radius lower bound. -/
structure AlgebraicOpenPatchProofWitness where
  targetNormal : Fin 2 → ℝ
  excludedNormal : Fin 2 → ℝ
  center : Fin 2 → ℝ
  coordinateRadius : ℝ
  targetSlack : ℝ
  excludedSlack : ℝ
  radius_pos : 0 < coordinateRadius
  targetSlack_pos : 0 < targetSlack
  excludedSlack_pos : 0 < excludedSlack
  target_at_center : coordinateDot center targetNormal = targetSlack
  excluded_at_center :
    coordinateDot center excludedNormal = -excludedSlack

noncomputable def differentHalfspacePatch : AlgebraicOpenPatchProofWitness :=
  { targetNormal := patchTargetNormal
    excludedNormal := patchExcludedNormal
    center := patchCenter
    coordinateRadius := 1 / 10
    targetSlack := 1
    excludedSlack := 1
    radius_pos := by norm_num
    targetSlack_pos := by norm_num
    excludedSlack_pos := by norm_num
    target_at_center := by
      norm_num [coordinateDot, patchCenter, patchTargetNormal, Fin.sum_univ_two]
    excluded_at_center := by
      norm_num [coordinateDot, patchCenter, patchExcludedNormal,
        Fin.sum_univ_two] }

theorem patchCenter_pairwise_not_selected :
    patchCenter ∈ pairwiseEvent patchTargetNormal ∧
      patchCenter ∉ selectedEvent [patchTargetNormal, patchExcludedNormal] := by
  constructor
  · norm_num [pairwiseEvent, coordinateDot, patchCenter, patchTargetNormal,
      Fin.sum_univ_two]
  · intro hselected
    have hexcluded := hselected patchExcludedNormal (by simp)
    norm_num [coordinateDot, patchCenter, patchExcludedNormal,
      Fin.sum_univ_two] at hexcluded

/-- Every point in the proved coordinate neighborhood remains in the
pairwise-only set difference. -/
theorem differentHalfspacePatch_stable {point : Fin 2 → ℝ}
    (hclose : coordinateClose2 (1 / 10) point patchCenter) :
    point ∈ pairwiseEvent patchTargetNormal ∧
      point ∉ selectedEvent [patchTargetNormal, patchExcludedNormal] := by
  rcases hclose with ⟨hzero, hone⟩
  have hzero' := (abs_lt.mp hzero)
  have hone' := (abs_lt.mp hone)
  constructor
  · norm_num [pairwiseEvent, coordinateDot, patchCenter, patchTargetNormal,
      Fin.sum_univ_two] at *
    linarith
  · intro hselected
    have hexcluded := hselected patchExcludedNormal (by simp)
    norm_num [coordinateDot, patchCenter, patchExcludedNormal,
      Fin.sum_univ_two] at *
    linarith

end PhonologicalCalculus.Selection
