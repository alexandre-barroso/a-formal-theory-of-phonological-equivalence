import PhonologicalCalculus.Selection.SphericalMeasure
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic

/-!
# An explicit measured open-patch proof for SEL-F1

This module closes the fixed-fixture open-patch proof goal for the registered
radius-two selected-output example.  The proof records a normalized
interior direction, exact strict target and excluded-comparison slacks, a
rational metric radius whose whole relative ball remains in the pairwise-only
gap, and an exact positive lower-bound object for normalized Haar surface
measure.

The proved patch is a chordal (subtype-metric) ball.  A separate bridge
proves that it contains a spherical angular ball of the recorded rational
radius, so the two notions of radius are not conflated.  The lower-bound object
is the measured chordal patch itself.  Lean proves that it is positive from the
normalized Haar measure's full support.  No closed-form rational value for the
surface mass is claimed.
-/

namespace PhonologicalCalculus.Selection

open MeasureTheory Metric Set
open scoped NNReal ENNReal

noncomputable section

/-! ## A reusable typed proof witness -/

/-- The ordinary unoriented angle, in radians, between two directions on a
real inner-product unit sphere. -/
def sphereAngularDistance
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x y : sphere (0 : E) 1) : ℝ :=
  InnerProductGeometry.angle (x : E) (y : E)

/-- Chordal distance between two unit vectors is at most their angular
distance in radians.  This is the bridge that turns an angular-radius bound
into containment in a subtype-metric ball. -/
theorem unitSphere_chordalDistance_le_angularDistance
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x y : sphere (0 : E) 1) :
    dist x y ≤ sphereAngularDistance x y := by
  have hx : ‖(x : E)‖ = 1 := by
    simpa only [mem_sphere, dist_zero_right] using x.property
  have hy : ‖(y : E)‖ = 1 := by
    simpa only [mem_sphere, dist_zero_right] using y.property
  rw [Subtype.dist_eq, dist_eq_norm]
  apply (sq_le_sq₀ (norm_nonneg _)
    (InnerProductGeometry.angle_nonneg _ _)).mp
  rw [norm_sub_sq_real, hx, hy,
    InnerProductGeometry.inner_eq_cos_angle_of_norm_eq_one hx hy]
  nlinarith [Real.one_sub_sq_div_two_le_cos
    (x := InnerProductGeometry.angle (x : E) (y : E))]

/-- A proof-carrying relatively open spherical patch inside a pairwise-only
region.  `metricRadius` is the chordal radius used to define `patch`;
`angularRadiusLowerBound` is a separately proved rational lower bound on
the angular radius contained in that patch.  `measureLowerBound` is an exact
`ℝ≥0∞` object and need not have a closed-form rational value. -/
structure OpenPatchMeasureProof
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E]
    (probability : Measure (sphere (0 : E) 1))
    (pairwise selected : Set (sphere (0 : E) 1))
    (targetScore excludedScore : sphere (0 : E) 1 → ℝ) where
  interior : sphere (0 : E) 1
  targetSlack : ℝ
  excludedSlack : ℝ
  metricRadius : ℚ
  angularRadiusLowerBound : ℚ
  patch : Set (sphere (0 : E) 1)
  measureLowerBound : ℝ≥0∞
  targetSlack_pos : 0 < targetSlack
  excludedSlack_pos : 0 < excludedSlack
  metricRadius_pos : 0 < metricRadius
  angularRadiusLowerBound_pos : 0 < angularRadiusLowerBound
  target_at_interior : targetScore interior = targetSlack
  excluded_at_interior : excludedScore interior = -excludedSlack
  patch_eq_ball : patch = Metric.ball interior (metricRadius : ℝ)
  angular_ball_subset_patch :
    {direction |
      sphereAngularDistance interior direction <
        (angularRadiusLowerBound : ℝ)} ⊆ patch
  patch_subset_pairwise_only : patch ⊆ pairwise \ selected
  measureLowerBound_pos : 0 < measureLowerBound
  measureLowerBound_le : measureLowerBound ≤ probability patch

/-! ## The exact radius-two fixture -/

abbrev RadiusTwoEuclidean := EuclideanSpace ℝ (Fin 3)
abbrev RadiusTwoUnitSphere := sphere (0 : RadiusTwoEuclidean) 1

local instance radiusTwoEuclideanMeasurableSpace :
    MeasurableSpace RadiusTwoEuclidean :=
  borel RadiusTwoEuclidean

local instance radiusTwoEuclideanBorelSpace :
    BorelSpace RadiusTwoEuclidean :=
  ⟨rfl⟩

/-- The normalized direction obtained from the registered radius-two witness
`(6/5, 3/2, √31/10)`. -/
noncomputable def selF1PatchCenterVector : RadiusTwoEuclidean :=
  WithLp.toLp 2 ![(3 / 5 : ℝ), 3 / 4, Real.sqrt 31 / 20]

theorem selF1PatchCenterVector_norm : ‖selF1PatchCenterVector‖ = 1 := by
  apply (sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).mp
  rw [EuclideanSpace.real_norm_sq_eq]
  have hsqrt : (Real.sqrt 31) ^ 2 = 31 := by norm_num
  simp [selF1PatchCenterVector, Fin.sum_univ_succ]
  simp only [div_pow]
  rw [hsqrt]
  norm_num

def selF1PatchCenter : RadiusTwoUnitSphere :=
  ⟨selF1PatchCenterVector, by
    simp only [mem_sphere, dist_zero_right, selF1PatchCenterVector_norm]⟩

/-- At shell radius two, this is the strict margin for crossing the named
target comparison. -/
def selF1TargetScore (direction : RadiusTwoUnitSphere) : ℝ :=
  2 * (direction : RadiusTwoEuclidean) 0 - 1

/-- At shell radius two, this is the strict margin for beating the additional
competitor.  Negative values therefore prove pairwise-only directions. -/
def selF1ExcludedScore (direction : RadiusTwoUnitSphere) : ℝ :=
  2 * ((direction : RadiusTwoEuclidean) 0 -
    (direction : RadiusTwoEuclidean) 1)

def selF1PairwiseDirectionEvent : Set RadiusTwoUnitSphere :=
  {direction | 0 < selF1TargetScore direction}

def selF1SelectedDirectionEvent : Set RadiusTwoUnitSphere :=
  {direction | 0 < selF1TargetScore direction ∧
    0 < selF1ExcludedScore direction}

def selF1Patch : Set RadiusTwoUnitSphere :=
  Metric.ball selF1PatchCenter (1 / 100 : ℝ)

local instance radiusTwoUnitSphereNonempty : Nonempty RadiusTwoUnitSphere :=
  ⟨selF1PatchCenter⟩

noncomputable def selF1SphericalLaw : ProbabilityMeasure RadiusTwoUnitSphere :=
  haarSphereProbability (volume : Measure RadiusTwoEuclidean)

/-- Every Euclidean coordinate is bounded by the ambient Euclidean norm. -/
lemma abs_coordinate_le_norm (point : RadiusTwoEuclidean) (i : Fin 3) :
    |point i| ≤ ‖point‖ := by
  apply (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mp
  rw [sq_abs, EuclideanSpace.real_norm_sq_eq]
  exact Finset.single_le_sum (fun j _ => sq_nonneg (point j))
    (Finset.mem_univ i)

lemma selF1Patch_coordinate_close {direction : RadiusTwoUnitSphere}
    (hdirection : direction ∈ selF1Patch) (i : Fin 3) :
    |(direction : RadiusTwoEuclidean) i - selF1PatchCenterVector i| <
      (1 / 100 : ℝ) := by
  have hdist : dist (direction : RadiusTwoEuclidean)
      selF1PatchCenterVector < (1 / 100 : ℝ) := by
    have hdsub : dist direction selF1PatchCenter < (1 / 100 : ℝ) := by
      simpa [selF1Patch] using hdirection
    simpa only [Subtype.dist_eq, selF1PatchCenter] using hdsub
  rw [dist_eq_norm] at hdist
  exact (abs_coordinate_le_norm
    ((direction : RadiusTwoEuclidean) - selF1PatchCenterVector) i).trans_lt
      (by simpa using hdist)

theorem selF1Patch_scores {direction : RadiusTwoUnitSphere}
    (hdirection : direction ∈ selF1Patch) :
    0 < selF1TargetScore direction ∧ selF1ExcludedScore direction < 0 := by
  have hzero := selF1Patch_coordinate_close hdirection (0 : Fin 3)
  have hone := selF1Patch_coordinate_close hdirection (1 : Fin 3)
  rcases abs_lt.mp hzero with ⟨hzeroLower, hzeroUpper⟩
  rcases abs_lt.mp hone with ⟨honeLower, honeUpper⟩
  simp [selF1PatchCenterVector] at hzeroLower hzeroUpper honeLower honeUpper
  constructor
  · unfold selF1TargetScore
    linarith
  · unfold selF1ExcludedScore
    linarith

theorem selF1Patch_subset_pairwise_only :
    selF1Patch ⊆
      selF1PairwiseDirectionEvent \ selF1SelectedDirectionEvent := by
  intro direction hdirection
  have hscores := selF1Patch_scores hdirection
  constructor
  · exact hscores.1
  · intro hselected
    exact (not_lt_of_ge hscores.2.le) hselected.2

/-- The rational angular ball of radius `1/100` radians is contained in the
proved chordal ball.  The comparison uses the exact inequality
`chordal distance ≤ angular distance` for unit vectors. -/
theorem selF1AngularBall_subset_patch :
    {direction |
      sphereAngularDistance selF1PatchCenter direction < (1 / 100 : ℝ)} ⊆
      selF1Patch := by
  intro direction hangle
  change dist direction selF1PatchCenter < (1 / 100 : ℝ)
  exact (unitSphere_chordalDistance_le_angularDistance
    direction selF1PatchCenter).trans_lt
      (by
        rw [sphereAngularDistance, InnerProductGeometry.angle_comm]
        exact hangle)

theorem selF1PatchCenter_exact_slacks :
    selF1TargetScore selF1PatchCenter = 1 / 5 ∧
      selF1ExcludedScore selF1PatchCenter = -(3 / 10) := by
  norm_num [selF1TargetScore, selF1ExcludedScore, selF1PatchCenter,
    selF1PatchCenterVector]

theorem selF1Patch_measure_pos :
    0 < (selF1SphericalLaw : Measure RadiusTwoUnitSphere) selF1Patch := by
  exact haarSphereProbability_open_pos (volume : Measure RadiusTwoEuclidean)
    (by
      unfold selF1Patch
      exact Metric.isOpen_ball)
    ⟨selF1PatchCenter, by simp [selF1Patch]⟩

/-- The requested fixed-fixture `OpenPatchMeasureProof`.  Its chordal
metric radius and its separately proved angular-radius lower bound are both
`1/100`; its exact measure lower-bound object is the actual normalized Haar
mass of the chordal ball, proved strictly positive. -/
noncomputable def selF1OpenPatchMeasureProof :
    OpenPatchMeasureProof
      (selF1SphericalLaw : Measure RadiusTwoUnitSphere)
      selF1PairwiseDirectionEvent selF1SelectedDirectionEvent
      selF1TargetScore selF1ExcludedScore :=
  { interior := selF1PatchCenter
    targetSlack := 1 / 5
    excludedSlack := 3 / 10
    metricRadius := 1 / 100
    angularRadiusLowerBound := 1 / 100
    patch := selF1Patch
    measureLowerBound :=
      (selF1SphericalLaw : Measure RadiusTwoUnitSphere) selF1Patch
    targetSlack_pos := by norm_num
    excludedSlack_pos := by norm_num
    metricRadius_pos := by norm_num
    angularRadiusLowerBound_pos := by norm_num
    target_at_interior := selF1PatchCenter_exact_slacks.1
    excluded_at_interior := selF1PatchCenter_exact_slacks.2
    patch_eq_ball := by norm_num [selF1Patch]
    angular_ball_subset_patch := by
      norm_num
      exact selF1AngularBall_subset_patch
    patch_subset_pairwise_only := selF1Patch_subset_pairwise_only
    measureLowerBound_pos := selF1Patch_measure_pos
    measureLowerBound_le := le_rfl }

/-- A compact umbrella theorem exposing every machine-checked field required
by `SEL-F1.MEASURE.04` at the fixed registered fixture. -/
theorem sel_f1_open_patch_measure_proof :
    selF1OpenPatchMeasureProof.targetSlack = 1 / 5 ∧
      selF1OpenPatchMeasureProof.excludedSlack = 3 / 10 ∧
      selF1OpenPatchMeasureProof.metricRadius = 1 / 100 ∧
      selF1OpenPatchMeasureProof.angularRadiusLowerBound = 1 / 100 ∧
      {direction |
        sphereAngularDistance selF1PatchCenter direction < (1 / 100 : ℝ)} ⊆
        selF1OpenPatchMeasureProof.patch ∧
      selF1OpenPatchMeasureProof.patch ⊆
        selF1PairwiseDirectionEvent \ selF1SelectedDirectionEvent ∧
      0 < selF1OpenPatchMeasureProof.measureLowerBound ∧
      selF1OpenPatchMeasureProof.measureLowerBound ≤
        (selF1SphericalLaw : Measure RadiusTwoUnitSphere)
          selF1OpenPatchMeasureProof.patch := by
  exact ⟨rfl, rfl, rfl, rfl,
    (by
      change {direction |
        sphereAngularDistance selF1PatchCenter direction < (1 / 100 : ℝ)} ⊆
        selF1Patch
      exact selF1AngularBall_subset_patch),
    selF1OpenPatchMeasureProof.patch_subset_pairwise_only,
    selF1OpenPatchMeasureProof.measureLowerBound_pos,
    selF1OpenPatchMeasureProof.measureLowerBound_le⟩

end

end PhonologicalCalculus.Selection
