import PhonologicalCalculus.Selection.SphericalMeasure
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Exact spherical probabilities for selected-output regions

This module evaluates the one-dimensional integral induced by the standard
coordinate disintegration of the uniform probability measure on the radius-two
sphere in three dimensions.  It then derives the exact pairwise and
selected-output probabilities registered by `SEL-F1.SPHERE.02`.

Mathlib supplies the normalized Haar-induced surface measure, but it does not
currently expose the exact marginal and conditional coordinate-disintegration
result needed here.  That single transport result is therefore an explicit,
typed premise.  It contains no final probability values: the derivative,
antiderivative, endpoint identities, exact integral, measure algebra, and
strict inequality are all proved below.
-/

namespace PhonologicalCalculus.Selection

open MeasureTheory Set intervalIntegral

noncomputable section

/-! ## Exact integral evaluation -/

/-- A derivative predicate using the scalar-module instance selected by
`NormedAlgebra`.  This fixes the otherwise ambiguous real scalar-module
instance in composed derivative proofs. -/
abbrev AlgebraHasDerivAt (f : ℝ → ℝ) (f' x : ℝ) : Prop :=
  @HasDerivAt ℝ _ ℝ
    ((inferInstance : NontriviallyNormedField ℝ).toDivisionRing.toAddCommGroup)
    (NormedAlgebra.toNormedSpace ℝ).toModule _ _ f f' x

lemma hasDerivAt_arccos_standard {x : ℝ} (hneg : x ≠ -1) (hone : x ≠ 1) :
    AlgebraHasDerivAt Real.arccos (-(1 / Real.sqrt (1 - x ^ 2))) x := by
  exact Real.hasDerivAt_arccos hneg hone

lemma hasDerivAt_arctan_standard (x : ℝ) :
    AlgebraHasDerivAt Real.arctan (1 / (1 + x ^ 2)) x := by
  exact Real.hasDerivAt_arctan x

/-- The angular fraction excluded by the extra selected-output comparison at
first coordinate `t`. -/
abbrev sphereExcludedIntegrand (t : ℝ) : ℝ :=
  Real.arccos (t / Real.sqrt (4 - t ^ 2))

/-- An exact primitive for `sphereExcludedIntegrand` on `(1, √2)`. -/
abbrev sphereExcludedPrimitive (t : ℝ) : ℝ :=
  t * sphereExcludedIntegrand t -
    2 * Real.arctan (Real.sqrt (2 - t ^ 2) / Real.sqrt 2)

lemma sphere_interval_bounds {t : ℝ}
    (ht : t ∈ Set.Ioo (1 : ℝ) (Real.sqrt 2)) :
    0 < t ∧ t ^ 2 < 2 ∧ 0 < 2 - t ^ 2 ∧ 0 < 4 - t ^ 2 := by
  have hsqrt : (Real.sqrt 2) ^ 2 = 2 := by norm_num
  have htpos : 0 < t := lt_trans (by norm_num) ht.1
  have htsq : t ^ 2 < 2 := by
    have hsq := (sq_lt_sq₀ htpos.le (Real.sqrt_nonneg 2)).2 ht.2
    rwa [hsqrt] at hsq
  exact ⟨htpos, htsq, by linarith, by linarith⟩

lemma sphere_ratio_bounds {t : ℝ}
    (ht : t ∈ Set.Ioo (1 : ℝ) (Real.sqrt 2)) :
    -1 < t / Real.sqrt (4 - t ^ 2) ∧
      t / Real.sqrt (4 - t ^ 2) < 1 := by
  rcases sphere_interval_bounds ht with ⟨htpos, htsq, htwo, hfour⟩
  have hsqrtpos : 0 < Real.sqrt (4 - t ^ 2) := Real.sqrt_pos.2 hfour
  have hsqrtsq : (Real.sqrt (4 - t ^ 2)) ^ 2 = 4 - t ^ 2 := by
    rw [Real.sq_sqrt hfour.le]
  have hlt : t < Real.sqrt (4 - t ^ 2) := by nlinarith
  constructor
  · have : 0 < t / Real.sqrt (4 - t ^ 2) := div_pos htpos hsqrtpos
    linarith
  · exact (div_lt_one hsqrtpos).2 hlt

lemma hasDerivAt_sphereExcludedIntegrand {t : ℝ}
    (ht : t ∈ Set.Ioo (1 : ℝ) (Real.sqrt 2)) :
    AlgebraHasDerivAt sphereExcludedIntegrand
      (-4 / ((4 - t ^ 2) * Real.sqrt (2 * (2 - t ^ 2)))) t := by
  rcases sphere_interval_bounds ht with ⟨htpos, htsq, htwo, hfour⟩
  have hDne : Real.sqrt (4 - t ^ 2) ≠ 0 := (Real.sqrt_pos.2 hfour).ne'
  have hbase : AlgebraHasDerivAt (fun x : ℝ => 4 - x ^ 2) (-2 * t) t := by
    have hbaseRaw :=
      (hasDerivAt_const t (4 : ℝ)).sub ((hasDerivAt_id t).pow 2)
    change AlgebraHasDerivAt (fun x : ℝ => 4 - x ^ 2)
      (0 - (2 : ℝ) * t ^ (2 - 1) * 1) t at hbaseRaw
    convert hbaseRaw using 1
    norm_num
  have hD : AlgebraHasDerivAt (fun x : ℝ => Real.sqrt (4 - x ^ 2))
      ((-2 * t) / (2 * Real.sqrt (4 - t ^ 2))) t :=
    hbase.sqrt (by linarith)
  have hratio : AlgebraHasDerivAt (fun x : ℝ => x / Real.sqrt (4 - x ^ 2))
      ((Real.sqrt (4 - t ^ 2) -
          t * ((-2 * t) / (2 * Real.sqrt (4 - t ^ 2)))) /
        (Real.sqrt (4 - t ^ 2)) ^ 2) t :=
    by
      have hratioRaw := (hasDerivAt_id t).div hD hDne
      change AlgebraHasDerivAt (fun x : ℝ => x / Real.sqrt (4 - x ^ 2))
        ((1 * Real.sqrt (4 - t ^ 2) -
            t * ((-2 * t) / (2 * Real.sqrt (4 - t ^ 2)))) /
          (Real.sqrt (4 - t ^ 2)) ^ 2) t at hratioRaw
      simpa only [one_mul] using hratioRaw
  rcases sphere_ratio_bounds ht with ⟨hratioLower, hratioUpper⟩
  have harccosBase : AlgebraHasDerivAt Real.arccos
      (-(1 / Real.sqrt
        (1 - (t / Real.sqrt (4 - t ^ 2)) ^ 2)))
      (t / Real.sqrt (4 - t ^ 2)) :=
    hasDerivAt_arccos_standard
      (ne_of_gt hratioLower) (ne_of_lt hratioUpper)
  have harccos : AlgebraHasDerivAt
      (fun x : ℝ => Real.arccos (x / Real.sqrt (4 - x ^ 2)))
      (-(1 / Real.sqrt (1 - (t / Real.sqrt (4 - t ^ 2)) ^ 2)) *
        ((Real.sqrt (4 - t ^ 2) -
            t * ((-2 * t) / (2 * Real.sqrt (4 - t ^ 2)))) /
          (Real.sqrt (4 - t ^ 2)) ^ 2)) t := by
    have hcomp := harccosBase.comp t hratio
    change AlgebraHasDerivAt
      (Real.arccos ∘ fun x : ℝ => x / Real.sqrt (4 - x ^ 2))
      (-(1 / Real.sqrt (1 - (t / Real.sqrt (4 - t ^ 2)) ^ 2)) *
        ((Real.sqrt (4 - t ^ 2) -
            t * ((-2 * t) / (2 * Real.sqrt (4 - t ^ 2)))) /
          (Real.sqrt (4 - t ^ 2)) ^ 2)) t at hcomp
    simpa only [Function.comp_def] using hcomp
  have hDsquare : (Real.sqrt (4 - t ^ 2)) ^ 2 = 4 - t ^ 2 :=
    Real.sq_sqrt hfour.le
  have hrootSquare :
      (Real.sqrt (2 * (2 - t ^ 2))) ^ 2 = 2 * (2 - t ^ 2) :=
    Real.sq_sqrt (mul_nonneg (by norm_num) htwo.le)
  have hrootpos : 0 < Real.sqrt (2 * (2 - t ^ 2)) :=
    Real.sqrt_pos.2 (mul_pos (by norm_num) htwo)
  have hratioRoot :
      Real.sqrt (1 - (t / Real.sqrt (4 - t ^ 2)) ^ 2) =
        Real.sqrt (2 * (2 - t ^ 2)) / Real.sqrt (4 - t ^ 2) := by
    apply (sq_eq_sq₀ (Real.sqrt_nonneg _)
      (div_nonneg hrootpos.le (Real.sqrt_pos.2 hfour).le)).mp
    rw [Real.sq_sqrt]
    · simp only [div_pow]
      rw [hrootSquare, hDsquare]
      field_simp [hDne]
      ring
    · have hratioNonneg : 0 ≤ t / Real.sqrt (4 - t ^ 2) := by positivity
      have hsquareLt : (t / Real.sqrt (4 - t ^ 2)) ^ 2 < 1 :=
        (sq_lt_one_iff₀ hratioNonneg).2 hratioUpper
      linarith
  have hcoeff :
      -(1 / Real.sqrt (1 - (t / Real.sqrt (4 - t ^ 2)) ^ 2)) *
          ((Real.sqrt (4 - t ^ 2) -
              t * ((-2 * t) / (2 * Real.sqrt (4 - t ^ 2)))) /
            (Real.sqrt (4 - t ^ 2)) ^ 2) =
        -4 / ((4 - t ^ 2) * Real.sqrt (2 * (2 - t ^ 2))) := by
    rw [hratioRoot, hDsquare]
    field_simp [hDne, hrootpos.ne']
    rw [hDsquare]
    ring
  simpa only [sphereExcludedIntegrand] using
    harccos.congr_deriv hcoeff

lemma hasDerivAt_sphereExcludedPrimitive {t : ℝ}
    (ht : t ∈ Set.Ioo (1 : ℝ) (Real.sqrt 2)) :
    AlgebraHasDerivAt sphereExcludedPrimitive (sphereExcludedIntegrand t) t := by
  rcases sphere_interval_bounds ht with ⟨htpos, htsq, htwo, hfour⟩
  have hSpos : 0 < Real.sqrt (2 - t ^ 2) := Real.sqrt_pos.2 htwo
  have hSbase : AlgebraHasDerivAt (fun x : ℝ => 2 - x ^ 2) (-2 * t) t := by
    have hbaseRaw :=
      (hasDerivAt_const t (2 : ℝ)).sub ((hasDerivAt_id t).pow 2)
    change AlgebraHasDerivAt (fun x : ℝ => 2 - x ^ 2)
      (0 - (2 : ℝ) * t ^ (2 - 1) * 1) t at hbaseRaw
    convert hbaseRaw using 1
    norm_num
  have hS : AlgebraHasDerivAt (fun x : ℝ => Real.sqrt (2 - x ^ 2))
      ((-2 * t) / (2 * Real.sqrt (2 - t ^ 2))) t :=
    hSbase.sqrt (by linarith)
  have hsqrt2pos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hquot : AlgebraHasDerivAt
      (fun x : ℝ => Real.sqrt (2 - x ^ 2) / Real.sqrt 2)
      (((-2 * t) / (2 * Real.sqrt (2 - t ^ 2))) / Real.sqrt 2) t :=
    hS.div_const (Real.sqrt 2)
  have hatanBase : AlgebraHasDerivAt Real.arctan
      (1 / (1 + (Real.sqrt (2 - t ^ 2) / Real.sqrt 2) ^ 2))
      (Real.sqrt (2 - t ^ 2) / Real.sqrt 2) :=
    hasDerivAt_arctan_standard _
  have hatan : AlgebraHasDerivAt
      (fun x : ℝ => Real.arctan (Real.sqrt (2 - x ^ 2) / Real.sqrt 2))
      (1 / (1 + (Real.sqrt (2 - t ^ 2) / Real.sqrt 2) ^ 2) *
        ((-2 * t) / (2 * Real.sqrt (2 - t ^ 2)) / Real.sqrt 2)) t := by
    have hcomp := hatanBase.comp t hquot
    change AlgebraHasDerivAt
      (Real.arctan ∘ fun x : ℝ => Real.sqrt (2 - x ^ 2) / Real.sqrt 2)
      (1 / (1 + (Real.sqrt (2 - t ^ 2) / Real.sqrt 2) ^ 2) *
        ((-2 * t) / (2 * Real.sqrt (2 - t ^ 2)) / Real.sqrt 2)) t at hcomp
    simpa only [Function.comp_def] using hcomp
  have hfirst : AlgebraHasDerivAt
      (fun x : ℝ => x * sphereExcludedIntegrand x)
      (sphereExcludedIntegrand t +
        t * (-4 / ((4 - t ^ 2) * Real.sqrt (2 * (2 - t ^ 2))))) t := by
    have hraw := (hasDerivAt_id t).mul (hasDerivAt_sphereExcludedIntegrand ht)
    change AlgebraHasDerivAt (fun x : ℝ => x * sphereExcludedIntegrand x)
      (1 * sphereExcludedIntegrand t +
        t * (-4 / ((4 - t ^ 2) * Real.sqrt (2 * (2 - t ^ 2))))) t at hraw
    simpa only [one_mul] using hraw
  have hraw := hfirst.sub (hatan.const_mul 2)
  change AlgebraHasDerivAt sphereExcludedPrimitive
    (sphereExcludedIntegrand t +
      t * (-4 / ((4 - t ^ 2) * Real.sqrt (2 * (2 - t ^ 2)))) -
      2 * (1 / (1 + (Real.sqrt (2 - t ^ 2) / Real.sqrt 2) ^ 2) *
        ((-2 * t) / (2 * Real.sqrt (2 - t ^ 2)) / Real.sqrt 2))) t at hraw
  have hSsquare : (Real.sqrt (2 - t ^ 2)) ^ 2 = 2 - t ^ 2 :=
    Real.sq_sqrt htwo.le
  have hRootIdentity :
      Real.sqrt (2 * (2 - t ^ 2)) = Real.sqrt 2 * Real.sqrt (2 - t ^ 2) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hcoeff :
      sphereExcludedIntegrand t +
          t * (-4 / ((4 - t ^ 2) * Real.sqrt (2 * (2 - t ^ 2)))) -
          2 * (1 / (1 + (Real.sqrt (2 - t ^ 2) / Real.sqrt 2) ^ 2) *
            ((-2 * t) / (2 * Real.sqrt (2 - t ^ 2)) / Real.sqrt 2)) =
        sphereExcludedIntegrand t := by
    rw [hRootIdentity]
    field_simp [hSpos.ne', hsqrt2pos.ne']
    rw [hSsquare, show (Real.sqrt 2) ^ 2 = 2 by norm_num]
    ring
  exact hraw.congr_deriv hcoeff

lemma continuousOn_sphereExcludedIntegrand :
    ContinuousOn sphereExcludedIntegrand (Set.Icc (1 : ℝ) (Real.sqrt 2)) := by
  intro t ht
  have htsq : t ^ 2 ≤ 2 := by
    have ht_nonneg : 0 ≤ t := le_trans (by norm_num) ht.1
    have hsq := (sq_le_sq₀ ht_nonneg (Real.sqrt_nonneg 2)).2 ht.2
    rwa [show (Real.sqrt 2) ^ 2 = 2 by norm_num] at hsq
  have hdenom : Real.sqrt (4 - t ^ 2) ≠ 0 := by
    exact (Real.sqrt_pos.2 (by linarith)).ne'
  apply ContinuousAt.continuousWithinAt
  change ContinuousAt (fun x : ℝ =>
    Real.arccos (x / Real.sqrt (4 - x ^ 2))) t
  fun_prop

lemma continuousOn_sphereExcludedPrimitive :
    ContinuousOn sphereExcludedPrimitive (Set.Icc (1 : ℝ) (Real.sqrt 2)) := by
  intro t ht
  have htsq : t ^ 2 ≤ 2 := by
    have ht_nonneg : 0 ≤ t := le_trans (by norm_num) ht.1
    have hsq := (sq_le_sq₀ ht_nonneg (Real.sqrt_nonneg 2)).2 ht.2
    rwa [show (Real.sqrt 2) ^ 2 = 2 by norm_num] at hsq
  have hdenom : Real.sqrt (4 - t ^ 2) ≠ 0 := by
    exact (Real.sqrt_pos.2 (by linarith)).ne'
  apply ContinuousAt.continuousWithinAt
  change ContinuousAt (fun x : ℝ =>
    x * Real.arccos (x / Real.sqrt (4 - x ^ 2)) -
      2 * Real.arctan (Real.sqrt (2 - x ^ 2) / Real.sqrt 2)) t
  fun_prop

lemma intervalIntegrable_sphereExcludedIntegrand :
    IntervalIntegrable sphereExcludedIntegrand MeasureTheory.volume
      (1 : ℝ) (Real.sqrt 2) :=
  by
    have hle : (1 : ℝ) ≤ Real.sqrt 2 := by
      nlinarith [show (Real.sqrt 2) ^ 2 = 2 by norm_num,
        Real.sqrt_nonneg 2]
    apply ContinuousOn.intervalIntegrable
    simpa [uIcc_of_le hle] using continuousOn_sphereExcludedIntegrand

lemma integral_sphereExcludedIntegrand_eq_sub :
    ∫ t in (1 : ℝ)..Real.sqrt 2, sphereExcludedIntegrand t =
      sphereExcludedPrimitive (Real.sqrt 2) - sphereExcludedPrimitive 1 := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      (by
        nlinarith [show (Real.sqrt 2) ^ 2 = 2 by norm_num,
          Real.sqrt_nonneg 2])
      continuousOn_sphereExcludedPrimitive
  · intro t ht
    exact hasDerivAt_sphereExcludedPrimitive ht
  · exact intervalIntegrable_sphereExcludedIntegrand

lemma sphereExcludedPrimitive_sqrt_two :
    sphereExcludedPrimitive (Real.sqrt 2) = 0 := by
  have hsqrt2 : (Real.sqrt 2) ^ 2 = 2 := by norm_num
  have hsqrt2ne : Real.sqrt 2 ≠ 0 := by positivity
  have hdenom : Real.sqrt (4 - (Real.sqrt 2) ^ 2) = Real.sqrt 2 := by
    rw [hsqrt2]
    norm_num
  have hratio : Real.sqrt 2 /
      Real.sqrt (4 - (Real.sqrt 2) ^ 2) = 1 := by
    rw [hdenom, div_self hsqrt2ne]
  change Real.sqrt 2 *
      Real.arccos (Real.sqrt 2 / Real.sqrt (4 - (Real.sqrt 2) ^ 2)) -
        2 * Real.arctan
          (Real.sqrt (2 - (Real.sqrt 2) ^ 2) / Real.sqrt 2) = 0
  rw [hratio, hsqrt2]
  norm_num

lemma sphereExcludedIntegrand_one :
    sphereExcludedIntegrand 1 = Real.arctan (Real.sqrt 2) := by
  have h := Real.arctan_eq_arccos (Real.sqrt_nonneg 2)
  rw [show sphereExcludedIntegrand 1 =
      Real.arccos ((Real.sqrt 3)⁻¹) by
      norm_num [sphereExcludedIntegrand, one_div]]
  symm
  convert h using 1
  rw [show 1 + (Real.sqrt 2) ^ 2 = 3 by norm_num]

lemma sphereExcludedPrimitive_one :
    sphereExcludedPrimitive 1 =
      Real.pi / 2 - 3 * Real.arctan (Real.sqrt 2)⁻¹ := by
  have hsqrt2pos : 0 < Real.sqrt 2 := by positivity
  have hinv := Real.arctan_inv_of_pos hsqrt2pos
  have hquot : Real.sqrt (2 - (1 : ℝ) ^ 2) / Real.sqrt 2 =
      (Real.sqrt 2)⁻¹ := by
    norm_num [one_div]
  change (1 : ℝ) * sphereExcludedIntegrand 1 -
      2 * Real.arctan
        (Real.sqrt (2 - (1 : ℝ) ^ 2) / Real.sqrt 2) = _
  simp only [one_mul]
  rw [hquot]
  rw [sphereExcludedIntegrand_one]
  linarith

theorem integral_sphereExcludedIntegrand_exact :
    ∫ t in (1 : ℝ)..Real.sqrt 2, sphereExcludedIntegrand t =
      3 * Real.arctan (Real.sqrt 2)⁻¹ - Real.pi / 2 := by
  rw [integral_sphereExcludedIntegrand_eq_sub,
    sphereExcludedPrimitive_sqrt_two, sphereExcludedPrimitive_one]
  ring

/-! ## Radius-two event geometry and fixture coordinate transport -/

/-- The pairwise halfspace on the radius-two sphere, expressed in its first
coordinate. -/
def radiusTwoPairwiseEvent : Set (Fin 3 → ℝ) :=
  {point | 1 < point 0}

/-- The selected-output region: the target first clears its pairwise boundary
and then beats the additional competitor represented by the second
coordinate. -/
def radiusTwoSelectedEvent : Set (Fin 3 → ℝ) :=
  {point | 1 < point 0 ∧ point 1 < point 0}

lemma radiusTwoSelectedEvent_subset_pairwise :
    radiusTwoSelectedEvent ⊆ radiusTwoPairwiseEvent := by
  intro point hpoint
  exact hpoint.1

lemma measurableSet_radiusTwoPairwiseEvent :
    MeasurableSet radiusTwoPairwiseEvent := by
  exact measurableSet_lt (measurable_const) (measurable_pi_apply 0)

lemma measurableSet_radiusTwoSelectedEvent :
    MeasurableSet radiusTwoSelectedEvent := by
  exact measurableSet_radiusTwoPairwiseEvent.inter
    (measurableSet_lt (measurable_pi_apply 1) (measurable_pi_apply 0))

/-- Real arccotangent on the positive branch used by the registered spherical
probability formula. -/
noncomputable def positiveArcCot (x : ℝ) : ℝ :=
  Real.arctan x⁻¹

/-- The closed-form selected-output probability registered by `SEL-F1`. -/
noncomputable def radiusTwoSelectedProbability : ℝ :=
  3 * (Real.pi - 2 * positiveArcCot (Real.sqrt 2)) /
    (8 * Real.pi)

lemma intervalIntegral_one_fourth :
    ∫ _t in (1 : ℝ)..2, (1 / 4 : ℝ) = 1 / 4 := by
  norm_num

/-- Project-specific coordinate-transport premise for the registered radius-two
fixture.  The record directly supplies the measures of the two project-defined
events as the displayed one-dimensional integrals.  It does not identify
`probability` with the canonical uniform/Haar sphere law; that specialization
would require a separate theorem.  All integral evaluation and subsequent
probability algebra remain below. -/
structure RadiusTwoSphereFixtureCoordinateTransport
    (probability : Measure (Fin 3 → ℝ)) : Prop where
  isProbabilityMeasure : IsProbabilityMeasure probability
  sphereSupport :
    probability {point | squaredRadius3 point = 4} = 1
  pairwiseCoordinateTransport :
    probability.real radiusTwoPairwiseEvent =
      ∫ _t in (1 : ℝ)..2, (1 / 4 : ℝ)
  overcountCoordinateTransport :
    probability.real (radiusTwoPairwiseEvent \ radiusTwoSelectedEvent) =
      (1 / (4 * Real.pi)) *
        ∫ t in (1 : ℝ)..Real.sqrt 2, sphereExcludedIntegrand t

lemma pairwise_probability_of_fixture_coordinate_transport
    {probability : Measure (Fin 3 → ℝ)}
    (foundation :
      RadiusTwoSphereFixtureCoordinateTransport probability) :
    probability.real radiusTwoPairwiseEvent = 1 / 4 := by
  rw [foundation.pairwiseCoordinateTransport, intervalIntegral_one_fourth]

lemma excluded_probability_of_fixture_coordinate_transport
    {probability : Measure (Fin 3 → ℝ)}
    (foundation :
      RadiusTwoSphereFixtureCoordinateTransport probability) :
    probability.real
        (radiusTwoPairwiseEvent \ radiusTwoSelectedEvent) =
      3 * Real.arctan (Real.sqrt 2)⁻¹ / (4 * Real.pi) - 1 / 8 := by
  rw [foundation.overcountCoordinateTransport,
    integral_sphereExcludedIntegrand_exact]
  field_simp [Real.pi_ne_zero]
  ring

lemma selected_probability_closed_form_identity :
    3 / 8 -
        3 * Real.arctan (Real.sqrt 2)⁻¹ / (4 * Real.pi) =
      radiusTwoSelectedProbability := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  unfold radiusTwoSelectedProbability positiveArcCot
  field_simp [hpi]
  ring

lemma excluded_probability_positive
    {probability : Measure (Fin 3 → ℝ)}
    (foundation :
      RadiusTwoSphereFixtureCoordinateTransport probability) :
    0 < probability.real
      (radiusTwoPairwiseEvent \ radiusTwoSelectedEvent) := by
  have hsqrt2pos : 0 < Real.sqrt 2 := by positivity
  have hsqrt3pos : 0 < Real.sqrt 3 := by positivity
  have hsqrtlt : Real.sqrt 2 < Real.sqrt 3 :=
    Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hinvlt : (Real.sqrt 3)⁻¹ < (Real.sqrt 2)⁻¹ :=
    (inv_lt_inv₀ hsqrt3pos hsqrt2pos).2 hsqrtlt
  have hatanlt := Real.arctan_strictMono hinvlt
  rw [Real.arctan_inv_sqrt_three] at hatanlt
  have hinner :
      0 < 3 * Real.arctan (Real.sqrt 2)⁻¹ - Real.pi / 2 := by
    linarith
  rw [foundation.overcountCoordinateTransport,
    integral_sphereExcludedIntegrand_exact]
  exact mul_pos (by positivity) hinner

lemma selected_probability_of_fixture_coordinate_transport
    {probability : Measure (Fin 3 → ℝ)}
    (foundation :
      RadiusTwoSphereFixtureCoordinateTransport probability) :
    probability.real radiusTwoSelectedEvent =
      radiusTwoSelectedProbability := by
  letI : IsProbabilityMeasure probability := foundation.isProbabilityMeasure
  have hsdiff := MeasureTheory.measureReal_sdiff
    (μ := probability)
    (s₁ := radiusTwoPairwiseEvent)
    (s₂ := radiusTwoSelectedEvent)
    radiusTwoSelectedEvent_subset_pairwise
    measurableSet_radiusTwoSelectedEvent
    (measure_ne_top probability radiusTwoPairwiseEvent)
  have hsolve :
      probability.real radiusTwoSelectedEvent =
        probability.real radiusTwoPairwiseEvent -
          probability.real
            (radiusTwoPairwiseEvent \ radiusTwoSelectedEvent) := by
    linarith
  rw [hsolve,
    pairwise_probability_of_fixture_coordinate_transport foundation,
    foundation.overcountCoordinateTransport,
    integral_sphereExcludedIntegrand_exact]
  calc
    1 / 4 -
        1 / (4 * Real.pi) *
          (3 * Real.arctan (Real.sqrt 2)⁻¹ - Real.pi / 2) =
      3 / 8 -
        3 * Real.arctan (Real.sqrt 2)⁻¹ / (4 * Real.pi) := by
          field_simp [Real.pi_ne_zero]
          ring
    _ = radiusTwoSelectedProbability :=
      selected_probability_closed_form_identity

lemma selected_probability_strictly_below_pairwise_of_fixture_coordinate_transport
    {probability : Measure (Fin 3 → ℝ)}
    (foundation :
      RadiusTwoSphereFixtureCoordinateTransport probability) :
    probability.real radiusTwoSelectedEvent <
      probability.real radiusTwoPairwiseEvent := by
  letI : IsProbabilityMeasure probability := foundation.isProbabilityMeasure
  have hsdiff := MeasureTheory.measureReal_sdiff
    (μ := probability)
    (s₁ := radiusTwoPairwiseEvent)
    (s₂ := radiusTwoSelectedEvent)
    radiusTwoSelectedEvent_subset_pairwise
    measurableSet_radiusTwoSelectedEvent
    (measure_ne_top probability radiusTwoPairwiseEvent)
  have hpositive := excluded_probability_positive foundation
  rw [hsdiff] at hpositive
  exact sub_pos.mp hpositive

/-- `SEL-F1.SPHERE.02`: conditional on the named project-specific fixture
coordinate-transport premise, the pairwise probability is exactly one quarter,
the selected probability is the registered arccotangent closed form, and the
pairwise calculation strictly overcounts selection. -/
theorem sel_f1_sphere_02_of_fixture_coordinate_transport
    {probability : Measure (Fin 3 → ℝ)}
    (foundation :
      RadiusTwoSphereFixtureCoordinateTransport probability) :
    probability.real radiusTwoPairwiseEvent = 1 / 4 ∧
      probability.real radiusTwoSelectedEvent =
        3 * (Real.pi - 2 * positiveArcCot (Real.sqrt 2)) /
          (8 * Real.pi) ∧
      probability.real radiusTwoSelectedEvent <
        probability.real radiusTwoPairwiseEvent := by
  exact ⟨pairwise_probability_of_fixture_coordinate_transport foundation,
    selected_probability_of_fixture_coordinate_transport foundation,
    selected_probability_strictly_below_pairwise_of_fixture_coordinate_transport
      foundation⟩

end

end PhonologicalCalculus.Selection
