import PhonologicalCalculus.ContinuousHG.Quadratic
import PhonologicalCalculus.Support.MatchedPowerInfinite
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# General-power optimizer for the directional continuous-HG path

This module supplies the real-exponent finite-dimensional optimization core
for the directional positive-part path family.  It proves the strict tangent
inequality for real powers, a strict finite-simplex KKT result, the
positive-part shifted-power candidate, existence of an active multiplier,
and exact extension of a boundary optimizer by an inactive zero tail.
-/

namespace PhonologicalCalculus.ContinuousHG

open scoped BigOperators
open Finset Set

/-! ## General-power monotone normal form -/

/-- Real-power directional penalty. -/
noncomputable def realPowerPenalty (p drop : ℝ) : ℝ := drop ^ p

theorem realPowerPenalty_monotone_on_nonnegative
    {p a b : ℝ} (hp : 1 < p) (ha : 0 ≤ a) (hab : a ≤ b) :
    realPowerPenalty p a ≤ realPowerPenalty p b := by
  unfold realPowerPenalty
  exact Real.rpow_le_rpow ha hab (le_trans zero_le_one hp.le)

/-- Running-minimum normalization lowers every real-power directional path
objective with positive exponent and nonnegative weights. -/
theorem generalPowerPathHarmony_runningMinimum_le
    {p h m : ℝ} (hp : 1 < p) (hh : 0 ≤ h) (hm : 0 ≤ m)
    (profile : List ℝ) :
    pathHarmony (realPowerPenalty p) h m (runningMinimum profile) ≤
      pathHarmony (realPowerPenalty p) h m profile := by
  exact pathHarmony_runningMinimum_le (realPowerPenalty p)
    (fun {_a _b : ℝ} ha hab =>
      realPowerPenalty_monotone_on_nonnegative hp ha hab)
    hh hm profile

/-- If normalization changes a coordinate and markedness is positive, the
general-power objective decreases strictly. -/
theorem generalPowerPathHarmony_runningMinimum_lt_of_changed
    {p h m : ℝ} (hp : 1 < p) (hh : 0 ≤ h) (hm : 0 < m)
    (profile : List ℝ) (hchanged : runningMinimum profile ≠ profile) :
    pathHarmony (realPowerPenalty p) h m (runningMinimum profile) <
      pathHarmony (realPowerPenalty p) h m profile := by
  exact pathHarmony_runningMinimum_lt_of_changed (realPowerPenalty p)
    (fun {_a _b : ℝ} ha hab =>
      realPowerPenalty_monotone_on_nonnegative hp ha hab)
    hh hm profile hchanged

section StrictPowerKKT

variable {ι : Type*} [Fintype ι]

/-- Reduced real-power objective on a finite decrease vector. -/
noncomputable def powerReducedObjective
    (h m p : ℝ) (weight d : ι → ℝ) : ℝ :=
  ∑ i, (h * (d i) ^ p - m * weight i * d i)

/-- Coordinate gradient of the real-power reduced objective on the
nonnegative orthant. -/
noncomputable def powerGradient
    (h m p : ℝ) (weight d : ι → ℝ) (i : ι) : ℝ :=
  p * h * (d i) ^ (p - 1) - m * weight i

/-- Strict supporting-line inequality for `x ↦ x^p` on the nonnegative
half-line.  Equality is possible only at the support point. -/
theorem rpow_strict_tangent
    {p u d : ℝ} (hp : 1 < p) (hu : 0 ≤ u) (hd : 0 ≤ d) :
    u ^ p + p * u ^ (p - 1) * (d - u) ≤ d ^ p ∧
      (u ^ p + p * u ^ (p - 1) * (d - u) = d ^ p → d = u) := by
  have derivative : HasDerivAt (fun x : ℝ => x ^ p)
      (p * u ^ (p - 1)) u :=
    Real.hasDerivAt_rpow_const (Or.inr (le_of_lt hp))
  rcases lt_trichotomy d u with hdu | rfl | hud
  · have slopeStrict := (strictConvexOn_rpow hp).slope_lt_of_hasDerivAt
      hd hu hdu derivative
    rw [slope_def_field] at slopeStrict
    have scaled := (div_lt_iff₀ (sub_pos.mpr hdu)).mp slopeStrict
    constructor
    · linarith
    · intro tangentEquality
      exfalso
      nlinarith
  · constructor
    · simp
    · exact fun _ => rfl
  · have slopeStrict := (strictConvexOn_rpow hp).lt_slope_of_hasDerivAt
      hu hd hud derivative
    rw [slope_def_field] at slopeStrict
    have scaled := (lt_div_iff₀ (sub_pos.mpr hud)).mp slopeStrict
    constructor
    · linarith
    · intro tangentEquality
      exfalso
      nlinarith

/-- Nonnegative strict-convexity remainder around a reference coordinate. -/
noncomputable def powerRemainder (p u d : ℝ) : ℝ :=
  d ^ p - u ^ p - p * u ^ (p - 1) * (d - u)

theorem powerRemainder_nonnegative
    {p u d : ℝ} (hp : 1 < p) (hu : 0 ≤ u) (hd : 0 ≤ d) :
    0 ≤ powerRemainder p u d := by
  unfold powerRemainder
  linarith [(rpow_strict_tangent hp hu hd).1]

theorem powerRemainder_eq_zero_iff
    {p u d : ℝ} (hp : 1 < p) (hu : 0 ≤ u) (hd : 0 ≤ d) :
    powerRemainder p u d = 0 ↔ d = u := by
  constructor
  · intro remainderZero
    apply (rpow_strict_tangent hp hu hd).2
    unfold powerRemainder at remainderZero
    linarith
  · rintro rfl
    simp [powerRemainder]

/-- Exact Bregman-gap decomposition of the real-power reduced objective. -/
theorem powerObjective_gap_identity
    (h m p : ℝ) (weight d u : ι → ℝ) :
    powerReducedObjective h m p weight d -
        powerReducedObjective h m p weight u =
      h * ∑ i, powerRemainder p (u i) (d i) +
        ∑ i, powerGradient h m p weight u i * (d i - u i) := by
  classical
  unfold powerReducedObjective powerRemainder powerGradient
  rw [← Finset.sum_sub_distrib]
  calc
    (∑ i, ((h * d i ^ p - m * weight i * d i) -
        (h * u i ^ p - m * weight i * u i))) =
        ∑ i, (h * (d i ^ p - u i ^ p -
          p * u i ^ (p - 1) * (d i - u i)) +
          (p * h * u i ^ (p - 1) - m * weight i) *
            (d i - u i)) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = h * ∑ i, (d i ^ p - u i ^ p -
          p * u i ^ (p - 1) * (d i - u i)) +
        ∑ i, (p * h * u i ^ (p - 1) - m * weight i) *
          (d i - u i) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]

/-- Strict supporting-hyperplane proof for the reduced objective on
the nonnegative orthant.  This is the finite-dimensional strict-convexity
fact used by the optimizer theorem. -/
theorem powerObjective_strict_supporting_hyperplane
    {h m p : ℝ} (weight d u : ι → ℝ)
    (hh : 0 < h) (hp : 1 < p)
    (hd : ∀ i, 0 ≤ d i) (hu : ∀ i, 0 ≤ u i) (hne : d ≠ u) :
    (∑ i, powerGradient h m p weight u i * (d i - u i)) <
      powerReducedObjective h m p weight d -
        powerReducedObjective h m p weight u := by
  classical
  have existsDifference : ∃ i, d i ≠ u i := by
    by_contra noDifference
    push Not at noDifference
    exact hne (funext noDifference)
  have remainderNonnegative :
      ∀ i, 0 ≤ powerRemainder p (u i) (d i) :=
    fun i => powerRemainder_nonnegative hp (hu i) (hd i)
  have remainderPositive :
      0 < ∑ i, powerRemainder p (u i) (d i) := by
    apply Finset.sum_pos'
    · exact fun i _ => remainderNonnegative i
    · obtain ⟨i, hi⟩ := existsDifference
      refine ⟨i, Finset.mem_univ i, lt_of_le_of_ne
        (remainderNonnegative i) ?_⟩
      intro remainderZero
      exact hi ((powerRemainder_eq_zero_iff hp (hu i) (hd i)).1
        remainderZero.symm)
  rw [powerObjective_gap_identity]
  nlinarith

/-- Integrated CHG-B1 bridge: running-minimum improvement, strict removal of
upward excursions, exact solid-simplex reparameterization without assuming a
terminal zero, and strict convexity of the reduced real-power objective. -/
theorem generalPower_monotone_simplex_strict_package
    {h m p : ℝ} (weight d u : ι → ℝ)
    (hh : 0 < h) (hm : 0 < m) (hp : 1 < p)
    (hd : ∀ i, 0 ≤ d i) (hu : ∀ i, 0 ≤ u i) :
    (∀ profile : List ℝ,
      pathHarmony (realPowerPenalty p) h m (runningMinimum profile) ≤
        pathHarmony (realPowerPenalty p) h m profile) ∧
    (∀ profile : List ℝ, runningMinimum profile ≠ profile →
      pathHarmony (realPowerPenalty p) h m (runningMinimum profile) <
        pathHarmony (realPowerPenalty p) h m profile) ∧
    ((∀ profile,
        AdmissibleProfileFrom 1 profile →
          SolidSimplexFrom 1 (decreasesFrom 1 profile)) ∧
      (∀ decreases,
        SolidSimplexFrom 1 decreases →
          AdmissibleProfileFrom 1 (profileFromDecreases 1 decreases)) ∧
      (∀ profile,
        profileFromDecreases 1 (decreasesFrom 1 profile) = profile) ∧
      (∀ decreases,
        decreasesFrom 1 (profileFromDecreases 1 decreases) = decreases)) ∧
    (d ≠ u →
      (∑ i, powerGradient h m p weight u i * (d i - u i)) <
        powerReducedObjective h m p weight d -
          powerReducedObjective h m p weight u) := by
  exact ⟨fun profile => generalPowerPathHarmony_runningMinimum_le
      hp hh.le hm.le profile,
    fun profile changed => generalPowerPathHarmony_runningMinimum_lt_of_changed
      hp hh.le hm profile changed,
    solidSimplex_profile_equivalence 1,
    fun different => powerObjective_strict_supporting_hyperplane
      weight d u hh hp hd hu different⟩

/-- General real-power KKT sufficiency and uniqueness on the solid simplex.
The strict remainder proves uniqueness without importing a black-box
optimization oracle. -/
theorem power_unique_minimizer_of_simplex_kkt
    {h m p lambda : ℝ} (weight u : ι → ℝ)
    (hh : 0 < h) (hp : 1 < p) (hu : SolidSimplex u)
    (hlambda : lambda ≤ 0)
    (hcomplementarity : lambda * ((∑ i, u i) - 1) = 0)
    (hgradient : ∀ i, lambda ≤ powerGradient h m p weight u i)
    (hactive : ∀ i, 0 < u i → powerGradient h m p weight u i = lambda) :
    IsUniqueMinimizerOn (SolidSimplex : (ι → ℝ) → Prop)
      (powerReducedObjective h m p weight) u := by
  classical
  refine ⟨hu, ?_⟩
  intro d hd
  let gradient : ι → ℝ := powerGradient h m p weight u
  have correctionPointwise :
      ∀ i, 0 ≤ (gradient i - lambda) * (d i - u i) := by
    intro i
    by_cases hui : u i = 0
    · rw [hui, sub_zero]
      exact mul_nonneg (sub_nonneg.mpr (hgradient i)) (hd.1 i)
    · have huiPositive : 0 < u i := lt_of_le_of_ne (hu.1 i) (Ne.symm hui)
      simp [gradient, hactive i huiPositive]
  have correctionNonnegative :
      0 ≤ ∑ i, (gradient i - lambda) * (d i - u i) :=
    Finset.sum_nonneg fun i _ => correctionPointwise i
  have massDifference : (∑ i, d i) - 1 ≤ 0 := by linarith [hd.2]
  have lambdaMassNonnegative :
      0 ≤ lambda * ((∑ i, d i) - ∑ i, u i) := by
    have towardBoundary : 0 ≤ lambda * ((∑ i, d i) - 1) :=
      mul_nonneg_of_nonpos_of_nonpos hlambda massDifference
    calc
      0 ≤ lambda * ((∑ i, d i) - 1) := towardBoundary
      _ = lambda * ((∑ i, d i) - ∑ i, u i) := by
        rw [show lambda * ((∑ i, d i) - ∑ i, u i) =
          lambda * ((∑ i, d i) - 1) -
            lambda * ((∑ i, u i) - 1) by ring,
          hcomplementarity, sub_zero]
  have linearIdentity :
      (∑ i, gradient i * (d i - u i)) =
        lambda * ((∑ i, d i) - ∑ i, u i) +
          ∑ i, (gradient i - lambda) * (d i - u i) := by
    calc
      (∑ i, gradient i * (d i - u i)) =
          ∑ i, (lambda * (d i - u i) +
            (gradient i - lambda) * (d i - u i)) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = (∑ i, lambda * (d i - u i)) +
          ∑ i, (gradient i - lambda) * (d i - u i) :=
        Finset.sum_add_distrib
      _ = lambda * (∑ i, (d i - u i)) +
          ∑ i, (gradient i - lambda) * (d i - u i) := by
        rw [Finset.mul_sum]
      _ = lambda * ((∑ i, d i) - ∑ i, u i) +
          ∑ i, (gradient i - lambda) * (d i - u i) := by
        rw [Finset.sum_sub_distrib]
  have linearNonnegative : 0 ≤ ∑ i, gradient i * (d i - u i) := by
    rw [linearIdentity]
    exact add_nonneg lambdaMassNonnegative correctionNonnegative
  have remainderPointwise : ∀ i, 0 ≤ powerRemainder p (u i) (d i) :=
    fun i => powerRemainder_nonnegative hp (hu.1 i) (hd.1 i)
  have remainderSumNonnegative :
      0 ≤ ∑ i, powerRemainder p (u i) (d i) :=
    Finset.sum_nonneg fun i _ => remainderPointwise i
  have gapNonnegative :
      0 ≤ powerReducedObjective h m p weight d -
        powerReducedObjective h m p weight u := by
    rw [powerObjective_gap_identity]
    exact add_nonneg (mul_nonneg hh.le remainderSumNonnegative)
      linearNonnegative
  constructor
  · linarith
  · intro objectiveEquality
    have gapZero : powerReducedObjective h m p weight d -
        powerReducedObjective h m p weight u = 0 := by linarith
    have remainderProductNonpositive :
        h * ∑ i, powerRemainder p (u i) (d i) ≤ 0 := by
      rw [powerObjective_gap_identity] at gapZero
      linarith
    have remainderSumZero :
        ∑ i, powerRemainder p (u i) (d i) = 0 := by
      have remainderProductNonnegative :
          0 ≤ h * ∑ i, powerRemainder p (u i) (d i) :=
        mul_nonneg hh.le remainderSumNonnegative
      nlinarith
    funext i
    have coordinateRemainderZero : powerRemainder p (u i) (d i) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => remainderPointwise j)).1 remainderSumZero i
          (Finset.mem_univ i)
    exact (powerRemainder_eq_zero_iff hp (hu.1 i) (hd.1 i)).1
      coordinateRemainderZero

end StrictPowerKKT

section ShiftedPowerCandidate

variable {ι : Type*} [Fintype ι]

/-- Hölder-conjugate shift exponent `q = 1 / (p - 1)`. -/
noncomputable def powerShiftExponent (p : ℝ) : ℝ := 1 / (p - 1)

theorem powerShiftExponent_positive {p : ℝ} (hp : 1 < p) :
    0 < powerShiftExponent p := by
  unfold powerShiftExponent
  positivity

/-- Positive-part shifted-power KKT candidate. -/
noncomputable def powerKKTDecrease
    (h m p eta : ℝ) (weight : ι → ℝ) (i : ι) : ℝ :=
  (max (m * weight i - eta) 0 / (p * h)) ^ powerShiftExponent p

/-- Total decrease mass of the shifted-power candidate. -/
noncomputable def powerKKTMass
    (h m p eta : ℝ) (weight : ι → ℝ) : ℝ :=
  ∑ i, powerKKTDecrease h m p eta weight i

omit [Fintype ι] in
theorem powerKKTDecrease_nonnegative
    {h m p eta : ℝ} (weight : ι → ℝ)
    (hh : 0 < h) (hp : 1 < p) (i : ι) :
    0 ≤ powerKKTDecrease h m p eta weight i := by
  have denominatorPositive : 0 < p * h :=
    mul_pos (lt_trans zero_lt_one hp) hh
  exact Real.rpow_nonneg
    (div_nonneg (le_max_right _ _) denominatorPositive.le) _

omit [Fintype ι] in
/-- Raising the shifted-power candidate to `p - 1` recovers its clipped
affine base. -/
theorem powerKKTDecrease_rpow_sub_one
    {h m p eta : ℝ} (weight : ι → ℝ)
    (hh : 0 < h) (hp : 1 < p) (i : ι) :
    (powerKKTDecrease h m p eta weight i) ^ (p - 1) =
      max (m * weight i - eta) 0 / (p * h) := by
  let base := max (m * weight i - eta) 0 / (p * h)
  have pPositive : 0 < p := lt_trans zero_lt_one hp
  have denominatorPositive : 0 < p * h := mul_pos pPositive hh
  have baseNonnegative : 0 ≤ base :=
    div_nonneg (le_max_right _ _) denominatorPositive.le
  have exponentProduct : powerShiftExponent p * (p - 1) = 1 := by
    unfold powerShiftExponent
    field_simp [ne_of_gt (sub_pos.mpr hp)]
  change (base ^ powerShiftExponent p) ^ (p - 1) = base
  rw [← Real.rpow_mul baseNonnegative, exponentProduct, Real.rpow_one]

omit [Fintype ι] in
theorem powerKKT_gradient_eq_neg_eta_of_positive
    {h m p eta : ℝ} (weight : ι → ℝ)
    (hh : 0 < h) (hp : 1 < p) (i : ι)
    (hpositive : 0 < m * weight i - eta) :
    powerGradient h m p weight (powerKKTDecrease h m p eta weight) i =
      -eta := by
  have denominatorNonzero : p * h ≠ 0 :=
    ne_of_gt (mul_pos (lt_trans zero_lt_one hp) hh)
  unfold powerGradient
  rw [powerKKTDecrease_rpow_sub_one weight hh hp i,
    max_eq_left hpositive.le]
  field_simp [denominatorNonzero]
  ring

omit [Fintype ι] in
theorem powerKKT_gradient_ge_neg_eta
    {h m p eta : ℝ} (weight : ι → ℝ)
    (hh : 0 < h) (hp : 1 < p) (i : ι) :
    -eta ≤ powerGradient h m p weight
      (powerKKTDecrease h m p eta weight) i := by
  by_cases hpositive : 0 < m * weight i - eta
  · rw [powerKKT_gradient_eq_neg_eta_of_positive weight hh hp i hpositive]
  · have numeratorNonpositive : m * weight i - eta ≤ 0 :=
      le_of_not_gt hpositive
    have denominatorNonzero : p * h ≠ 0 :=
      ne_of_gt (mul_pos (lt_trans zero_lt_one hp) hh)
    unfold powerGradient
    rw [powerKKTDecrease_rpow_sub_one weight hh hp i,
      max_eq_right numeratorNonpositive]
    field_simp [denominatorNonzero]
    linarith

omit [Fintype ι] in
theorem powerKKT_active_gradient
    {h m p eta : ℝ} (weight : ι → ℝ)
    (hh : 0 < h) (hp : 1 < p) (i : ι)
    (hactive : 0 < powerKKTDecrease h m p eta weight i) :
    powerGradient h m p weight
      (powerKKTDecrease h m p eta weight) i = -eta := by
  have numeratorPositive : 0 < m * weight i - eta := by
    by_contra notPositive
    have numeratorNonpositive : m * weight i - eta ≤ 0 :=
      le_of_not_gt notPositive
    have qPositive := powerShiftExponent_positive hp
    unfold powerKKTDecrease at hactive
    rw [max_eq_right numeratorNonpositive, zero_div,
      Real.zero_rpow qPositive.ne'] at hactive
    exact (lt_irrefl 0 hactive)
  exact powerKKT_gradient_eq_neg_eta_of_positive weight hh hp i
    numeratorPositive

/-- Any nonnegative multiplier whose shifted-power mass is one produces the
unique solid-simplex optimizer. -/
theorem powerKKTDecrease_unique_minimizer
    {h m p eta : ℝ} (weight : ι → ℝ)
    (hh : 0 < h) (hp : 1 < p) (heta : 0 ≤ eta)
    (hmass : powerKKTMass h m p eta weight = 1) :
    IsUniqueMinimizerOn (SolidSimplex : (ι → ℝ) → Prop)
      (powerReducedObjective h m p weight)
      (powerKKTDecrease h m p eta weight) := by
  have simplex : SolidSimplex (powerKKTDecrease h m p eta weight) := by
    constructor
    · exact fun i => powerKKTDecrease_nonnegative weight hh hp i
    · simpa [powerKKTMass] using hmass.le
  apply power_unique_minimizer_of_simplex_kkt (lambda := -eta) weight
    (powerKKTDecrease h m p eta weight) hh hp simplex
  · linarith
  · have candidateMass :
        (∑ i, powerKKTDecrease h m p eta weight i) = 1 := by
      simpa [powerKKTMass] using hmass
    rw [candidateMass, sub_self, mul_zero]
  · exact fun i => powerKKT_gradient_ge_neg_eta weight hh hp i
  · exact fun i => powerKKT_active_gradient weight hh hp i

/-- Before the decrease budget is exhausted, the zero-multiplier
shifted-power point is already the unique solid-simplex optimizer. -/
theorem powerKKTDecrease_zero_unique_minimizer
    {h m p : ℝ} (weight : ι → ℝ)
    (hh : 0 < h) (hp : 1 < p)
    (hmass : powerKKTMass h m p 0 weight ≤ 1) :
    IsUniqueMinimizerOn (SolidSimplex : (ι → ℝ) → Prop)
      (powerReducedObjective h m p weight)
      (powerKKTDecrease h m p 0 weight) := by
  have simplex : SolidSimplex (powerKKTDecrease h m p 0 weight) := by
    exact ⟨fun i => powerKKTDecrease_nonnegative weight hh hp i,
      by simpa [powerKKTMass] using hmass⟩
  apply power_unique_minimizer_of_simplex_kkt (lambda := 0) weight
    (powerKKTDecrease h m p 0 weight) hh hp simplex
  · exact le_rfl
  · simp
  · intro i
    simpa using powerKKT_gradient_ge_neg_eta (h := h) (m := m)
      (p := p) (eta := 0) weight hh hp i
  · intro i hi
    simpa using powerKKT_active_gradient (h := h) (m := m)
      (p := p) (eta := 0) weight hh hp i hi

/-- Shifted-power mass is continuous in the multiplier. -/
theorem continuous_powerKKTMass
    {h m p : ℝ} (weight : ι → ℝ) (_hh : 0 < h) (hp : 1 < p) :
    Continuous (fun eta => powerKKTMass h m p eta weight) := by
  classical
  unfold powerKKTMass powerKKTDecrease
  apply continuous_finsetSum
  intro i _
  apply (Real.continuous_rpow_const (powerShiftExponent_positive hp).le).comp
  apply Continuous.div_const
  exact (continuous_const.sub continuous_id).max continuous_const

omit [Fintype ι] in
/-- Increasing the nonnegative clipping multiplier weakly decreases every
shifted-power coordinate. -/
theorem powerKKTDecrease_antitone_multiplier
    {h m p etaOne etaTwo : ℝ} (weight : ι → ℝ)
    (hh : 0 < h) (hp : 1 < p) (heta : etaOne ≤ etaTwo) (i : ι) :
    powerKKTDecrease h m p etaTwo weight i ≤
      powerKKTDecrease h m p etaOne weight i := by
  have denominatorPositive : 0 < p * h :=
    mul_pos (lt_trans zero_lt_one hp) hh
  have numeratorOrder :
      max (m * weight i - etaTwo) 0 ≤
        max (m * weight i - etaOne) 0 := by
    exact max_le_max (by linarith) le_rfl
  have baseOrder :
      max (m * weight i - etaTwo) 0 / (p * h) ≤
        max (m * weight i - etaOne) 0 / (p * h) :=
    div_le_div_of_nonneg_right numeratorOrder denominatorPositive.le
  unfold powerKKTDecrease
  exact Real.rpow_le_rpow
    (div_nonneg (le_max_right _ _) denominatorPositive.le)
    baseOrder (powerShiftExponent_positive hp).le

theorem powerKKTMass_antitone_multiplier
    {h m p etaOne etaTwo : ℝ} (weight : ι → ℝ)
    (hh : 0 < h) (hp : 1 < p) (heta : etaOne ≤ etaTwo) :
    powerKKTMass h m p etaTwo weight ≤
      powerKKTMass h m p etaOne weight := by
  unfold powerKKTMass
  exact Finset.sum_le_sum fun i _ =>
    powerKKTDecrease_antitone_multiplier weight hh hp heta i

/-- If multiplier zero supplies at least unit mass and a nonnegative upper
multiplier clips every coordinate, continuity supplies an active KKT root. -/
theorem exists_powerKKT_multiplier
    {h m p upper : ℝ} (weight : ι → ℝ)
    (hh : 0 < h) (hp : 1 < p) (hupper : 0 ≤ upper)
    (hclips : ∀ i, m * weight i ≤ upper)
    (hmassZero : 1 ≤ powerKKTMass h m p 0 weight) :
    ∃ eta, 0 ≤ eta ∧ eta ≤ upper ∧
      powerKKTMass h m p eta weight = 1 := by
  have massUpperZero : powerKKTMass h m p upper weight = 0 := by
    classical
    unfold powerKKTMass powerKKTDecrease
    apply Finset.sum_eq_zero
    intro i _
    have numeratorNonpositive : m * weight i - upper ≤ 0 := by
      linarith [hclips i]
    rw [max_eq_right numeratorNonpositive, zero_div,
      Real.zero_rpow (powerShiftExponent_positive hp).ne']
  have targetInInterval :
      (1 : ℝ) ∈ Icc (powerKKTMass h m p upper weight)
        (powerKKTMass h m p 0 weight) := by
    rw [massUpperZero]
    exact ⟨zero_le_one, hmassZero⟩
  obtain ⟨eta, etaInterval, etaMass⟩ :=
    (intermediate_value_Icc' hupper
      (continuous_powerKKTMass weight hh hp).continuousOn) targetInInterval
  exact ⟨eta, etaInterval.1, etaInterval.2, etaMass⟩

end ShiftedPowerCandidate

section DirectionalPath

/-- Positional weight `N-i` on zero-based decrease coordinates. -/
def powerPathWeight (N : ℕ) (i : Fin N) : ℝ := ((N - i.1 : ℕ) : ℝ)

theorem powerPathWeight_positive {N : ℕ} (i : Fin N) :
    0 < powerPathWeight N i := by
  unfold powerPathWeight
  exact_mod_cast Nat.sub_pos_of_lt i.2

/-- Shifted-power decrease vector for a directional path of horizon `N`. -/
noncomputable def powerPathDecrease
    (h m p eta : ℝ) (N : ℕ) (i : Fin N) : ℝ :=
  powerKKTDecrease h m p eta (powerPathWeight N) i

/-- Total shifted-power decrease mass at a path horizon. -/
noncomputable def powerPathMass
    (h m p eta : ℝ) (N : ℕ) : ℝ :=
  powerKKTMass h m p eta (powerPathWeight N)

/-- Scale factor in the canonical zero-multiplier shifted-power sum. -/
noncomputable def powerPathScale (h m p : ℝ) : ℝ :=
  (m / (p * h)) ^ powerShiftExponent p

theorem powerPathScale_positive
    {h m p : ℝ} (hh : 0 < h) (hm : 0 < m) (hp : 1 < p) :
    0 < powerPathScale h m p := by
  unfold powerPathScale
  exact Real.rpow_pos_of_pos
    (div_pos hm (mul_pos (lt_trans zero_lt_one hp) hh)) _

/-- Canonical finite power sum `a Σ r^q`, written with the path's exact
positional weights. -/
noncomputable def powerPathShiftedSum
    (h m p : ℝ) (N : ℕ) : ℝ :=
  powerPathScale h m p *
    ∑ i : Fin N, (powerPathWeight N i) ^ powerShiftExponent p

/-- Reversal of finite path coordinates. -/
def finReverseEquiv (N : ℕ) : Fin N ≃ Fin N where
  toFun := Fin.rev
  invFun := Fin.rev
  left_inv := Fin.rev_involutive
  right_inv := Fin.rev_involutive

theorem powerPathWeight_reverse (N : ℕ) (i : Fin N) :
    powerPathWeight N (Fin.rev i) = ((i.1 + 1 : ℕ) : ℝ) := by
  unfold powerPathWeight Fin.rev
  have naturalIdentity : N - (N - (i.1 + 1)) = i.1 + 1 := by omega
  rw [naturalIdentity]

/-- Public ascending-index form `a Σ_{r=1}^N r^q` of the threshold sum. -/
theorem powerPathShiftedSum_eq_range
    (h m p : ℝ) (N : ℕ) :
    powerPathShiftedSum h m p N =
      powerPathScale h m p *
        ∑ r ∈ Finset.range N,
          (((r + 1 : ℕ) : ℝ) ^ powerShiftExponent p) := by
  unfold powerPathShiftedSum
  congr 1
  calc
    (∑ i : Fin N, powerPathWeight N i ^ powerShiftExponent p) =
        ∑ i : Fin N,
          powerPathWeight N ((finReverseEquiv N) i) ^ powerShiftExponent p := by
      symm
      exact Equiv.sum_comp (finReverseEquiv N)
        (fun i : Fin N => powerPathWeight N i ^ powerShiftExponent p)
    _ = ∑ i : Fin N, (((i.1 + 1 : ℕ) : ℝ) ^ powerShiftExponent p) := by
      apply Finset.sum_congr rfl
      intro i _
      change powerPathWeight N (Fin.rev i) ^ powerShiftExponent p = _
      rw [powerPathWeight_reverse]
    _ = ∑ r ∈ Finset.range N,
        (((r + 1 : ℕ) : ℝ) ^ powerShiftExponent p) := by
      exact Fin.sum_univ_eq_sum_range
        (fun r : ℕ => (((r + 1 : ℕ) : ℝ) ^ powerShiftExponent p)) N

/-- The canonical threshold sum dominates its linear lower bound `aN`.
This elementary bound is sufficient to prove that a first-zero threshold
exists at some finite horizon. -/
theorem powerPathShiftedSum_linear_lower_bound
    {h m p : ℝ} (N : ℕ) (hh : 0 < h) (hm : 0 < m) (hp : 1 < p) :
    powerPathScale h m p * (N : ℝ) ≤ powerPathShiftedSum h m p N := by
  rw [powerPathShiftedSum_eq_range]
  have eachTerm : ∀ r ∈ Finset.range N,
      (1 : ℝ) ≤ (((r + 1 : ℕ) : ℝ) ^ powerShiftExponent p) := by
    intro r _
    apply Real.one_le_rpow
    · exact_mod_cast Nat.succ_le_succ (Nat.zero_le r)
    · exact (powerShiftExponent_positive hp).le
  have sumLower :
      (N : ℝ) ≤ ∑ r ∈ Finset.range N,
        (((r + 1 : ℕ) : ℝ) ^ powerShiftExponent p) := by
    have := Finset.sum_le_sum eachTerm
    simpa using this
  exact mul_le_mul_of_nonneg_left sumLower
    (powerPathScale_positive hh hm hp).le

/-- For every positive parameter triple and real exponent above one, some
finite horizon reaches the canonical shifted-power threshold. -/
theorem exists_generalPower_threshold
    {h m p : ℝ} (hh : 0 < h) (hm : 0 < m) (hp : 1 < p) :
    ∃ N : ℕ, 1 ≤ powerPathShiftedSum h m p N := by
  let scale := powerPathScale h m p
  have scalePositive : 0 < scale := powerPathScale_positive hh hm hp
  obtain ⟨N, hN⟩ := exists_nat_ge (1 / scale)
  have scaledOne : 1 ≤ scale * (N : ℝ) := by
    have := (div_le_iff₀ scalePositive).mp hN
    simpa [one_div, mul_comm] using this
  exact ⟨N, scaledOne.trans
    (powerPathShiftedSum_linear_lower_bound N hh hm hp)⟩

theorem powerPathDecrease_zero_factorization
    {h m p : ℝ} {N : ℕ} (hh : 0 < h) (hm : 0 < m) (hp : 1 < p)
    (i : Fin N) :
    powerPathDecrease h m p 0 N i =
      powerPathScale h m p *
        (powerPathWeight N i) ^ powerShiftExponent p := by
  have denominatorPositive : 0 < p * h :=
    mul_pos (lt_trans zero_lt_one hp) hh
  have weightPositive : 0 < powerPathWeight N i := powerPathWeight_positive i
  have weightedPositive : 0 < m * powerPathWeight N i :=
    mul_pos hm weightPositive
  have scaleNonnegative : 0 ≤ m / (p * h) :=
    (div_pos hm denominatorPositive).le
  unfold powerPathDecrease powerKKTDecrease powerPathScale
  rw [sub_zero, max_eq_left weightedPositive.le]
  have factorization :
      m * powerPathWeight N i / (p * h) =
        (m / (p * h)) * powerPathWeight N i := by ring
  rw [factorization, Real.mul_rpow scaleNonnegative weightPositive.le]

theorem powerPathMass_zero_eq_shiftedSum
    {h m p : ℝ} (N : ℕ) (hh : 0 < h) (hm : 0 < m) (hp : 1 < p) :
    powerPathMass h m p 0 N = powerPathShiftedSum h m p N := by
  classical
  unfold powerPathMass powerKKTMass powerPathShiftedSum
  calc
    (∑ i : Fin N, powerKKTDecrease h m p 0 (powerPathWeight N) i) =
        ∑ i : Fin N, powerPathScale h m p *
          powerPathWeight N i ^ powerShiftExponent p := by
      apply Finset.sum_congr rfl
      intro i _
      exact powerPathDecrease_zero_factorization hh hm hp i
    _ = powerPathScale h m p *
        ∑ i : Fin N, powerPathWeight N i ^ powerShiftExponent p := by
      rw [Finset.mul_sum]

/-- Strict/weak all-horizon threshold cell.  It is stated directly in the
exact shifted-power mass whose closed form is the canonical power sum. -/
def GeneralPowerFirstZeroCell
    (h m p : ℝ) (K : ℕ) : Prop :=
  0 < K ∧ 0 < h ∧ 0 < m ∧ 1 < p ∧
    powerPathMass h m p 0 (K - 1) < 1 ∧
    1 ≤ powerPathMass h m p 0 K

theorem generalPowerFirstZeroCell_iff_shiftedSum
    {h m p : ℝ} {K : ℕ} :
    GeneralPowerFirstZeroCell h m p K ↔
      0 < K ∧ 0 < h ∧ 0 < m ∧ 1 < p ∧
        powerPathShiftedSum h m p (K - 1) < 1 ∧
        1 ≤ powerPathShiftedSum h m p K := by
  constructor
  · rintro ⟨hK, hh, hm, hp, hprevious, hboundary⟩
    rw [powerPathMass_zero_eq_shiftedSum (K - 1) hh hm hp] at hprevious
    rw [powerPathMass_zero_eq_shiftedSum K hh hm hp] at hboundary
    exact ⟨hK, hh, hm, hp, hprevious, hboundary⟩
  · rintro ⟨hK, hh, hm, hp, hprevious, hboundary⟩
    rw [← powerPathMass_zero_eq_shiftedSum (K - 1) hh hm hp] at hprevious
    rw [← powerPathMass_zero_eq_shiftedSum K hh hm hp] at hboundary
    exact ⟨hK, hh, hm, hp, hprevious, hboundary⟩

theorem powerPathShiftedSum_monotone
    {h m p : ℝ} (hh : 0 < h) (hm : 0 < m) (hp : 1 < p) :
    Monotone (powerPathShiftedSum h m p) := by
  intro M N hMN
  rw [powerPathShiftedSum_eq_range, powerPathShiftedSum_eq_range]
  apply mul_le_mul_of_nonneg_left _ (powerPathScale_positive hh hm hp).le
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hMN)
    (fun r _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-- The strict/weak threshold cell exists for every positive parameter triple
and is selected by the least horizon reaching the canonical power sum. -/
theorem exists_generalPowerFirstZeroCell
    {h m p : ℝ} (hh : 0 < h) (hm : 0 < m) (hp : 1 < p) :
    ∃ K : ℕ, GeneralPowerFirstZeroCell h m p K := by
  have thresholdExists :
      ∃ N : ℕ, 1 ≤ powerPathShiftedSum h m p N :=
    exists_generalPower_threshold hh hm hp
  let K := Nat.find thresholdExists
  have thresholdAtK : 1 ≤ powerPathShiftedSum h m p K :=
    Nat.find_spec thresholdExists
  have KPositive : 0 < K := by
    have KNonzero : K ≠ 0 := by
      intro KZero
      have impossible :
          (1 : ℝ) ≤ powerPathShiftedSum h m p 0 := by
        simpa [K, KZero] using thresholdAtK
      norm_num [powerPathShiftedSum] at impossible
    exact Nat.pos_of_ne_zero KNonzero
  have previousBelow : powerPathShiftedSum h m p (K - 1) < 1 := by
    have previousBefore : K - 1 < K := by omega
    exact lt_of_not_ge (Nat.find_min thresholdExists previousBefore)
  exact ⟨K, (generalPowerFirstZeroCell_iff_shiftedSum).2
    ⟨KPositive, hh, hm, hp, previousBelow, thresholdAtK⟩⟩

/-- The strict/weak threshold cell determines one and only one first-zero
horizon. -/
theorem generalPowerFirstZeroCell_unique
    {h m p : ℝ} {K L : ℕ}
    (hK : GeneralPowerFirstZeroCell h m p K)
    (hL : GeneralPowerFirstZeroCell h m p L) : K = L := by
  rcases (generalPowerFirstZeroCell_iff_shiftedSum).1 hK with
    ⟨_KPositive, hh, hm, hp, KPrevious, KThreshold⟩
  rcases (generalPowerFirstZeroCell_iff_shiftedSum).1 hL with
    ⟨_LPositive, _hh, _hm, _hp, LPrevious, LThreshold⟩
  rcases lt_trichotomy K L with KBeforeL | rfl | LBeforeK
  · have KlePrevious : K ≤ L - 1 := by omega
    have monotoneBound := powerPathShiftedSum_monotone hh hm hp KlePrevious
    exfalso
    linarith
  · rfl
  · have LlePrevious : L ≤ K - 1 := by omega
    have monotoneBound := powerPathShiftedSum_monotone hh hm hp LlePrevious
    exfalso
    linarith

theorem powerPathWeight_le_horizon {N : ℕ} (i : Fin N) :
    powerPathWeight N i ≤ (N : ℝ) := by
  unfold powerPathWeight
  exact_mod_cast Nat.sub_le N i.1

/-- A threshold cell supplies an active multiplier and hence an explicit
unique optimizer at its boundary horizon. -/
theorem generalPower_boundary_optimizer_exists
    {h m p : ℝ} {K : ℕ} (hcell : GeneralPowerFirstZeroCell h m p K) :
    ∃ eta, 0 ≤ eta ∧ eta ≤ m * K ∧
      powerPathMass h m p eta K = 1 ∧
      IsUniqueMinimizerOn (SolidSimplex : (Fin K → ℝ) → Prop)
        (powerReducedObjective h m p (powerPathWeight K))
        (powerPathDecrease h m p eta K) := by
  rcases hcell with ⟨hK, hh, hm, hp, _hprevious, hboundary⟩
  have upperNonnegative : 0 ≤ m * (K : ℝ) :=
    mul_nonneg hm.le (Nat.cast_nonneg K)
  have clips : ∀ i : Fin K, m * powerPathWeight K i ≤ m * (K : ℝ) :=
    fun i => mul_le_mul_of_nonneg_left (powerPathWeight_le_horizon i) hm.le
  obtain ⟨eta, etaNonnegative, etaUpper, etaMass⟩ :=
    exists_powerKKT_multiplier (powerPathWeight K) hh hp upperNonnegative
      clips (by simpa [powerPathMass] using hboundary)
  refine ⟨eta, etaNonnegative, etaUpper, ?_, ?_⟩
  · simpa [powerPathMass] using etaMass
  · change IsUniqueMinimizerOn (SolidSimplex : (Fin K → ℝ) → Prop)
      (powerReducedObjective h m p (powerPathWeight K))
      (powerKKTDecrease h m p eta (powerPathWeight K))
    exact powerKKTDecrease_unique_minimizer (powerPathWeight K) hh hp
      etaNonnegative etaMass

/-- Canonical embedding of an old boundary coordinate into an extended
horizon. -/
def powerPathOldIndex {K : ℕ} (R : ℕ) (i : Fin K) : Fin (K + R) :=
  ⟨i.1, lt_of_lt_of_le i.2 (Nat.le_add_right K R)⟩

/-- Canonical coordinate in the appended tail. -/
def powerPathNewIndex (K : ℕ) {R : ℕ} (j : Fin R) : Fin (K + R) :=
  ⟨K + j.1, Nat.add_lt_add_left j.2 K⟩

theorem powerPathWeight_oldIndex
    {K : ℕ} (R : ℕ) (i : Fin K) :
    powerPathWeight (K + R) (powerPathOldIndex R i) =
      powerPathWeight K i + (R : ℝ) := by
  unfold powerPathWeight powerPathOldIndex
  have naturalIdentity : K + R - i.1 = (K - i.1) + R := by omega
  rw [naturalIdentity, Nat.cast_add]

theorem powerPathWeight_newIndex
    (K : ℕ) {R : ℕ} (j : Fin R) :
    powerPathWeight (K + R) (powerPathNewIndex K j) =
      powerPathWeight R j := by
  unfold powerPathWeight powerPathNewIndex
  have naturalIdentity : K + R - (K + j.1) = R - j.1 := by omega
  rw [naturalIdentity]

/-- Shifting the multiplier by `mR` preserves every old decrease exactly. -/
theorem powerPathDecrease_extension_old
    {h m p eta : ℝ} {K : ℕ} (R : ℕ) (i : Fin K) :
    powerPathDecrease h m p (eta + m * R) (K + R)
        (powerPathOldIndex R i) =
      powerPathDecrease h m p eta K i := by
  unfold powerPathDecrease powerKKTDecrease
  rw [powerPathWeight_oldIndex]
  have numeratorIdentity :
      m * (powerPathWeight K i + (R : ℝ)) - (eta + m * (R : ℝ)) =
        m * powerPathWeight K i - eta := by ring
  rw [numeratorIdentity]

/-- Every newly appended coordinate is clipped to zero by the shifted
multiplier. -/
theorem powerPathDecrease_extension_new_zero
    {h m p eta : ℝ} {K R : ℕ}
    (_hh : 0 < h) (hm : 0 < m) (hp : 1 < p) (heta : 0 ≤ eta)
    (j : Fin R) :
    powerPathDecrease h m p (eta + m * R) (K + R)
        (powerPathNewIndex K j) = 0 := by
  have weightBound : powerPathWeight R j ≤ (R : ℝ) :=
    powerPathWeight_le_horizon j
  have numeratorNonpositive :
      m * powerPathWeight (K + R) (powerPathNewIndex K j) -
          (eta + m * (R : ℝ)) ≤ 0 := by
    rw [powerPathWeight_newIndex]
    have := mul_le_mul_of_nonneg_left weightBound hm.le
    linarith
  unfold powerPathDecrease powerKKTDecrease
  rw [max_eq_right numeratorNonpositive, zero_div,
    Real.zero_rpow (powerShiftExponent_positive hp).ne']

/-- Exact total-mass preservation under extension. -/
theorem powerPathMass_extension
    {h m p eta : ℝ} {K : ℕ} (R : ℕ)
    (hh : 0 < h) (hm : 0 < m) (hp : 1 < p) (heta : 0 ≤ eta) :
    powerPathMass h m p (eta + m * R) (K + R) =
      powerPathMass h m p eta K := by
  classical
  unfold powerPathMass powerKKTMass
  rw [Fin.sum_univ_add]
  have oldPart :
      (∑ i : Fin K,
        powerKKTDecrease h m p (eta + m * R)
          (powerPathWeight (K + R)) (Fin.castAdd R i)) =
        ∑ i : Fin K,
          powerKKTDecrease h m p eta (powerPathWeight K) i := by
    apply Finset.sum_congr rfl
    intro i _
    have indexIdentity : Fin.castAdd R i = powerPathOldIndex R i := by
      apply Fin.ext
      rfl
    rw [indexIdentity]
    exact powerPathDecrease_extension_old (h := h) (m := m) (p := p)
      (eta := eta) R i
  rw [oldPart]
  have newPart :
      (∑ j : Fin R,
        powerKKTDecrease h m p (eta + m * R)
          (powerPathWeight (K + R)) (Fin.natAdd K j)) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    have indexIdentity : Fin.natAdd K j = powerPathNewIndex K j := by
      apply Fin.ext
      rfl
    rw [indexIdentity]
    exact powerPathDecrease_extension_new_zero (h := h) (m := m) (p := p)
      (eta := eta) (K := K) hh hm hp heta j
  rw [newPart, add_zero]

/-- The boundary multiplier selected by the strict/weak threshold cell is
strictly smaller than the smallest positive path load `m`. -/
theorem generalPower_boundary_multiplier_lt_m
    {h m p eta : ℝ} {K : ℕ}
    (hcell : GeneralPowerFirstZeroCell h m p K)
    (_heta : 0 ≤ eta) (hmass : powerPathMass h m p eta K = 1) :
    eta < m := by
  rcases hcell with ⟨hK, hh, hm, hp, hprevious, _hboundary⟩
  by_contra notLess
  have mLeEta : m ≤ eta := le_of_not_gt notLess
  let previousEta := eta - m
  have previousEtaNonnegative : 0 ≤ previousEta := by
    dsimp [previousEta]
    linarith
  have extensionIdentity :
      powerPathMass h m p eta K =
        powerPathMass h m p previousEta (K - 1) := by
    have raw := powerPathMass_extension (h := h) (m := m) (p := p)
      (eta := previousEta) (K := K - 1) 1 hh hm hp previousEtaNonnegative
    have horizonIdentity : K - 1 + 1 = K := Nat.sub_add_cancel hK
    have etaIdentity : previousEta + m = eta := by
      dsimp [previousEta]
      ring
    simpa [horizonIdentity, etaIdentity] using raw
  have massOrder :
      powerPathMass h m p previousEta (K - 1) ≤
        powerPathMass h m p 0 (K - 1) := by
    unfold powerPathMass
    exact powerKKTMass_antitone_multiplier (powerPathWeight (K - 1))
      hh hp previousEtaNonnegative
  rw [hmass] at extensionIdentity
  linarith

/-- Every decrease at the first-zero horizon is strictly positive. -/
theorem powerPathDecrease_boundary_positive
    {h m p eta : ℝ} {K : ℕ}
    (hh : 0 < h) (hm : 0 < m) (hp : 1 < p) (heta : eta < m)
    (i : Fin K) :
    0 < powerPathDecrease h m p eta K i := by
  have oneLeWeight : (1 : ℝ) ≤ powerPathWeight K i := by
    have naturalPositive : 0 < K - i.1 := Nat.sub_pos_of_lt i.2
    have naturalOneLe : 1 ≤ K - i.1 := naturalPositive
    unfold powerPathWeight
    exact_mod_cast naturalOneLe
  have mLeWeighted : m ≤ m * powerPathWeight K i := by
    nlinarith
  have numeratorPositive : 0 < m * powerPathWeight K i - eta := by
    linarith
  have denominatorPositive : 0 < p * h :=
    mul_pos (lt_trans zero_lt_one hp) hh
  unfold powerPathDecrease powerKKTDecrease
  rw [max_eq_left numeratorPositive.le]
  exact Real.rpow_pos_of_pos
    (div_pos numeratorPositive denominatorPositive) _

/-- Activity reconstructed as the remaining decrease mass. -/
noncomputable def powerProfileFromDecreases
    {K : ℕ} (decrease : Fin K → ℝ) (i : ℕ) : ℝ :=
  ∑ j : Fin K, if i ≤ j.1 then decrease j else 0

theorem powerProfileFromDecreases_at_zero
    {K : ℕ} (decrease : Fin K → ℝ) :
    powerProfileFromDecreases decrease 0 = ∑ j, decrease j := by
  simp [powerProfileFromDecreases]

theorem powerProfileFromDecreases_zero_of_support_le
    {K i : ℕ} (decrease : Fin K → ℝ) (hKi : K ≤ i) :
    powerProfileFromDecreases decrease i = 0 := by
  unfold powerProfileFromDecreases
  apply Finset.sum_eq_zero
  intro j _
  rw [if_neg]
  exact not_le.mpr (lt_of_lt_of_le j.2 hKi)

theorem powerProfileFromDecreases_positive_before_support
    {K i : ℕ} (decrease : Fin K → ℝ)
    (hNonnegative : ∀ j, 0 ≤ decrease j)
    (hPositive : ∀ j, 0 < decrease j) (hiK : i < K) :
    0 < powerProfileFromDecreases decrease i := by
  unfold powerProfileFromDecreases
  apply Finset.sum_pos'
  · intro j _
    split_ifs
    · exact hNonnegative j
    · exact le_rfl
  · let selected : Fin K := ⟨i, hiK⟩
    refine ⟨selected, Finset.mem_univ selected, ?_⟩
    simp [selected, hPositive selected]

/-- Exact first-zero law at the active boundary: the reconstructed profile
is positive precisely before `K` and zero at and after `K`. -/
theorem generalPower_exact_first_zero
    {h m p eta : ℝ} {K i : ℕ}
    (hcell : GeneralPowerFirstZeroCell h m p K)
    (heta : 0 ≤ eta) (hmass : powerPathMass h m p eta K = 1) :
    0 < powerProfileFromDecreases (powerPathDecrease h m p eta K) i ↔ i < K := by
  rcases hcell with ⟨hK, hh, hm, hp, hprevious, hboundary⟩
  have etaBelowM : eta < m :=
    generalPower_boundary_multiplier_lt_m
      ⟨hK, hh, hm, hp, hprevious, hboundary⟩ heta hmass
  constructor
  · intro profilePositive
    by_contra notBefore
    have supportLe : K ≤ i := Nat.le_of_not_gt notBefore
    rw [powerProfileFromDecreases_zero_of_support_le _ supportLe] at profilePositive
    exact (lt_irrefl 0 profilePositive)
  · intro before
    apply powerProfileFromDecreases_positive_before_support
    · exact fun j => powerKKTDecrease_nonnegative (powerPathWeight K) hh hp j
    · exact fun j => powerPathDecrease_boundary_positive hh hm hp etaBelowM j
    · exact before

/-- A boundary optimizer remains the unique optimizer at every longer
horizon after the exact affine multiplier shift. -/
theorem generalPower_extension_stable_unique_optimizer
    {h m p eta : ℝ} {K : ℕ}
    (hh : 0 < h) (hm : 0 < m) (hp : 1 < p) (heta : 0 ≤ eta)
    (hmass : powerPathMass h m p eta K = 1) (R : ℕ) :
    IsUniqueMinimizerOn (SolidSimplex : (Fin (K + R) → ℝ) → Prop)
      (powerReducedObjective h m p (powerPathWeight (K + R)))
      (powerPathDecrease h m p (eta + m * R) (K + R)) := by
  have extendedEtaNonnegative : 0 ≤ eta + m * (R : ℝ) :=
    add_nonneg heta (mul_nonneg hm.le (Nat.cast_nonneg R))
  have extendedMass :
      powerPathMass h m p (eta + m * R) (K + R) = 1 := by
    rw [powerPathMass_extension R hh hm hp heta, hmass]
  change IsUniqueMinimizerOn
    (SolidSimplex : (Fin (K + R) → ℝ) → Prop)
    (powerReducedObjective h m p (powerPathWeight (K + R)))
    (powerKKTDecrease h m p (eta + m * R) (powerPathWeight (K + R)))
  exact powerKKTDecrease_unique_minimizer (powerPathWeight (K + R)) hh hp
    extendedEtaNonnegative (by simpa [powerPathMass] using extendedMass)

/-- Reconstructing activities after extension gives exactly the same old
profile: the appended inactive decreases contribute no tail mass. -/
theorem generalPower_profile_extension_stable
    {h m p eta : ℝ} {K : ℕ}
    (hh : 0 < h) (hm : 0 < m) (hp : 1 < p) (heta : 0 ≤ eta)
    (R i : ℕ) :
    powerProfileFromDecreases
        (powerPathDecrease h m p (eta + m * R) (K + R)) i =
      powerProfileFromDecreases (powerPathDecrease h m p eta K) i := by
  classical
  unfold powerProfileFromDecreases
  rw [Fin.sum_univ_add]
  have oldPart :
      (∑ j : Fin K,
        if i ≤ (Fin.castAdd R j).1 then
          powerPathDecrease h m p (eta + m * R) (K + R)
            (Fin.castAdd R j)
        else 0) =
      ∑ j : Fin K, if i ≤ j.1 then powerPathDecrease h m p eta K j else 0 := by
    apply Finset.sum_congr rfl
    intro j _
    have indexIdentity : Fin.castAdd R j = powerPathOldIndex R j := by
      apply Fin.ext
      rfl
    by_cases hij : i ≤ j.1
    · simp only [Fin.val_castAdd, hij, if_true]
      rw [indexIdentity, powerPathDecrease_extension_old]
    · simp only [Fin.val_castAdd, hij, if_false]
  rw [oldPart]
  have newPart :
      (∑ j : Fin R,
        if i ≤ (Fin.natAdd K j).1 then
          powerPathDecrease h m p (eta + m * R) (K + R)
            (Fin.natAdd K j)
        else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    split_ifs
    · have indexIdentity : Fin.natAdd K j = powerPathNewIndex K j := by
        apply Fin.ext
        rfl
      rw [indexIdentity]
      exact powerPathDecrease_extension_new_zero hh hm hp heta j
    · rfl
  rw [newPart, add_zero]

/-- The exact first-zero index is unchanged at every extended horizon. -/
theorem generalPower_all_horizon_exact_first_zero
    {h m p eta : ℝ} {K : ℕ}
    (hcell : GeneralPowerFirstZeroCell h m p K)
    (heta : 0 ≤ eta) (hmass : powerPathMass h m p eta K = 1)
    (R i : ℕ) :
    0 < powerProfileFromDecreases
        (powerPathDecrease h m p (eta + m * R) (K + R)) i ↔ i < K := by
  have cellData := hcell
  rcases cellData with ⟨_hK, hh, hm, hp, _hprevious, _hboundary⟩
  rw [generalPower_profile_extension_stable hh hm hp heta]
  exact generalPower_exact_first_zero hcell heta hmass

/-- General real-exponent all-horizon finite-persistence package.  The
threshold power sum selects a boundary multiplier below `m`; the unique
boundary winner has first zero exactly at `K`; and every longer unique winner
preserves the old decrease vector while appending inactive zeros. -/
theorem generalPower_all_horizon_finite_persistence
    {h m p : ℝ} {K : ℕ} (hcell : GeneralPowerFirstZeroCell h m p K) :
    ∃ eta,
      0 ≤ eta ∧ eta < m ∧ powerPathMass h m p eta K = 1 ∧
      IsUniqueMinimizerOn (SolidSimplex : (Fin K → ℝ) → Prop)
        (powerReducedObjective h m p (powerPathWeight K))
        (powerPathDecrease h m p eta K) ∧
      (∀ i : ℕ,
        0 < powerProfileFromDecreases
          (powerPathDecrease h m p eta K) i ↔ i < K) ∧
      (∀ R : ℕ,
        IsUniqueMinimizerOn
          (SolidSimplex : (Fin (K + R) → ℝ) → Prop)
          (powerReducedObjective h m p (powerPathWeight (K + R)))
          (powerPathDecrease h m p (eta + m * R) (K + R)) ∧
        (∀ i : Fin K,
          powerPathDecrease h m p (eta + m * R) (K + R)
              (powerPathOldIndex R i) =
            powerPathDecrease h m p eta K i) ∧
        (∀ j : Fin R,
          powerPathDecrease h m p (eta + m * R) (K + R)
              (powerPathNewIndex K j) = 0)) := by
  obtain ⟨eta, etaNonnegative, _etaUpper, etaMass, boundaryUnique⟩ :=
    generalPower_boundary_optimizer_exists hcell
  have cellData := hcell
  rcases cellData with ⟨_hK, hh, hm, hp, _hprevious, _hboundary⟩
  have etaBelowM :=
    generalPower_boundary_multiplier_lt_m hcell etaNonnegative etaMass
  refine ⟨eta, etaNonnegative, etaBelowM, etaMass, boundaryUnique,
    fun i => generalPower_exact_first_zero hcell etaNonnegative etaMass,
    ?_⟩
  intro R
  exact ⟨generalPower_extension_stable_unique_optimizer
      hh hm hp etaNonnegative etaMass R,
    fun i => powerPathDecrease_extension_old R i,
    fun j => powerPathDecrease_extension_new_zero
      hh hm hp etaNonnegative j⟩

/-- Unconditional CHG-B2 closure.  Every positive parameter triple with
`p > 1` determines a unique finite first-zero horizon, a boundary
shifted-power multiplier, and unique extension-stable optimizers whose
reconstructed activity has that same exact first zero at every horizon. -/
theorem generalPower_unconditional_all_horizon_finite_persistence
    {h m p : ℝ} (hh : 0 < h) (hm : 0 < m) (hp : 1 < p) :
    ∃ K : ℕ,
      GeneralPowerFirstZeroCell h m p K ∧
      (∀ L : ℕ, GeneralPowerFirstZeroCell h m p L → L = K) ∧
      ∃ eta,
        0 ≤ eta ∧ eta < m ∧ powerPathMass h m p eta K = 1 ∧
        IsUniqueMinimizerOn (SolidSimplex : (Fin K → ℝ) → Prop)
          (powerReducedObjective h m p (powerPathWeight K))
          (powerPathDecrease h m p eta K) ∧
        (∀ R : ℕ,
          IsUniqueMinimizerOn
            (SolidSimplex : (Fin (K + R) → ℝ) → Prop)
            (powerReducedObjective h m p (powerPathWeight (K + R)))
            (powerPathDecrease h m p (eta + m * R) (K + R))) ∧
        (∀ R i : ℕ,
          0 < powerProfileFromDecreases
              (powerPathDecrease h m p (eta + m * R) (K + R)) i ↔
            i < K) := by
  obtain ⟨K, hcell⟩ := exists_generalPowerFirstZeroCell hh hm hp
  obtain ⟨eta, etaNonnegative, etaBelowM, etaMass, boundaryUnique,
      _boundarySupport, extensions⟩ :=
    generalPower_all_horizon_finite_persistence hcell
  refine ⟨K, hcell,
    fun L hL => generalPowerFirstZeroCell_unique hL hcell,
    eta, etaNonnegative, etaBelowM, etaMass, boundaryUnique, ?_, ?_⟩
  · intro R
    exact (extensions R).1
  · intro R i
    exact generalPower_all_horizon_exact_first_zero
      hcell etaNonnegative etaMass R i

end DirectionalPath

end PhonologicalCalculus.ContinuousHG
