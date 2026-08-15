import PhonologicalCalculus.ContinuousHG.ParameterIdentifiability
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Strict log-concavity and triple identifiability

This file proves the positive-root theorem underlying three-point recovery of
the exponent in the directional continuous-HG family.  The proof is separated
into an exponential normal form and an exact bridge to positive ratios.
-/

namespace PhonologicalCalculus.ContinuousHG

noncomputable section

/-- Exponential normal form of the normalized three-point equation. -/
def exponentialTriple (alpha beta s : ℝ) : ℝ :=
  Real.exp (alpha * s) + Real.exp (-beta * s)

/-- The exponential normal form takes the value two at exponent zero. -/
@[simp] theorem exponentialTriple_zero (alpha beta : ℝ) :
    exponentialTriple alpha beta 0 = 2 := by
  norm_num [exponentialTriple]

/-- Derivative of the exponential normal form. -/
theorem hasDerivAt_exponentialTriple (alpha beta s : ℝ) :
    HasDerivAt (exponentialTriple alpha beta)
      (alpha * Real.exp (alpha * s) -
        beta * Real.exp (-beta * s)) s := by
  have h₁ := ((hasDerivAt_id s).const_mul alpha).exp
  have h₂ := ((hasDerivAt_id s).const_mul (-beta)).exp
  change HasDerivAt
    ((fun x : ℝ => Real.exp (alpha * x)) +
      fun x : ℝ => Real.exp (-beta * x))
    (alpha * Real.exp (alpha * s) - beta * Real.exp (-beta * s)) s
  simpa only [id_eq, mul_one, sub_eq_add_neg,
    neg_mul, mul_neg, Pi.add_apply, mul_comm] using h₁.add h₂

/-- The derivative at zero is the difference of the two logarithmic slopes. -/
theorem deriv_exponentialTriple_zero (alpha beta : ℝ) :
    deriv (exponentialTriple alpha beta) 0 = alpha - beta := by
  simpa using (hasDerivAt_exponentialTriple alpha beta 0).deriv

/-- A nonconstant exponential of a linear form is strictly convex. -/
theorem strictConvexOn_exp_mul {k : ℝ} (hk : k ≠ 0) :
    StrictConvexOn ℝ Set.univ (fun x : ℝ => Real.exp (k * x)) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ hxy a b ha hb hab
  have hargs : k * x ≠ k * y := by
    intro h
    apply hxy
    exact mul_left_cancel₀ hk h
  have h := strictConvexOn_exp.2 (Set.mem_univ (k * x))
    (Set.mem_univ (k * y)) hargs ha hb hab
  have hlin : k * (a * x + b * y) = a * (k * x) + b * (k * y) := by
    ring
  simp only [smul_eq_mul] at h ⊢
  rw [hlin]
  exact h

/-- Positive logarithmic slopes make the normalized triple strictly convex. -/
theorem strictConvexOn_exponentialTriple
    {alpha beta : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta) :
    StrictConvexOn ℝ Set.univ (exponentialTriple alpha beta) := by
  have h₁ := strictConvexOn_exp_mul (ne_of_gt halpha)
  have h₂ := strictConvexOn_exp_mul (neg_ne_zero.mpr (ne_of_gt hbeta))
  change StrictConvexOn ℝ Set.univ
    ((fun x : ℝ => Real.exp (alpha * x)) +
      fun x : ℝ => Real.exp (-beta * x))
  exact h₁.add h₂

/-- If the rising logarithmic slope is positive but smaller than the falling
logarithmic slope, the normalized triple returns to two at some positive
exponent. -/
theorem exponentialTriple_exists_positive_root
    {alpha beta : ℝ} (halpha : 0 < alpha) (hslope : alpha < beta) :
    ∃ s : ℝ, 0 < s ∧ exponentialTriple alpha beta s = 2 := by
  let g : ℝ → ℝ := fun s =>
    alpha * Real.exp (alpha * s) - beta * Real.exp (-beta * s)
  have hgContinuous : Continuous g := by
    dsimp [g]
    fun_prop
  have hgZero : g 0 < 0 := by
    dsimp [g]
    simp
    linarith
  have hgOpen : IsOpen {s : ℝ | g s < 0} :=
    isOpen_lt hgContinuous continuous_const
  obtain ⟨epsilon, hepsilon, hball⟩ :=
    (Metric.isOpen_iff.mp hgOpen) 0 hgZero
  let t : ℝ := epsilon / 2
  have htPositive : 0 < t := by
    dsimp [t]
    linarith
  have htSmall : t < epsilon := by
    dsimp [t]
    linarith
  have hContinuous : Continuous (exponentialTriple alpha beta) := by
    unfold exponentialTriple
    fun_prop
  have hAnti : StrictAntiOn (exponentialTriple alpha beta) (Set.Icc 0 t) := by
    apply strictAntiOn_of_deriv_neg (D := Set.Icc 0 t)
      (convex_Icc (𝕜 := ℝ) 0 t) hContinuous.continuousOn
    intro x hx
    rw [(hasDerivAt_exponentialTriple alpha beta x).deriv]
    apply hball
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]
    have hxIcc : x ∈ Set.Icc 0 t := interior_subset hx
    rw [abs_of_nonneg hxIcc.1]
    exact lt_of_le_of_lt hxIcc.2 htSmall
  have htBelow : exponentialTriple alpha beta t < 2 := by
    have h := hAnti (show 0 ∈ Set.Icc (0 : ℝ) t by
        exact ⟨le_rfl, htPositive.le⟩)
      (show t ∈ Set.Icc (0 : ℝ) t by exact ⟨htPositive.le, le_rfl⟩)
      htPositive
    simpa using h
  have hLinear : Filter.Tendsto (fun s : ℝ => alpha * s)
      Filter.atTop Filter.atTop :=
    Filter.tendsto_id.const_mul_atTop halpha
  have hExp : Filter.Tendsto (fun s : ℝ => Real.exp (alpha * s))
      Filter.atTop Filter.atTop :=
    Real.tendsto_exp_atTop.comp hLinear
  obtain ⟨S, htS, hSExp⟩ :=
    ((Filter.eventually_gt_atTop t).and
      (hExp.eventually_gt_atTop 2)).exists
  have hSAbove : 2 < exponentialTriple alpha beta S := by
    unfold exponentialTriple
    nlinarith [Real.exp_pos (-beta * S)]
  have hTwoBetween :
      (2 : ℝ) ∈ Set.Icc (exponentialTriple alpha beta t)
        (exponentialTriple alpha beta S) :=
    ⟨htBelow.le, hSAbove.le⟩
  obtain ⟨s, hsInterval, hsValue⟩ :=
    (intermediate_value_Icc htS.le hContinuous.continuousOn) hTwoBetween
  exact ⟨s, lt_of_lt_of_le htPositive hsInterval.1, hsValue⟩

/-- Under the strict logarithmic-slope inequality, the return to two has one
and only one positive exponent. -/
theorem exponentialTriple_existsUnique_positive_root
    {alpha beta : ℝ} (halpha : 0 < alpha) (hslope : alpha < beta) :
    ∃! s : ℝ, 0 < s ∧ exponentialTriple alpha beta s = 2 := by
  obtain ⟨s, hsPositive, hsValue⟩ :=
    exponentialTriple_exists_positive_root halpha hslope
  have hbeta : 0 < beta := lt_trans halpha hslope
  have hStrict := strictConvexOn_exponentialTriple halpha hbeta
  refine ⟨s, ⟨hsPositive, hsValue⟩, ?_⟩
  intro y hy
  rcases lt_trichotomy y s with hys | hys | hsy
  · have hySegment : y ∈ openSegment ℝ (0 : ℝ) s := by
      rw [openSegment_eq_Ioo hsPositive]
      exact ⟨hy.1, hys⟩
    have hBelow := hStrict.lt_on_openSegment
      (show (0 : ℝ) ∈ Set.univ by simp)
      (show s ∈ Set.univ by simp) (ne_of_lt hsPositive) hySegment
    rw [exponentialTriple_zero, hsValue, max_self, hy.2] at hBelow
    exact (lt_irrefl 2 hBelow).elim
  · exact hys
  · have hsSegment : s ∈ openSegment ℝ (0 : ℝ) y := by
      rw [openSegment_eq_Ioo hy.1]
      exact ⟨hsPositive, hsy⟩
    have hBelow := hStrict.lt_on_openSegment
      (show (0 : ℝ) ∈ Set.univ by simp)
      (show y ∈ Set.univ by simp) (ne_of_lt hy.1) hsSegment
    rw [exponentialTriple_zero, hy.2, max_self, hsValue] at hBelow
    exact (lt_irrefl 2 hBelow).elim

/-- For a strictly decreasing positive triple, strict log-concavity is exactly
the slope condition that forces one nonzero positive solution of the
normalized powered-ratio equation. -/
theorem logConcaveTriple_existsUnique_positive_root
    {a b c : ℝ} (hc : 0 < c) (hcb : c < b) (hba : b < a)
    (hLogConcave : a * c < b ^ 2) :
    ∃! s : ℝ,
      0 < s ∧ (a / b) ^ s + (c / b) ^ s = 2 := by
  have hb : 0 < b := lt_trans hc hcb
  have hrise : 1 < a / b := (one_lt_div hb).2 hba
  have hrisePositive : 0 < a / b := lt_trans zero_lt_one hrise
  have hfallPositive : 0 < c / b := div_pos hc hb
  have hfall : c / b < 1 := (div_lt_one hb).2 hcb
  have hproduct : (a / b) * (c / b) < 1 := by
    rw [div_mul_div_comm, div_lt_one (mul_pos hb hb)]
    simpa only [pow_two] using hLogConcave
  have hlogProduct : Real.log ((a / b) * (c / b)) < 0 :=
    Real.log_neg (mul_pos hrisePositive hfallPositive) hproduct
  have hlogSum : Real.log (a / b) + Real.log (c / b) < 0 := by
    rw [Real.log_mul hrisePositive.ne' hfallPositive.ne'] at hlogProduct
    exact hlogProduct
  have hAlpha : 0 < Real.log (a / b) := Real.log_pos hrise
  have hSlope : Real.log (a / b) < -Real.log (c / b) := by
    linarith
  obtain ⟨s, hs, hunique⟩ :=
    exponentialTriple_existsUnique_positive_root hAlpha hSlope
  refine ⟨s, ⟨hs.1, ?_⟩, ?_⟩
  · rw [Real.rpow_def_of_pos hrisePositive,
      Real.rpow_def_of_pos hfallPositive]
    simpa [exponentialTriple] using hs.2
  · intro y hy
    apply hunique y
    refine ⟨hy.1, ?_⟩
    rw [Real.rpow_def_of_pos hrisePositive,
      Real.rpow_def_of_pos hfallPositive] at hy
    simpa [exponentialTriple] using hy.2

/-- Reparameterizing the unique positive root by `p = s + 1` gives one and
only one admissible penalty exponent above one. -/
theorem logConcaveTriple_existsUnique_exponentAboveOne
    {a b c : ℝ} (hc : 0 < c) (hcb : c < b) (hba : b < a)
    (hLogConcave : a * c < b ^ 2) :
    ∃! p : ℝ,
      1 < p ∧ (a / b) ^ (p - 1) + (c / b) ^ (p - 1) = 2 := by
  obtain ⟨s, hs, hunique⟩ :=
    logConcaveTriple_existsUnique_positive_root hc hcb hba hLogConcave
  refine ⟨s + 1, ⟨by linarith, ?_⟩, ?_⟩
  · simpa using hs.2
  · intro p hp
    have hroot : p - 1 = s := hunique (p - 1) ⟨by linarith, hp.2⟩
    linarith

end

end PhonologicalCalculus.ContinuousHG
