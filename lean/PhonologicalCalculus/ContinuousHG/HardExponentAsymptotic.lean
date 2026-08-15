import PhonologicalCalculus.ContinuousHG.HardExponent
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Sharp hard-exponent magnitude asymptotic

The basic hard-exponent theorem proves that the sole positive follower tends
to zero.  This module proves the sharper asymptotic equivalence: its activity
is first-order equal to the logarithmic scale
`log (p * rho) / (p - 1)`.
-/

namespace PhonologicalCalculus.ContinuousHG

open Filter Set
open scoped Topology

/-- The exponential remainder has unit first-order ratio at zero. -/
theorem one_sub_exp_neg_div_tendsto_one :
    Tendsto (fun t : ℝ => (1 - Real.exp (-t)) / t)
      (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
  have hderiv : HasDerivAt (fun t : ℝ => Real.exp (-t)) (-1) 0 := by
    (convert (hasDerivAt_neg' (x := (0 : ℝ))).exp using 1; norm_num)
  have hslope := hderiv.tendsto_slope_zero
  have hneg := hslope.neg
  convert hneg using 1
  · funext t
    simp [div_eq_mul_inv]
    ring
  · norm_num

/-- For a fixed positive harmony ratio, the hard-exponent logarithmic scale
is eventually strictly positive, hence eventually nonzero. -/
theorem hardExponentScale_eventually_pos {rho : ℝ} (hrho : 0 < rho) :
    ∀ᶠ p : ℝ in atTop, 0 < hardExponentScale rho p := by
  filter_upwards [eventually_gt_atTop (max 1 (1 / rho))] with p hp
  have hp1 : 1 < p := lt_of_le_of_lt (le_max_left _ _) hp
  have hprho : 1 < p * rho := by
    have hpinv : 1 / rho < p := lt_of_le_of_lt (le_max_right _ _) hp
    exact (div_lt_iff₀ hrho).mp (by simpa using hpinv)
  unfold hardExponentScale
  exact div_pos (Real.log_pos hprho) (sub_pos.mpr hp1)

/-- Sharp hard-exponent law: the follower activity divided by its logarithmic
scale converges to one. -/
theorem hardExponentFollower_div_scale_tendsto_one
    {rho : ℝ} (hrho : 0 < rho) :
    Tendsto
      (fun p : ℝ => hardExponentFollower rho p /
        hardExponentScale rho p)
      atTop (𝓝 1) := by
  have hscale := hardExponentScale_tendsto_zero hrho
  have hpositive := hardExponentScale_eventually_pos hrho
  have hscaleNe : ∀ᶠ p : ℝ in atTop,
      hardExponentScale rho p ∈ ({0} : Set ℝ)ᶜ := by
    filter_upwards [hpositive] with p hp
    simpa using hp.ne'
  have hpunctured :
      Tendsto (hardExponentScale rho) atTop (𝓝[≠] (0 : ℝ)) := by
    exact tendsto_inf.2 ⟨hscale, tendsto_principal.2 hscaleNe⟩
  have hcomposition := one_sub_exp_neg_div_tendsto_one.comp hpunctured
  refine hcomposition.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with p hp
  simp only [Function.comp_apply]
  rw [hardExponentFollower_exp_identity hrho hp]

/-- Exponential growth eventually dominates the linear coefficient in the
hard-exponent phase inequality. -/
theorem eventually_linear_le_two_rpow_sub_one
    {rho : ℝ} (_hrho : 0 < rho) :
    ∀ᶠ p : ℝ in atTop, p * rho ≤ (2 : ℝ) ^ (p - 1) := by
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hgrowth :=
    tendsto_exp_mul_div_rpow_atTop (1 : ℝ) (Real.log 2) hlogTwo
  have hlarge := hgrowth.eventually_ge_atTop (2 * rho)
  filter_upwards [hlarge, eventually_gt_atTop (1 : ℝ)] with p hlargeP hp
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hexp : Real.exp (Real.log 2 * p) = (2 : ℝ) ^ p := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hratio : 2 * rho ≤ (2 : ℝ) ^ p / p := by
    simpa [hexp, Real.rpow_one] using hlargeP
  have hcross : 2 * rho * p ≤ (2 : ℝ) ^ p :=
    (le_div_iff₀ hp0).mp hratio
  rw [Real.rpow_sub_one (by norm_num : (2 : ℝ) ≠ 0)]
  nlinarith

/-- For every fixed positive ratio, the exact phase-two inequalities hold at
all sufficiently large finite exponents. -/
theorem hardExponentPhaseTwo_eventually
    {rho : ℝ} (hrho : 0 < rho) :
    ∀ᶠ p : ℝ in atTop, HardExponentPhaseTwo rho p := by
  filter_upwards [eventually_gt_atTop (max 1 (1 / rho)),
    eventually_linear_le_two_rpow_sub_one hrho] with p hp hlinear
  have hp1 : 1 < p := lt_of_le_of_lt (le_max_left _ _) hp
  have hpinv : 1 / rho < p := lt_of_le_of_lt (le_max_right _ _) hp
  have hprho : 1 < p * rho :=
    (div_lt_iff₀ hrho).mp (by simpa using hpinv)
  have hq : 0 < 1 / (p - 1) := by positivity
  have htwoq : 1 < (2 : ℝ) ^ (1 / (p - 1)) := by
    exact (Real.one_lt_rpow_iff_of_pos (by norm_num : (0 : ℝ) < 2)).2
      (Or.inl ⟨by norm_num, hq⟩)
  have hbase : (2 : ℝ) ≤ 1 + (2 : ℝ) ^ (1 / (p - 1)) := by
    linarith
  have hrpow : (2 : ℝ) ^ (p - 1) ≤
      (1 + (2 : ℝ) ^ (1 / (p - 1))) ^ (p - 1) :=
    Real.rpow_le_rpow (by norm_num) hbase (sub_nonneg.mpr hp1.le)
  exact ⟨hprho, le_trans hlinear hrpow⟩

/-- Complete hard-exponent support--magnitude theorem: the phase-two support
cell holds eventually, the sole positive follower has the exact logarithmic
first-order scale, and its magnitude nevertheless tends to zero. -/
theorem chg_b16_complete_hard_exponent_law
    {rho : ℝ} (hrho : 0 < rho) :
    (∀ᶠ p : ℝ in atTop, HardExponentPhaseTwo rho p) ∧
    Tendsto
      (fun p : ℝ => hardExponentFollower rho p /
        hardExponentScale rho p)
      atTop (𝓝 1) ∧
    Tendsto (hardExponentFollower rho) atTop (𝓝 0) := by
  exact ⟨hardExponentPhaseTwo_eventually hrho,
    hardExponentFollower_div_scale_tendsto_one hrho,
    hardExponentFollower_tendsto_zero hrho⟩

end PhonologicalCalculus.ContinuousHG
