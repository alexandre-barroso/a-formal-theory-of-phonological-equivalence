import PhonologicalCalculus.ContinuousHG.ScalingLimit
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Exact moments of the continuous-HG scaling law

This module closes the analytic moment identities attached to the universal
long-support profile.  The proofs differentiate explicit real-power
antiderivatives on the whole closed unit interval, including the endpoint
where the real-power base is zero.
-/

namespace PhonologicalCalculus.ContinuousHG

open Set
open scoped Interval

/-- Antiderivative of the normalized scaling profile. -/
noncomputable def scalingProfileAntiderivative (p u : ℝ) : ℝ :=
  -((1 - u) ^ (scalingExponent p + 1)) /
    (scalingExponent p + 1)

/-- The declared antiderivative differentiates to the scaling profile at
every point, including the zero-base endpoint. -/
theorem scalingProfileAntiderivative_hasDerivAt
    {p u : ℝ} (hp : 1 < p) :
    HasDerivAt (scalingProfileAntiderivative p) (scalingProfile p u) u := by
  have hexponent : 1 ≤ scalingExponent p + 1 := by
    have hpositive : 0 < scalingExponent p :=
      lt_trans zero_lt_one (one_lt_scalingExponent hp)
    linarith
  have hinner : HasDerivAt (fun z : ℝ => (1 : ℝ) - z) (-1) u :=
    (hasDerivAt_id u).const_sub (1 : ℝ)
  have hpower := (Real.hasDerivAt_rpow_const
    (x := 1 - u) (p := scalingExponent p + 1)
    (Or.inr hexponent)).comp u hinner
  have hscaled := hpower.const_mul
    (-(scalingExponent p + 1)⁻¹)
  have hfunction : HasDerivAt (scalingProfileAntiderivative p)
      (-(scalingExponent p + 1)⁻¹ *
        ((scalingExponent p + 1) *
          (1 - u) ^ (scalingExponent p + 1 - 1) * -1)) u := by
    apply hscaled.congr_of_eventuallyEq
    filter_upwards [] with z
    unfold scalingProfileAntiderivative
    simp only [Function.comp_apply]
    ring
  apply hfunction.congr_deriv
  unfold scalingProfile
  have hden : scalingExponent p + 1 ≠ 0 := by
    have hpositive : 0 < scalingExponent p :=
      lt_trans zero_lt_one (one_lt_scalingExponent hp)
    linarith
  field_simp [hden]
  ring

/-- The normalized scaling profile has exact unit-interval mass
`(p - 1) / (2p - 1)`. -/
theorem scalingProfile_intervalIntegral
    {p : ℝ} (hp : 1 < p) :
    ∫ u in (0 : ℝ)..1, scalingProfile p u =
      (p - 1) / (2 * p - 1) := by
  have hcontinuous : Continuous (scalingProfile p) := by
    unfold scalingProfile
    exact (Real.continuous_rpow_const
      (le_trans zero_le_one (one_lt_scalingExponent hp).le)).comp
      (continuous_const.sub continuous_id)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _ => scalingProfileAntiderivative_hasDerivAt hp)
    (hcontinuous.intervalIntegrable 0 1)]
  have hexponentPositive : 0 < scalingExponent p + 1 := by
    have := one_lt_scalingExponent hp
    linarith
  have hden : scalingExponent p + 1 ≠ 0 :=
    ne_of_gt hexponentPositive
  have htop : scalingProfileAntiderivative p 1 = 0 := by
    simp [scalingProfileAntiderivative,
      Real.zero_rpow (ne_of_gt hexponentPositive)]
  have hbottom : scalingProfileAntiderivative p 0 =
      -(scalingExponent p + 1)⁻¹ := by
    simp [scalingProfileAntiderivative, div_eq_mul_inv]
  rw [htop, hbottom, zero_sub, neg_neg]
  have htargetPositive : 0 < 2 * p - 1 := by linarith
  unfold scalingExponent
  field_simp [ne_of_gt (sub_pos.mpr hp), ne_of_gt htargetPositive]
  ring

/-- Antiderivative of the first moment of the decrement density. -/
noncomputable def scalingDensityFirstMomentAntiderivative
    (p u : ℝ) : ℝ :=
  -((1 - u) ^ scalingExponent p) +
    scalingExponent p / (scalingExponent p + 1) *
      ((1 - u) ^ (scalingExponent p + 1))

/-- The first-moment antiderivative differentiates to `u * D_p(u)` on the
whole closed unit interval. -/
theorem scalingDensityFirstMomentAntiderivative_hasDerivAt
    {p u : ℝ} (hp : 1 < p) (hu : u ≤ 1) :
    HasDerivAt (scalingDensityFirstMomentAntiderivative p)
      (u * scalingDensity p u) u := by
  have hexponentOne : 1 ≤ scalingExponent p :=
    (one_lt_scalingExponent hp).le
  have hexponentSucc : 1 ≤ scalingExponent p + 1 := by linarith
  have hinner : HasDerivAt (fun z : ℝ => (1 : ℝ) - z) (-1) u :=
    (hasDerivAt_id u).const_sub (1 : ℝ)
  have hfirst := (Real.hasDerivAt_rpow_const
    (x := 1 - u) (p := scalingExponent p)
    (Or.inr hexponentOne)).comp u hinner
  have hsecond := (Real.hasDerivAt_rpow_const
    (x := 1 - u) (p := scalingExponent p + 1)
    (Or.inr hexponentSucc)).comp u hinner
  have hcombined := hfirst.neg.add
    (hsecond.const_mul
      (scalingExponent p / (scalingExponent p + 1)))
  have hfunction : HasDerivAt
      (scalingDensityFirstMomentAntiderivative p)
      (-(scalingExponent p *
          (1 - u) ^ (scalingExponent p - 1) * -1) +
        scalingExponent p / (scalingExponent p + 1) *
          ((scalingExponent p + 1) *
            (1 - u) ^ (scalingExponent p + 1 - 1) * -1)) u := by
    apply hcombined.congr_of_eventuallyEq
    filter_upwards [] with z
    unfold scalingDensityFirstMomentAntiderivative
    simp only [Function.comp_apply, Pi.neg_apply, Pi.add_apply]
  apply hfunction.congr_deriv
  unfold scalingDensity
  rw [scalingExponent_sub_one hp]
  have hden : scalingExponent p + 1 ≠ 0 := by
    have := one_lt_scalingExponent hp
    linarith
  field_simp [hden]
  have hbase : 0 ≤ 1 - u := sub_nonneg.mpr hu
  by_cases huOne : u = 1
  · subst u
    have hscalingPositive : 0 < scalingExponent p :=
      lt_trans zero_lt_one (one_lt_scalingExponent hp)
    simp [Real.zero_rpow hscalingPositive.ne']
  have huStrict : u < 1 := lt_of_le_of_ne hu huOne
  have hbasePositive : 0 < 1 - u := sub_pos.mpr huStrict
  have hexponentIdentity :
      scalingExponent p = 1 / (p - 1) + 1 := by
    have := scalingExponent_sub_one hp
    linarith
  rw [hexponentIdentity]
  have hexponentSimplify :
      1 / (p - 1) + 1 + 1 - 1 = 1 / (p - 1) + 1 := by ring
  rw [hexponentSimplify, Real.rpow_add hbasePositive, Real.rpow_one]
  ring

/-- The decrement density's normalized center of repair equals the profile
mass and has the exact closed form `(p - 1) / (2p - 1)`. -/
theorem scalingDensity_firstMoment_intervalIntegral
    {p : ℝ} (hp : 1 < p) :
    ∫ u in (0 : ℝ)..1, u * scalingDensity p u =
      (p - 1) / (2 * p - 1) := by
  have hq : 0 ≤ 1 / (p - 1) := by positivity
  have hcontinuous : Continuous (fun u : ℝ =>
      u * scalingDensity p u) := by
    unfold scalingDensity
    exact continuous_id.mul
      (continuous_const.mul
        ((Real.continuous_rpow_const hq).comp
          (continuous_const.sub continuous_id)))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u hu =>
      scalingDensityFirstMomentAntiderivative_hasDerivAt hp (by
        simpa only [max_eq_right zero_le_one] using hu.2))
    (hcontinuous.intervalIntegrable 0 1)]
  have hexponentPositive : 0 < scalingExponent p :=
    lt_trans zero_lt_one (one_lt_scalingExponent hp)
  have hexponentSuccPositive : 0 < scalingExponent p + 1 := by linarith
  have hden : scalingExponent p + 1 ≠ 0 :=
    ne_of_gt hexponentSuccPositive
  have htop : scalingDensityFirstMomentAntiderivative p 1 = 0 := by
    simp [scalingDensityFirstMomentAntiderivative,
      Real.zero_rpow (ne_of_gt hexponentPositive),
      Real.zero_rpow (ne_of_gt hexponentSuccPositive)]
  have hbottom : scalingDensityFirstMomentAntiderivative p 0 =
      -1 + scalingExponent p / (scalingExponent p + 1) := by
    simp [scalingDensityFirstMomentAntiderivative]
  rw [htop, hbottom, zero_sub]
  have hcollapse :
      -(-1 + scalingExponent p / (scalingExponent p + 1)) =
        (scalingExponent p + 1)⁻¹ := by
    field_simp [hden]
    ring
  rw [hcollapse]
  have htargetPositive : 0 < 2 * p - 1 := by linarith
  unfold scalingExponent
  field_simp [ne_of_gt (sub_pos.mpr hp), ne_of_gt htargetPositive]
  ring

/-- The two exact moment descriptions of the scaling law agree. -/
theorem scaling_profile_mass_eq_density_center
    {p : ℝ} (hp : 1 < p) :
    (∫ u in (0 : ℝ)..1, scalingProfile p u) =
      ∫ u in (0 : ℝ)..1, u * scalingDensity p u := by
  rw [scalingProfile_intervalIntegral hp,
    scalingDensity_firstMoment_intervalIntegral hp]

/-- Normalized ordinal position by which a fraction `alpha` of the total
repair mass has occurred. -/
noncomputable def scalingRepairQuantile (p alpha : ℝ) : ℝ :=
  1 - (1 - alpha) ^ ((p - 1) / p)

/-- The quantile formula exactly inverts the scaling profile on the unit
probability interval. -/
theorem scalingProfile_at_repairQuantile
    {p alpha : ℝ} (hp : 1 < p) (_halphaZero : 0 ≤ alpha)
    (halphaOne : alpha ≤ 1) :
    scalingProfile p (scalingRepairQuantile p alpha) = 1 - alpha := by
  have hpPositive : 0 < p := lt_trans zero_lt_one hp
  have hbase : 0 ≤ 1 - alpha := sub_nonneg.mpr halphaOne
  have hexponentProduct :
      ((p - 1) / p) * scalingExponent p = 1 := by
    unfold scalingExponent
    field_simp [hpPositive.ne', ne_of_gt (sub_pos.mpr hp)]
  unfold scalingProfile scalingRepairQuantile
  rw [show 1 - (1 - (1 - alpha) ^ ((p - 1) / p)) =
      (1 - alpha) ^ ((p - 1) / p) by ring]
  rw [← Real.rpow_mul hbase, hexponentProduct, Real.rpow_one]

/-- The accumulated-repair reader returns exactly the registered fraction at
the analytic quantile. -/
theorem scalingRepairFraction_at_quantile
    {p alpha : ℝ} (hp : 1 < p) (halphaZero : 0 ≤ alpha)
    (halphaOne : alpha ≤ 1) :
    1 - scalingProfile p (scalingRepairQuantile p alpha) = alpha := by
  rw [scalingProfile_at_repairQuantile hp halphaZero halphaOne]
  ring

/-- Closed analytic moment package associated with the scaling law. -/
theorem chg_b13_exact_moment_package
    {p : ℝ} (hp : 1 < p) :
    (∫ u in (0 : ℝ)..1, scalingDensity p u) = 1 ∧
    (∫ u in (0 : ℝ)..1, scalingProfile p u) =
      (p - 1) / (2 * p - 1) ∧
    (∫ u in (0 : ℝ)..1, u * scalingDensity p u) =
      (p - 1) / (2 * p - 1) ∧
    (∀ alpha : ℝ, 0 ≤ alpha → alpha ≤ 1 →
      1 - scalingProfile p (scalingRepairQuantile p alpha) = alpha) := by
  exact ⟨scalingDensity_intervalIntegral hp,
    scalingProfile_intervalIntegral hp,
    scalingDensity_firstMoment_intervalIntegral hp,
    fun alpha hzero hone =>
      scalingRepairFraction_at_quantile hp hzero hone⟩

end PhonologicalCalculus.ContinuousHG
