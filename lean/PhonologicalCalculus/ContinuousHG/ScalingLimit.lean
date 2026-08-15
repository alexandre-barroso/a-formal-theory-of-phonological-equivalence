import PhonologicalCalculus.ContinuousHG.PhaseProfile
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.NormNum

/-!
# Scaling profile and decrement density

The long-support theorem has a universal limiting shape.  This module
formalizes that shape independently of the remaining uniform power-sum
convergence bridge: its derivative is the negative decrement density and that
density has unit mass.  It also proves every registered quadratic anchor.
-/

namespace PhonologicalCalculus.ContinuousHG

open Filter Set
open scoped Interval

/-- Shape exponent `p / (p - 1)`. -/
noncomputable def scalingExponent (p : ℝ) : ℝ := p / (p - 1)

/-- Universal normalized activity profile. -/
noncomputable def scalingProfile (p u : ℝ) : ℝ :=
  (1 - u) ^ scalingExponent p

/-- Universal normalized decrement density. -/
noncomputable def scalingDensity (p u : ℝ) : ℝ :=
  scalingExponent p * (1 - u) ^ (1 / (p - 1))

theorem scalingExponent_sub_one {p : ℝ} (hp : 1 < p) :
    scalingExponent p - 1 = 1 / (p - 1) := by
  unfold scalingExponent
  field_simp [ne_of_gt (sub_pos.mpr hp)]
  ring

theorem one_lt_scalingExponent {p : ℝ} (hp : 1 < p) :
    1 < scalingExponent p := by
  unfold scalingExponent
  have hden : 0 < p - 1 := sub_pos.mpr hp
  exact (lt_div_iff₀ hden).2 (by linarith)

/-- The decrement density is exactly the negative derivative of the scaling
profile. -/
theorem scalingProfile_hasDerivAt {p u : ℝ} (hp : 1 < p) :
    HasDerivAt (scalingProfile p) (-scalingDensity p u) u := by
  have hexp : 1 ≤ scalingExponent p := (one_lt_scalingExponent hp).le
  have hinner : HasDerivAt (fun z : ℝ => (1 : ℝ) - z) (-1) u :=
    (hasDerivAt_id u).const_sub (1 : ℝ)
  have hpow := (Real.hasDerivAt_rpow_const
    (x := 1 - u) (p := scalingExponent p) (Or.inr hexp)).comp u hinner
  change HasDerivAt (fun z : ℝ => ((1 : ℝ) - z) ^ scalingExponent p)
    (-scalingDensity p u) u
  have hfun : (fun z : ℝ => ((1 : ℝ) - z) ^ scalingExponent p) =ᶠ[
      nhds u] ((fun x : ℝ => x ^ scalingExponent p) ∘ fun z : ℝ => 1 - z) :=
    Filter.Eventually.of_forall fun _ => rfl
  apply (hpow.congr_of_eventuallyEq hfun).congr_deriv
  rw [scalingExponent_sub_one hp]
  unfold scalingDensity
  ring

/-- The universal decrement density integrates to one on the normalized
support interval. -/
theorem scalingDensity_intervalIntegral {p : ℝ} (hp : 1 < p) :
    ∫ u in (0 : ℝ)..1, scalingDensity p u = 1 := by
  have hq : 0 ≤ 1 / (p - 1) := by positivity
  have hcontinuous : Continuous (scalingDensity p) := by
    unfold scalingDensity
    exact continuous_const.mul
      ((Real.continuous_rpow_const hq).comp
        (continuous_const.sub continuous_id))
  have hnegativeIntegral :
      ∫ u in (0 : ℝ)..1, -scalingDensity p u =
        scalingProfile p 1 - scalingProfile p 0 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro u _
      exact scalingProfile_hasDerivAt hp
    · exact hcontinuous.neg.intervalIntegrable 0 1
  rw [intervalIntegral.integral_neg] at hnegativeIntegral
  have hexp0 : 0 < scalingExponent p := lt_trans zero_lt_one
    (one_lt_scalingExponent hp)
  have hend : scalingProfile p 1 = 0 := by
    simp [scalingProfile, Real.zero_rpow (ne_of_gt hexp0)]
  have hstart : scalingProfile p 0 = 1 := by
    simp [scalingProfile]
  rw [hend, hstart] at hnegativeIntegral
  linarith

/-- Exact rational sequence used by the registered quadratic profile anchor. -/
noncomputable def quadraticScalingAnchor (n : ℝ) : ℝ :=
  (4 / 9 + 2 / (3 * n)) / (1 + 1 / n)

/-- `CHG-B13.PARABOLA.01`: the quadratic normalized profile anchor tends to
`4/9`. -/
theorem chg_b13_parabola_01 :
    Tendsto quadraticScalingAnchor atTop (nhds (4 / 9 : ℝ)) := by
  have hinv : Tendsto (fun n : ℝ => n⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero
  unfold quadraticScalingAnchor
  have hnum : Tendsto (fun n : ℝ => 4 / 9 + (2 / 3) * n⁻¹)
      atTop (nhds (4 / 9)) := by
    convert tendsto_const_nhds.add (hinv.const_mul (2 / 3)) using 1
    all_goals norm_num
  have hden : Tendsto (fun n : ℝ => 1 + n⁻¹) atTop (nhds 1) := by
    convert tendsto_const_nhds.add hinv using 1
    all_goals norm_num
  have hform : (fun n : ℝ => (4 / 9 + 2 / (3 * n)) / (1 + 1 / n)) =
      (fun n : ℝ => (4 / 9 + (2 / 3) * n⁻¹) / (1 + n⁻¹)) := by
    funext n
    field_simp
  rw [hform]
  change Tendsto
    ((fun n : ℝ => 4 / 9 + (2 / 3) * n⁻¹) /
      (fun n : ℝ => 1 + n⁻¹)) atTop (nhds (4 / 9))
  simpa using hnum.div hden (by norm_num)

/-- `CHG-B13.DENSITY.02`: the quadratic decrement density has unit mass and
first moment `1/3`. -/
theorem chg_b13_density_02 :
    (∫ u in (0 : ℝ)..1, scalingDensity 2 u) = 1 ∧
    (∫ u in (0 : ℝ)..1, u * scalingDensity 2 u) = 1 / 3 := by
  constructor
  · exact scalingDensity_intervalIntegral (by norm_num)
  · have hderiv : ∀ u : ℝ,
        HasDerivAt (fun z : ℝ => z ^ 2 - (2 / 3) * z ^ 3)
          (u * scalingDensity 2 u) u := by
      intro u
      have hraw := ((hasDerivAt_id u).pow 2).sub
        (((hasDerivAt_id u).pow 3).const_mul (2 / 3))
      have hvalue : u * scalingDensity 2 u =
          2 * u - 2 * u ^ 2 := by
        norm_num [scalingDensity, scalingExponent, Real.rpow_one]
        ring
      rw [hvalue]
      have hfun : (fun z : ℝ => z ^ 2 - (2 / 3) * z ^ 3) =ᶠ[nhds u]
          ((id ^ 2) - fun z : ℝ => (2 / 3) * (id ^ 3) z) := by
        filter_upwards [] with z
        simp only [Pi.sub_apply, Pi.pow_apply, id_eq]
      apply (hraw.congr_of_eventuallyEq hfun).congr_deriv
      simp only [id_eq]
      ring
    have hint : IntervalIntegrable (fun u : ℝ => u * scalingDensity 2 u)
        MeasureTheory.volume 0 1 := by
      have hc : Continuous (fun u : ℝ => u * (2 * (1 - u))) :=
        continuous_id.mul (continuous_const.mul
          (continuous_const.sub continuous_id))
      have hfun : (fun u : ℝ => u * scalingDensity 2 u) =
          (fun u : ℝ => u * (2 * (1 - u))) := by
        funext u
        norm_num [scalingDensity, scalingExponent, Real.rpow_one]
      rw [hfun]
      exact hc.intervalIntegrable 0 1
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun u _ => hderiv u) hint]
    norm_num

/-- `CHG-B13.QUANTILE.03`: the registered quadratic repair quantile. -/
theorem chg_b13_quantile_03 :
    1 - Real.sqrt (1 - (3 / 4 : ℝ)) = 1 / 2 := by
  have hsqrt : Real.sqrt (1 / 4 : ℝ) = 1 / 2 := by
    rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num,
      Real.sqrt_sq_eq_abs]
    norm_num
  rw [show (1 - (3 / 4 : ℝ)) = 1 / 4 by norm_num, hsqrt]
  norm_num

/-- The exact analytic and registered finite components of `CHG-B13`. -/
theorem chg_b13_registered_components :
    (∀ p, 1 < p → ∫ u in (0 : ℝ)..1, scalingDensity p u = 1) ∧
    Tendsto quadraticScalingAnchor atTop (nhds (4 / 9 : ℝ)) ∧
    (∫ u in (0 : ℝ)..1, scalingDensity 2 u) = 1 ∧
    (∫ u in (0 : ℝ)..1, u * scalingDensity 2 u) = 1 / 3 ∧
    1 - Real.sqrt (1 - (3 / 4 : ℝ)) = 1 / 2 := by
  exact ⟨fun p hp => scalingDensity_intervalIntegral hp,
    chg_b13_parabola_01, chg_b13_density_02.1,
    chg_b13_density_02.2, chg_b13_quantile_03⟩

end PhonologicalCalculus.ContinuousHG
