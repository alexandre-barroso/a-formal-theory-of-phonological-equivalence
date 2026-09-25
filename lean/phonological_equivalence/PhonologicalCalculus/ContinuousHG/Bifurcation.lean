import PhonologicalCalculus.ContinuousHG.PhaseProfile
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.NormNum

namespace PhonologicalCalculus.ContinuousHG

open Filter Set

noncomputable def supportOnsetOrder (p : ℝ) : ℝ :=
  if p < 2 then 1 / (p - 1) else 1

theorem supportOnsetOrder_subquadratic
    {p : ℝ} (_hp₁ : 1 < p) (hp₂ : p < 2) :
    supportOnsetOrder p = 1 / (p - 1) := by
  simp [supportOnsetOrder, hp₂]

theorem supportOnsetOrder_quadratic_or_harder
    {p : ℝ} (hp : 2 ≤ p) : supportOnsetOrder p = 1 := by
  simp [supportOnsetOrder, not_lt.mpr hp]

theorem positivePower_ratio_tendsto_zero
    {q b : ℝ} {denominator : ℝ → ℝ}
    (hq : 0 < q) (hb : 0 < b)
    (hden : Tendsto denominator (nhdsWithin 0 (Ioi 0)) (nhds b)) :
    Tendsto (fun t : ℝ => t ^ q / denominator t)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  have hpower : Tendsto (fun t : ℝ => t ^ q)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    have hcontinuous := Real.continuousAt_rpow_const 0 q (Or.inr hq.le)
    change Tendsto (fun t : ℝ => t ^ q)
      (nhds 0 ⊓ Filter.principal (Ioi 0)) (nhds 0)
    simpa [Real.zero_rpow (ne_of_gt hq)] using
      hcontinuous.tendsto.mono_left inf_le_left
  change Tendsto ((fun t : ℝ => t ^ q) / denominator)
    (nhdsWithin 0 (Ioi 0)) (nhds 0)
  simpa using hpower.div hden (ne_of_gt hb)

noncomputable def quadraticEnteringCoordinate (t : ℝ) : ℝ :=
  t / (10 + 5 * t)

                        
theorem chg_b14_continuity_03 :
    Tendsto quadraticEnteringCoordinate (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  unfold quadraticEnteringCoordinate
  have hden : Tendsto (fun t : ℝ => 10 + 5 * t)
      (nhdsWithin 0 (Ioi 0)) (nhds 10) := by
    have hc : Continuous (fun t : ℝ => 10 + 5 * t) := by fun_prop
    have hc0 : ContinuousAt (fun t : ℝ => 10 + 5 * t) 0 := hc.continuousAt
    change Tendsto (fun t : ℝ => 10 + 5 * t)
      (nhds 0 ⊓ Filter.principal (Ioi 0)) (nhds 10)
    simpa using hc0.tendsto.mono_left inf_le_left
  simpa [Real.rpow_one] using
    positivePower_ratio_tendsto_zero (q := (1 : ℝ)) (b := (10 : ℝ))
      (by norm_num) (by norm_num) hden

                     
theorem chg_b14_regimes_01 :
    [supportOnsetOrder (3 / 2), supportOnsetOrder 2,
      supportOnsetOrder 3] = [2, 1, 1] := by
  norm_num [supportOnsetOrder]

                         
theorem chg_b14_coefficient_02 : (1 : ℝ) / 5 ^ 2 = 1 / 25 := by
  norm_num

          
theorem chg_b14_registered_components :
    [supportOnsetOrder (3 / 2), supportOnsetOrder 2,
      supportOnsetOrder 3] = [2, 1, 1] ∧
    (1 : ℝ) / 5 ^ 2 = 1 / 25 ∧
    Tendsto quadraticEnteringCoordinate (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  exact ⟨chg_b14_regimes_01, chg_b14_coefficient_02,
    chg_b14_continuity_03⟩

end PhonologicalCalculus.ContinuousHG
