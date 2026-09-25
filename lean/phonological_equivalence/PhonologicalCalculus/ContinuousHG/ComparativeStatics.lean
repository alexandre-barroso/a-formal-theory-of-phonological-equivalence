import PhonologicalCalculus.ContinuousHG.PhaseProfile
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

namespace PhonologicalCalculus.ContinuousHG

open Filter Set

theorem quadraticSaturatedProfile_mono_h
    {h₁ h₂ m : ℝ} {K i : ℕ}
    (hh₁ : 0 < h₁) (hh₂ : 0 < h₂) (hm : 0 ≤ m) (hh : h₁ ≤ h₂) :
    quadraticSaturatedProfile h₁ m K i ≤
      quadraticSaturatedProfile h₂ m K i := by
  have hnum : 0 ≤ m * (i : ℝ) := mul_nonneg hm (Nat.cast_nonneg i)
  have hden₁ : 0 < 4 * h₁ := by positivity
  have hden₂ : 0 < 4 * h₂ := by positivity
  have hfraction : m * (i : ℝ) / (4 * h₂) ≤
      m * (i : ℝ) / (4 * h₁) := by
    exact (div_le_div_iff₀ hden₂ hden₁).2 (by nlinarith)
  unfold quadraticSaturatedProfile
  have hfactor : 0 ≤ ((K - i : ℕ) : ℝ) := Nat.cast_nonneg _
  exact mul_le_mul_of_nonneg_left (sub_le_sub_left hfraction _ ) hfactor

                      
theorem chg_b10_monotone_01 :
    List.Forall₂ (· ≤ ·)
      [quadraticSaturatedProfile 5 1 4 0,
        quadraticSaturatedProfile 5 1 4 1,
        quadraticSaturatedProfile 5 1 4 2,
        quadraticSaturatedProfile 5 1 4 3,
        quadraticSaturatedProfile 5 1 4 4]
      [quadraticUnsaturatedProfile 6 1 4 0,
        quadraticUnsaturatedProfile 6 1 4 1,
        quadraticUnsaturatedProfile 6 1 4 2,
        quadraticUnsaturatedProfile 6 1 4 3,
        quadraticUnsaturatedProfile 6 1 4 4] := by
  norm_num [quadraticSaturatedProfile, quadraticUnsaturatedProfile]

theorem chg_b10_extension_02 :
    QuadraticPhaseCell 5 1 4 ∧
    QuadraticThresholdReached 5 1 4 ∧
    (∀ j, j < 4 → ¬ QuadraticThresholdReached 5 1 j) ∧
    (∀ R, IsUniqueMinimizerOn
      (SolidSimplex : (Fin (4 + R) → ℝ) → Prop)
      (quadraticReducedObjective 5 1 (quadraticPathWeight (4 + R)))
      (quadraticExtendedDecrease 5 1 4 R)) := by
  have hphase : QuadraticPhaseCell 5 1 4 := by
    norm_num [QuadraticPhaseCell]
  have hleast := quadraticPhaseCell_least_threshold hphase
  exact ⟨hphase, hleast.1, hleast.2,
    fun R => quadraticExtension_stable_unique_minimizer hphase⟩

theorem chg_b10_boundary_03 :
    [normalizedPhaseProfile 1 1 5 0,
      normalizedPhaseProfile 1 1 5 1,
      normalizedPhaseProfile 1 1 5 2,
      normalizedPhaseProfile 1 1 5 3,
      normalizedPhaseProfile 1 1 5 4,
      normalizedPhaseProfile 1 1 5 5] =
        [1, 3 / 5, 3 / 10, 1 / 10, 0, 0] ∧
    [normalizedPhaseProfile 1 1 5 0,
      normalizedPhaseProfile 1 1 5 1,
      normalizedPhaseProfile 1 1 5 2,
      normalizedPhaseProfile 1 1 5 3,
      normalizedPhaseProfile 1 1 5 4] =
    [normalizedPhaseProfile 1 0 4 0,
      normalizedPhaseProfile 1 0 4 1,
      normalizedPhaseProfile 1 0 4 2,
      normalizedPhaseProfile 1 0 4 3,
      normalizedPhaseProfile 1 0 4 4] := by
  norm_num [normalizedPhaseProfile, shiftedPowerSum, Finset.sum_range_succ]

private theorem quadraticEnteringProfile_coordinate_tendsto
    (i : Fin 6) :
    Tendsto (fun tau : ℝ => normalizedPhaseProfile 1 tau 5 i.1)
      (nhdsWithin 1 (Iio 1))
      (nhds (normalizedPhaseProfile 1 1 5 i.1)) := by
  have hc : ContinuousAt
      (fun tau : ℝ => normalizedPhaseProfile 1 tau 5 i.1) 1 := by
    unfold normalizedPhaseProfile shiftedPowerSum
    simp only [Real.rpow_one]
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · norm_num [Finset.sum_range_succ]
  change Tendsto (fun tau : ℝ => normalizedPhaseProfile 1 tau 5 i.1)
    (nhds 1 ⊓ Filter.principal (Iio 1))
    (nhds (normalizedPhaseProfile 1 1 5 i.1))
  exact hc.tendsto.mono_left inf_le_left

theorem chg_b10_boundary_03_tendsto :
    ∀ i : Fin 6,
      Tendsto (fun tau : ℝ => normalizedPhaseProfile 1 tau 5 i.1)
        (nhdsWithin 1 (Iio 1))
        (nhds (normalizedPhaseProfile 1 1 5 i.1)) :=
  quadraticEnteringProfile_coordinate_tendsto

end PhonologicalCalculus.ContinuousHG
