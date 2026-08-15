import PhonologicalCalculus.ContinuousHG.UniformLattice
import Mathlib.Analysis.Real.Sqrt

/-!
# Exact persistence phases and quadratic reach asymptotic

This module separates the inherited common-scale gauge from the path-family
phase staircase.  It proves the exact ratio cell and a sharp, selection-rule
independent asymptotic: every integer phase index satisfying the triangular
first-zero inequalities is asymptotic to twice the square root of the harmony
ratio.
-/

namespace PhonologicalCalculus.ContinuousHG

open Filter Set
open scoped Topology

/-- Ratio-only quadratic persistence cell. -/
def QuadraticRatioPhaseCell (rho : ℝ) (K : ℕ) : Prop :=
  0 < rho ∧ 0 < K ∧
    ((K - 1 : ℕ) : ℝ) * (K : ℝ) < 4 * rho ∧
    4 * rho ≤ (K : ℝ) * ((K + 1 : ℕ) : ℝ)

/-- Exact phase interval in the ratio coordinate. -/
theorem quadraticRatioPhaseCell_iff
    {rho : ℝ} {K : ℕ} :
    QuadraticRatioPhaseCell rho K ↔
      0 < rho ∧ 0 < K ∧
      ((K - 1 : ℕ) : ℝ) * (K : ℝ) / 4 < rho ∧
      rho ≤ (K : ℝ) * ((K + 1 : ℕ) : ℝ) / 4 := by
  unfold QuadraticRatioPhaseCell
  constructor <;> rintro ⟨hrho, hK, hlower, hupper⟩
  · exact ⟨hrho, hK, by linarith, by linarith⟩
  · exact ⟨hrho, hK, by linarith, by linarith⟩

/-- The first five registered quadratic cells have exactly the stated
half-open endpoints. -/
theorem chg_b7_phase_02 :
    (∀ rho : ℝ, QuadraticRatioPhaseCell rho 1 ↔
      0 < rho ∧ rho ≤ 1 / 2) ∧
    (∀ rho : ℝ, QuadraticRatioPhaseCell rho 2 ↔
      1 / 2 < rho ∧ rho ≤ 3 / 2) ∧
    (∀ rho : ℝ, QuadraticRatioPhaseCell rho 3 ↔
      3 / 2 < rho ∧ rho ≤ 3) ∧
    (∀ rho : ℝ, QuadraticRatioPhaseCell rho 4 ↔
      3 < rho ∧ rho ≤ 5) ∧
    (∀ rho : ℝ, QuadraticRatioPhaseCell rho 5 ↔
      5 < rho ∧ rho ≤ 15 / 2) := by
  constructor
  · intro rho
    constructor
    · rintro ⟨hrho, _hK, _hlower, hupper⟩
      norm_num at hupper
      exact ⟨hrho, by linarith⟩
    · rintro ⟨hrho, hupper⟩
      exact ⟨hrho, by norm_num, by norm_num; linarith,
        by norm_num; linarith⟩
  constructor
  · intro rho
    constructor
    · rintro ⟨_hrho, _hK, hlower, hupper⟩
      norm_num at hlower hupper
      exact ⟨by linarith, by linarith⟩
    · rintro ⟨hlower, hupper⟩
      exact ⟨by linarith, by norm_num, by norm_num; linarith,
        by norm_num; linarith⟩
  constructor
  · intro rho
    constructor
    · rintro ⟨_hrho, _hK, hlower, hupper⟩
      norm_num at hlower hupper
      exact ⟨by linarith, by linarith⟩
    · rintro ⟨hlower, hupper⟩
      exact ⟨by linarith, by norm_num, by norm_num; linarith,
        by norm_num; linarith⟩
  constructor
  · intro rho
    constructor
    · rintro ⟨_hrho, _hK, hlower, hupper⟩
      norm_num at hlower hupper
      exact ⟨by linarith, by linarith⟩
    · rintro ⟨hlower, hupper⟩
      exact ⟨by linarith, by norm_num, by norm_num; linarith,
        by norm_num; linarith⟩
  · intro rho
    constructor
    · rintro ⟨_hrho, _hK, hlower, hupper⟩
      norm_num at hlower hupper
      exact ⟨by linarith, by linarith⟩
    · rintro ⟨hlower, hupper⟩
      exact ⟨by linarith, by norm_num, by norm_num; linarith,
        by norm_num; linarith⟩

/-- Any integer-valued phase selector satisfying the exact triangular cell
has the universal quadratic reach constant two.  No rounding convention or
particular closed form for the selector is assumed. -/
theorem quadratic_phase_index_div_sqrt_tendsto_two
    (K : ℝ → ℕ)
    (hphase : ∀ᶠ rho : ℝ in atTop,
      QuadraticRatioPhaseCell rho (K rho)) :
    Tendsto (fun rho : ℝ => (K rho : ℝ) / Real.sqrt rho)
      atTop (𝓝 2) := by
  have hinvSqrt : Tendsto (fun rho : ℝ => (Real.sqrt rho)⁻¹)
      atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop
  have hlowerLimit : Tendsto
      (fun rho : ℝ => 2 - (Real.sqrt rho)⁻¹) atTop (𝓝 2) := by
    simpa using tendsto_const_nhds.sub hinvSqrt
  have hupperLimit : Tendsto
      (fun rho : ℝ => 2 + (Real.sqrt rho)⁻¹) atTop (𝓝 2) := by
    simpa using tendsto_const_nhds.add hinvSqrt
  have hbounds : ∀ᶠ rho : ℝ in atTop,
      2 - (Real.sqrt rho)⁻¹ ≤ (K rho : ℝ) / Real.sqrt rho ∧
      (K rho : ℝ) / Real.sqrt rho ≤ 2 + (Real.sqrt rho)⁻¹ := by
    filter_upwards [hphase] with rho hcell
    rcases hcell with ⟨hrho, hK, htriLower, htriUpper⟩
    have hsqrt : 0 < Real.sqrt rho := Real.sqrt_pos.2 hrho
    have hsqrtSq : (Real.sqrt rho) ^ 2 = rho := Real.sq_sqrt hrho.le
    have hKnonnegative : 0 ≤ (K rho : ℝ) := Nat.cast_nonneg _
    have hpredNat : K rho - 1 + 1 = K rho := Nat.sub_add_cancel hK
    have hpredCastAux : (((K rho - 1 : ℕ) : ℝ)) + 1 = (K rho : ℝ) := by
      exact_mod_cast hpredNat
    have hpredCast : (((K rho - 1 : ℕ) : ℝ)) = (K rho : ℝ) - 1 := by
      linarith
    have hsuccCast : (((K rho + 1 : ℕ) : ℝ)) = (K rho : ℝ) + 1 := by
      norm_num
    rw [hpredCast] at htriLower
    rw [hsuccCast] at htriUpper
    have hKupper : (K rho : ℝ) ≤ 2 * Real.sqrt rho + 1 := by
      by_contra hnot
      have hstrict : 2 * Real.sqrt rho + 1 < (K rho : ℝ) :=
        lt_of_not_ge hnot
      nlinarith
    have hKlower : 2 * Real.sqrt rho - 1 ≤ (K rho : ℝ) := by
      by_contra hnot
      have hstrict : (K rho : ℝ) < 2 * Real.sqrt rho - 1 :=
        lt_of_not_ge hnot
      nlinarith
    constructor
    · apply (le_div_iff₀ hsqrt).2
      field_simp [ne_of_gt hsqrt]
      nlinarith
    · apply (div_le_iff₀ hsqrt).2
      field_simp [ne_of_gt hsqrt]
      nlinarith
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hlowerLimit hupperLimit
    (hbounds.mono fun _ h => h.1)
    (hbounds.mono fun _ h => h.2)

/-- Integrated quadratic gauge-and-persistence package. -/
theorem chg_b7_complete_quadratic_persistence
    (K : ℝ → ℕ)
    (hphase : ∀ᶠ rho : ℝ in atTop,
      QuadraticRatioPhaseCell rho (K rho)) :
    (∀ (penalty : ℝ → ℝ) (lambda h m : ℝ), 0 < lambda →
      ∀ x y : List ℝ,
        pathHarmony penalty (lambda * h) (lambda * m) x ≤
            pathHarmony penalty (lambda * h) (lambda * m) y ↔
          pathHarmony penalty h m x ≤ pathHarmony penalty h m y) ∧
    (∀ rho : ℝ, QuadraticRatioPhaseCell rho 4 ↔
      3 < rho ∧ rho ≤ 5) ∧
    Tendsto (fun rho : ℝ => (K rho : ℝ) / Real.sqrt rho)
      atTop (𝓝 2) := by
  refine ⟨?_, (chg_b7_phase_02.2.2.2.1),
    quadratic_phase_index_div_sqrt_tendsto_two K hphase⟩
  intro penalty lambda h m hlambda x y
  exact chg_b7_common_scale_preorder penalty hlambda h m x y

end PhonologicalCalculus.ContinuousHG
