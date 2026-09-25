import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace PhonologicalCalculus.Flux

open scoped Matrix

theorem finiteLedger_exists_nonzero_nullVector {J K : ℕ} (hJK : J < K)
    (A : Matrix (Fin J) (Fin K) ℝ) :
    ∃ v : Fin K → ℝ, v ≠ 0 ∧ A *ᵥ v = 0 := by
  have hdim : Module.finrank ℝ (Fin J → ℝ) <
      Module.finrank ℝ (Fin K → ℝ) := by
    simpa using hJK
  have hkernel : LinearMap.ker A.mulVecLin ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt hdim
  obtain ⟨v, hvKernel, hvNonzero⟩ :=
    (LinearMap.ker A.mulVecLin).ne_bot_iff.mp hkernel
  refine ⟨v, hvNonzero, ?_⟩
  simpa [LinearMap.mem_ker, Matrix.mulVecLin_apply] using hvKernel

theorem finiteLedger_nullity_lowerBound {J K : ℕ}
    (A : Matrix (Fin J) (Fin K) ℝ) :
    K - J ≤ Module.finrank ℝ (LinearMap.ker A.mulVecLin) := by
  have hrange : Module.finrank ℝ (LinearMap.range A.mulVecLin) ≤ J := by
    simpa using (LinearMap.range A.mulVecLin).finrank_le
  have hnullity := A.mulVecLin.finrank_range_add_finrank_ker
  have hsource : Module.finrank ℝ (Fin K → ℝ) = K := by simp
  rw [hsource] at hnullity
  omega

def ledgerMatrix : Matrix (Fin 2) (Fin 3) ℚ :=
  !![(3 / 2), (3 / 4), 0;
     1,       1,       (1 / 3)]

def ledgerNullVector : Fin 3 → ℚ := ![(1 / 3), (-2 / 3), 1]

                  
theorem flux_d3_null_01 :
    ledgerMatrix *ᵥ ledgerNullVector = (0 : Fin 2 → ℚ) := by
  funext i
  fin_cases i <;>
    norm_num [ledgerMatrix, ledgerNullVector, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ]

def ledgerWeightedNorm : ℚ :=
  1 * |(1 / 3 : ℚ)| + 2 * |(-2 / 3 : ℚ)| + 3 * |(1 : ℚ)|

theorem ledgerWeightedNorm_eq : ledgerWeightedNorm = 14 / 3 := by
  norm_num [ledgerWeightedNorm, abs_of_nonneg, abs_of_nonpos]

noncomputable def ledgerScale : ℝ :=
  1 / (10 * (2 * Real.pi) * (14 / 3))

noncomputable def ledgerDerivativeLowerBound : ℝ :=
  1 - 2 * Real.pi * ledgerScale * (14 / 3)

                      
theorem flux_d3_monotone_02 :
    ledgerDerivativeLowerBound = 9 / 10 ∧
      0 < ledgerDerivativeLowerBound := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  constructor
  · unfold ledgerDerivativeLowerBound ledgerScale
    field_simp [hpi]
    ring
  · rw [show ledgerDerivativeLowerBound = 9 / 10 by
      unfold ledgerDerivativeLowerBound ledgerScale
      field_simp [hpi]
      ring]
    norm_num

noncomputable def ledgerPrimitive (d : ℝ) : ℝ :=
  ledgerScale *
    ((1 / 3) * (1 - Real.cos (2 * Real.pi * d)) / (2 * Real.pi) +
      (-2 / 3) * (1 - Real.cos (4 * Real.pi * d)) / (4 * Real.pi) +
      (1 - Real.cos (6 * Real.pi * d)) / (6 * Real.pi))

noncomputable def ledgerTwoEdgeScore (d : ℝ) : ℝ :=
  2 * ledgerPrimitive d

theorem ledgerPrimitive_one_third : ledgerPrimitive (1 / 3) = 0 := by
  unfold ledgerPrimitive
  rw [show 2 * Real.pi * (1 / 3 : ℝ) = 2 * Real.pi / 3 by ring,
    show 4 * Real.pi * (1 / 3 : ℝ) = 4 * Real.pi / 3 by ring,
    show 6 * Real.pi * (1 / 3 : ℝ) = 2 * Real.pi by ring]
  rw [Real.cos_two_pi]
  have hcosTwoThird : Real.cos (2 * Real.pi / 3) = -(1 / 2 : ℝ) := by
    rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring,
      Real.cos_pi_sub, Real.cos_pi_div_three]
  have hcosFourThird : Real.cos (4 * Real.pi / 3) = -(1 / 2 : ℝ) := by
    rw [show 4 * Real.pi / 3 = 2 * Real.pi - 2 * Real.pi / 3 by ring,
      Real.cos_two_pi_sub, hcosTwoThird]
  rw [hcosTwoThird, hcosFourThird]
  field_simp [Real.pi_ne_zero]
  ring

theorem ledgerPrimitive_one_fourth : ledgerPrimitive (1 / 4) = 0 := by
  unfold ledgerPrimitive
  rw [show 2 * Real.pi * (1 / 4 : ℝ) = Real.pi / 2 by ring,
    show 4 * Real.pi * (1 / 4 : ℝ) = Real.pi by ring,
    show 6 * Real.pi * (1 / 4 : ℝ) = 3 * Real.pi / 2 by ring]
  rw [Real.cos_pi_div_two, Real.cos_pi]
  have hcosThreeHalves : Real.cos (3 * Real.pi / 2) = 0 := by
    rw [show 3 * Real.pi / 2 = 2 * Real.pi - Real.pi / 2 by ring,
      Real.cos_two_pi_sub, Real.cos_pi_div_two]
  rw [hcosThreeHalves]
  field_simp [Real.pi_ne_zero]
  ring

                          
theorem flux_d3_unregistered_03 :
    ledgerTwoEdgeScore (1 / 8) = 1 / (280 * Real.pi ^ 2) ∧
      ledgerTwoEdgeScore (1 / 8) ≠ 0 := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hcosQuarter : Real.cos (Real.pi / 4) = Real.sqrt 2 / 2 := by
    exact Real.cos_pi_div_four
  have hcosThreeQuarter : Real.cos (3 * Real.pi / 4) = -Real.sqrt 2 / 2 := by
    rw [show 3 * Real.pi / 4 = Real.pi - Real.pi / 4 by ring,
      Real.cos_pi_sub, hcosQuarter]
    ring
  have hvalue : ledgerTwoEdgeScore (1 / 8) =
      1 / (280 * Real.pi ^ 2) := by
    unfold ledgerTwoEdgeScore ledgerPrimitive ledgerScale
    rw [show 2 * Real.pi * (1 / 8 : ℝ) = Real.pi / 4 by ring,
      show 4 * Real.pi * (1 / 8 : ℝ) = Real.pi / 2 by ring,
      show 6 * Real.pi * (1 / 8 : ℝ) = 3 * Real.pi / 4 by ring,
      hcosQuarter, Real.cos_pi_div_two, hcosThreeQuarter]
    field_simp [hpi]
    ring
  exact ⟨hvalue, by
    rw [hvalue]
    exact div_ne_zero one_ne_zero
      (mul_ne_zero (by norm_num) (pow_ne_zero 2 hpi))⟩

end PhonologicalCalculus.Flux
