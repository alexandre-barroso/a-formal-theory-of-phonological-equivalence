import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace PhonologicalCalculus.Flux

open Filter Finset Set
open scoped Topology

theorem telescoping_recurrence {f g : ℕ → ℝ} {i N : ℕ}
    (hiN : i ≤ N)
    (hstep : ∀ j, f j - f (j + 1) = g j) :
    f i = f (N + 1) + ∑ j ∈ Icc i N, g j := by
  induction N, hiN using Nat.le_induction with
  | base =>
      simpa using show f i = f (i + 1) + g i by
        linarith [hstep i]
  | succ N hi ih =>
      rw [sum_Icc_succ_top (Nat.le_succ_of_le hi)]
      linarith [hstep (N + 1)]

                        
theorem flux_d5_recurrence_02 {Fz x : ℕ → ℝ} {i N : ℕ}
    {mu epsilon : ℝ}
    (hiN : i ≤ N)
    (hstep : ∀ j,
      Fz j - Fz (j + 1) = mu * (1 + epsilon) * (x j) ^ epsilon)
    (hterminal : Fz (N + 1) = 0) :
    Fz i = mu * (1 + epsilon) *
      ∑ j ∈ Icc i N, (x j) ^ epsilon := by
  have htel := telescoping_recurrence hiN hstep
  rw [hterminal, zero_add] at htel
  rw [Finset.mul_sum]
  exact htel

noncomputable def finiteAuditBaseFactor (z : ℝ) : ℝ :=
  Real.sin (2 * Real.pi * z) *
    (1 - Real.cos (2 * Real.pi * z)) ^ 3

noncomputable def finiteAuditContactFactor (z : ℝ) : ℝ :=
  1 - Real.cos (2 * Real.pi * (z - 1 / 4))

noncomputable def finiteAuditPrimitive (z : ℝ) : ℝ :=
  finiteAuditBaseFactor z * finiteAuditContactFactor z ^ 2

theorem finiteAuditPrimitive_analytic :
    ∀ z, AnalyticAt ℝ finiteAuditPrimitive z := by
  intro z
  unfold finiteAuditPrimitive finiteAuditBaseFactor finiteAuditContactFactor
  fun_prop

theorem finiteAuditPrimitive_periodic :
    Function.Periodic finiteAuditPrimitive 1 := by
  intro z
  unfold finiteAuditPrimitive finiteAuditBaseFactor finiteAuditContactFactor
  rw [show 2 * Real.pi * (z + 1) = 2 * Real.pi * z + 2 * Real.pi by ring,
    Real.sin_add_two_pi, Real.cos_add_two_pi,
    show 2 * Real.pi * (z + 1 - 1 / 4) =
      2 * Real.pi * (z - 1 / 4) + 2 * Real.pi by ring,
    Real.cos_add_two_pi]

theorem finiteAuditContactFactor_hasDerivAt (z : ℝ) :
    HasDerivAt finiteAuditContactFactor
      (2 * Real.pi * Real.sin (2 * Real.pi * (z - 1 / 4))) z := by
  have hinner : HasDerivAt (fun x : ℝ => 2 * Real.pi * (x - 1 / 4))
      (2 * Real.pi) z := by
    have h := (hasDerivAt_const_mul (2 * Real.pi)).comp z
      ((hasDerivAt_id z).sub_const (1 / 4))
    simpa only [Function.comp_apply, id_eq, mul_one] using! h
  have hcos := hinner.cos
  have hsub := (hasDerivAt_const z 1).sub hcos
  exact hsub.congr_deriv (by ring)

theorem finiteAuditContactFactor_order_two :
    analyticOrderAt finiteAuditContactFactor (1 / 4) = 2 := by
  change analyticOrderAt finiteAuditContactFactor (1 / 4) =
    ((2 : ℕ) : ℕ∞)
  have hanalytic : AnalyticAt ℝ finiteAuditContactFactor (1 / 4) := by
    unfold finiteAuditContactFactor
    fun_prop
  rw [analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero hanalytic]
  constructor
  · intro k hk
    interval_cases k
    · simp [iteratedDeriv_zero, finiteAuditContactFactor]
    · rw [iteratedDeriv_one,
          (finiteAuditContactFactor_hasDerivAt (1 / 4)).deriv]
      simp
  · have hderiv : deriv finiteAuditContactFactor =
        fun z : ℝ =>
          2 * Real.pi * Real.sin (2 * Real.pi * (z - 1 / 4)) := by
      funext z
      exact (finiteAuditContactFactor_hasDerivAt z).deriv
    have hiter : iteratedDeriv 2 finiteAuditContactFactor =
        deriv (deriv finiteAuditContactFactor) := by
      rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ,
        iteratedDeriv_one]
    rw [hiter, hderiv]
    have hinner : HasDerivAt
        (fun z : ℝ => 2 * Real.pi * (z - 1 / 4))
        (2 * Real.pi) (1 / 4) := by
      have h := (hasDerivAt_const_mul (2 * Real.pi)).comp (1 / 4)
        ((hasDerivAt_id (1 / 4 : ℝ)).sub_const (1 / 4))
      simpa only [Function.comp_apply, id_eq, mul_one] using! h
    have hsin := hinner.sin
    have htotal := hsin.const_mul (2 * Real.pi)
    rw [htotal.deriv]
    simp

                    
theorem finiteAuditMarginalJet :
    iteratedDeriv 1 finiteAuditPrimitive (1 / 4) = 0 ∧
      iteratedDeriv 2 finiteAuditPrimitive (1 / 4) = 0 ∧
      iteratedDeriv 3 finiteAuditPrimitive (1 / 4) = 0 := by
  have hbase : AnalyticAt ℝ finiteAuditBaseFactor (1 / 4) := by
    unfold finiteAuditBaseFactor
    fun_prop
  have hcontact : AnalyticAt ℝ finiteAuditContactFactor (1 / 4) := by
    unfold finiteAuditContactFactor
    fun_prop
  have hprimitive : AnalyticAt ℝ finiteAuditPrimitive (1 / 4) := by
    unfold finiteAuditPrimitive
    fun_prop
  have horder : (4 : ℕ∞) ≤
      analyticOrderAt finiteAuditPrimitive (1 / 4) := by
    rw [show finiteAuditPrimitive =
        finiteAuditBaseFactor * finiteAuditContactFactor ^ 2 by rfl,
      analyticOrderAt_mul hbase (hcontact.pow 2),
      analyticOrderAt_pow hcontact,
      finiteAuditContactFactor_order_two]
    norm_num
  have hvanish :=
    (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hprimitive).mp horder
  exact ⟨hvanish 1 (by norm_num), hvanish 2 (by norm_num),
    hvanish 3 (by norm_num)⟩

theorem finiteAuditPrimitive_zero : finiteAuditPrimitive 0 = 0 := by
  simp [finiteAuditPrimitive, finiteAuditBaseFactor]

theorem finiteAuditPrimitive_half : finiteAuditPrimitive (1 / 2) = 0 := by
  unfold finiteAuditPrimitive finiteAuditBaseFactor
  rw [show 2 * Real.pi * (1 / 2 : ℝ) = Real.pi by ring, Real.sin_pi]
  ring

theorem finiteAuditPrimitive_one_eighth_ne_zero :
    finiteAuditPrimitive (1 / 8) ≠ 0 := by
  unfold finiteAuditPrimitive finiteAuditBaseFactor finiteAuditContactFactor
  rw [show 2 * Real.pi * (1 / 8 : ℝ) = Real.pi / 4 by ring,
    show 2 * Real.pi * ((1 / 8 : ℝ) - 1 / 4) = -Real.pi / 4 by ring,
    show -Real.pi / 4 = -(Real.pi / 4) by ring,
    Real.sin_pi_div_four, Real.cos_pi_div_four, Real.cos_neg,
    Real.cos_pi_div_four]
  have hsqrt : Real.sqrt 2 ≠ 0 := by positivity
  have hfactor : 1 - Real.sqrt 2 / 2 ≠ 0 := by
    have hsqrt_lt_two : Real.sqrt 2 < 2 := by
      have hsqrt_sq : (Real.sqrt 2) ^ 2 = 2 := by norm_num
      have hsqrt_nonneg := Real.sqrt_nonneg 2
      nlinarith
    linarith
  exact mul_ne_zero (mul_ne_zero (div_ne_zero hsqrt (by norm_num))
    (pow_ne_zero 3 hfactor)) (pow_ne_zero 2 hfactor)

                    
theorem flux_d5_finite_01 :
    finiteAuditPrimitive 0 = 0 ∧
      finiteAuditPrimitive (1 / 2) = 0 ∧
      (iteratedDeriv 1 finiteAuditPrimitive (1 / 4) = 0 ∧
        iteratedDeriv 2 finiteAuditPrimitive (1 / 4) = 0 ∧
        iteratedDeriv 3 finiteAuditPrimitive (1 / 4) = 0) ∧
      finiteAuditPrimitive (1 / 8) ≠ 0 := by
  exact ⟨finiteAuditPrimitive_zero, finiteAuditPrimitive_half,
    finiteAuditMarginalJet, finiteAuditPrimitive_one_eighth_ne_zero⟩

noncomputable def finiteAuditPerturbation (eta z : ℝ) : ℝ :=
  eta * finiteAuditPrimitive z

theorem finiteAuditPerturbation_preserves_ledger (eta : ℝ) :
    finiteAuditPerturbation eta 0 = 0 ∧
      finiteAuditPerturbation eta (1 / 2) = 0 ∧
      (iteratedDeriv 1 (finiteAuditPerturbation eta) (1 / 4) = 0 ∧
        iteratedDeriv 2 (finiteAuditPerturbation eta) (1 / 4) = 0 ∧
        iteratedDeriv 3 (finiteAuditPerturbation eta) (1 / 4) = 0) := by
  have hjet := finiteAuditMarginalJet
  constructor
  · simp [finiteAuditPerturbation, finiteAuditPrimitive_zero]
  constructor
  · rw [finiteAuditPerturbation, finiteAuditPrimitive_half, mul_zero]
  change
    iteratedDeriv 1 (eta • finiteAuditPrimitive) (1 / 4) = 0 ∧
      iteratedDeriv 2 (eta • finiteAuditPrimitive) (1 / 4) = 0 ∧
      iteratedDeriv 3 (eta • finiteAuditPrimitive) (1 / 4) = 0
  constructor
  · rw [iteratedDeriv_const_smul_field, hjet.1, smul_zero]
  constructor
  · rw [iteratedDeriv_const_smul_field, hjet.2.1, smul_zero]
  · rw [iteratedDeriv_const_smul_field, hjet.2.2, smul_zero]

theorem finiteAuditPerturbation_injective :
    Function.Injective (fun eta : ℝ => finiteAuditPerturbation eta) := by
  intro eta zeta heq
  have hpoint := congrFun heq (1 / 8)
  change eta * finiteAuditPrimitive (1 / 8) =
    zeta * finiteAuditPrimitive (1 / 8) at hpoint
  exact mul_right_cancel₀ finiteAuditPrimitive_one_eighth_ne_zero hpoint

                      
theorem flux_d5_identity_03 {U : Set ℝ} {F G : ℝ → ℝ} {z0 : ℝ}
    (hF : AnalyticOnNhd ℝ F U) (hG : AnalyticOnNhd ℝ G U)
    (hU : IsPreconnected U) (hz0 : z0 ∈ U)
    (hresponse : ∃ᶠ z in 𝓝[≠] z0, F z = G z) :
    EqOn F G U :=
  hF.eqOn_of_preconnected_of_frequently_eq hG hU hz0 hresponse

end PhonologicalCalculus.Flux
