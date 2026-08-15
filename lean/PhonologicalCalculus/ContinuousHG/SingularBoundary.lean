import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Singular selection at the linear exponent boundary

The superlinear optimizer has a singular limit as the exponent decreases to
one.  This file proves the exact equality-path limit, the variational selector
for the first-order correction, and the resulting failure of retrospective
winner-set upcasting.
-/

namespace PhonologicalCalculus.ContinuousHG

open Filter Set
open scoped Topology

/-- The decrease selected on the equality path, expressed with a real-valued
asymptotic parameter. -/
noncomputable def equalityBoundaryDecrease (x : ℝ) : ℝ :=
  (1 + 1 / x) ^ (-x)

/-- The equality-path decrease converges to `exp (-1)`. -/
theorem equalityBoundaryDecrease_tendsto :
    Tendsto equalityBoundaryDecrease atTop (𝓝 (Real.exp (-1))) := by
  have hbase := Real.tendsto_one_add_div_rpow_exp (1 : ℝ)
  have hinverse :
      Tendsto (fun x : ℝ => ((1 + 1 / x) ^ x)⁻¹) atTop
        (𝓝 ((Real.exp 1)⁻¹)) :=
    hbase.inv₀ (Real.exp_ne_zero 1)
  have hfunctions :
      equalityBoundaryDecrease =ᶠ[atTop]
        (fun x : ℝ => ((1 + 1 / x) ^ x)⁻¹) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    unfold equalityBoundaryDecrease
    rw [Real.rpow_neg]
    positivity
  have hlimit : (Real.exp 1)⁻¹ = Real.exp (-1) := by
    rw [← Real.exp_neg]
  rw [hlimit] at hinverse
  exact hinverse.congr' hfunctions.symm

/-- The corresponding activity profile converges to `1 - exp (-1)`. -/
theorem equalityBoundaryProfile_tendsto :
    Tendsto (fun x : ℝ => 1 - equalityBoundaryDecrease x) atTop
      (𝓝 (1 - Real.exp (-1))) := by
  exact tendsto_const_nhds.sub equalityBoundaryDecrease_tendsto

/-- Joint equality-boundary perturbation with first-order parameter `c`. -/
noncomputable def jointBoundaryDecrease (c x : ℝ) : ℝ :=
  ((1 + 1 / x) * (1 + c / x)) ^ (-x)

/-- Every fixed first-order joint path has the exact decrease limit
`exp (-(1+c))`. -/
theorem jointBoundaryDecrease_tendsto (c : ℝ) :
    Tendsto (jointBoundaryDecrease c) atTop
      (𝓝 (Real.exp (-(1 + c)))) := by
  have hone := Real.tendsto_one_add_div_rpow_exp (1 : ℝ)
  have hc := Real.tendsto_one_add_div_rpow_exp c
  have hproduct :
      Tendsto
        (fun x : ℝ => (1 + 1 / x) ^ x * (1 + c / x) ^ x)
        atTop (𝓝 (Real.exp 1 * Real.exp c)) := hone.mul hc
  have hproductLimit : Real.exp 1 * Real.exp c = Real.exp (1 + c) := by
    rw [← Real.exp_add]
  rw [hproductLimit] at hproduct
  have hinverse := hproduct.inv₀ (Real.exp_ne_zero (1 + c))
  have hfunctions :
      jointBoundaryDecrease c =ᶠ[atTop]
        (fun x : ℝ =>
          ((1 + 1 / x) ^ x * (1 + c / x) ^ x)⁻¹) := by
    filter_upwards [eventually_gt_atTop (max 0 (-c))] with x hx
    have hx0 : 0 < x := lt_of_le_of_lt (le_max_left 0 (-c)) hx
    have hxc : 0 < x + c := by
      have hxnegc : -c < x := lt_of_le_of_lt (le_max_right 0 (-c)) hx
      linarith
    have hfactorOne : 0 ≤ 1 + 1 / x := by positivity
    have hfactorC : 0 ≤ 1 + c / x := by
      have heq : 1 + c / x = (x + c) / x := by
        field_simp [ne_of_gt hx0]
      rw [heq]
      positivity
    unfold jointBoundaryDecrease
    rw [Real.rpow_neg (mul_nonneg hfactorOne hfactorC)]
    rw [Real.mul_rpow hfactorOne hfactorC]
  have hlimit : (Real.exp (1 + c))⁻¹ = Real.exp (-(1 + c)) := by
    rw [← Real.exp_neg]
  rw [hlimit] at hinverse
  exact hinverse.congr' hfunctions.symm

/-- The activity selected by a joint path has limit
`1 - exp (-(1+c))`. -/
theorem jointBoundaryProfile_tendsto (c : ℝ) :
    Tendsto (fun x : ℝ => 1 - jointBoundaryDecrease c x) atTop
      (𝓝 (1 - Real.exp (-(1 + c)))) := by
  exact tendsto_const_nhds.sub (jointBoundaryDecrease_tendsto c)

/-- Every admissible joint-path parameter selects a strict interior point of
the linear tie segment. -/
theorem jointBoundaryLimit_mem_Ioo {c : ℝ} (hc : -1 < c) :
    1 - Real.exp (-(1 + c)) ∈ Ioo (0 : ℝ) 1 := by
  have hexpPositive := Real.exp_pos (-(1 + c))
  have hnegative : -(1 + c) < 0 := by linarith
  have hexpBelowOne : Real.exp (-(1 + c)) < 1 :=
    Real.exp_lt_one_iff.mpr hnegative
  constructor <;> linarith

/-- Conversely, every strict interior point of the linear tie segment is the
limit selected by a unique displayed first-order path parameter. -/
theorem exists_jointBoundaryParameter {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
    ∃ c : ℝ, -1 < c ∧ 1 - Real.exp (-(1 + c)) = y := by
  let c : ℝ := -1 - Real.log (1 - y)
  have honeMinusPositive : 0 < 1 - y := sub_pos.mpr hy.2
  have honeMinusBelowOne : 1 - y < 1 := by linarith [hy.1]
  have hlogNegative : Real.log (1 - y) < 0 :=
    (Real.log_neg honeMinusPositive honeMinusBelowOne)
  refine ⟨c, ?_, ?_⟩
  · dsimp [c]
    linarith
  · have hexplog : Real.exp (Real.log (1 - y)) = 1 - y :=
      Real.exp_log honeMinusPositive
    dsimp [c]
    rw [show -(1 + (-1 - Real.log (1 - y))) = Real.log (1 - y) by ring]
    linarith

/-- Unconstrained decrease along a fixed ratio path, where `r` is the
critical support coefficient divided by the fixed harmony ratio. -/
noncomputable def fixedRatioUnclippedDecrease (r x : ℝ) : ℝ :=
  (r / (1 + 1 / x)) ^ x

/-- The solid-simplex constraint clips the decrease at one. -/
noncomputable def fixedRatioDecrease (r x : ℝ) : ℝ :=
  min 1 (fixedRatioUnclippedDecrease r x)

/-- The fixed-ratio candidate factors into a pure exponential base and the
equality-boundary decay. -/
theorem fixedRatioUnclippedDecrease_eq
    {r x : ℝ} (hr : 0 ≤ r) (hx : 0 < x) :
    fixedRatioUnclippedDecrease r x =
      r ^ x * equalityBoundaryDecrease x := by
  have hden : 0 ≤ 1 + 1 / x := by positivity
  unfold fixedRatioUnclippedDecrease equalityBoundaryDecrease
  rw [Real.div_rpow hr hden]
  rw [Real.rpow_neg hden]
  simp [div_eq_mul_inv]

/-- Below the critical fixed ratio (`0 < r < 1`), the decrease converges to
zero and the activity converges to the all-front endpoint. -/
theorem fixedRatioDecrease_tendsto_zero
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    Tendsto (fixedRatioDecrease r) atTop (𝓝 0) := by
  have hrpow := tendsto_rpow_atTop_of_base_lt_one r (by linarith) hr1
  have hcandidateProduct :
      Tendsto (fun x : ℝ => r ^ x * equalityBoundaryDecrease x) atTop
        (𝓝 (0 * Real.exp (-1))) :=
    hrpow.mul equalityBoundaryDecrease_tendsto
  have hcandidate :
      Tendsto (fixedRatioUnclippedDecrease r) atTop (𝓝 0) := by
    have heq : fixedRatioUnclippedDecrease r =ᶠ[atTop]
        (fun x : ℝ => r ^ x * equalityBoundaryDecrease x) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      exact fixedRatioUnclippedDecrease_eq hr0.le hx
    simpa using hcandidateProduct.congr' heq.symm
  unfold fixedRatioDecrease
  have hone : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1) :=
    tendsto_const_nhds
  simpa using hone.min hcandidate

/-- Below the critical fixed harmony ratio, the activity converges to one. -/
theorem fixedRatioProfile_tendsto_one
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    Tendsto (fun x : ℝ => 1 - fixedRatioDecrease r x) atTop (𝓝 1) := by
  simpa using tendsto_const_nhds.sub
    (fixedRatioDecrease_tendsto_zero hr0 hr1)

/-- Above the critical fixed coefficient ratio (`r > 1`), the unconstrained
decrease diverges. -/
theorem fixedRatioUnclippedDecrease_tendsto_atTop
    {r : ℝ} (hr1 : 1 < r) :
    Tendsto (fixedRatioUnclippedDecrease r) atTop atTop := by
  have hrpow := tendsto_rpow_atTop_of_base_gt_one r hr1
  have hproduct :
      Tendsto (fun x : ℝ => r ^ x * equalityBoundaryDecrease x) atTop atTop :=
    hrpow.atTop_mul_pos (Real.exp_pos (-1)) equalityBoundaryDecrease_tendsto
  have heq : fixedRatioUnclippedDecrease r =ᶠ[atTop]
      (fun x : ℝ => r ^ x * equalityBoundaryDecrease x) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact fixedRatioUnclippedDecrease_eq (by linarith) hx
  exact hproduct.congr' heq.symm

/-- Above the critical fixed coefficient ratio, clipping eventually selects
the concentrated decrease exactly. -/
theorem fixedRatioDecrease_eventually_one
    {r : ℝ} (hr1 : 1 < r) :
    ∀ᶠ x in atTop, fixedRatioDecrease r x = 1 := by
  have hlarge :=
    (fixedRatioUnclippedDecrease_tendsto_atTop hr1).eventually_ge_atTop 1
  filter_upwards [hlarge] with x hx
  simp [fixedRatioDecrease, min_eq_left hx]

/-- Above the critical fixed coefficient ratio, the activity converges to the
all-back endpoint. -/
theorem fixedRatioProfile_tendsto_zero
    {r : ℝ} (hr1 : 1 < r) :
    Tendsto (fun x : ℝ => 1 - fixedRatioDecrease r x) atTop (𝓝 0) := by
  apply tendsto_nhds_of_eventually_eq
  filter_upwards [fixedRatioDecrease_eventually_one hr1] with x hx
  simp [hx]

/-- The coefficient ratio `N/rho` lies below one exactly when the fixed
harmony ratio lies above the critical horizon. -/
theorem criticalCoefficient_lt_one_iff
    {N rho : ℝ} (hrho : 0 < rho) :
    N / rho < 1 ↔ N < rho := by
  exact (div_lt_one hrho).trans (by simp)

/-- The coefficient ratio lies above one exactly when the fixed harmony ratio
lies below the critical horizon. -/
theorem one_lt_criticalCoefficient_iff
    {N rho : ℝ} (hrho : 0 < rho) :
    1 < N / rho ↔ rho < N := by
  simpa [one_div] using (one_lt_div hrho)

/-- First-order variational correction on the nonnegative ray. -/
noncomputable def linearBoundaryCorrection (t : ℝ) : ℝ :=
  t * Real.log t

/-- `exp (-1)` globally minimizes the first-order correction on the
nonnegative ray. -/
theorem exp_neg_one_minimizes_linearBoundaryCorrection
    {t : ℝ} (ht : 0 ≤ t) :
    linearBoundaryCorrection (Real.exp (-1)) ≤
      linearBoundaryCorrection t := by
  unfold linearBoundaryCorrection
  by_cases hte : t ≤ Real.exp (-1)
  · exact Real.mul_log_strictAntiOn.antitoneOn
      ⟨ht, hte⟩
      ⟨(Real.exp_pos (-1)).le, le_rfl⟩ hte
  · have het : Real.exp (-1) ≤ t := le_of_lt (lt_of_not_ge hte)
    exact Real.mul_log_strictMonoOn.monotoneOn
      (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr het) het

/-- The variational minimizer is unique. -/
theorem linearBoundaryCorrection_minimizer_iff
    {t : ℝ} (ht : 0 ≤ t) :
    (∀ s : ℝ, 0 ≤ s →
      linearBoundaryCorrection t ≤ linearBoundaryCorrection s) ↔
      t = Real.exp (-1) := by
  constructor
  · intro hmin
    have hle := hmin (Real.exp (-1)) (Real.exp_pos (-1)).le
    rcases lt_trichotomy t (Real.exp (-1)) with hlt | heq | hgt
    · have hstrict :
          linearBoundaryCorrection (Real.exp (-1)) <
            linearBoundaryCorrection t := by
        unfold linearBoundaryCorrection
        exact Real.mul_log_strictAntiOn
          ⟨ht, hlt.le⟩
          ⟨(Real.exp_pos (-1)).le, le_rfl⟩ hlt
      exact (not_lt_of_ge hle hstrict).elim
    · exact heq
    · have hstrict :
          linearBoundaryCorrection (Real.exp (-1)) <
            linearBoundaryCorrection t := by
        unfold linearBoundaryCorrection
        exact Real.mul_log_strictMonoOn
          (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hgt.le) hgt
      exact (not_lt_of_ge hle hstrict).elim
  · rintro rfl s hs
    exact exp_neg_one_minimizes_linearBoundaryCorrection hs

/-- The limiting set of selected unique winners cannot be retrospectively
identified with the complete linear tie face.  The midpoint is a direct
counterwitness. -/
theorem singular_selected_set_ne_linear_tie_face :
    ({0, Real.exp (-1), 1} : Set ℝ) ≠ Icc 0 1 := by
  intro heq
  have hhalf : (1 / 2 : ℝ) ∈ Icc 0 1 := by norm_num
  have hmember : (1 / 2 : ℝ) ∈ ({0, Real.exp (-1), 1} : Set ℝ) := by
    rw [heq]
    exact hhalf
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmember
  rcases hmember with hzero | hexp | hone
  · norm_num at hzero
  · have hlt := Real.exp_neg_one_lt_half
    linarith
  · norm_num at hone

/-- Complete singular-boundary law for the clipped scalar optimizer.  Fixed
ratios on opposite sides of the critical horizon converge to opposite
endpoints, equality selects `1-exp(-1)`, first-order joint paths cover the
strict tie interior, and the three fixed-ratio path limits do not equal the
full linear argmin face. -/
theorem chg_b15_singular_boundary_law :
    (∀ r : ℝ, 0 < r → r < 1 →
      Tendsto (fun x : ℝ => 1 - fixedRatioDecrease r x) atTop (𝓝 1)) ∧
    (∀ r : ℝ, 1 < r →
      Tendsto (fun x : ℝ => 1 - fixedRatioDecrease r x) atTop (𝓝 0)) ∧
    Tendsto (fun x : ℝ => 1 - equalityBoundaryDecrease x) atTop
      (𝓝 (1 - Real.exp (-1))) ∧
    (∀ c : ℝ, -1 < c →
      1 - Real.exp (-(1 + c)) ∈ Ioo (0 : ℝ) 1) ∧
    (∀ y : ℝ, y ∈ Ioo (0 : ℝ) 1 →
      ∃ c : ℝ, -1 < c ∧ 1 - Real.exp (-(1 + c)) = y) ∧
    ({0, Real.exp (-1), 1} : Set ℝ) ≠ Icc 0 1 := by
  refine ⟨?_, ?_, equalityBoundaryProfile_tendsto, ?_, ?_,
    singular_selected_set_ne_linear_tie_face⟩
  · intro r hr0 hr1
    exact fixedRatioProfile_tendsto_one hr0 hr1
  · intro r hr1
    exact fixedRatioProfile_tendsto_zero hr1
  · intro c hc
    exact jointBoundaryLimit_mem_Ioo hc
  · intro y hy
    exact exists_jointBoundaryParameter hy

/-- Registered fixed-equality limit. -/
theorem chg_b15_equality_01 :
    Tendsto (fun x : ℝ => 1 - (1 + 1 / x) ^ (-x)) atTop
      (𝓝 (1 - Real.exp (-1))) := by
  simpa [equalityBoundaryDecrease] using equalityBoundaryProfile_tendsto

/-- Registered first-order variational selector. -/
theorem chg_b15_variational_02 :
    (∀ s : ℝ, 0 ≤ s →
      linearBoundaryCorrection (Real.exp (-1)) ≤
        linearBoundaryCorrection s) ∧
    (∀ t : ℝ, 0 ≤ t →
      (∀ s : ℝ, 0 ≤ s →
        linearBoundaryCorrection t ≤ linearBoundaryCorrection s) →
      t = Real.exp (-1)) := by
  constructor
  · intro s hs
    exact exp_neg_one_minimizes_linearBoundaryCorrection hs
  · intro t ht hmin
    exact (linearBoundaryCorrection_minimizer_iff ht).mp hmin

/-- The zero-perturbation joint path is the fixed equality path. -/
theorem chg_b15_path_03 :
    Tendsto (fun x : ℝ => 1 - equalityBoundaryDecrease x) atTop
      (𝓝 (1 - Real.exp (-(1 + 0)))) := by
  simpa using equalityBoundaryProfile_tendsto

/-- Registered no-upcast counterexample. -/
theorem chg_b15_upcast_04 :
    ¬ ({0, Real.exp (-1), 1} : Set ℝ) = Icc 0 1 :=
  singular_selected_set_ne_linear_tie_face

end PhonologicalCalculus.ContinuousHG
