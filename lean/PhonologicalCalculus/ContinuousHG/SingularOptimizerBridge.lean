import PhonologicalCalculus.ContinuousHG.GeneralPowerOptimizer
import PhonologicalCalculus.ContinuousHG.SingularBoundary

/-!
# Scalar optimizer bridge at the singular exponent boundary

The singular-boundary limit is meaningful only if its clipped scalar profile
is the optimizer of the declared superlinear grammar.  This module proves that
bridge directly.  It first establishes the unique minimizer of a general
one-coordinate power objective on the unit interval, then identifies the
closed form with `fixedRatioDecrease` under the reparameterization
`p = 1 + 1/x`.
-/

namespace PhonologicalCalculus.ContinuousHG

open Filter Set
open scoped Topology

/-- One-coordinate reduced power objective. -/
noncomputable def scalarPowerObjective (p r d : ℝ) : ℝ := d ^ p - r * d

/-- The clipped stationary point of the scalar power objective. -/
noncomputable def scalarPowerCandidate (p r : ℝ) : ℝ :=
  min 1 ((r / p) ^ (1 / (p - 1)))

theorem scalarPowerCandidate_mem_Icc
    {p r : ℝ} (hp : 1 < p) (hr : 0 < r) :
    scalarPowerCandidate p r ∈ Icc (0 : ℝ) 1 := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hbase : 0 ≤ r / p := (div_pos hr hp0).le
  have hpower : 0 ≤ (r / p) ^ (1 / (p - 1)) :=
    Real.rpow_nonneg hbase _
  exact ⟨le_min zero_le_one hpower, min_le_left _ _⟩

private theorem stationaryPower_sub_one
    {p r : ℝ} (hp : 1 < p) (hr : 0 < r) :
    (((r / p) ^ (1 / (p - 1))) : ℝ) ^ (p - 1) = r / p := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hbase : 0 ≤ r / p := (div_pos hr hp0).le
  have hexponent : (1 / (p - 1)) * (p - 1) = 1 := by
    field_simp [ne_of_gt (sub_pos.mpr hp)]
  rw [← Real.rpow_mul hbase, hexponent, Real.rpow_one]

/-- The clipped stationary point is the unique minimizer on the unit
interval for every positive coefficient and every superlinear exponent. -/
theorem scalarPowerCandidate_unique_minimizer
    {p r : ℝ} (hp : 1 < p) (hr : 0 < r) :
    scalarPowerCandidate p r ∈ Icc (0 : ℝ) 1 ∧
    ∀ d ∈ Icc (0 : ℝ) 1,
      scalarPowerObjective p r (scalarPowerCandidate p r) ≤
          scalarPowerObjective p r d ∧
      (scalarPowerObjective p r d =
          scalarPowerObjective p r (scalarPowerCandidate p r) →
        d = scalarPowerCandidate p r) := by
  let w : ℝ := (r / p) ^ (1 / (p - 1))
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hq : 0 < 1 / (p - 1) := by positivity
  have hbase : 0 < r / p := div_pos hr hp0
  have hw0 : 0 < w := Real.rpow_pos_of_pos hbase _
  refine ⟨scalarPowerCandidate_mem_Icc hp hr, ?_⟩
  intro d hd
  by_cases hw1 : w ≤ 1
  · have hcandidate : scalarPowerCandidate p r = w := by
      unfold scalarPowerCandidate
      change min 1 w = w
      exact min_eq_right hw1
    have hstation : p * w ^ (p - 1) = r := by
      have hpow : w ^ (p - 1) = r / p := by
        simpa [w] using stationaryPower_sub_one hp hr
      rw [hpow]
      field_simp [ne_of_gt hp0]
    have htangent := rpow_strict_tangent hp hw0.le hd.1
    rw [hstation] at htangent
    rw [hcandidate]
    constructor
    · unfold scalarPowerObjective
      linarith [htangent.1]
    · intro hequal
      apply htangent.2
      unfold scalarPowerObjective at hequal
      linarith [htangent.1]
  · have honew : 1 < w := lt_of_not_ge hw1
    have hbaseOne : 1 < r / p := by
      have hrpow := (Real.one_lt_rpow_iff_of_pos hbase).mp honew
      rcases hrpow with hforward | himpossible
      · exact hforward.1
      · exact (not_lt_of_ge hq.le himpossible.2).elim
    have hpr : p < r := by
      simpa using (lt_div_iff₀ hp0).mp hbaseOne
    have hcandidate : scalarPowerCandidate p r = 1 := by
      unfold scalarPowerCandidate
      change min 1 w = 1
      exact min_eq_left honew.le
    have htangent := rpow_strict_tangent hp (show 0 ≤ (1 : ℝ) by norm_num) hd.1
    rw [hcandidate]
    constructor
    · unfold scalarPowerObjective
      have hlinear : 0 ≤ (p - r) * (d - 1) :=
        mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith [hd.2])
      have hlinear' : 0 ≤ p * d - p - r * d + r := by
        nlinarith [hlinear]
      norm_num [Real.one_rpow] at htangent
      rw [Real.one_rpow]
      norm_num
      linarith [htangent.1, hlinear']
    · intro hequal
      have hlinear : 0 ≤ (p - r) * (d - 1) :=
        mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith [hd.2])
      have hlinear' : 0 ≤ p * d - p - r * d + r := by
        nlinarith [hlinear]
      have htangent' := htangent
      norm_num [Real.one_rpow] at htangent'
      apply htangent.2
      norm_num [Real.one_rpow]
      unfold scalarPowerObjective at hequal
      rw [Real.one_rpow] at hequal
      norm_num at hequal
      linarith [htangent'.1, hlinear']

/-- Under `p = 1 + 1/x`, the clipped scalar stationary point is exactly the
fixed-ratio decrease used in the singular-boundary law. -/
theorem scalarPowerCandidate_eq_fixedRatioDecrease
    {r x : ℝ} (hx : 0 < x) :
    scalarPowerCandidate (1 + 1 / x) r = fixedRatioDecrease r x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  unfold scalarPowerCandidate fixedRatioDecrease fixedRatioUnclippedDecrease
  congr 1
  have hexponent : 1 / (1 + 1 / x - 1) = x := by
    field_simp [hx0]
    ring
  rw [hexponent]

/-- Exact optimizer bridge for every positive fixed ratio and every
superlinear reparameterization `p = 1 + 1/x`. -/
theorem fixedRatioDecrease_unique_minimizer
    {r x : ℝ} (hr : 0 < r) (hx : 0 < x) :
    fixedRatioDecrease r x ∈ Icc (0 : ℝ) 1 ∧
    ∀ d ∈ Icc (0 : ℝ) 1,
      scalarPowerObjective (1 + 1 / x) r (fixedRatioDecrease r x) ≤
          scalarPowerObjective (1 + 1 / x) r d ∧
      (scalarPowerObjective (1 + 1 / x) r d =
          scalarPowerObjective (1 + 1 / x) r (fixedRatioDecrease r x) →
        d = fixedRatioDecrease r x) := by
  have hinverse : 0 < 1 / x := one_div_pos.mpr hx
  have hp : 1 < 1 + 1 / x := by linarith
  have h := scalarPowerCandidate_unique_minimizer hp hr
  rw [scalarPowerCandidate_eq_fixedRatioDecrease hx] at h
  exact h

/-- Complete optimizer-to-limit composition for the singular boundary.  The
first conjunct proves that every prelimit selected point is the unique winner
of the declared scalar grammar; the second conjunct is the exact fixed-ratio,
equality-path, joint-path, and no-upcast limit law. -/
theorem chg_b15_complete_optimizer_boundary_law :
    (∀ (r x : ℝ), 0 < r → 0 < x →
      fixedRatioDecrease r x ∈ Icc (0 : ℝ) 1 ∧
      ∀ d ∈ Icc (0 : ℝ) 1,
        scalarPowerObjective (1 + 1 / x) r (fixedRatioDecrease r x) ≤
            scalarPowerObjective (1 + 1 / x) r d ∧
        (scalarPowerObjective (1 + 1 / x) r d =
            scalarPowerObjective (1 + 1 / x) r (fixedRatioDecrease r x) →
          d = fixedRatioDecrease r x)) ∧
    ((∀ r : ℝ, 0 < r → r < 1 →
        Tendsto (fun x : ℝ => 1 - fixedRatioDecrease r x) atTop (𝓝 1)) ∧
      (∀ r : ℝ, 1 < r →
        Tendsto (fun x : ℝ => 1 - fixedRatioDecrease r x) atTop (𝓝 0)) ∧
      Tendsto (fun x : ℝ => 1 - equalityBoundaryDecrease x) atTop
        (𝓝 (1 - Real.exp (-1))) ∧
      (∀ c : ℝ, -1 < c →
        1 - Real.exp (-(1 + c)) ∈ Ioo (0 : ℝ) 1) ∧
      (∀ y : ℝ, y ∈ Ioo (0 : ℝ) 1 →
        ∃ c : ℝ, -1 < c ∧ 1 - Real.exp (-(1 + c)) = y) ∧
      ({0, Real.exp (-1), 1} : Set ℝ) ≠ Icc 0 1) := by
  exact ⟨fun r x hr hx => fixedRatioDecrease_unique_minimizer hr hx,
    chg_b15_singular_boundary_law⟩

end PhonologicalCalculus.ContinuousHG
