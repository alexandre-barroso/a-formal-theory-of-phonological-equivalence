import PhonologicalCalculus.ContinuousHG.Bifurcation
import PhonologicalCalculus.ContinuousHG.PhaseComparativeStatics
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Phase-parameter asymptotics at support birth

This module derives the exact local asymptotic regimes of a newly active
coordinate.  The phase parameter is `t = 1 - tau`, approaching zero from the
positive side.  The finite old-support contribution is differentiated
exactly, while the new shifted-power term determines whether entry is flat,
linear with a joint coefficient, or cusp-dominated.
-/

namespace PhonologicalCalculus.ContinuousHG

open Filter Set
open scoped Topology BigOperators

/-- Contribution of the already active coordinates after the support-birth
parameter is shifted by `t`. -/
noncomputable def supportBirthOldSum (q : ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  ∑ r ∈ Finset.range k, ((((r + 1 : ℕ) : ℝ) + t) ^ q)

/-- Full shifted-power mass in the entering `(k+1)`-support phase. -/
noncomputable def supportBirthMass (q : ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  t ^ q + supportBirthOldSum q k t

/-- Linear coefficient contributed by the old support. -/
noncomputable def supportBirthLinearCoefficient (q : ℝ) (k : ℕ) : ℝ :=
  q * ∑ r ∈ Finset.range k,
    (((r + 1 : ℕ) : ℝ) ^ (q - 1))

/-- The reindexed entering-phase mass is exactly the canonical shifted-power
sum. -/
theorem supportBirthMass_eq_shiftedPowerSum
    (q t : ℝ) (k : ℕ) :
    supportBirthMass q k t = shiftedPowerSum q (1 - t) (k + 1) := by
  induction k with
  | zero =>
      simp [supportBirthMass, supportBirthOldSum, shiftedPowerSum]
  | succ k ih =>
      rw [show k + 1 + 1 = (k + 1) + 1 by omega,
        shiftedPowerSum_succ]
      unfold supportBirthMass supportBirthOldSum at ih ⊢
      rw [Finset.sum_range_succ]
      calc
        t ^ q +
            ((∑ x ∈ Finset.range k, (↑(x + 1) + t) ^ q) +
              (↑(k + 1) + t) ^ q) =
            (t ^ q + ∑ x ∈ Finset.range k,
              (↑(x + 1) + t) ^ q) +
              (↑(k + 1) + t) ^ q := by ring
        _ = shiftedPowerSum q (1 - t) (k + 1) +
              (↑(k + 1) + t) ^ q := by rw [ih]
        _ = shiftedPowerSum q (1 - t) (k + 1) +
              (↑(k + 1 + 1) - (1 - t)) ^ q := by
          congr 1
          have hbase :
              (↑(k + 1) : ℝ) + t =
                (↑(k + 1 + 1) : ℝ) - (1 - t) := by
            norm_num
            ring
          rw [hbase]

/-- The old-support contribution at birth is the preceding phase boundary
mass. -/
theorem supportBirthOldSum_zero (q : ℝ) (k : ℕ) :
    supportBirthOldSum q k 0 = shiftedPowerSum q 0 k := by
  unfold supportBirthOldSum shiftedPowerSum
  apply Finset.sum_congr rfl
  intro r _
  norm_num

/-- Exact derivative of the finite old-support contribution. -/
theorem supportBirthOldSum_hasDerivAt
    {q : ℝ} (k : ℕ) :
    HasDerivAt (supportBirthOldSum q k)
      (supportBirthLinearCoefficient q k) 0 := by
  unfold supportBirthOldSum supportBirthLinearCoefficient
  have hsum := HasDerivAt.fun_sum (u := Finset.range k) (x := (0 : ℝ))
    (A := fun r t => ((((r + 1 : ℕ) : ℝ) + t) ^ q))
    (A' := fun r => q * (((r + 1 : ℕ) : ℝ) ^ (q - 1))) (by
      intro r _
      have hbase : (((r + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
      have hinner : HasDerivAt
          (fun t : ℝ => ((r + 1 : ℕ) : ℝ) + t) 1 0 := by
        simpa using
          (hasDerivAt_id (0 : ℝ)).const_add (((r + 1 : ℕ) : ℝ))
      have hpowerAt : HasDerivAt (fun x : ℝ => x ^ q)
          (q * (((r + 1 : ℕ) : ℝ) ^ (q - 1)))
          (((r + 1 : ℕ) : ℝ) + 0) := by
        simpa using Real.hasDerivAt_rpow_const
          (x := ((r + 1 : ℕ) : ℝ)) (p := q) (Or.inl hbase)
      have hpower := hpowerAt.comp 0 hinner
      have hfun :
          ((fun x : ℝ => x ^ q) ∘
              (fun t : ℝ => ((r + 1 : ℕ) : ℝ) + t)) =
            (fun t : ℝ => (((r + 1 : ℕ) : ℝ) + t) ^ q) := rfl
      rw [hfun] at hpower
      simpa only [mul_one] using hpower)
  simpa only [Finset.mul_sum] using hsum

/-- First-order finite-sum expansion at support birth. -/
theorem supportBirthOldSum_slope_tendsto
    {q : ℝ} (k : ℕ) :
    Tendsto
      (fun t : ℝ =>
        (supportBirthOldSum q k t - supportBirthOldSum q k 0) / t)
      (nhdsWithin 0 (Ioi 0))
      (nhds (supportBirthLinearCoefficient q k)) := by
  have hslope := (supportBirthOldSum_hasDerivAt (q := q) k).tendsto_slope_zero
  have hfilter : nhdsWithin (0 : ℝ) (Ioi 0) ≤
      nhdsWithin (0 : ℝ) ({0}ᶜ) := by
    rw [nhdsWithin, nhdsWithin]
    apply inf_le_inf_left
    exact Filter.principal_mono.mpr fun t ht => by
      simpa using ht.ne'
  have hrestricted := hslope.mono_left hfilter
  simpa [div_eq_inv_mul, smul_eq_mul, add_zero] using hrestricted

/-- Positive real powers converge to zero from the positive side. -/
theorem positive_rpow_tendsto_zero_nhdsGT
    {a : ℝ} (ha : 0 < a) :
    Tendsto (fun t : ℝ => t ^ a)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  have hcontinuous :=
    Real.continuousAt_rpow_const 0 a (Or.inr ha.le)
  simpa [Real.zero_rpow ha.ne'] using
    hcontinuous.tendsto.mono_left
      (show nhdsWithin (0 : ℝ) (Ioi 0) ≤ nhds 0 from inf_le_left)

/-- In the subquadratic penalty regime `q>1`, the old-support linear term
dominates the newborn `t^q` term. -/
theorem supportBirthMass_excess_div_t_tendsto_subquadratic
    {q : ℝ} (hq : 1 < q) (k : ℕ) :
    Tendsto
      (fun t : ℝ =>
        (supportBirthMass q k t - supportBirthMass q k 0) / t)
      (nhdsWithin 0 (Ioi 0))
      (nhds (supportBirthLinearCoefficient q k)) := by
  have hpower := positive_rpow_tendsto_zero_nhdsGT
    (sub_pos.mpr hq)
  have hold := supportBirthOldSum_slope_tendsto (q := q) k
  have hsum : Tendsto
      (fun t : ℝ => t ^ (q - 1) +
        (supportBirthOldSum q k t - supportBirthOldSum q k 0) / t)
      (nhdsWithin 0 (Ioi 0))
      (nhds (supportBirthLinearCoefficient q k)) := by
    simpa using hpower.add hold
  refine hsum.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have htPositive : 0 < t := ht
  simp only [supportBirthMass]
  rw [show (t ^ q + supportBirthOldSum q k t -
      (0 ^ q + supportBirthOldSum q k 0)) / t =
      t ^ (q - 1) +
        (supportBirthOldSum q k t - supportBirthOldSum q k 0) / t by
    rw [Real.zero_rpow (ne_of_gt (lt_trans zero_lt_one hq))]
    rw [Real.rpow_sub_one htPositive.ne' q]
    field_simp [htPositive.ne']
    ring]

/-- At the quadratic boundary `q=1`, the newborn term contributes one to
the old-support slope. -/
theorem supportBirthMass_excess_div_t_tendsto_quadratic
    (k : ℕ) :
    Tendsto
      (fun t : ℝ =>
        (supportBirthMass 1 k t - supportBirthMass 1 k 0) / t)
      (nhdsWithin 0 (Ioi 0))
      (nhds (1 + supportBirthLinearCoefficient 1 k)) := by
  have hold := supportBirthOldSum_slope_tendsto (q := (1 : ℝ)) k
  have hone : Tendsto (fun _ : ℝ => (1 : ℝ))
      (nhdsWithin 0 (Ioi 0)) (nhds 1) := tendsto_const_nhds
  have hsum := hone.add hold
  have hsum' : Tendsto
      (fun t : ℝ => 1 +
        (supportBirthOldSum 1 k t - supportBirthOldSum 1 k 0) / t)
      (nhdsWithin 0 (Ioi 0))
      (nhds (1 + supportBirthLinearCoefficient 1 k)) := by
    simpa using hsum
  refine hsum'.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have htPositive : 0 < t := ht
  simp only [supportBirthMass, Real.rpow_one, Real.zero_rpow one_ne_zero]
  field_simp [htPositive.ne']
  ring

/-- In the superquadratic penalty regime `0<q<1`, the newborn `t^q` term
dominates the finite old-support linear displacement. -/
theorem supportBirthMass_excess_div_rpow_tendsto_superquadratic
    {q : ℝ} (hqZero : 0 < q) (hqOne : q < 1) (k : ℕ) :
    Tendsto
      (fun t : ℝ =>
        (supportBirthMass q k t - supportBirthMass q k 0) / t ^ q)
      (nhdsWithin 0 (Ioi 0)) (nhds 1) := by
  have hold := supportBirthOldSum_slope_tendsto (q := q) k
  have hpower := positive_rpow_tendsto_zero_nhdsGT
    (sub_pos.mpr hqOne)
  have hproduct := hold.mul hpower
  have hone : Tendsto (fun _ : ℝ => (1 : ℝ))
      (nhdsWithin 0 (Ioi 0)) (nhds 1) := tendsto_const_nhds
  have hsum : Tendsto
      (fun t : ℝ => 1 +
        ((supportBirthOldSum q k t - supportBirthOldSum q k 0) / t) *
          t ^ (1 - q))
      (nhdsWithin 0 (Ioi 0)) (nhds 1) := by
    simpa using hone.add hproduct
  refine hsum.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have htPositive : 0 < t := ht
  have htNonzero : t ≠ 0 := htPositive.ne'
  simp only [supportBirthMass]
  rw [Real.zero_rpow hqZero.ne']
  have hfactor :
      t ^ (1 - q) = t / t ^ q := by
    rw [show 1 - q = 1 + (-q) by ring, Real.rpow_add htPositive,
      Real.rpow_one, Real.rpow_neg htPositive.le]
    rfl
  rw [hfactor]
  field_simp [htNonzero, ne_of_gt (Real.rpow_pos_of_pos htPositive q)]
  ring

/-- Activity of the newly born coordinate in phase parameter `t`. -/
noncomputable def supportBirthCoordinate (q : ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  t ^ q / supportBirthMass q k t

/-- The newborn coordinate has exact leading scale `t^q / A_k` for every
positive exponent and nonempty old support. -/
theorem supportBirthCoordinate_div_rpow_tendsto
    {q : ℝ} (hq : 0 < q) {k : ℕ} (hk : 0 < k) :
    Tendsto
      (fun t : ℝ => supportBirthCoordinate q k t / t ^ q)
      (nhdsWithin 0 (Ioi 0))
      (nhds ((shiftedPowerSum q 0 k)⁻¹)) := by
  have hmassContinuous : ContinuousAt (supportBirthMass q k) 0 := by
    unfold supportBirthMass
    apply ContinuousAt.add
    · exact Real.continuousAt_rpow_const 0 q (Or.inr hq.le)
    · have holdContinuous : Continuous (supportBirthOldSum q k) := by
        unfold supportBirthOldSum
        apply continuous_finsetSum
        intro r _
        exact (Real.continuous_rpow_const hq.le).comp
          (continuous_const.add continuous_id)
      exact holdContinuous.continuousAt
  have hmassLimit : Tendsto (supportBirthMass q k)
      (nhdsWithin 0 (Ioi 0)) (nhds (shiftedPowerSum q 0 k)) := by
    simpa [supportBirthMass, Real.zero_rpow hq.ne',
      supportBirthOldSum_zero] using
      hmassContinuous.tendsto.mono_left
        (show nhdsWithin (0 : ℝ) (Ioi 0) ≤ nhds 0 from inf_le_left)
  have hboundaryPositive : 0 < shiftedPowerSum q 0 k :=
    shiftedPowerSum_pos hq (by norm_num) hk
  have hinverse := hmassLimit.inv₀ (ne_of_gt hboundaryPositive)
  refine hinverse.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have htPositive : 0 < t := ht
  unfold supportBirthCoordinate
  field_simp [ne_of_gt (Real.rpow_pos_of_pos htPositive q)]

/-- Exact phase-parameter form of the three onset orders. -/
theorem chg_b14_phaseParameter_asymptotic_package
    (k : ℕ) :
    (∀ q : ℝ, 1 < q →
      Tendsto
        (fun t : ℝ =>
          (supportBirthMass q k t - supportBirthMass q k 0) / t)
        (nhdsWithin 0 (Ioi 0))
        (nhds (supportBirthLinearCoefficient q k))) ∧
    Tendsto
      (fun t : ℝ =>
        (supportBirthMass 1 k t - supportBirthMass 1 k 0) / t)
      (nhdsWithin 0 (Ioi 0))
      (nhds (1 + supportBirthLinearCoefficient 1 k)) ∧
    (∀ q : ℝ, 0 < q → q < 1 →
      Tendsto
        (fun t : ℝ =>
          (supportBirthMass q k t - supportBirthMass q k 0) / t ^ q)
        (nhdsWithin 0 (Ioi 0)) (nhds 1)) := by
  exact ⟨fun q hq =>
      supportBirthMass_excess_div_t_tendsto_subquadratic hq k,
    supportBirthMass_excess_div_t_tendsto_quadratic k,
    fun q hqZero hqOne =>
      supportBirthMass_excess_div_rpow_tendsto_superquadratic
        hqZero hqOne k⟩

end PhonologicalCalculus.ContinuousHG
