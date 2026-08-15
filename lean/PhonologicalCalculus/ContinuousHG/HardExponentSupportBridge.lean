import PhonologicalCalculus.ContinuousHG.HardExponentAsymptotic
import PhonologicalCalculus.ContinuousHG.GeneralPowerOptimizer

/-!
# Hard-exponent phase-two support bridge

This module connects the scalar phase-two inequalities to the exact
first-zero cell of the general-power directional optimizer.  It deliberately
does not identify the phase-two follower with the one-horizon closed form:
those two quantities are only asymptotically equivalent.
-/

namespace PhonologicalCalculus.ContinuousHG

open Filter
open scoped Topology

private theorem powerPathShiftedSum_one
    {rho p : ℝ} (_hrho : 0 < rho) (_hp : 1 < p) :
    powerPathShiftedSum rho 1 p 1 =
      (1 / (p * rho)) ^ powerShiftExponent p := by
  unfold powerPathShiftedSum powerPathScale powerPathWeight
  simp

private theorem powerPathShiftedSum_two
    {rho p : ℝ} (_hrho : 0 < rho) (_hp : 1 < p) :
    powerPathShiftedSum rho 1 p 2 =
      (1 / (p * rho)) ^ powerShiftExponent p *
        (2 ^ powerShiftExponent p + 1) := by
  unfold powerPathShiftedSum powerPathScale powerPathWeight
  norm_num [Real.one_rpow]

/-- Under the declared positive parameter contract, the scalar phase-two
inequalities are exactly the `K = 2` first-zero cell of the general-power
directional optimizer. -/
theorem hardExponentPhaseTwo_iff_generalPowerFirstZeroCell_two
    {rho p : ℝ} (hrho : 0 < rho) (hp : 1 < p) :
    HardExponentPhaseTwo rho p ↔
      GeneralPowerFirstZeroCell rho 1 p 2 := by
  have hpPositive : 0 < p := lt_trans zero_lt_one hp
  have hA : 0 < p * rho := mul_pos hpPositive hrho
  have hr : 0 < p - 1 := sub_pos.mpr hp
  have hq : 0 < powerShiftExponent p := powerShiftExponent_positive hp
  have hrq : (p - 1) * powerShiftExponent p = 1 := by
    unfold powerShiftExponent
    field_simp [hr.ne']
  have hqr : powerShiftExponent p * (p - 1) = 1 := by
    rw [mul_comm]
    exact hrq
  have hbase : 0 < 1 + (2 : ℝ) ^ powerShiftExponent p := by
    positivity
  rw [generalPowerFirstZeroCell_iff_shiftedSum]
  constructor
  · rintro ⟨hAlower, hAupper⟩
    have hprevious : powerPathShiftedSum rho 1 p 1 < 1 := by
      rw [powerPathShiftedSum_one hrho hp]
      have hinvLt : 1 / (p * rho) < 1 := by
        rw [div_lt_one hA]
        simpa using hAlower
      exact Real.rpow_lt_one (by positivity) hinvLt hq
    have hAq : (p * rho) ^ powerShiftExponent p ≤
        1 + (2 : ℝ) ^ powerShiftExponent p := by
      change p * rho ≤
        (1 + (2 : ℝ) ^ powerShiftExponent p) ^ (p - 1) at hAupper
      have raised := Real.rpow_le_rpow hA.le hAupper hq.le
      rw [← Real.rpow_mul hbase.le, hrq, Real.rpow_one] at raised
      exact raised
    have hboundary : 1 ≤ powerPathShiftedSum rho 1 p 2 := by
      rw [powerPathShiftedSum_two hrho hp]
      have hAqPositive : 0 < (p * rho) ^ powerShiftExponent p :=
        Real.rpow_pos_of_pos hA _
      have hquotient :
          1 ≤ (1 + (2 : ℝ) ^ powerShiftExponent p) /
            ((p * rho) ^ powerShiftExponent p) :=
        (one_le_div hAqPositive).2 hAq
      have hinvPower :
          (1 / (p * rho)) ^ powerShiftExponent p =
            ((p * rho) ^ powerShiftExponent p)⁻¹ := by
        rw [one_div, Real.inv_rpow hA.le]
      rw [hinvPower]
      simpa [div_eq_mul_inv, mul_comm, add_comm] using hquotient
    exact ⟨by norm_num, hrho, by norm_num, hp, hprevious, hboundary⟩
  · rintro ⟨_hK, _hh, _hm, _hp, hprevious, hboundary⟩
    rw [powerPathShiftedSum_one hrho hp] at hprevious
    rw [powerPathShiftedSum_two hrho hp] at hboundary
    have hinvLt : 1 / (p * rho) < 1 :=
      (Real.rpow_lt_one_iff' (by positivity) hq).mp hprevious
    have hAlower : 1 < p * rho := by
      exact lt_of_one_div_lt_one_div hA (by simpa using hinvLt)
    have hAqPositive : 0 < (p * rho) ^ powerShiftExponent p :=
      Real.rpow_pos_of_pos hA _
    have hinvPower :
        (1 / (p * rho)) ^ powerShiftExponent p =
          ((p * rho) ^ powerShiftExponent p)⁻¹ := by
      rw [one_div, Real.inv_rpow hA.le]
    rw [hinvPower] at hboundary
    have hAq : (p * rho) ^ powerShiftExponent p ≤
        1 + (2 : ℝ) ^ powerShiftExponent p := by
      have hdivision :
          1 ≤ (1 + (2 : ℝ) ^ powerShiftExponent p) /
            ((p * rho) ^ powerShiftExponent p) := by
        simpa [div_eq_mul_inv, mul_comm, add_comm] using hboundary
      exact (one_le_div hAqPositive).mp hdivision
    have hAupper : p * rho ≤
        (1 + (2 : ℝ) ^ (1 / (p - 1) : ℝ)) ^ (p - 1) := by
      have raised := Real.rpow_le_rpow
        (Real.rpow_nonneg hA.le _) hAq hr.le
      rw [← Real.rpow_mul hA.le, hqr, Real.rpow_one] at raised
      simpa [powerShiftExponent] using raised
    exact ⟨hAlower, hAupper⟩

/-- Exact optimizer and all-longer-horizon support proof associated
with the hard-exponent `K = 2` cell. -/
def HardExponentSupportTwoProof (rho p : ℝ) : Prop :=
  ∃ eta,
    0 ≤ eta ∧ eta < 1 ∧
    powerPathMass rho 1 p eta 2 = 1 ∧
    IsUniqueMinimizerOn (SolidSimplex : (Fin 2 → ℝ) → Prop)
      (powerReducedObjective rho 1 p (powerPathWeight 2))
      (powerPathDecrease rho 1 p eta 2) ∧
    ∀ R : ℕ,
      IsUniqueMinimizerOn (SolidSimplex : (Fin (2 + R) → ℝ) → Prop)
        (powerReducedObjective rho 1 p (powerPathWeight (2 + R)))
        (powerPathDecrease rho 1 p (eta + 1 * R) (2 + R)) ∧
      ∀ i : ℕ,
        0 < powerProfileFromDecreases
          (powerPathDecrease rho 1 p (eta + 1 * R) (2 + R)) i ↔ i < 2

/-- The scalar phase-two inequalities imply a unique general-power optimizer
whose reconstructed profile is positive exactly at indices zero and one and
zero from index two onward, at every longer finite horizon. -/
theorem hardExponentSupportTwoProof_of_phaseTwo
    {rho p : ℝ} (hrho : 0 < rho) (hp : 1 < p)
    (hphase : HardExponentPhaseTwo rho p) :
    HardExponentSupportTwoProof rho p := by
  have hcell : GeneralPowerFirstZeroCell rho 1 p 2 :=
    (hardExponentPhaseTwo_iff_generalPowerFirstZeroCell_two hrho hp).1 hphase
  obtain ⟨eta, heta, hetaOne, hmass, hboundaryUnique, _hboundarySupport,
      hextension⟩ := generalPower_all_horizon_finite_persistence hcell
  refine ⟨eta, heta, by simpa using hetaOne, hmass, hboundaryUnique, ?_⟩
  intro R
  refine ⟨(hextension R).1, ?_⟩
  intro i
  simpa using generalPower_all_horizon_exact_first_zero
    hcell heta hmass R i

/-- For every fixed positive ratio, the exact `K = 2` cell and its unique
all-horizon support proof hold at all sufficiently large finite
exponents. -/
theorem hardExponentGeneralPower_supportTwo_eventually
    {rho : ℝ} (hrho : 0 < rho) :
    ∀ᶠ p : ℝ in atTop,
      GeneralPowerFirstZeroCell rho 1 p 2 ∧
        HardExponentSupportTwoProof rho p := by
  filter_upwards [hardExponentPhaseTwo_eventually hrho,
    eventually_gt_atTop (1 : ℝ)] with p hphase hp
  have hcell : GeneralPowerFirstZeroCell rho 1 p 2 :=
    (hardExponentPhaseTwo_iff_generalPowerFirstZeroCell_two hrho hp).1 hphase
  exact ⟨hcell,
    hardExponentSupportTwoProof_of_phaseTwo hrho hp hphase⟩

/-- Machine-closed part of the full hard-exponent theorem: arbitrary positive
ratios eventually enter the exact support-two optimizer cell, while the
closed-form one-horizon follower has the sharp logarithmic scale and tends to
zero.  The distinct phase-two follower asymptotic is intentionally not
asserted here. -/
theorem chg_b16_phase_support_and_oneHorizon_asymptotic
    {rho : ℝ} (hrho : 0 < rho) :
    (∀ᶠ p : ℝ in atTop,
      GeneralPowerFirstZeroCell rho 1 p 2 ∧
        HardExponentSupportTwoProof rho p) ∧
    Tendsto
      (fun p : ℝ => hardExponentFollower rho p /
        hardExponentScale rho p)
      atTop (nhds 1) ∧
    Tendsto (hardExponentFollower rho) atTop (nhds 0) := by
  exact ⟨hardExponentGeneralPower_supportTwo_eventually hrho,
    hardExponentFollower_div_scale_tendsto_one hrho,
    hardExponentFollower_tendsto_zero hrho⟩

end PhonologicalCalculus.ContinuousHG
