import PhonologicalCalculus.ContinuousHG.HardExponentSupportBridge
import PhonologicalCalculus.ContinuousHG.PhaseProfileOptimizerBridge
import PhonologicalCalculus.ContinuousHG.PhaseComparativeStatics

/-!
# Actual phase-two follower at the hard-exponent boundary

The one-horizon expression is an upper envelope, not the actual follower in
the saturated two-decrease phase.  This module derives the actual follower's
powered-gap equation, proves its nonnegativity and sharp envelope, and then
deduces metric convergence to zero for every admitted multiplier path.
-/

namespace PhonologicalCalculus.ContinuousHG

open Filter Set
open scoped Topology

/-- The second activity coordinate in a normalized two-decrease phase. -/
noncomputable def phaseTwoNormalizedFollower (p eta : ℝ) : ℝ :=
  normalizedPhaseProfile (powerShiftExponent p) eta 2 1

/-- The normalized phase-two follower and its preceding decrease obey the
exact powered-gap equation. -/
theorem phaseTwoNormalizedFollower_poweredGap
    {rho p eta : ℝ} (hrho : 0 < rho) (hp : 1 < p)
    (hetaZero : 0 ≤ eta) (hetaOne : eta < 1)
    (hphase : shiftedPowerSum (powerShiftExponent p) eta 2 =
      (p * rho) ^ powerShiftExponent p) :
    (1 - phaseTwoNormalizedFollower p eta) ^ (p - 1) -
        (phaseTwoNormalizedFollower p eta) ^ (p - 1) =
      1 / (p * rho) := by
  have hden : shiftedPowerSum (powerShiftExponent p) eta 2 ≠ 0 := by
    rw [hphase]
    exact ne_of_gt (Real.rpow_pos_of_pos
      (mul_pos (lt_trans zero_lt_one hp) hrho) _)
  have hgap := normalizedProfileLoss_powered_gap
    (p := p) (rho := rho) (tau := eta) (K := 2)
    (i := 0) (j := 1) hp hrho hetaZero hetaOne
    (by omega) (by omega) hphase
  unfold normalizedProfileLoss at hgap
  norm_num at hgap
  have hdenInverse : shiftedPowerSum ((p - 1)⁻¹) eta 2 ≠ 0 := by
    simpa [powerShiftExponent, one_div] using hden
  rw [normalizedPhaseProfile_zero hdenInverse,
    normalizedPhaseProfile_at_support] at hgap
  simpa [phaseTwoNormalizedFollower, powerShiftExponent, one_div,
    div_eq_mul_inv, mul_comm] using hgap

/-- The actual phase-two follower is nonnegative. -/
theorem phaseTwoNormalizedFollower_nonnegative
    {p eta : ℝ} (hp : 1 < p) (hetaOne : eta < 1) :
    0 ≤ phaseTwoNormalizedFollower p eta := by
  have hq : 0 < powerShiftExponent p :=
    powerShiftExponent_positive hp
  have hnumerator : 0 ≤ shiftedPowerSum
      (powerShiftExponent p) eta 1 := by
    exact (shiftedPowerSum_pos hq hetaOne (by norm_num)).le
  have hdenominator : 0 < shiftedPowerSum
      (powerShiftExponent p) eta 2 :=
    shiftedPowerSum_pos hq hetaOne (by norm_num)
  unfold phaseTwoNormalizedFollower normalizedPhaseProfile
  norm_num
  exact div_nonneg hnumerator hdenominator.le

/-- The preceding phase-two decrease `1 - x₁` is nonnegative. -/
theorem one_sub_phaseTwoNormalizedFollower_nonnegative
    {p eta : ℝ} (hp : 1 < p) (hetaOne : eta < 1) :
    0 ≤ 1 - phaseTwoNormalizedFollower p eta := by
  have hq : 0 < powerShiftExponent p :=
    powerShiftExponent_positive hp
  have hden : shiftedPowerSum (powerShiftExponent p) eta 2 ≠ 0 :=
    ne_of_gt (shiftedPowerSum_pos hq hetaOne (by norm_num))
  have hloss := normalizedPhaseProfile_sub_succ
    (q := powerShiftExponent p) (tau := eta)
    (K := 2) (i := 0) (by omega)
  rw [normalizedPhaseProfile_zero hden] at hloss
  have hright : 0 ≤
      ((((2 - 0 : ℕ) : ℝ) - eta) ^ powerShiftExponent p) /
        shiftedPowerSum (powerShiftExponent p) eta 2 := by
    exact div_nonneg
      (Real.rpow_nonneg (by norm_num; linarith) _)
      (shiftedPowerSum_pos hq hetaOne (by norm_num)).le
  unfold phaseTwoNormalizedFollower
  linarith

/-- In the saturated phase-two optimizer, the actual follower never exceeds
the one-horizon follower envelope. -/
theorem phaseTwoNormalizedFollower_le_hardExponentFollower
    {rho p eta : ℝ} (hrho : 0 < rho) (hp : 1 < p)
    (hetaZero : 0 ≤ eta) (hetaOne : eta < 1)
    (hphase : shiftedPowerSum (powerShiftExponent p) eta 2 =
      (p * rho) ^ powerShiftExponent p) :
    phaseTwoNormalizedFollower p eta ≤ hardExponentFollower rho p := by
  let y := phaseTwoNormalizedFollower p eta
  let exponent := p - 1
  let q := powerShiftExponent p
  let scale := p * rho
  have hscale : 0 < scale :=
    mul_pos (lt_trans zero_lt_one hp) hrho
  have hexponent : 0 < exponent := sub_pos.mpr hp
  have hq : 0 < q := powerShiftExponent_positive hp
  have hy : 0 ≤ y := phaseTwoNormalizedFollower_nonnegative hp hetaOne
  have honeSubY : 0 ≤ 1 - y :=
    one_sub_phaseTwoNormalizedFollower_nonnegative hp hetaOne
  have hgap :
      (1 - y) ^ exponent - y ^ exponent = 1 / scale := by
    simpa [y, exponent, scale] using
      phaseTwoNormalizedFollower_poweredGap hrho hp hetaZero hetaOne hphase
  have hyPower : 0 ≤ y ^ exponent := Real.rpow_nonneg hy _
  have hpowerLower : (1 / scale) ≤ (1 - y) ^ exponent := by
    linarith
  have hraised := Real.rpow_le_rpow
    (by positivity : 0 ≤ 1 / scale) hpowerLower hq.le
  have hexponentTimesQ : exponent * q = 1 := by
    unfold exponent q powerShiftExponent
    simp [one_div, sub_ne_zero.mpr (ne_of_gt hp)]
  have hright : ((1 - y) ^ exponent) ^ q = 1 - y := by
    rw [← Real.rpow_mul honeSubY, hexponentTimesQ, Real.rpow_one]
  have hleft : (1 / scale) ^ q = scale ^ (-q) := by
    rw [one_div, ← Real.rpow_neg_eq_inv_rpow]
  rw [hleft, hright] at hraised
  have hhard : hardExponentFollower rho p = 1 - scale ^ (-q) := by
    unfold hardExponentFollower scale q powerShiftExponent
    congr 2
    field_simp [hexponent.ne']
  rw [hhard]
  linarith

/-- The KKT follower at a unit-site phase-two multiplier is exactly the
normalized phase follower. -/
theorem phaseTwo_actualFollower_eq_normalized
    {rho p eta : ℝ} (hrho : 0 < rho) (hp : 1 < p)
    (hetaOne : eta < 1)
    (hmass : powerPathMass rho 1 p eta 2 = 1) :
    powerProfileFromDecreases (powerPathDecrease rho 1 p eta 2) 1 =
      phaseTwoNormalizedFollower p eta := by
  simpa [phaseTwoNormalizedFollower] using
    powerProfileFromDecreases_eq_normalizedPhaseProfile
      hrho (by norm_num) hp hetaOne hmass (i := 1)

/-- Every admitted family of actual phase-two optimizers converges to the
all-front metric profile at its sole positive follower. -/
theorem phaseTwo_actualFollower_tendsto_zero
    {rho : ℝ} (hrho : 0 < rho) (eta : ℝ → ℝ)
    (hadmitted : ∀ᶠ p : ℝ in atTop,
      1 < p ∧ 0 ≤ eta p ∧ eta p < 1 ∧
        powerPathMass rho 1 p (eta p) 2 = 1) :
    Tendsto
      (fun p : ℝ => powerProfileFromDecreases
        (powerPathDecrease rho 1 p (eta p) 2) 1)
      atTop (nhds 0) := by
  have hnonnegative : ∀ᶠ p : ℝ in atTop,
      0 ≤ powerProfileFromDecreases
        (powerPathDecrease rho 1 p (eta p) 2) 1 := by
    filter_upwards [hadmitted] with p h
    rw [phaseTwo_actualFollower_eq_normalized hrho h.1 h.2.2.1 h.2.2.2]
    exact phaseTwoNormalizedFollower_nonnegative h.1 h.2.2.1
  have hupper : ∀ᶠ p : ℝ in atTop,
      powerProfileFromDecreases
          (powerPathDecrease rho 1 p (eta p) 2) 1 ≤
        hardExponentFollower rho p := by
    filter_upwards [hadmitted] with p h
    have hphase : shiftedPowerSum (powerShiftExponent p) (eta p) 2 =
        (p * rho) ^ powerShiftExponent p := by
      simpa using (powerPathMass_one_iff_phaseEquation hrho (by norm_num)
        h.1 h.2.2.1).1 h.2.2.2
    rw [phaseTwo_actualFollower_eq_normalized hrho h.1 h.2.2.1 h.2.2.2]
    exact phaseTwoNormalizedFollower_le_hardExponentFollower
      hrho h.1 h.2.1 h.2.2.1 hphase
  exact squeeze_zero' hnonnegative hupper
    (hardExponentFollower_tendsto_zero hrho)

/-- Exact support persists at every admitted phase-two point even though the
actual positive follower converges metrically to zero. -/
theorem chg_b16_actual_support_metric_noncommutation
    {rho : ℝ} (hrho : 0 < rho) (eta : ℝ → ℝ)
    (hadmitted : ∀ᶠ p : ℝ in atTop,
      1 < p ∧ 0 ≤ eta p ∧ eta p < 1 ∧
        powerPathMass rho 1 p (eta p) 2 = 1) :
    (∀ᶠ p : ℝ in atTop,
      0 < powerProfileFromDecreases
        (powerPathDecrease rho 1 p (eta p) 2) 1) ∧
    Tendsto
      (fun p : ℝ => powerProfileFromDecreases
        (powerPathDecrease rho 1 p (eta p) 2) 1)
      atTop (nhds 0) := by
  constructor
  · filter_upwards [hadmitted] with p h
    apply powerProfileFromDecreases_positive_before_support
    · exact fun j => powerKKTDecrease_nonnegative
        (powerPathWeight 2) hrho h.1 j
    · exact fun j => powerPathDecrease_boundary_positive
        hrho (by norm_num) h.1 h.2.2.1 j
    · norm_num
  · exact phaseTwo_actualFollower_tendsto_zero hrho eta hadmitted

end PhonologicalCalculus.ContinuousHG
