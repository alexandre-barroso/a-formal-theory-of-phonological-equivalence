import PhonologicalCalculus.ContinuousHG.HardExponentActualFollower
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Sharp asymptotic for the actual phase-two follower

The one-horizon follower is only an upper envelope for the saturated
two-decrease optimizer.  This module proves that the actual follower has the
same logarithmic first-order scale.  The proof is uniform over every admitted
choice of the phase multiplier.
-/

namespace PhonologicalCalculus.ContinuousHG

open Filter Set
open scoped Topology

/-- In an admitted phase-two cell, the actual follower lies between the
one-horizon envelope and that envelope divided by `1 + 1 / (p - 1)`.

The lower bound follows from Bernoulli's inequality.  If
`a = 1 - eta` and `q = 1 / (p - 1)`, the phase equation is
`a^q + (1 + a)^q = (p * rho)^q`, while Bernoulli gives
`(1 + a)^q - 1 <= q * a <= q * a^q`.
-/
theorem phaseTwoNormalizedFollower_sharp_bounds
    {rho p eta : ℝ} (hrho : 0 < rho) (hp : 2 ≤ p)
    (hetaZero : 0 ≤ eta) (hetaOne : eta < 1)
    (hphase : shiftedPowerSum (powerShiftExponent p) eta 2 =
      (p * rho) ^ powerShiftExponent p) :
    hardExponentFollower rho p / (1 + powerShiftExponent p) ≤
        phaseTwoNormalizedFollower p eta ∧
      phaseTwoNormalizedFollower p eta ≤ hardExponentFollower rho p := by
  have hpOne : 1 < p := lt_of_lt_of_le (by norm_num) hp
  have hqPos : 0 < powerShiftExponent p :=
    powerShiftExponent_positive hpOne
  have hqNonnegative : 0 ≤ powerShiftExponent p := hqPos.le
  have hqLeOne : powerShiftExponent p ≤ 1 := by
    unfold powerShiftExponent
    rw [div_le_one (sub_pos.mpr hpOne)]
    linarith
  let a : ℝ := 1 - eta
  let q : ℝ := powerShiftExponent p
  let z : ℝ := a ^ q
  let total : ℝ := shiftedPowerSum q eta 2
  have haPos : 0 < a := by
    dsimp [a]
    linarith
  have haLeOne : a ≤ 1 := by
    dsimp [a]
    linarith
  have hzNonnegative : 0 ≤ z := Real.rpow_nonneg haPos.le _
  have haLeZ : a ≤ z := by
    dsimp [z, q]
    exact Real.self_le_rpow_of_le_one haPos.le haLeOne hqLeOne
  have hsecondLower : 1 ≤ (1 + a) ^ q := by
    have honeBase : 1 ≤ 1 + a := by linarith
    simpa using Real.one_le_rpow honeBase hqNonnegative
  have hsecondUpper : (1 + a) ^ q ≤ 1 + q * z := by
    calc
      (1 + a) ^ q ≤ 1 + q * a := by
        exact rpow_one_add_le_one_add_mul_self (by linarith) hqNonnegative hqLeOne
      _ ≤ 1 + q * z := by
        gcongr
  have htotalExpansion : total = z + (1 + a) ^ q := by
    dsimp [total, z, q, a]
    norm_num [shiftedPowerSum, Finset.sum_range_succ]
    congr 1
    ring
  have htotalPositive : 0 < total := by
    rw [htotalExpansion]
    positivity
  have htotalMinusOneLower : z ≤ total - 1 := by
    rw [htotalExpansion]
    linarith
  have htotalMinusOneUpper : total - 1 ≤ (1 + q) * z := by
    rw [htotalExpansion]
    nlinarith
  have hphaseTotal : total = (p * rho) ^ q := by
    simpa [total, q] using hphase
  have hactual : phaseTwoNormalizedFollower p eta = z / total := by
    dsimp [phaseTwoNormalizedFollower, normalizedPhaseProfile, z, total, q, a]
    norm_num [shiftedPowerSum, Finset.sum_range_succ]
  have hhard : hardExponentFollower rho p = (total - 1) / total := by
    have hbase : 0 < p * rho :=
      mul_pos (lt_trans zero_lt_one hpOne) hrho
    have hqIdentity : (-1 : ℝ) / (p - 1) = -q := by
      dsimp [q, powerShiftExponent]
      ring
    unfold hardExponentFollower
    rw [hqIdentity, Real.rpow_neg hbase.le, ← hphaseTotal]
    field_simp [ne_of_gt htotalPositive]
  have hdenFactor : 0 < 1 + q := by linarith
  constructor
  · rw [hhard, hactual]
    change (total - 1) / total / (1 + q) ≤ z / total
    rw [div_le_iff₀ hdenFactor]
    rw [show z / total * (1 + q) = ((1 + q) * z) / total by ring]
    exact (div_le_div_iff_of_pos_right htotalPositive).2
      htotalMinusOneUpper
  · exact phaseTwoNormalizedFollower_le_hardExponentFollower
      hrho hpOne hetaZero hetaOne hphase

/-- The reciprocal hard-exponent coordinate tends to zero. -/
theorem powerShiftExponent_tendsto_zero :
    Tendsto powerShiftExponent atTop (nhds 0) := by
  have hsub : Tendsto (fun p : ℝ => p - 1) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    filter_upwards [eventually_ge_atTop (b + 1)] with p hp
    linarith
  have hinverse : Tendsto (fun p : ℝ => (p - 1)⁻¹)
      atTop (nhds 0) := tendsto_inv_atTop_zero.comp hsub
  change Tendsto (fun p : ℝ => 1 / (p - 1)) atTop (nhds 0)
  simpa only [one_div] using hinverse

/-- A canonical phase-two multiplier.  Outside the exact phase-two cell its
value is immaterial; inside the cell it selects the multiplier furnished by
the all-horizon persistence theorem. -/
noncomputable def hardExponentActualOffset (rho p : ℝ) : ℝ := by
  classical
  exact if hcell : GeneralPowerFirstZeroCell rho 1 p 2 then
      Classical.choose (generalPower_all_horizon_finite_persistence hcell)
    else 0

/-- Every in-cell canonical multiplier carries the complete finite-horizon
optimizer proof, including exact support and extension stability. -/
theorem hardExponentActualOffset_spec
    {rho p : ℝ} (hcell : GeneralPowerFirstZeroCell rho 1 p 2) :
    0 ≤ hardExponentActualOffset rho p ∧
    hardExponentActualOffset rho p < 1 ∧
    powerPathMass rho 1 p (hardExponentActualOffset rho p) 2 = 1 ∧
    IsUniqueMinimizerOn (SolidSimplex : (Fin 2 → ℝ) → Prop)
      (powerReducedObjective rho 1 p (powerPathWeight 2))
      (powerPathDecrease rho 1 p (hardExponentActualOffset rho p) 2) ∧
    (∀ i : ℕ,
      0 < powerProfileFromDecreases
          (powerPathDecrease rho 1 p (hardExponentActualOffset rho p) 2) i ↔
        i < 2) ∧
    (∀ R : ℕ,
      IsUniqueMinimizerOn (SolidSimplex : (Fin (2 + R) → ℝ) → Prop)
        (powerReducedObjective rho 1 p (powerPathWeight (2 + R)))
        (powerPathDecrease rho 1 p
          (hardExponentActualOffset rho p + 1 * R) (2 + R)) ∧
      (∀ i : Fin 2,
        powerPathDecrease rho 1 p
            (hardExponentActualOffset rho p + 1 * R) (2 + R)
            (powerPathOldIndex R i) =
          powerPathDecrease rho 1 p (hardExponentActualOffset rho p) 2 i) ∧
      (∀ j : Fin R,
        powerPathDecrease rho 1 p
            (hardExponentActualOffset rho p + 1 * R) (2 + R)
            (powerPathNewIndex 2 j) = 0)) := by
  have hchosen := Classical.choose_spec
    (generalPower_all_horizon_finite_persistence hcell)
  simpa only [hardExponentActualOffset, dif_pos hcell] using hchosen

/-- For every fixed positive ratio, the canonical actual-offset path is
eventually an admitted phase-two path. -/
theorem hardExponentActualOffset_eventually_admitted
    {rho : ℝ} (hrho : 0 < rho) :
    ∀ᶠ p : ℝ in atTop,
      1 < p ∧ 0 ≤ hardExponentActualOffset rho p ∧
      hardExponentActualOffset rho p < 1 ∧
      powerPathMass rho 1 p (hardExponentActualOffset rho p) 2 = 1 := by
  filter_upwards [hardExponentGeneralPower_supportTwo_eventually hrho]
      with p hp
  have hspec := hardExponentActualOffset_spec hp.1
  exact ⟨hp.1.2.2.2.1, hspec.1, hspec.2.1, hspec.2.2.1⟩

/-- For every fixed positive ratio, the selected path is eventually the
unique phase-two optimizer with exact first zero at index two and stable
all-horizon extensions. -/
theorem hardExponentActualOffset_eventually_unique
    {rho : ℝ} (hrho : 0 < rho) :
    ∀ᶠ p : ℝ in atTop,
      GeneralPowerFirstZeroCell rho 1 p 2 ∧
      IsUniqueMinimizerOn (SolidSimplex : (Fin 2 → ℝ) → Prop)
        (powerReducedObjective rho 1 p (powerPathWeight 2))
        (powerPathDecrease rho 1 p (hardExponentActualOffset rho p) 2) ∧
      (∀ i : ℕ,
        0 < powerProfileFromDecreases
            (powerPathDecrease rho 1 p (hardExponentActualOffset rho p) 2) i ↔
          i < 2) ∧
      (∀ R : ℕ,
        IsUniqueMinimizerOn
          (SolidSimplex : (Fin (2 + R) → ℝ) → Prop)
          (powerReducedObjective rho 1 p (powerPathWeight (2 + R)))
          (powerPathDecrease rho 1 p
            (hardExponentActualOffset rho p + 1 * R) (2 + R))) := by
  filter_upwards [hardExponentGeneralPower_supportTwo_eventually hrho]
      with p hp
  have hspec := hardExponentActualOffset_spec hp.1
  exact ⟨hp.1, hspec.2.2.2.1, hspec.2.2.2.2.1,
    fun R => (hspec.2.2.2.2.2 R).1⟩

/-- Sharp actual-follower law.  For every admitted phase-multiplier path, the
positive follower of the unique phase-two optimizer is first-order equivalent
to `log (p * rho) / (p - 1)`.

The conclusion is independent of how the admitted multiplier is selected.
-/
theorem phaseTwo_actualFollower_div_scale_tendsto_one
    {rho : ℝ} (hrho : 0 < rho) (eta : ℝ → ℝ)
    (hadmitted : ∀ᶠ p : ℝ in atTop,
      1 < p ∧ 0 ≤ eta p ∧ eta p < 1 ∧
        powerPathMass rho 1 p (eta p) 2 = 1) :
    Tendsto
      (fun p : ℝ =>
        powerProfileFromDecreases
            (powerPathDecrease rho 1 p (eta p) 2) 1 /
          hardExponentScale rho p)
      atTop (nhds 1) := by
  have henvelope := hardExponentFollower_div_scale_tendsto_one hrho
  have honePlus : Tendsto
      (fun p : ℝ => 1 + powerShiftExponent p)
      atTop (nhds 1) := by
    have hone : Tendsto (fun _p : ℝ => (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    simpa using hone.add powerShiftExponent_tendsto_zero
  have hlowerReference : Tendsto
      (fun p : ℝ =>
        (hardExponentFollower rho p / hardExponentScale rho p) /
          (1 + powerShiftExponent p))
      atTop (nhds 1) := by
    change Tendsto
      ((fun p : ℝ =>
          hardExponentFollower rho p / hardExponentScale rho p) /
        (fun p : ℝ => 1 + powerShiftExponent p))
      atTop (nhds 1)
    simpa using henvelope.div honePlus (by norm_num : (1 : ℝ) ≠ 0)
  have hlower : Tendsto
      (fun p : ℝ =>
        hardExponentFollower rho p / (1 + powerShiftExponent p) /
          hardExponentScale rho p)
      atTop (nhds 1) := by
    refine hlowerReference.congr' ?_
    filter_upwards with p
    ring
  have hscalePositive := hardExponentScale_eventually_pos hrho
  have hbetweenLower : ∀ᶠ p : ℝ in atTop,
      hardExponentFollower rho p / (1 + powerShiftExponent p) /
          hardExponentScale rho p ≤
        powerProfileFromDecreases
            (powerPathDecrease rho 1 p (eta p) 2) 1 /
          hardExponentScale rho p := by
    filter_upwards [hadmitted, hscalePositive,
      eventually_ge_atTop (2 : ℝ)] with p hp hs hpTwo
    have hphase : shiftedPowerSum (powerShiftExponent p) (eta p) 2 =
        (p * rho) ^ powerShiftExponent p := by
      simpa using (powerPathMass_one_iff_phaseEquation hrho (by norm_num)
        hp.1 hp.2.2.1).1 hp.2.2.2
    have hbounds := phaseTwoNormalizedFollower_sharp_bounds
      hrho hpTwo hp.2.1 hp.2.2.1 hphase
    rw [phaseTwo_actualFollower_eq_normalized
      hrho hp.1 hp.2.2.1 hp.2.2.2]
    exact (div_le_div_iff_of_pos_right hs).2 hbounds.1
  have hbetweenUpper : ∀ᶠ p : ℝ in atTop,
      powerProfileFromDecreases
            (powerPathDecrease rho 1 p (eta p) 2) 1 /
          hardExponentScale rho p ≤
        hardExponentFollower rho p / hardExponentScale rho p := by
    filter_upwards [hadmitted, hscalePositive,
      eventually_ge_atTop (2 : ℝ)] with p hp hs hpTwo
    have hphase : shiftedPowerSum (powerShiftExponent p) (eta p) 2 =
        (p * rho) ^ powerShiftExponent p := by
      simpa using (powerPathMass_one_iff_phaseEquation hrho (by norm_num)
        hp.1 hp.2.2.1).1 hp.2.2.2
    have hbounds := phaseTwoNormalizedFollower_sharp_bounds
      hrho hpTwo hp.2.1 hp.2.2.1 hphase
    rw [phaseTwo_actualFollower_eq_normalized
      hrho hp.1 hp.2.2.1 hp.2.2.2]
    exact (div_le_div_iff_of_pos_right hs).2 hbounds.2
  exact hlower.squeeze' henvelope hbetweenLower hbetweenUpper

/-- Complete actual phase-two support--magnitude package along every admitted
multiplier path: the follower stays strictly positive at every admitted finite
exponent, is sharply logarithmic in magnitude, and converges metrically to
zero. -/
theorem chg_b16_actualFollower_complete_asymptotic
    {rho : ℝ} (hrho : 0 < rho) (eta : ℝ → ℝ)
    (hadmitted : ∀ᶠ p : ℝ in atTop,
      1 < p ∧ 0 ≤ eta p ∧ eta p < 1 ∧
        powerPathMass rho 1 p (eta p) 2 = 1) :
    (∀ᶠ p : ℝ in atTop,
      0 < powerProfileFromDecreases
        (powerPathDecrease rho 1 p (eta p) 2) 1) ∧
    Tendsto
      (fun p : ℝ =>
        powerProfileFromDecreases
            (powerPathDecrease rho 1 p (eta p) 2) 1 /
          hardExponentScale rho p)
      atTop (nhds 1) ∧
    Tendsto
      (fun p : ℝ => powerProfileFromDecreases
        (powerPathDecrease rho 1 p (eta p) 2) 1)
      atTop (nhds 0) := by
  have hsupportMetric :=
    chg_b16_actual_support_metric_noncommutation hrho eta hadmitted
  exact ⟨hsupportMetric.1,
    phaseTwo_actualFollower_div_scale_tendsto_one hrho eta hadmitted,
    hsupportMetric.2⟩

/-- Unconditional fixed-ratio closure of the actual hard-exponent law.  The
canonical multiplier path exists, is eventually the unique exact phase-two
optimizer at every finite horizon, keeps one strictly positive follower, has
the sharp logarithmic first-order magnitude, and converges metrically to the
hard categorical profile. -/
theorem chg_b16_unconditional_actual_hard_exponent_law
    {rho : ℝ} (hrho : 0 < rho) :
    (∀ᶠ p : ℝ in atTop,
      GeneralPowerFirstZeroCell rho 1 p 2 ∧
      IsUniqueMinimizerOn (SolidSimplex : (Fin 2 → ℝ) → Prop)
        (powerReducedObjective rho 1 p (powerPathWeight 2))
        (powerPathDecrease rho 1 p (hardExponentActualOffset rho p) 2) ∧
      0 < powerProfileFromDecreases
        (powerPathDecrease rho 1 p (hardExponentActualOffset rho p) 2) 1 ∧
      (∀ R : ℕ,
        IsUniqueMinimizerOn
          (SolidSimplex : (Fin (2 + R) → ℝ) → Prop)
          (powerReducedObjective rho 1 p (powerPathWeight (2 + R)))
          (powerPathDecrease rho 1 p
            (hardExponentActualOffset rho p + 1 * R) (2 + R)))) ∧
    Tendsto
      (fun p : ℝ =>
        powerProfileFromDecreases
            (powerPathDecrease rho 1 p (hardExponentActualOffset rho p) 2) 1 /
          hardExponentScale rho p)
      atTop (nhds 1) ∧
    Tendsto
      (fun p : ℝ => powerProfileFromDecreases
        (powerPathDecrease rho 1 p (hardExponentActualOffset rho p) 2) 1)
      atTop (nhds 0) := by
  have hadmitted := hardExponentActualOffset_eventually_admitted hrho
  have hunique := hardExponentActualOffset_eventually_unique hrho
  have hasymptotic := chg_b16_actualFollower_complete_asymptotic
    hrho (hardExponentActualOffset rho) hadmitted
  refine ⟨?_, hasymptotic.2.1, hasymptotic.2.2⟩
  filter_upwards [hunique] with p hp
  exact ⟨hp.1, hp.2.1, (hp.2.2.1 1).2 (by norm_num), hp.2.2.2⟩

end PhonologicalCalculus.ContinuousHG
