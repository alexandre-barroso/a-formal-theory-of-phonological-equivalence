import PhonologicalCalculus.ContinuousHG.Quadratic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-!
# Normalized phase profiles

This module develops the shifted-power normal form used inside one saturated
phase of the directional continuous-HG family.  It separates three exact
facts: normalization of the active decrease mass, reconstruction of the
profile by tail sums, and the arithmetic progression followed by powered
decreases once the phase equation is imposed.
-/

namespace PhonologicalCalculus.ContinuousHG

open scoped BigOperators

/-- Shifted power sum `B_K(tau)`. -/
noncomputable def shiftedPowerSum (q tau : ℝ) (K : ℕ) : ℝ :=
  ∑ r ∈ Finset.range K, (((r + 1 : ℕ) : ℝ) - tau) ^ q

/-- The decrease attached to shifted index `r + 1`, normalized to unit mass. -/
noncomputable def normalizedPhaseDecrease
    (q tau : ℝ) (K r : ℕ) : ℝ :=
  ((((r + 1 : ℕ) : ℝ) - tau) ^ q) / shiftedPowerSum q tau K

/-- The activity at position `i`, reconstructed as the remaining normalized
decrease mass.  Natural subtraction gives an exact zero from `K` onward. -/
noncomputable def normalizedPhaseProfile
    (q tau : ℝ) (K i : ℕ) : ℝ :=
  shiftedPowerSum q tau (K - i) / shiftedPowerSum q tau K

theorem shiftedPowerSum_zero (q tau : ℝ) :
    shiftedPowerSum q tau 0 = 0 := by
  simp [shiftedPowerSum]

theorem shiftedPowerSum_succ (q tau : ℝ) (K : ℕ) :
    shiftedPowerSum q tau (K + 1) =
      shiftedPowerSum q tau K + (((K + 1 : ℕ) : ℝ) - tau) ^ q := by
  simp [shiftedPowerSum, Finset.sum_range_succ]

/-- Normalization is exact whenever the shifted-power denominator is nonzero. -/
theorem normalizedPhaseDecrease_sum
    {q tau : ℝ} {K : ℕ} (hden : shiftedPowerSum q tau K ≠ 0) :
    (∑ r ∈ Finset.range K, normalizedPhaseDecrease q tau K r) = 1 := by
  simp only [normalizedPhaseDecrease]
  rw [← Finset.sum_div]
  exact div_self hden

theorem normalizedPhaseProfile_zero
    {q tau : ℝ} {K : ℕ} (hden : shiftedPowerSum q tau K ≠ 0) :
    normalizedPhaseProfile q tau K 0 = 1 := by
  simp [normalizedPhaseProfile, hden]

theorem normalizedPhaseProfile_at_support (q tau : ℝ) (K : ℕ) :
    normalizedPhaseProfile q tau K K = 0 := by
  simp [normalizedPhaseProfile, shiftedPowerSum]

theorem normalizedPhaseProfile_beyond_support
    (q tau : ℝ) {K i : ℕ} (hKi : K ≤ i) :
    normalizedPhaseProfile q tau K i = 0 := by
  simp [normalizedPhaseProfile, Nat.sub_eq_zero_of_le hKi, shiftedPowerSum]

/-- Consecutive profile loss is exactly one normalized shifted-power term. -/
theorem normalizedPhaseProfile_sub_succ
    {q tau : ℝ} {K i : ℕ} (hi : i < K) :
    normalizedPhaseProfile q tau K i -
        normalizedPhaseProfile q tau K (i + 1) =
      ((((K - i : ℕ) : ℝ) - tau) ^ q) /
        shiftedPowerSum q tau K := by
  have hindex : K - i = (K - (i + 1)) + 1 := by omega
  unfold normalizedPhaseProfile
  rw [hindex, shiftedPowerSum_succ]
  ring

/-- Consecutive loss in the normalized profile. -/
noncomputable def normalizedProfileLoss
    (q tau : ℝ) (K i : ℕ) : ℝ :=
  normalizedPhaseProfile q tau K i -
    normalizedPhaseProfile q tau K (i + 1)

private theorem normalizedProfileLoss_power
    {p rho tau : ℝ} {K i : ℕ}
    (hp : 1 < p) (hrho : 0 < rho) (htau : tau < 1) (hi : i < K)
    (hphase : shiftedPowerSum (1 / (p - 1)) tau K =
      (p * rho) ^ (1 / (p - 1))) :
    (normalizedProfileLoss (1 / (p - 1)) tau K i) ^ (p - 1) =
      (((K - i : ℕ) : ℝ) - tau) / (p * rho) := by
  let q : ℝ := 1 / (p - 1)
  let a : ℝ := ((K - i : ℕ) : ℝ) - tau
  let base : ℝ := p * rho
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hbase : 0 < base := mul_pos hp0 hrho
  have hq : 0 < q := by
    dsimp [q]
    positivity
  have hKi : 1 ≤ K - i := by omega
  have ha : 0 < a := by
    dsimp [a]
    have hcast : (1 : ℝ) ≤ ((K - i : ℕ) : ℝ) := by exact_mod_cast hKi
    linarith
  have hqmul : q * (p - 1) = 1 := by
    dsimp [q]
    field_simp [ne_of_gt (sub_pos.mpr hp)]
  have hden : 0 < shiftedPowerSum q tau K := by
    rw [show q = 1 / (p - 1) by rfl, hphase]
    exact Real.rpow_pos_of_pos hbase q
  have hloss : normalizedProfileLoss q tau K i = a ^ q /
      shiftedPowerSum q tau K := by
    unfold normalizedProfileLoss
    simpa [q, a] using
      (normalizedPhaseProfile_sub_succ
        (q := q) (tau := tau) (K := K) (i := i) hi)
  rw [hloss, Real.div_rpow (Real.rpow_nonneg ha.le q) hden.le]
  have hnum : (a ^ q) ^ (p - 1) = a := by
    rw [← Real.rpow_mul ha.le, hqmul, Real.rpow_one]
  have hdenPower : (shiftedPowerSum q tau K) ^ (p - 1) = base := by
    rw [show q = 1 / (p - 1) by rfl, hphase]
    rw [← Real.rpow_mul hbase.le]
    rw [show (1 / (p - 1)) * (p - 1) = 1 by
      field_simp [ne_of_gt (sub_pos.mpr hp)]]
    rw [Real.rpow_one]
  rw [hnum, hdenPower]

/-- Inside a registered saturated phase, powered consecutive profile losses
form the exact arithmetic progression `1 / (p * rho)`. -/
theorem normalizedProfileLoss_powered_gap
    {p rho tau : ℝ} {K i j : ℕ}
    (hp : 1 < p) (hrho : 0 < rho) (_htau0 : 0 ≤ tau) (htau1 : tau < 1)
    (hij : i < j) (hjK : j < K)
    (hphase : shiftedPowerSum (1 / (p - 1)) tau K =
      (p * rho) ^ (1 / (p - 1))) :
    (normalizedProfileLoss (1 / (p - 1)) tau K i) ^ (p - 1) -
        (normalizedProfileLoss (1 / (p - 1)) tau K j) ^ (p - 1) =
      ((j - i : ℕ) : ℝ) / (p * rho) := by
  have hiK : i < K := lt_trans hij hjK
  rw [normalizedProfileLoss_power hp hrho htau1 hiK hphase,
    normalizedProfileLoss_power hp hrho htau1 hjK hphase]
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hden : p * rho ≠ 0 := ne_of_gt (mul_pos hp0 hrho)
  have hnat : ((K - i : ℕ) : ℝ) - ((K - j : ℕ) : ℝ) =
      ((j - i : ℕ) : ℝ) := by
    rw [Nat.cast_sub (Nat.le_of_lt hiK),
      Nat.cast_sub (Nat.le_of_lt hjK),
      Nat.cast_sub (Nat.le_of_lt hij)]
    ring
  field_simp [hden]
  linarith

/-- Quadratic registered normalization fixture for `CHG-B9.NORMALIZE.01`. -/
theorem chg_b9_normalize_01 :
    (∑ r ∈ Finset.range 4,
      normalizedPhaseDecrease 1 (1 / 3) 4 r) = 1 := by
  norm_num [normalizedPhaseDecrease, shiftedPowerSum, Finset.sum_range_succ]

/-- Quadratic powered-gap fixture for `CHG-B9.GAPS.02`. -/
theorem chg_b9_gaps_02 :
    List.zipWith (fun a b : ℝ => b - a)
      [2 / 5, 3 / 10, 1 / 5, 1 / 10]
      [3 / 10, 1 / 5, 1 / 10] =
        [-1 / 10, -1 / 10, -1 / 10] := by
  norm_num

/-- Quadratic normalized profile fixture for `CHG-B9.PROFILE.03`. -/
theorem chg_b9_profile_03 :
    [normalizedPhaseProfile 1 0 4 0,
      normalizedPhaseProfile 1 0 4 1,
      normalizedPhaseProfile 1 0 4 2,
      normalizedPhaseProfile 1 0 4 3,
      normalizedPhaseProfile 1 0 4 4] =
        [1, 3 / 5, 3 / 10, 1 / 10, 0] := by
  norm_num [normalizedPhaseProfile, shiftedPowerSum, Finset.sum_range_succ]

/-- The three registered finite components of `CHG-B9`. -/
theorem chg_b9_registered_components :
    ((∑ r ∈ Finset.range 4,
      normalizedPhaseDecrease 1 (1 / 3) 4 r) = 1) ∧
    List.zipWith (fun a b : ℝ => b - a)
      [2 / 5, 3 / 10, 1 / 5, 1 / 10]
      [3 / 10, 1 / 5, 1 / 10] =
        [-1 / 10, -1 / 10, -1 / 10] ∧
    [normalizedPhaseProfile 1 0 4 0,
      normalizedPhaseProfile 1 0 4 1,
      normalizedPhaseProfile 1 0 4 2,
      normalizedPhaseProfile 1 0 4 3,
      normalizedPhaseProfile 1 0 4 4] =
        [1, 3 / 5, 3 / 10, 1 / 10, 0] := by
  exact ⟨chg_b9_normalize_01, chg_b9_gaps_02, chg_b9_profile_03⟩

end PhonologicalCalculus.ContinuousHG
