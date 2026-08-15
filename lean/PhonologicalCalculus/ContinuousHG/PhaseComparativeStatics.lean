import PhonologicalCalculus.ContinuousHG.PhaseProfileOptimizerBridge
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# General-power phase comparative statics

This module proves the finite monotone-likelihood-ratio argument underlying
coordinatewise comparative statics inside every fixed active-support phase.
The proof is entirely finite: a pairwise cross-product inequality between
the early and late shifted-power terms is summed over the corresponding
rectangles and then normalized.
-/

namespace PhonologicalCalculus.ContinuousHG

open scoped BigOperators
open Filter Finset Set

/-- A positive shifted exponent and an offset below one make every nonempty
shifted-power sum strictly positive. -/
theorem shiftedPowerSum_pos
    {q tau : ℝ} {K : ℕ} (_hq : 0 < q) (htau : tau < 1) (hK : 0 < K) :
    0 < shiftedPowerSum q tau K := by
  unfold shiftedPowerSum
  apply Finset.sum_pos'
  · intro r _
    exact Real.rpow_nonneg (by
      have hone : (1 : ℝ) ≤ ((r + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le r)
      linarith) q
  · refine ⟨0, Finset.mem_range.mpr hK, ?_⟩
    exact Real.rpow_pos_of_pos (by norm_num; linarith) q

/-- Summing a pointwise cross-product inequality over a finite rectangle
preserves it. -/
theorem sum_mul_sum_cross_le
    {alpha beta : Type*} (S : Finset alpha) (T : Finset beta)
    (aOne aTwo : alpha → ℝ) (bOne bTwo : beta → ℝ)
    (hcross : ∀ i ∈ S, ∀ j ∈ T,
      aOne i * bTwo j ≤ aTwo i * bOne j) :
    (∑ i ∈ S, aOne i) * (∑ j ∈ T, bTwo j) ≤
      (∑ i ∈ S, aTwo i) * (∑ j ∈ T, bOne j) := by
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum]
  exact Finset.sum_le_sum fun i hi =>
    Finset.sum_le_sum fun j hj => hcross i hi j hj

/-- Earlier shifted-power terms gain weakly more, in relative terms, when
the offset is lowered.  This is the pairwise likelihood-ratio inequality. -/
theorem shiftedPowerTerm_cross_le
    {q tauLow tauHigh : ℝ} {r s : ℕ}
    (hq : 0 ≤ q) (htau : tauLow ≤ tauHigh) (htauHigh : tauHigh < 1)
    (hrs : r < s) :
    ((((r + 1 : ℕ) : ℝ) - tauHigh) ^ q) *
        ((((s + 1 : ℕ) : ℝ) - tauLow) ^ q) ≤
      ((((r + 1 : ℕ) : ℝ) - tauLow) ^ q) *
        ((((s + 1 : ℕ) : ℝ) - tauHigh) ^ q) := by
  have hrOne : (1 : ℝ) ≤ ((r + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le r)
  have hsOne : (1 : ℝ) ≤ ((s + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le s)
  have hrsReal : ((r + 1 : ℕ) : ℝ) ≤ ((s + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.le_of_lt hrs)
  have hrHigh : 0 ≤ ((r + 1 : ℕ) : ℝ) - tauHigh := by linarith
  have hrLow : 0 ≤ ((r + 1 : ℕ) : ℝ) - tauLow := by linarith
  have hsHigh : 0 ≤ ((s + 1 : ℕ) : ℝ) - tauHigh := by linarith
  have hsLow : 0 ≤ ((s + 1 : ℕ) : ℝ) - tauLow := by linarith
  have baseCross :
      (((r + 1 : ℕ) : ℝ) - tauHigh) *
          (((s + 1 : ℕ) : ℝ) - tauLow) ≤
        (((r + 1 : ℕ) : ℝ) - tauLow) *
          (((s + 1 : ℕ) : ℝ) - tauHigh) := by
    nlinarith
  rw [← Real.mul_rpow hrHigh hsLow, ← Real.mul_rpow hrLow hsHigh]
  exact Real.rpow_le_rpow (mul_nonneg hrHigh hsLow) baseCross hq

/-- The shifted-power sum decomposes into its initial segment and its
complementary terminal segment. -/
theorem shiftedPowerSum_eq_prefix_add_tail
    (q tau : ℝ) {n K : ℕ} (hnK : n ≤ K) :
    shiftedPowerSum q tau K =
      shiftedPowerSum q tau n +
        ∑ r ∈ Finset.Ico n K, ((((r + 1 : ℕ) : ℝ) - tau) ^ q) := by
  unfold shiftedPowerSum
  exact (Finset.sum_range_add_sum_Ico
    (fun r : ℕ => ((((r + 1 : ℕ) : ℝ) - tau) ^ q)) hnK).symm

/-- For a fixed support size, lowering the phase offset weakly increases
every aligned activity coordinate. -/
theorem normalizedPhaseProfile_antitone_offset
    {q tauLow tauHigh : ℝ} {K i : ℕ}
    (hq : 0 < q) (htau : tauLow ≤ tauHigh) (htauHigh : tauHigh < 1) :
    normalizedPhaseProfile q tauHigh K i ≤
      normalizedPhaseProfile q tauLow K i := by
  by_cases hKi : K ≤ i
  · rw [normalizedPhaseProfile_beyond_support q tauHigh hKi,
      normalizedPhaseProfile_beyond_support q tauLow hKi]
  · have hiK : i < K := Nat.lt_of_not_ge hKi
    have hK : 0 < K := lt_of_le_of_lt (Nat.zero_le i) hiK
    have hnK : K - i ≤ K := Nat.sub_le K i
    let n := K - i
    let earlyHigh := shiftedPowerSum q tauHigh n
    let earlyLow := shiftedPowerSum q tauLow n
    let lateHigh :=
      ∑ r ∈ Finset.Ico n K, ((((r + 1 : ℕ) : ℝ) - tauHigh) ^ q)
    let lateLow :=
      ∑ r ∈ Finset.Ico n K, ((((r + 1 : ℕ) : ℝ) - tauLow) ^ q)
    have cross : earlyHigh * lateLow ≤ earlyLow * lateHigh := by
      dsimp [earlyHigh, earlyLow, lateHigh, lateLow, shiftedPowerSum]
      apply sum_mul_sum_cross_le
      intro r hr s hs
      have hrn : r < n := Finset.mem_range.mp hr
      have hns : n ≤ s := (Finset.mem_Ico.mp hs).1
      exact shiftedPowerTerm_cross_le hq.le htau htauHigh
        (lt_of_lt_of_le hrn hns)
    have highDenominatorPositive : 0 < shiftedPowerSum q tauHigh K :=
      shiftedPowerSum_pos hq htauHigh hK
    have lowDenominatorPositive : 0 < shiftedPowerSum q tauLow K :=
      shiftedPowerSum_pos hq (lt_of_le_of_lt htau htauHigh) hK
    have highDecomposition :
        shiftedPowerSum q tauHigh K = earlyHigh + lateHigh := by
      simpa [earlyHigh, lateHigh, n] using
        shiftedPowerSum_eq_prefix_add_tail q tauHigh hnK
    have lowDecomposition :
        shiftedPowerSum q tauLow K = earlyLow + lateLow := by
      simpa [earlyLow, lateLow, n] using
        shiftedPowerSum_eq_prefix_add_tail q tauLow hnK
    unfold normalizedPhaseProfile
    change earlyHigh / shiftedPowerSum q tauHigh K ≤
      earlyLow / shiftedPowerSum q tauLow K
    rw [div_le_div_iff₀ highDenominatorPositive lowDenominatorPositive]
    rw [highDecomposition, lowDecomposition]
    nlinarith

/-- Inside one admitted support phase, increasing the harmony-to-markedness
ratio weakly raises every aligned activity coordinate. -/
theorem normalizedPhaseProfile_mono_ratio_of_phase
    {p rhoOne rhoTwo tauOne tauTwo : ℝ} {K i : ℕ}
    (hp : 1 < p) (hrhoOne : 0 < rhoOne) (hrho : rhoOne ≤ rhoTwo)
    (htauOne : tauOne ∈ Ico (0 : ℝ) 1)
    (htauTwo : tauTwo ∈ Ico (0 : ℝ) 1)
    (hphaseOne : shiftedPowerSum (powerShiftExponent p) tauOne K =
      (p * rhoOne) ^ powerShiftExponent p)
    (hphaseTwo : shiftedPowerSum (powerShiftExponent p) tauTwo K =
      (p * rhoTwo) ^ powerShiftExponent p) :
    normalizedPhaseProfile (powerShiftExponent p) tauOne K i ≤
      normalizedPhaseProfile (powerShiftExponent p) tauTwo K i := by
  have hrhoTwo : 0 < rhoTwo := lt_of_lt_of_le hrhoOne hrho
  have hpPositive : 0 < p := lt_trans zero_lt_one hp
  have targetOrder :
      (p * rhoOne) ^ powerShiftExponent p ≤
        (p * rhoTwo) ^ powerShiftExponent p := by
    exact Real.rpow_le_rpow (mul_nonneg hpPositive.le hrhoOne.le)
      (mul_le_mul_of_nonneg_left hrho hpPositive.le)
      (powerShiftExponent_positive hp).le
  have tauOrder : tauTwo ≤ tauOne := by
    by_contra hnot
    have htauStrict : tauOne < tauTwo := lt_of_not_ge hnot
    have hK : 0 < K := by
      by_contra hzero
      have : K = 0 := Nat.eq_zero_of_not_pos hzero
      subst K
      have targetPositive :
          0 < (p * rhoOne) ^ powerShiftExponent p :=
        Real.rpow_pos_of_pos (mul_pos hpPositive hrhoOne) _
      simp [shiftedPowerSum] at hphaseOne
      linarith
    have sumStrict :=
      shiftedPowerSum_strictAntiOn_Ico
        (powerShiftExponent_positive hp) hK htauOne htauTwo htauStrict
    change shiftedPowerSum (powerShiftExponent p) tauTwo K <
      shiftedPowerSum (powerShiftExponent p) tauOne K at sumStrict
    rw [hphaseOne, hphaseTwo] at sumStrict
    exact (not_lt_of_ge targetOrder) sumStrict
  exact normalizedPhaseProfile_antitone_offset
    (powerShiftExponent_positive hp) tauOrder htauOne.2

/-- Universal fixed-phase comparative-statics package. -/
theorem chg_b10_fixed_phase_ratio_monotonicity
    {p rhoOne rhoTwo tauOne tauTwo : ℝ} {K : ℕ}
    (hp : 1 < p) (hrhoOne : 0 < rhoOne) (hrho : rhoOne ≤ rhoTwo)
    (htauOne : tauOne ∈ Ico (0 : ℝ) 1)
    (htauTwo : tauTwo ∈ Ico (0 : ℝ) 1)
    (hphaseOne : shiftedPowerSum (powerShiftExponent p) tauOne K =
      (p * rhoOne) ^ powerShiftExponent p)
    (hphaseTwo : shiftedPowerSum (powerShiftExponent p) tauTwo K =
      (p * rhoTwo) ^ powerShiftExponent p) :
    ∀ i : ℕ,
      normalizedPhaseProfile (powerShiftExponent p) tauOne K i ≤
        normalizedPhaseProfile (powerShiftExponent p) tauTwo K i := by
  intro i
  exact normalizedPhaseProfile_mono_ratio_of_phase hp hrhoOne hrho
    htauOne htauTwo hphaseOne hphaseTwo

/-- At the upper edge of a phase, the shifted-power sum is exactly the
zero-offset sum for the preceding support size. -/
theorem shiftedPowerSum_one_succ_eq_zero
    {q : ℝ} (hq : 0 < q) (K : ℕ) :
    shiftedPowerSum q 1 (K + 1) = shiftedPowerSum q 0 K := by
  induction K with
  | zero =>
      simp [shiftedPowerSum, Real.zero_rpow hq.ne']
  | succ K ih =>
      rw [show K + 1 + 1 = (K + 1) + 1 by omega,
        shiftedPowerSum_succ, ih, shiftedPowerSum_succ]
      congr 1
      norm_num

/-- Adjacent normalized phase profiles paste exactly: the entering
`K+1`-support formula at offset one is the `K`-support formula at offset
zero, coordinate by coordinate. -/
theorem normalizedPhaseProfile_phase_boundary
    {q : ℝ} (hq : 0 < q) (K i : ℕ) :
    normalizedPhaseProfile q 1 (K + 1) i =
      normalizedPhaseProfile q 0 K i := by
  unfold normalizedPhaseProfile
  rw [shiftedPowerSum_one_succ_eq_zero hq K]
  by_cases hiK : i ≤ K
  · have indexIdentity : K + 1 - i = (K - i) + 1 := by omega
    rw [indexIdentity, shiftedPowerSum_one_succ_eq_zero hq (K - i)]
  · have hKlt : K < i := Nat.lt_of_not_ge hiK
    have hleft : K + 1 - i = 0 := by omega
    have hright : K - i = 0 := by omega
    rw [hleft, hright]
    simp [shiftedPowerSum]

/-- The shifted-power sum depends continuously on its offset. -/
theorem continuous_shiftedPowerSum_offset
    {q : ℝ} (hq : 0 ≤ q) (K : ℕ) :
    Continuous (fun tau : ℝ => shiftedPowerSum q tau K) := by
  unfold shiftedPowerSum
  apply continuous_finsetSum
  intro r _
  exact (Real.continuous_rpow_const hq).comp
    (continuous_const.sub continuous_id)

/-- Every normalized coordinate is continuous wherever its phase
denominator is nonzero. -/
theorem continuousAt_normalizedPhaseProfile_offset
    {q tau : ℝ} {K i : ℕ} (hq : 0 ≤ q)
    (hden : shiftedPowerSum q tau K ≠ 0) :
    ContinuousAt (fun offset : ℝ =>
      normalizedPhaseProfile q offset K i) tau := by
  unfold normalizedPhaseProfile
  exact (continuous_shiftedPowerSum_offset hq (K - i)).continuousAt.div
    (continuous_shiftedPowerSum_offset hq K).continuousAt hden

/-- The profile entering a phase converges coordinatewise to the exact
preceding-phase profile at the support boundary. -/
theorem normalizedPhaseProfile_phase_paste_tendsto
    {q : ℝ} (hq : 0 < q) {K : ℕ} (hK : 0 < K) (i : ℕ) :
    Tendsto (fun tau : ℝ => normalizedPhaseProfile q tau (K + 1) i)
      (nhdsWithin 1 (Iio 1))
      (nhds (normalizedPhaseProfile q 0 K i)) := by
  have denominatorNonzero : shiftedPowerSum q 1 (K + 1) ≠ 0 := by
    rw [shiftedPowerSum_one_succ_eq_zero hq K]
    exact ne_of_gt (shiftedPowerSum_pos hq (by norm_num) hK)
  have hcontinuous :=
    continuousAt_normalizedPhaseProfile_offset (i := i) hq.le denominatorNonzero
  rw [← normalizedPhaseProfile_phase_boundary hq K i]
  exact hcontinuous.tendsto.mono_left inf_le_left

/-- General fixed-phase monotonicity and adjacent-phase continuity, the two
analytic components of the CHG-B10 comparative-statics package. -/
theorem chg_b10_general_phase_comparative_statics :
    (∀ (p rhoOne rhoTwo tauOne tauTwo : ℝ) (K : ℕ),
      1 < p → 0 < rhoOne → rhoOne ≤ rhoTwo →
      tauOne ∈ Ico (0 : ℝ) 1 → tauTwo ∈ Ico (0 : ℝ) 1 →
      shiftedPowerSum (powerShiftExponent p) tauOne K =
        (p * rhoOne) ^ powerShiftExponent p →
      shiftedPowerSum (powerShiftExponent p) tauTwo K =
        (p * rhoTwo) ^ powerShiftExponent p →
      ∀ i : ℕ,
        normalizedPhaseProfile (powerShiftExponent p) tauOne K i ≤
          normalizedPhaseProfile (powerShiftExponent p) tauTwo K i) ∧
    (∀ (q : ℝ) (K : ℕ), 0 < q → 0 < K → ∀ i : ℕ,
      Tendsto (fun tau : ℝ => normalizedPhaseProfile q tau (K + 1) i)
        (nhdsWithin 1 (Iio 1))
        (nhds (normalizedPhaseProfile q 0 K i))) := by
  constructor
  · intro p rhoOne rhoTwo tauOne tauTwo K hp hrhoOne hrho
      htauOne htauTwo hphaseOne hphaseTwo i
    exact normalizedPhaseProfile_mono_ratio_of_phase hp hrhoOne hrho
      htauOne htauTwo hphaseOne hphaseTwo
  · intro q K hq hK i
    exact normalizedPhaseProfile_phase_paste_tendsto hq hK i

section ValueConcavity

variable {iota : Type*} [Fintype iota]

/-- At fixed exponent, markedness scale, and candidate, the reduced
objective is affine in the harmony ratio. -/
theorem powerReducedObjective_affine_ratio
    (rhoOne rhoTwo theta p : ℝ) (weight d : iota → ℝ) :
    powerReducedObjective
        (theta * rhoOne + (1 - theta) * rhoTwo) 1 p weight d =
      theta * powerReducedObjective rhoOne 1 p weight d +
        (1 - theta) * powerReducedObjective rhoTwo 1 p weight d := by
  classical
  unfold powerReducedObjective
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Minimum values of the fixed-candidate real-power family are concave in
the harmony ratio.  The statement is optimizer-independent: any three
proved minimizers at the two endpoints and their convexly interpolated
ratio satisfy the same inequality. -/
theorem powerMinimumValue_concave_in_ratio
    {rhoOne rhoTwo theta p : ℝ} {weight : iota → ℝ}
    {winnerOne winnerTwo winnerMiddle : iota → ℝ}
    (hthetaZero : 0 ≤ theta) (hthetaOne : theta ≤ 1)
    (hOne : IsUniqueMinimizerOn
      (SolidSimplex : (iota → ℝ) → Prop)
      (powerReducedObjective rhoOne 1 p weight) winnerOne)
    (hTwo : IsUniqueMinimizerOn
      (SolidSimplex : (iota → ℝ) → Prop)
      (powerReducedObjective rhoTwo 1 p weight) winnerTwo)
    (hMiddle : IsUniqueMinimizerOn
      (SolidSimplex : (iota → ℝ) → Prop)
      (powerReducedObjective
        (theta * rhoOne + (1 - theta) * rhoTwo) 1 p weight)
      winnerMiddle) :
    theta * powerReducedObjective rhoOne 1 p weight winnerOne +
        (1 - theta) * powerReducedObjective rhoTwo 1 p weight winnerTwo ≤
      powerReducedObjective
        (theta * rhoOne + (1 - theta) * rhoTwo) 1 p weight winnerMiddle := by
  have endpointOneBound :
      powerReducedObjective rhoOne 1 p weight winnerOne ≤
        powerReducedObjective rhoOne 1 p weight winnerMiddle :=
    (hOne.2 winnerMiddle hMiddle.1).1
  have endpointTwoBound :
      powerReducedObjective rhoTwo 1 p weight winnerTwo ≤
        powerReducedObjective rhoTwo 1 p weight winnerMiddle :=
    (hTwo.2 winnerMiddle hMiddle.1).1
  calc
    theta * powerReducedObjective rhoOne 1 p weight winnerOne +
        (1 - theta) * powerReducedObjective rhoTwo 1 p weight winnerTwo ≤
      theta * powerReducedObjective rhoOne 1 p weight winnerMiddle +
        (1 - theta) * powerReducedObjective rhoTwo 1 p weight winnerMiddle :=
      add_le_add
        (mul_le_mul_of_nonneg_left endpointOneBound hthetaZero)
        (mul_le_mul_of_nonneg_left endpointTwoBound (sub_nonneg.mpr hthetaOne))
    _ = powerReducedObjective
        (theta * rhoOne + (1 - theta) * rhoTwo) 1 p weight winnerMiddle := by
      rw [powerReducedObjective_affine_ratio]

end ValueConcavity

end PhonologicalCalculus.ContinuousHG
