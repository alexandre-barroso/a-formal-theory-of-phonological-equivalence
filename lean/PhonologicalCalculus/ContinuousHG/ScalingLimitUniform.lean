import PhonologicalCalculus.ContinuousHG.GeneralPersistenceAsymptotic
import PhonologicalCalculus.ContinuousHG.ScalingLimitMoments
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Uniform long-support scaling

This module proves the uniform finite-profile and finite-decrement limits of
the normalized phase profile.  The phase offset is allowed to vary throughout
the full bounded interval `0 ≤ tau < 1`; only the power exponent is fixed.
-/

namespace PhonologicalCalculus.ContinuousHG

open Filter Set
open scoped BigOperators Topology

/-- The exponent in the shifted power sum is one less than the exponent of
the limiting profile. -/
theorem powerShiftExponent_add_one_eq_scalingExponent
    {p : ℝ} (hp : 1 < p) :
    powerShiftExponent p + 1 = scalingExponent p := by
  unfold powerShiftExponent scalingExponent
  field_simp [ne_of_gt (sub_pos.mpr hp)]
  ring

/-- A shifted power sum is bounded above by the unshifted power sum with the
same number of terms, uniformly over `0 ≤ tau < 1`. -/
theorem shiftedPowerSum_le_generalPowerSum
    {p tau : ℝ} (hp : 1 < p) (htauZero : 0 ≤ tau)
    (htauOne : tau < 1) (K : ℕ) :
    shiftedPowerSum (powerShiftExponent p) tau K ≤
      generalPowerSum p K := by
  have hq : 0 ≤ powerShiftExponent p :=
    (powerShiftExponent_positive hp).le
  induction K with
  | zero => simp [shiftedPowerSum, generalPowerSum]
  | succ K ih =>
      rw [show K + 1 = K + 1 by rfl, shiftedPowerSum_succ]
      simp only [generalPowerSum, Finset.sum_range_succ]
      apply add_le_add ih
      apply Real.rpow_le_rpow
      · have hcast : (1 : ℝ) ≤ ((K + 1 : ℕ) : ℝ) := by
          exact_mod_cast Nat.succ_le_succ (Nat.zero_le K)
        linarith
      · linarith
      · exact hq

/-- Omitting the first shifted term gives the matching lower unshifted power
sum.  This successor form avoids any convention at `K = 0`. -/
theorem generalPowerSum_le_shiftedPowerSum_succ
    {p tau : ℝ} (hp : 1 < p) (_htauZero : 0 ≤ tau)
    (htauOne : tau < 1) (K : ℕ) :
    generalPowerSum p K ≤
      shiftedPowerSum (powerShiftExponent p) tau (K + 1) := by
  have hq : 0 ≤ powerShiftExponent p :=
    (powerShiftExponent_positive hp).le
  induction K with
  | zero =>
      simp [generalPowerSum, shiftedPowerSum]
      exact Real.rpow_nonneg (by linarith) _
  | succ K ih =>
      simp only [generalPowerSum, Finset.sum_range_succ]
      rw [show K + 1 + 1 = (K + 1) + 1 by omega,
        shiftedPowerSum_succ]
      apply add_le_add ih
      apply Real.rpow_le_rpow
      · exact Nat.cast_nonneg _
      · have hcast : (((K + 1 : ℕ) : ℝ)) ≤
            (((K + 1 + 1 : ℕ) : ℝ) - tau) := by
          norm_num [Nat.cast_add, Nat.cast_one]
          linarith
        exact hcast
      · exact hq

/-- Integral-comparison sandwich for the shifted power sum.  The estimate is
uniform over the complete bounded phase-offset interval. -/
theorem shiftedPowerSum_integral_sandwich
    {p tau : ℝ} (hp : 1 < p) (htauZero : 0 ≤ tau)
    (htauOne : tau < 1) {K : ℕ} (hK : 0 < K) :
    (((K - 1 : ℕ) : ℝ) ^ scalingExponent p) /
          scalingExponent p ≤
        shiftedPowerSum (powerShiftExponent p) tau K ∧
      shiftedPowerSum (powerShiftExponent p) tau K ≤
        ((((K + 1 : ℕ) : ℝ) ^ scalingExponent p) /
          scalingExponent p) := by
  have hexponent := powerShiftExponent_add_one_eq_scalingExponent hp
  constructor
  · have hsum := generalPowerSum_le_shiftedPowerSum_succ
      hp htauZero htauOne (K - 1)
    rw [Nat.sub_add_cancel hK] at hsum
    have hlower := (generalPowerSum_bounds hp (K - 1)).1
    rw [hexponent] at hlower
    exact hlower.trans hsum
  · have hupper := (generalPowerSum_bounds hp K).2
    rw [hexponent] at hupper
    exact (shiftedPowerSum_le_generalPowerSum hp htauZero htauOne K).trans
      hupper

/-- Normalized shifted power sums converge to their power-integral profile,
uniformly over every prefix `n ≤ K` and every phase offset `0 ≤ tau < 1`.
The eventual quantifier over `K` is the exact epsilon formulation of the
uniform Riemann estimate used by the long-support theorem. -/
theorem shiftedPowerSum_uniform_integral_scaling
    {p : ℝ} (hp : 1 < p) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ K : ℕ in atTop,
        ∀ tau : ℝ, 0 ≤ tau → tau < 1 →
          ∀ n : ℕ, n ≤ K →
            |shiftedPowerSum (powerShiftExponent p) tau n /
                  ((K : ℝ) ^ scalingExponent p) -
                (((n : ℝ) / (K : ℝ)) ^ scalingExponent p) /
                  scalingExponent p| < epsilon := by
  intro epsilon hepsilon
  have hsigma : 0 < scalingExponent p :=
    lt_trans zero_lt_one (one_lt_scalingExponent hp)
  have hcontinuous : ContinuousOn
      (fun z : ℝ => z ^ scalingExponent p) (Icc 0 2) :=
    (Real.continuous_rpow_const hsigma.le).continuousOn
  have huniform := isCompact_Icc.uniformContinuousOn_of_continuous
    hcontinuous
  rw [Metric.uniformContinuousOn_iff] at huniform
  obtain ⟨delta, hdelta, hpower⟩ :=
    huniform (epsilon * scalingExponent p)
      (mul_pos hepsilon hsigma)
  have hcastTop : Tendsto (fun K : ℕ => (K : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hinverse : Tendsto (fun K : ℕ => ((K : ℝ))⁻¹)
      atTop (nhds 0) := tendsto_inv_atTop_zero.comp hcastTop
  have hsmall : ∀ᶠ K : ℕ in atTop, ((K : ℝ))⁻¹ < delta := by
    have hball := hinverse.eventually (Metric.ball_mem_nhds 0 hdelta)
    filter_upwards [hball] with K hK
    rw [Real.dist_eq] at hK
    have hInverseNonnegative : 0 ≤ ((K : ℝ))⁻¹ :=
      inv_nonneg.mpr (Nat.cast_nonneg K)
    simpa [abs_of_nonneg hInverseNonnegative] using hK
  filter_upwards [hsmall, eventually_gt_atTop (0 : ℕ)] with K hKsmall hKpositive
  intro tau htauZero htauOne n hnK
  by_cases hnZero : n = 0
  · subst n
    simp [shiftedPowerSum, Real.zero_rpow (ne_of_gt hsigma), hepsilon]
  have hnPositive : 0 < n := Nat.pos_of_ne_zero hnZero
  have hKreal : 0 < (K : ℝ) := by exact_mod_cast hKpositive
  have hKpower : 0 < (K : ℝ) ^ scalingExponent p :=
    Real.rpow_pos_of_pos hKreal _
  have hminusNonnegative : 0 ≤ ((n - 1 : ℕ) : ℝ) / (K : ℝ) :=
    div_nonneg (Nat.cast_nonneg _) hKreal.le
  have hcenterNonnegative : 0 ≤ (n : ℝ) / (K : ℝ) :=
    div_nonneg (Nat.cast_nonneg _) hKreal.le
  have hplusNonnegative : 0 ≤ ((n + 1 : ℕ) : ℝ) / (K : ℝ) :=
    div_nonneg (Nat.cast_nonneg _) hKreal.le
  have hcenterLeOne : (n : ℝ) / (K : ℝ) ≤ 1 := by
    exact (div_le_one hKreal).2 (by exact_mod_cast hnK)
  have hminusLeTwo : ((n - 1 : ℕ) : ℝ) / (K : ℝ) ≤ 2 := by
    have hminusLeK : n - 1 ≤ K := le_trans (Nat.sub_le n 1) hnK
    have hcast : (((n - 1 : ℕ) : ℝ)) ≤ (K : ℝ) := by
      exact_mod_cast hminusLeK
    have := (div_le_one hKreal).2 hcast
    linarith
  have hplusLeTwo : ((n + 1 : ℕ) : ℝ) / (K : ℝ) ≤ 2 := by
    have hcast : (((n + 1 : ℕ) : ℝ)) ≤ (K : ℝ) + 1 := by
      exact_mod_cast Nat.add_le_add_right hnK 1
    apply (div_le_iff₀ hKreal).2
    have hKone : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hKpositive
    linarith
  have hminusMem : ((n - 1 : ℕ) : ℝ) / (K : ℝ) ∈ Icc (0 : ℝ) 2 :=
    ⟨hminusNonnegative, hminusLeTwo⟩
  have hcenterMem : (n : ℝ) / (K : ℝ) ∈ Icc (0 : ℝ) 2 :=
    ⟨hcenterNonnegative, hcenterLeOne.trans (by norm_num)⟩
  have hplusMem : ((n + 1 : ℕ) : ℝ) / (K : ℝ) ∈ Icc (0 : ℝ) 2 :=
    ⟨hplusNonnegative, hplusLeTwo⟩
  have hminusDistance :
      dist (((n - 1 : ℕ) : ℝ) / (K : ℝ))
          ((n : ℝ) / (K : ℝ)) = ((K : ℝ))⁻¹ := by
    rw [Real.dist_eq]
    have hcastPred : (((n - 1 : ℕ) : ℝ)) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.2 hnZero)]
      norm_num
    rw [hcastPred]
    have hnonnegative :
        0 ≤ (n : ℝ) / (K : ℝ) -
          ((n : ℝ) - 1) / (K : ℝ) := by
      apply sub_nonneg.mpr
      apply div_le_div_of_nonneg_right _ hKreal.le
      linarith
    rw [abs_of_nonpos (by linarith)]
    field_simp [ne_of_gt hKreal]
    ring
  have hplusDistance :
      dist (((n + 1 : ℕ) : ℝ) / (K : ℝ))
          ((n : ℝ) / (K : ℝ)) = ((K : ℝ))⁻¹ := by
    rw [Real.dist_eq]
    norm_num [Nat.cast_add, Nat.cast_one]
    have hnonnegative :
        0 ≤ ((n : ℝ) + 1) / (K : ℝ) -
          (n : ℝ) / (K : ℝ) := by
      apply sub_nonneg.mpr
      apply div_le_div_of_nonneg_right _ hKreal.le
      linarith
    rw [abs_of_nonneg hnonnegative]
    field_simp [ne_of_gt hKreal]
    ring
  have hminusPower := hpower _ hminusMem _ hcenterMem
    (hminusDistance.trans_lt hKsmall)
  have hplusPower := hpower _ hplusMem _ hcenterMem
    (hplusDistance.trans_lt hKsmall)
  rw [Real.dist_eq] at hminusPower hplusPower
  have hsandwich := shiftedPowerSum_integral_sandwich
    hp htauZero htauOne hnPositive
  have hscaledLower :
      ((((n - 1 : ℕ) : ℝ) ^ scalingExponent p) /
            scalingExponent p) /
          ((K : ℝ) ^ scalingExponent p) ≤
        shiftedPowerSum (powerShiftExponent p) tau n /
          ((K : ℝ) ^ scalingExponent p) :=
    div_le_div_of_nonneg_right hsandwich.1 hKpower.le
  have hscaledUpper :
      shiftedPowerSum (powerShiftExponent p) tau n /
          ((K : ℝ) ^ scalingExponent p) ≤
        ((((n + 1 : ℕ) : ℝ) ^ scalingExponent p) /
            scalingExponent p) /
          ((K : ℝ) ^ scalingExponent p) :=
    div_le_div_of_nonneg_right hsandwich.2 hKpower.le
  have hminusForm :
      ((((n - 1 : ℕ) : ℝ) ^ scalingExponent p) /
            scalingExponent p) /
          ((K : ℝ) ^ scalingExponent p) =
        ((((n - 1 : ℕ) : ℝ) / (K : ℝ)) ^
            scalingExponent p) / scalingExponent p := by
    rw [Real.div_rpow (Nat.cast_nonneg _) hKreal.le]
    ring
  have hplusForm :
      ((((n + 1 : ℕ) : ℝ) ^ scalingExponent p) /
            scalingExponent p) /
          ((K : ℝ) ^ scalingExponent p) =
        ((((n + 1 : ℕ) : ℝ) / (K : ℝ)) ^
            scalingExponent p) / scalingExponent p := by
    rw [Real.div_rpow (Nat.cast_nonneg _) hKreal.le]
    ring
  rw [hminusForm] at hscaledLower
  rw [hplusForm] at hscaledUpper
  rw [abs_lt]
  constructor
  · have hminusDifference :
        (((n : ℝ) / (K : ℝ)) ^ scalingExponent p -
            (((n - 1 : ℕ) : ℝ) / (K : ℝ)) ^
              scalingExponent p) <
          epsilon * scalingExponent p := by
      exact lt_of_le_of_lt (le_abs_self _) (by
        simpa [abs_sub_comm] using hminusPower)
    have hdivDifference :
        (((n : ℝ) / (K : ℝ)) ^ scalingExponent p) /
              scalingExponent p - epsilon <
          ((((n - 1 : ℕ) : ℝ) / (K : ℝ)) ^
              scalingExponent p) / scalingExponent p := by
      apply (lt_div_iff₀ hsigma).2
      rw [sub_mul, div_mul_cancel₀ _ (ne_of_gt hsigma)]
      nlinarith
    have hcombined := lt_of_lt_of_le hdivDifference hscaledLower
    linarith
  · have hplusDifference :
        ((((n + 1 : ℕ) : ℝ) / (K : ℝ)) ^
              scalingExponent p -
            ((n : ℝ) / (K : ℝ)) ^ scalingExponent p) <
          epsilon * scalingExponent p := by
      exact lt_of_le_of_lt (le_abs_self _) hplusPower
    have hdivDifference :
        ((((n + 1 : ℕ) : ℝ) / (K : ℝ)) ^
              scalingExponent p) / scalingExponent p <
          (((n : ℝ) / (K : ℝ)) ^ scalingExponent p) /
              scalingExponent p + epsilon := by
      apply (div_lt_iff₀ hsigma).2
      rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hsigma)]
      nlinarith
    have hcombined := lt_of_le_of_lt hscaledUpper hdivDifference
    linarith

/-- A quantitative quotient lemma used to pass from uniformly normalized
power sums to uniformly normalized phase profiles. -/
theorem abs_div_sub_lt_of_normalized_close
    {a b A c eta epsilon : ℝ}
    (hc : 0 < c) (hAZero : 0 ≤ A) (hAOne : A ≤ 1)
    (hetaPositive : 0 < eta) (hetaC : eta ≤ c / 4)
    (hetaEpsilon : eta ≤ epsilon * c / 8)
    (hepsilon : 0 < epsilon)
    (ha : |a - c * A| < eta) (hb : |b - c| < eta) :
    |a / b - A| < epsilon := by
  have hbBounds := (abs_lt.mp hb)
  have hbPositive : 0 < b := by
    have hcQuarter : 0 < c / 4 := div_pos hc (by norm_num)
    nlinarith
  have hAAbs : |A| ≤ 1 := by
    rw [abs_of_nonneg hAZero]
    exact hAOne
  have hsecond : |A| * |c - b| < eta := by
    have hcb : |c - b| < eta := by
      simpa [abs_sub_comm] using hb
    have hnonnegative : 0 ≤ |c - b| := abs_nonneg _
    have := mul_le_mul_of_nonneg_right hAAbs hnonnegative
    exact lt_of_le_of_lt this (by simpa using hcb)
  have hnumerator : |a - A * b| < 2 * eta := by
    calc
      |a - A * b| = |(a - c * A) + A * (c - b)| := by
        congr 1
        ring
      _ ≤ |a - c * A| + |A * (c - b)| := abs_add_le _ _
      _ = |a - c * A| + |A| * |c - b| := by rw [abs_mul]
      _ < 2 * eta := by linarith
  have hdenominator : 2 * eta < epsilon * b := by
    have hbLower : c - eta < b := by linarith [hbBounds.1]
    have hcQuarter : 0 < c / 4 := div_pos hc (by norm_num)
    have hepsilonC : 0 < epsilon * c := mul_pos hepsilon hc
    nlinarith
  rw [show a / b - A = (a - A * b) / b by
    field_simp [ne_of_gt hbPositive]]
  rw [abs_div, abs_of_pos hbPositive]
  exact (div_lt_iff₀ hbPositive).2 (lt_trans hnumerator hdenominator)

/-- `B13.2`: the complete normalized phase profile converges uniformly to
`(1-u)^(p/(p-1))`, simultaneously over all active coordinates and every
admissible bounded phase offset. -/
theorem normalizedPhaseProfile_uniform_scaling
    {p : ℝ} (hp : 1 < p) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ K : ℕ in atTop,
        ∀ tau : ℝ, 0 ≤ tau → tau < 1 →
          ∀ i : ℕ, i ≤ K →
            |normalizedPhaseProfile (powerShiftExponent p) tau K i -
              scalingProfile p ((i : ℝ) / (K : ℝ))| < epsilon := by
  intro epsilon hepsilon
  let sigma := scalingExponent p
  let c := sigma⁻¹
  let eta := min (c / 4) (epsilon * c / 8)
  have hsigma : 0 < sigma := by
    dsimp [sigma]
    exact lt_trans zero_lt_one (one_lt_scalingExponent hp)
  have hc : 0 < c := by dsimp [c]; positivity
  have hetaPositive : 0 < eta := by
    dsimp [eta]
    exact lt_min (div_pos hc (by norm_num))
      (div_pos (mul_pos hepsilon hc) (by norm_num))
  have hetaC : eta ≤ c / 4 := by
    dsimp [eta]
    exact min_le_left _ _
  have hetaEpsilon : eta ≤ epsilon * c / 8 := by
    dsimp [eta]
    exact min_le_right _ _
  have hsums := shiftedPowerSum_uniform_integral_scaling hp eta hetaPositive
  filter_upwards [hsums, eventually_gt_atTop (0 : ℕ)] with K hsum hKpositive
  intro tau htauZero htauOne i hiK
  let n := K - i
  let A := ((n : ℝ) / (K : ℝ)) ^ sigma
  let a := shiftedPowerSum (powerShiftExponent p) tau n /
    ((K : ℝ) ^ sigma)
  let b := shiftedPowerSum (powerShiftExponent p) tau K /
    ((K : ℝ) ^ sigma)
  have hKreal : 0 < (K : ℝ) := by exact_mod_cast hKpositive
  have hnK : n ≤ K := by dsimp [n]; exact Nat.sub_le _ _
  have hbaseZero : 0 ≤ (n : ℝ) / (K : ℝ) :=
    div_nonneg (Nat.cast_nonneg _) hKreal.le
  have hbaseOne : (n : ℝ) / (K : ℝ) ≤ 1 := by
    exact (div_le_one hKreal).2 (by exact_mod_cast hnK)
  have hAZero : 0 ≤ A := by
    dsimp [A]
    exact Real.rpow_nonneg hbaseZero _
  have hAOne : A ≤ 1 := by
    dsimp [A]
    simpa using Real.rpow_le_one hbaseZero hbaseOne hsigma.le
  have ha : |a - c * A| < eta := by
    have raw := hsum tau htauZero htauOne n hnK
    dsimp [a, c, A, sigma] at raw ⊢
    simpa [div_eq_mul_inv, mul_comm] using raw
  have hb : |b - c| < eta := by
    have raw := hsum tau htauZero htauOne K (le_refl K)
    dsimp [b, c, sigma] at raw ⊢
    have hquotient : (K : ℝ) / (K : ℝ) = 1 :=
      div_self (ne_of_gt hKreal)
    rw [hquotient, Real.one_rpow] at raw
    simpa [div_eq_mul_inv] using raw
  have hquotient := abs_div_sub_lt_of_normalized_close
    hc hAZero hAOne hetaPositive hetaC hetaEpsilon hepsilon ha hb
  have hKpower : (K : ℝ) ^ sigma ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hKreal _)
  have hprofileForm :
      normalizedPhaseProfile (powerShiftExponent p) tau K i = a / b := by
    dsimp [a, b, n, sigma]
    unfold normalizedPhaseProfile
    field_simp [hKpower]
  have htargetForm :
      scalingProfile p ((i : ℝ) / (K : ℝ)) = A := by
    dsimp [A, n, sigma]
    unfold scalingProfile
    have hcastSub : ((K - i : ℕ) : ℝ) = (K : ℝ) - (i : ℝ) := by
      rw [Nat.cast_sub hiK]
    rw [hcastSub]
    congr 1
    field_simp [ne_of_gt hKreal]
  rw [hprofileForm, htargetForm]
  exact hquotient

/-- `B13.3`: after multiplication by the active support length, every local
decrease converges uniformly to the decrement density.  The coordinate range
is exactly `1 ≤ i ≤ K`, and the phase offset may vary arbitrarily in
`[0,1)`. -/
theorem normalizedPhaseDecrease_uniform_scaling
    {p : ℝ} (hp : 1 < p) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ K : ℕ in atTop,
        ∀ tau : ℝ, 0 ≤ tau → tau < 1 →
          ∀ i : ℕ, 1 ≤ i → i ≤ K →
            |(K : ℝ) *
                normalizedPhaseDecrease (powerShiftExponent p) tau K (K - i) -
              scalingDensity p ((i : ℝ) / (K : ℝ))| < epsilon := by
  intro epsilon hepsilon
  let q := powerShiftExponent p
  let sigma := scalingExponent p
  let c := sigma⁻¹
  let epsilonQuotient := epsilon * c
  let eta := min (c / 4) (epsilonQuotient * c / 8)
  have hq : 0 < q := by
    dsimp [q]
    exact powerShiftExponent_positive hp
  have hsigma : 0 < sigma := by
    dsimp [sigma]
    exact lt_trans zero_lt_one (one_lt_scalingExponent hp)
  have hc : 0 < c := by dsimp [c]; positivity
  have hepsilonQuotient : 0 < epsilonQuotient := by
    dsimp [epsilonQuotient]
    exact mul_pos hepsilon hc
  have hetaPositive : 0 < eta := by
    dsimp [eta]
    exact lt_min (div_pos hc (by norm_num))
      (div_pos (mul_pos hepsilonQuotient hc) (by norm_num))
  have hetaC : eta ≤ c / 4 := by
    dsimp [eta]
    exact min_le_left _ _
  have hetaEpsilon : eta ≤ epsilonQuotient * c / 8 := by
    dsimp [eta]
    exact min_le_right _ _
  have hcontinuous : ContinuousOn (fun z : ℝ => z ^ q) (Icc 0 2) :=
    (Real.continuous_rpow_const hq.le).continuousOn
  have huniform := isCompact_Icc.uniformContinuousOn_of_continuous hcontinuous
  rw [Metric.uniformContinuousOn_iff] at huniform
  obtain ⟨delta, hdelta, hpower⟩ :=
    huniform (eta / c) (div_pos hetaPositive hc)
  have hcastTop : Tendsto (fun K : ℕ => (K : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hinverse : Tendsto (fun K : ℕ => ((K : ℝ))⁻¹)
      atTop (nhds 0) := tendsto_inv_atTop_zero.comp hcastTop
  have hsmall : ∀ᶠ K : ℕ in atTop, ((K : ℝ))⁻¹ < delta := by
    have hball := hinverse.eventually (Metric.ball_mem_nhds 0 hdelta)
    filter_upwards [hball] with K hK
    rw [Real.dist_eq] at hK
    have hInverseNonnegative : 0 ≤ ((K : ℝ))⁻¹ :=
      inv_nonneg.mpr (Nat.cast_nonneg K)
    simpa [abs_of_nonneg hInverseNonnegative] using hK
  have hsums := shiftedPowerSum_uniform_integral_scaling hp eta hetaPositive
  filter_upwards [hsmall, hsums, eventually_gt_atTop (0 : ℕ)] with
      K hKsmall hsum hKpositive
  intro tau htauZero htauOne i hiOne hiK
  let n := K - i
  let t := (n : ℝ) / (K : ℝ)
  let y := (((n + 1 : ℕ) : ℝ) - tau) / (K : ℝ)
  let A := t ^ q
  let b := shiftedPowerSum q tau K / ((K : ℝ) ^ sigma)
  have hKreal : 0 < (K : ℝ) := by exact_mod_cast hKpositive
  have hnK : n ≤ K := by dsimp [n]; exact Nat.sub_le _ _
  have hnSuccK : n + 1 ≤ K := by
    dsimp [n]
    omega
  have htZero : 0 ≤ t := by
    dsimp [t]
    exact div_nonneg (Nat.cast_nonneg _) hKreal.le
  have htOne : t ≤ 1 := by
    dsimp [t]
    exact (div_le_one hKreal).2 (by exact_mod_cast hnK)
  have hyNumeratorPositive : 0 < (((n + 1 : ℕ) : ℝ) - tau) := by
    have hcast : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    linarith
  have hyZero : 0 ≤ y := by
    dsimp [y]
    exact div_nonneg hyNumeratorPositive.le hKreal.le
  have hyOne : y ≤ 1 := by
    dsimp [y]
    apply (div_le_one hKreal).2
    have hcast : ((n + 1 : ℕ) : ℝ) ≤ (K : ℝ) := by
      exact_mod_cast hnSuccK
    linarith
  have htMem : t ∈ Icc (0 : ℝ) 2 := ⟨htZero, htOne.trans (by norm_num)⟩
  have hyMem : y ∈ Icc (0 : ℝ) 2 := ⟨hyZero, hyOne.trans (by norm_num)⟩
  have hytDistance : dist y t ≤ ((K : ℝ))⁻¹ := by
    rw [Real.dist_eq]
    dsimp [y, t]
    have hnonnegative :
        0 ≤ ((((n + 1 : ℕ) : ℝ) - tau) / (K : ℝ)) -
          (n : ℝ) / (K : ℝ) := by
      apply sub_nonneg.mpr
      apply div_le_div_of_nonneg_right _ hKreal.le
      norm_num [Nat.cast_add, Nat.cast_one]
      linarith
    rw [abs_of_nonneg hnonnegative]
    rw [show (((n + 1 : ℕ) : ℝ)) = (n : ℝ) + 1 by norm_num]
    rw [show (((n : ℝ) + 1 - tau) / (K : ℝ) -
        (n : ℝ) / (K : ℝ)) = (1 - tau) / (K : ℝ) by ring]
    rw [inv_eq_one_div]
    exact div_le_div_of_nonneg_right (by linarith) hKreal.le
  have hytStrict : dist y t < delta := lt_of_le_of_lt hytDistance hKsmall
  have hpowerClose := hpower y hyMem t htMem hytStrict
  rw [Real.dist_eq] at hpowerClose
  have hAZero : 0 ≤ A := by
    dsimp [A]
    exact Real.rpow_nonneg htZero _
  have hAOne : A ≤ 1 := by
    dsimp [A]
    simpa using Real.rpow_le_one htZero htOne hq.le
  have hb : |b - c| < eta := by
    have raw := hsum tau htauZero htauOne K (le_refl K)
    dsimp [b, c, sigma, q] at raw ⊢
    have hquotient : (K : ℝ) / (K : ℝ) = 1 :=
      div_self (ne_of_gt hKreal)
    rw [hquotient, Real.one_rpow] at raw
    simpa [div_eq_mul_inv] using raw
  have ha : |c * (y ^ q) - c * A| < eta := by
    rw [← mul_sub, abs_mul, abs_of_pos hc]
    calc
      c * |y ^ q - A| < c * (eta / c) :=
        mul_lt_mul_of_pos_left (by
          simpa [A, abs_sub_comm] using hpowerClose) hc
      _ = eta := by field_simp [ne_of_gt hc]
  have hquotient := abs_div_sub_lt_of_normalized_close
    hc hAZero hAOne hetaPositive hetaC hetaEpsilon hepsilonQuotient
      ha hb
  have hbPositive : 0 < b := by
    have hbBounds := abs_lt.mp hb
    have hcQuarter : 0 < c / 4 := div_pos hc (by norm_num)
    nlinarith
  have hscaledDecrease :
      (K : ℝ) * normalizedPhaseDecrease q tau K (K - i) =
        (y ^ q) / b := by
    have hKpower : (K : ℝ) ^ sigma ≠ 0 :=
      ne_of_gt (Real.rpow_pos_of_pos hKreal _)
    have hsumNonzero : shiftedPowerSum q tau K ≠ 0 := by
      dsimp [b] at hbPositive
      exact fun hzero => by simp [hzero] at hbPositive
    have hsigmaEq : sigma = q + 1 := by
      dsimp [sigma, q]
      exact (powerShiftExponent_add_one_eq_scalingExponent hp).symm
    have hKsigma : (K : ℝ) ^ sigma =
        (K : ℝ) ^ q * (K : ℝ) := by
      rw [hsigmaEq, Real.rpow_add hKreal, Real.rpow_one]
    dsimp [y, b]
    unfold normalizedPhaseDecrease
    rw [Real.div_rpow hyNumeratorPositive.le hKreal.le, hKsigma]
    field_simp [hKpower, hsumNonzero,
      ne_of_gt (Real.rpow_pos_of_pos hKreal q)]
    ring
  have htarget : scalingDensity p ((i : ℝ) / (K : ℝ)) = A / c := by
    have hcastSub : ((K - i : ℕ) : ℝ) = (K : ℝ) - (i : ℝ) := by
      rw [Nat.cast_sub hiK]
    have hbase : 1 - (i : ℝ) / (K : ℝ) = t := by
      dsimp [t, n]
      rw [hcastSub]
      field_simp [ne_of_gt hKreal]
    unfold scalingDensity
    rw [show 1 / (p - 1) = q by rfl, hbase]
    dsimp [A, c, sigma]
    field_simp [ne_of_gt hsigma]
  rw [hscaledDecrease, htarget]
  have hidentity :
      (y ^ q) / b - A / c =
        (c * (y ^ q) / b - A) / c := by
    field_simp [ne_of_gt hbPositive, ne_of_gt hc]
  rw [hidentity, abs_div, abs_of_pos hc]
  apply (div_lt_iff₀ hc).2
  simpa [epsilonQuotient, mul_comm] using hquotient

/-- The two exact uniform scaling laws of `CHG-B13`, stated together at the
fixed-`p`, bounded-phase-offset scope. -/
theorem chg_b13_uniform_long_support_scaling
    {p : ℝ} (hp : 1 < p) :
    (∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ K : ℕ in atTop,
        ∀ tau : ℝ, 0 ≤ tau → tau < 1 →
          ∀ i : ℕ, i ≤ K →
            |normalizedPhaseProfile (powerShiftExponent p) tau K i -
              scalingProfile p ((i : ℝ) / (K : ℝ))| < epsilon) ∧
    (∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ K : ℕ in atTop,
        ∀ tau : ℝ, 0 ≤ tau → tau < 1 →
          ∀ i : ℕ, 1 ≤ i → i ≤ K →
            |(K : ℝ) *
                normalizedPhaseDecrease (powerShiftExponent p) tau K (K - i) -
              scalingDensity p ((i : ℝ) / (K : ℝ))| < epsilon) := by
  exact ⟨normalizedPhaseProfile_uniform_scaling hp,
    normalizedPhaseDecrease_uniform_scaling hp⟩

end PhonologicalCalculus.ContinuousHG
