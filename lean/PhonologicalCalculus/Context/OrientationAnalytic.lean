import PhonologicalCalculus.Context.Orientation
import PhonologicalCalculus.ContinuousHG.GeneralPowerOptimizer
import PhonologicalCalculus.ContinuousHG.PhaseProfileOptimizerBridge
import Mathlib.Data.Real.Sign
import Mathlib.Topology.Order.Compact

/-!
# Analytic objective bridge for contextual orientation

This module derives the support semantics used by `CTX-C2.GENERAL.03` from
the declared real-power objectives.  It does not take the integer support
thresholds as optimizer axioms.  The directional branch is connected to the
finite shifted-power KKT optimizer.  The absolute-edge branch is developed
through its signed edge-slope objective, including a strict tangent proof and
an explicit unconstrained interval optimizer.
-/

namespace PhonologicalCalculus.Context

open scoped BigOperators
open Finset Set
open PhonologicalCalculus.ContinuousHG

/-! ## Strict absolute-power objective -/

/-- Absolute real-power edge cost. -/
noncomputable def absolutePowerPenalty (p edge : ℝ) : ℝ :=
  |edge| ^ p

/-- Derivative of the absolute real-power edge cost for `p > 1`. -/
noncomputable def absolutePowerSlope (p edge : ℝ) : ℝ :=
  p * Real.sign edge * |edge| ^ (p - 1)

/-- Strict supporting-line inequality for `edge ↦ |edge|^p` on the real
line. -/
theorem absolutePower_strict_tangent {p u d : ℝ} (hp : 1 < p) :
    absolutePowerPenalty p u + absolutePowerSlope p u * (d - u) ≤
        absolutePowerPenalty p d ∧
      (absolutePowerPenalty p u + absolutePowerSlope p u * (d - u) =
          absolutePowerPenalty p d → d = u) := by
  have hpPositive : 0 < p := lt_trans zero_lt_one hp
  simp only [absolutePowerPenalty, absolutePowerSlope]
  have huAbs : 0 ≤ |u| := abs_nonneg u
  have hdAbs : 0 ≤ |d| := abs_nonneg d
  have htangent := rpow_strict_tangent hp huAbs hdAbs
  have hsubgradient : Real.sign u * (d - u) ≤ |d| - |u| := by
    rcases lt_trichotomy u 0 with huNegative | rfl | huPositive
    · rw [Real.sign_of_neg huNegative, abs_of_neg huNegative]
      have hnegD : -d ≤ |d| := neg_le_abs d
      linarith
    · simp
    · rw [Real.sign_of_pos huPositive, abs_of_pos huPositive]
      have hposD : d ≤ |d| := le_abs_self d
      linarith
  have hcoefficientNonnegative : 0 ≤ p * |u| ^ (p - 1) :=
    mul_nonneg hpPositive.le (Real.rpow_nonneg huAbs (p - 1))
  have hscaled :
      p * |u| ^ (p - 1) * (Real.sign u * (d - u)) ≤
        p * |u| ^ (p - 1) * (|d| - |u|) :=
    mul_le_mul_of_nonneg_left hsubgradient hcoefficientNonnegative
  have hsupport :
      |u| ^ p + p * Real.sign u * |u| ^ (p - 1) * (d - u) ≤
        |u| ^ p + p * |u| ^ (p - 1) * (|d| - |u|) := by
    nlinarith
  constructor
  · exact hsupport.trans htangent.1
  · intro heq
    have habsTangent :
        |u| ^ p + p * |u| ^ (p - 1) * (|d| - |u|) = |d| ^ p := by
      apply le_antisymm htangent.1
      linarith
    have habs : |d| = |u| := htangent.2 habsTangent
    by_cases huZero : u = 0
    · subst u
      simpa using (abs_eq_zero.mp (by simpa using habs))
    · have huAbsPositive : 0 < |u| := abs_pos.mpr huZero
      have hcoefficientPositive : 0 < p * |u| ^ (p - 1) :=
        mul_pos hpPositive
          (Real.rpow_pos_of_pos huAbsPositive (p - 1))
      have hscaledEquality :
          p * |u| ^ (p - 1) * (Real.sign u * (d - u)) =
            p * |u| ^ (p - 1) * (|d| - |u|) := by
        nlinarith
      have hsubgradientEquality :
          Real.sign u * (d - u) = |d| - |u| :=
        mul_left_cancel₀ hcoefficientPositive.ne' hscaledEquality
      rcases lt_or_gt_of_ne huZero with huNegative | huPositive
      · rw [Real.sign_of_neg huNegative, habs] at hsubgradientEquality
        linarith
      · rw [Real.sign_of_pos huPositive, habs] at hsubgradientEquality
        linarith

/-- Strict-convexity remainder for the absolute-power edge cost. -/
noncomputable def absolutePowerRemainder (p u d : ℝ) : ℝ :=
  absolutePowerPenalty p d - absolutePowerPenalty p u -
    absolutePowerSlope p u * (d - u)

theorem absolutePowerRemainder_nonnegative {p u d : ℝ} (hp : 1 < p) :
    0 ≤ absolutePowerRemainder p u d := by
  unfold absolutePowerRemainder
  linarith [(absolutePower_strict_tangent hp (u := u) (d := d)).1]

theorem absolutePowerRemainder_eq_zero_iff {p u d : ℝ} (hp : 1 < p) :
    absolutePowerRemainder p u d = 0 ↔ d = u := by
  constructor
  · intro hzero
    apply (absolutePower_strict_tangent hp (u := u) (d := d)).2
    unfold absolutePowerRemainder at hzero
    linarith
  · rintro rfl
    simp [absolutePowerRemainder]

/-! ## Strict finite signed-slope optimization -/

section SignedSlopeObjective

variable {ι : Type*} [Fintype ι]

/-- The reduced absolute-edge objective in signed edge-slope coordinates.
The linear weights arise when the site term is expanded as a weighted sum
of cumulative edge slopes. -/
noncomputable def absoluteSlopeObjective
    (h m p : ℝ) (weight slope : ι → ℝ) : ℝ :=
  ∑ i, (h * absolutePowerPenalty p (slope i) -
    m * weight i * slope i)

/-- Coordinate gradient of the reduced signed-slope objective. -/
noncomputable def absoluteSlopeGradient
    (h m p : ℝ) (weight slope : ι → ℝ) (i : ι) : ℝ :=
  h * absolutePowerSlope p (slope i) - m * weight i

/-- Exact Bregman-gap identity for the signed-slope objective. -/
theorem absoluteSlopeObjective_gap_identity
    (h m p : ℝ) (weight d u : ι → ℝ) :
    absoluteSlopeObjective h m p weight d -
        absoluteSlopeObjective h m p weight u =
      h * ∑ i, absolutePowerRemainder p (u i) (d i) +
        ∑ i, absoluteSlopeGradient h m p weight u i * (d i - u i) := by
  classical
  unfold absoluteSlopeObjective absolutePowerRemainder absoluteSlopeGradient
  rw [← Finset.sum_sub_distrib]
  calc
    (∑ i, ((h * absolutePowerPenalty p (d i) - m * weight i * d i) -
        (h * absolutePowerPenalty p (u i) - m * weight i * u i))) =
        ∑ i, (h * (absolutePowerPenalty p (d i) -
          absolutePowerPenalty p (u i) -
          absolutePowerSlope p (u i) * (d i - u i)) +
          (h * absolutePowerSlope p (u i) - m * weight i) *
            (d i - u i)) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = h * ∑ i, (absolutePowerPenalty p (d i) -
          absolutePowerPenalty p (u i) -
          absolutePowerSlope p (u i) * (d i - u i)) +
        ∑ i, (h * absolutePowerSlope p (u i) - m * weight i) *
          (d i - u i) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]

/-- A constant gradient gives the exact stationarity proof for the affine
hyperplane of signed slopes having a prescribed total.  Strict convexity of
the absolute-power term then gives the unique global minimizer on that
hyperplane. -/
theorem absoluteSlope_unique_minimizer_of_constant_gradient
    {h m p total lambda : ℝ} (weight u : ι → ℝ)
    (hh : 0 < h) (hp : 1 < p)
    (huMass : ∑ i, u i = total)
    (hgradient : ∀ i, absoluteSlopeGradient h m p weight u i = lambda) :
    IsUniqueMinimizerOn (fun d : ι → ℝ => ∑ i, d i = total)
      (absoluteSlopeObjective h m p weight) u := by
  classical
  refine ⟨huMass, ?_⟩
  intro d hdMass
  have linearZero :
      (∑ i, absoluteSlopeGradient h m p weight u i * (d i - u i)) = 0 := by
    calc
      (∑ i, absoluteSlopeGradient h m p weight u i * (d i - u i)) =
          ∑ i, lambda * (d i - u i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hgradient i]
      _ = lambda * (∑ i, (d i - u i)) := by rw [Finset.mul_sum]
      _ = 0 := by rw [Finset.sum_sub_distrib, hdMass, huMass, sub_self, mul_zero]
  have remainderPointwise :
      ∀ i, 0 ≤ absolutePowerRemainder p (u i) (d i) :=
    fun i => absolutePowerRemainder_nonnegative hp
  have remainderSumNonnegative :
      0 ≤ ∑ i, absolutePowerRemainder p (u i) (d i) :=
    Finset.sum_nonneg fun i _ => remainderPointwise i
  have gapNonnegative :
      0 ≤ absoluteSlopeObjective h m p weight d -
        absoluteSlopeObjective h m p weight u := by
    rw [absoluteSlopeObjective_gap_identity, linearZero, add_zero]
    exact mul_nonneg hh.le remainderSumNonnegative
  constructor
  · linarith
  · intro objectiveEquality
    have gapZero : absoluteSlopeObjective h m p weight d -
        absoluteSlopeObjective h m p weight u = 0 := by linarith
    have remainderProductZero :
        h * ∑ i, absolutePowerRemainder p (u i) (d i) = 0 := by
      rw [absoluteSlopeObjective_gap_identity, linearZero, add_zero] at gapZero
      exact gapZero
    have remainderSumZero :
        ∑ i, absolutePowerRemainder p (u i) (d i) = 0 := by
      exact (mul_eq_zero.mp remainderProductZero).resolve_left hh.ne'
    funext i
    have coordinateRemainderZero : absolutePowerRemainder p (u i) (d i) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => remainderPointwise j)).1 remainderSumZero i
          (Finset.mem_univ i)
    exact (absolutePowerRemainder_eq_zero_iff hp).1 coordinateRemainderZero

end SignedSlopeObjective

/-! ## Explicit free equal-endpoint interval optimizer -/

/-- Odd signed-power response with the conjugate exponent of `p`. -/
noncomputable def signedPowerResponse (p scale z : ℝ) : ℝ :=
  Real.sign z * (scale * |z|) ^ powerShiftExponent p

/-- The absolute-power derivative of the signed-power response is linear in
its load.  This is the analytic inversion used by the equal-endpoint KKT
system. -/
theorem absolutePowerSlope_signedPowerResponse
    {p scale z : ℝ} (hp : 1 < p) (hscale : 0 < scale) :
    absolutePowerSlope p (signedPowerResponse p scale z) = p * scale * z := by
  have hq : 0 < powerShiftExponent p := powerShiftExponent_positive hp
  have hproduct : powerShiftExponent p * (p - 1) = 1 := by
    unfold powerShiftExponent
    field_simp [ne_of_gt (sub_pos.mpr hp)]
  rcases lt_trichotomy z 0 with hzNegative | rfl | hzPositive
  · have habsPositive : 0 < |z| := abs_pos.mpr hzNegative.ne
    have hbasePositive : 0 < scale * |z| := mul_pos hscale habsPositive
    have hresponseMagnitude : 0 <
        (scale * |z|) ^ powerShiftExponent p :=
      Real.rpow_pos_of_pos hbasePositive _
    have hpower :
        ((scale * |z|) ^ powerShiftExponent p) ^ (p - 1) =
          scale * |z| := by
      rw [← Real.rpow_mul hbasePositive.le, hproduct, Real.rpow_one]
    rw [signedPowerResponse, Real.sign_of_neg hzNegative]
    simp only [neg_one_mul]
    rw [absolutePowerSlope, Real.sign_of_neg (neg_lt_zero.mpr hresponseMagnitude),
      abs_of_neg (neg_lt_zero.mpr hresponseMagnitude), neg_neg, hpower,
      abs_of_neg hzNegative]
    ring
  · simp [signedPowerResponse, absolutePowerSlope,
      Real.zero_rpow hq.ne']
  · have habsPositive : 0 < |z| := abs_pos.mpr hzPositive.ne'
    have hbasePositive : 0 < scale * |z| := mul_pos hscale habsPositive
    have hresponsePositive : 0 <
        (scale * |z|) ^ powerShiftExponent p :=
      Real.rpow_pos_of_pos hbasePositive _
    have hpower :
        ((scale * |z|) ^ powerShiftExponent p) ^ (p - 1) =
          scale * |z| := by
      rw [← Real.rpow_mul hbasePositive.le, hproduct, Real.rpow_one]
    rw [signedPowerResponse, Real.sign_of_pos hzPositive, one_mul,
      absolutePowerSlope, Real.sign_of_pos hresponsePositive,
      abs_of_pos hresponsePositive, hpower, abs_of_pos hzPositive]
    ring

/-- Linear positional weight obtained by expanding the sum of the interior
deficits on an interval with `L` edges. -/
def absoluteIntervalWeight (L : ℕ) (i : Fin L) : ℝ :=
  (L : ℝ) - (i.1 : ℝ)

/-- Centered signed load on edge `i` of an `L`-edge equal-endpoint interval. -/
def absoluteIntervalCentered (L : ℕ) (i : Fin L) : ℝ :=
  (L : ℝ) - 1 - 2 * (i.1 : ℝ)

/-- Free signed slope solving the equal-endpoint absolute-edge stationarity
equations before the lower obstacle is imposed. -/
noncomputable def absoluteIntervalFreeSlope
    (h m p : ℝ) (L : ℕ) (i : Fin L) : ℝ :=
  signedPowerResponse p (m / (2 * p * h))
    (absoluteIntervalCentered L i)

theorem absoluteIntervalCentered_reverse (L : ℕ) (i : Fin L) :
    absoluteIntervalCentered L (Fin.rev i) =
      -absoluteIntervalCentered L i := by
  unfold absoluteIntervalCentered Fin.rev
  have hcast : (((L - (i.1 + 1) : ℕ) : ℕ) : ℝ) =
      (L : ℝ) - ((i.1 + 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (Nat.succ_le_iff.mpr i.2)]
  rw [hcast]
  push_cast
  ring

theorem signedPowerResponse_neg (p scale z : ℝ) :
    signedPowerResponse p scale (-z) = -signedPowerResponse p scale z := by
  rw [signedPowerResponse, signedPowerResponse, Real.sign_neg, abs_neg]
  ring

theorem absoluteIntervalFreeSlope_reverse
    (h m p : ℝ) (L : ℕ) (i : Fin L) :
    absoluteIntervalFreeSlope h m p L (Fin.rev i) =
      -absoluteIntervalFreeSlope h m p L i := by
  unfold absoluteIntervalFreeSlope
  rw [absoluteIntervalCentered_reverse, signedPowerResponse_neg]

/-- Reflection antisymmetry makes the free equal-endpoint slope sum exactly
zero. -/
theorem absoluteIntervalFreeSlope_sum_zero
    (h m p : ℝ) (L : ℕ) :
    ∑ i : Fin L, absoluteIntervalFreeSlope h m p L i = 0 := by
  classical
  let S := ∑ i : Fin L, absoluteIntervalFreeSlope h m p L i
  have hreverse : S = -S := by
    calc
      S = ∑ i : Fin L,
          absoluteIntervalFreeSlope h m p L ((finReverseEquiv L) i) := by
        symm
        exact Equiv.sum_comp (finReverseEquiv L)
          (absoluteIntervalFreeSlope h m p L)
      _ = ∑ i : Fin L, -absoluteIntervalFreeSlope h m p L i := by
        apply Finset.sum_congr rfl
        intro i _
        exact absoluteIntervalFreeSlope_reverse h m p L i
      _ = -S := by simp [S]
  linarith

/-- Every free interval slope has the same Lagrange gradient. -/
theorem absoluteIntervalFreeSlope_gradient_constant
    {h m p : ℝ} (L : ℕ) (hh : 0 < h) (hm : 0 < m) (hp : 1 < p)
    (i : Fin L) :
    absoluteSlopeGradient h m p (absoluteIntervalWeight L)
        (absoluteIntervalFreeSlope h m p L) i =
      -m * ((L : ℝ) + 1) / 2 := by
  have hpPositive : 0 < p := lt_trans zero_lt_one hp
  have hscale : 0 < m / (2 * p * h) := by positivity
  rw [absoluteSlopeGradient, absoluteIntervalFreeSlope,
    absolutePowerSlope_signedPowerResponse hp hscale]
  unfold absoluteIntervalWeight absoluteIntervalCentered
  field_simp [ne_of_gt hpPositive, ne_of_gt hh]
  ring

/-- The explicit free slope is the unique global minimizer of the actual
signed-slope objective under the equal-endpoint constraint. -/
theorem absoluteIntervalFreeSlope_unique_minimizer
    {h m p : ℝ} (L : ℕ) (hh : 0 < h) (hm : 0 < m) (hp : 1 < p) :
    IsUniqueMinimizerOn (fun slope : Fin L → ℝ => ∑ i, slope i = 0)
      (absoluteSlopeObjective h m p (absoluteIntervalWeight L))
      (absoluteIntervalFreeSlope h m p L) := by
  apply absoluteSlope_unique_minimizer_of_constant_gradient
    (total := 0) (lambda := -m * ((L : ℝ) + 1) / 2)
  · exact hh
  · exact hp
  · exact absoluteIntervalFreeSlope_sum_zero h m p L
  · exact absoluteIntervalFreeSlope_gradient_constant L hh hm hp

/-! ## Exact bridge back to the declared list-valued path objective -/

/-- Positional linear form on a finite list of signed decreases. -/
def weightedSlopeSum : List ℝ → ℝ
  | [] => 0
  | slope :: tail => ((tail.length + 1 : ℕ) : ℝ) * slope +
      weightedSlopeSum tail

/-- Reconstructed path sum as a constant minus its positional signed-slope
linear form.  This identity does not assume nonnegative slopes. -/
theorem profileFromDecreases_sum_eq
    (previous : ℝ) (slope : List ℝ) :
    (profileFromDecreases previous slope).sum =
      (slope.length : ℝ) * previous - weightedSlopeSum slope := by
  induction slope generalizing previous with
  | nil => simp [profileFromDecreases, weightedSlopeSum]
  | cons d ds ih =>
      simp only [profileFromDecreases, List.sum_cons, List.length_cons,
        weightedSlopeSum]
      rw [ih (previous - d)]
      push_cast
      ring

/-- Absolute edge changes of a reconstructed path are exactly the absolute
values of its signed decreases. -/
theorem absoluteDropsFrom_profileFromDecreases
    (previous : ℝ) (slope : List ℝ) :
    absoluteDropsFrom previous (profileFromDecreases previous slope) =
      slope.map abs := by
  induction slope generalizing previous with
  | nil => rfl
  | cons d ds ih =>
      simp [profileFromDecreases, absoluteDropsFrom, absoluteDrop, ih]

/-- The recursive list linear form agrees exactly with the finite positional
weight used by the analytic optimizer. -/
theorem weightedSlopeSum_ofFn
    {L : ℕ} (slope : Fin L → ℝ) :
    weightedSlopeSum (List.ofFn slope) =
      ∑ i : Fin L, absoluteIntervalWeight L i * slope i := by
  induction L with
  | zero => simp [weightedSlopeSum]
  | succ L ih =>
      rw [List.ofFn_succ]
      simp only [weightedSlopeSum, List.length_ofFn]
      rw [ih (fun i : Fin L => slope i.succ), Fin.sum_univ_succ]
      unfold absoluteIntervalWeight
      push_cast
      congr 1
      · simp
      · apply Finset.sum_congr rfl
        intro i _
        simp

/-- The declared opposite-trigger absolute-edge Harmony, represented by its
signed consecutive decreases.  The equal-endpoint constraint is `sum = 0`;
it is kept separate from the objective. -/
noncomputable def absoluteIntervalPathHarmony
    (h m p : ℝ) {L : ℕ} (slope : Fin L → ℝ) : ℝ :=
  absolutePathHarmony (powerPenalty p) h m
    (profileFromDecreases 1 (List.ofFn slope))

/-- Exact objective correspondence: the list-valued Harmony is the reduced
signed-slope objective plus the fixed markedness constant `mL`. -/
theorem absoluteIntervalPathHarmony_eq_reduced
    (h m p : ℝ) {L : ℕ} (slope : Fin L → ℝ) :
    absoluteIntervalPathHarmony h m p slope =
      m * (L : ℝ) +
        absoluteSlopeObjective h m p (absoluteIntervalWeight L) slope := by
  classical
  unfold absoluteIntervalPathHarmony absolutePathHarmony absoluteDrops
  rw [absoluteDropsFrom_profileFromDecreases,
    profileFromDecreases_sum_eq, weightedSlopeSum_ofFn]
  simp only [List.length_ofFn, List.map_ofFn,
    List.sum_ofFn, Function.comp_apply]
  unfold absoluteSlopeObjective absolutePowerPenalty powerPenalty
  simp only [Real.rpow_eq_pow]
  rw [Finset.sum_sub_distrib]
  have hedge : (∑ i : Fin L, h * |slope i| ^ p) =
      h * ∑ i : Fin L, |slope i| ^ p := by
    exact (Finset.mul_sum _ _ _).symm
  have hsite : (∑ i : Fin L,
      m * absoluteIntervalWeight L i * slope i) =
      m * ∑ i : Fin L, absoluteIntervalWeight L i * slope i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hedge, hsite]
  ring

/-- The explicit free slope is therefore the unique minimizer of the actual
declared list-valued absolute-edge Harmony on equal-endpoint paths. -/
theorem absoluteIntervalPathHarmony_unique_minimizer
    {h m p : ℝ} (L : ℕ) (hh : 0 < h) (hm : 0 < m) (hp : 1 < p) :
    IsUniqueMinimizerOn (fun slope : Fin L → ℝ => ∑ i, slope i = 0)
      (absoluteIntervalPathHarmony h m p)
      (absoluteIntervalFreeSlope h m p L) := by
  have hreduced := absoluteIntervalFreeSlope_unique_minimizer L hh hm hp
  refine ⟨hreduced.1, ?_⟩
  intro slope hslope
  have hcomparison := hreduced.2 slope hslope
  constructor
  · rw [absoluteIntervalPathHarmony_eq_reduced,
      absoluteIntervalPathHarmony_eq_reduced]
    exact add_le_add_right hcomparison.1 _
  · intro heq
    exact hcomparison.2 (by
      rw [absoluteIntervalPathHarmony_eq_reduced,
        absoluteIntervalPathHarmony_eq_reduced] at heq
      linarith)

/-! ## Directional objective bridge and exact gap support -/

/-- On a nonnegative decrease list, the declared directional drops of the
reconstructed path are the decreases themselves. -/
theorem directionalDropsFrom_profileFromDecreases_of_nonnegative
    (previous : ℝ) (slope : List ℝ)
    (hnonnegative : ∀ d ∈ slope, 0 ≤ d) :
    directionalDropsFrom previous (profileFromDecreases previous slope) =
      slope := by
  induction slope generalizing previous with
  | nil => rfl
  | cons d ds ih =>
      have hd : 0 ≤ d := hnonnegative d (by simp)
      have hds : ∀ e ∈ ds, 0 ≤ e := by
        intro e he
        exact hnonnegative e (by simp [he])
      simp [profileFromDecreases, directionalDropsFrom, directionalDrop,
        hd, ih (previous - d) hds]

/-- The declared one-trigger directional Harmony in finite decrease
coordinates. -/
noncomputable def directionalIntervalPathHarmony
    (h m p : ℝ) {N : ℕ} (decrease : Fin N → ℝ) : ℝ :=
  pathHarmony (powerPenalty p) h m
    (profileFromDecreases 1 (List.ofFn decrease))

/-- Exact reduction of the declared directional path objective on its solid
simplex. -/
theorem directionalIntervalPathHarmony_eq_reduced
    (h m p : ℝ) {N : ℕ} (decrease : Fin N → ℝ)
    (hnonnegative : ∀ i, 0 ≤ decrease i) :
    directionalIntervalPathHarmony h m p decrease =
      m * (N : ℝ) +
        powerReducedObjective h m p (powerPathWeight N) decrease := by
  classical
  have hlistNonnegative : ∀ d ∈ List.ofFn decrease, 0 ≤ d := by
    intro d hd
    rw [List.mem_ofFn] at hd
    obtain ⟨i, rfl⟩ := hd
    exact hnonnegative i
  unfold directionalIntervalPathHarmony pathHarmony directionalDrops
  rw [directionalDropsFrom_profileFromDecreases_of_nonnegative
      1 (List.ofFn decrease) hlistNonnegative,
    profileFromDecreases_sum_eq, weightedSlopeSum_ofFn]
  simp only [List.length_ofFn, List.map_ofFn, List.sum_ofFn,
    Function.comp_apply]
  unfold powerReducedObjective powerPathWeight absoluteIntervalWeight
  unfold powerPenalty
  simp only [Real.rpow_eq_pow]
  rw [Finset.sum_sub_distrib]
  have hedge : (∑ i : Fin N, h * decrease i ^ p) =
      h * ∑ i : Fin N, decrease i ^ p := by
    exact (Finset.mul_sum _ _ _).symm
  have hsite : (∑ i : Fin N,
      m * ((N - i.1 : ℕ) : ℝ) * decrease i) =
      m * ∑ i : Fin N, ((N : ℝ) - (i.1 : ℝ)) * decrease i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Nat.cast_sub (Nat.le_of_lt i.2)]
    ring
  rw [hedge, hsite]
  ring

/-- KKT uniqueness for the reduced directional objective transfers exactly
to the declared list-valued path Harmony. -/
theorem directionalPath_uniqueMinimizer_of_reduced
    {h m p : ℝ} {N : ℕ} {winner : Fin N → ℝ}
    (hreduced : IsUniqueMinimizerOn
      (SolidSimplex : (Fin N → ℝ) → Prop)
      (powerReducedObjective h m p (powerPathWeight N)) winner) :
    IsUniqueMinimizerOn (SolidSimplex : (Fin N → ℝ) → Prop)
      (directionalIntervalPathHarmony h m p) winner := by
  refine ⟨hreduced.1, ?_⟩
  intro decrease hdecrease
  have hcomparison := hreduced.2 decrease hdecrease
  have hwinnerNonnegative := hreduced.1.1
  constructor
  · rw [directionalIntervalPathHarmony_eq_reduced h m p winner
        hwinnerNonnegative,
      directionalIntervalPathHarmony_eq_reduced h m p decrease
        hdecrease.1]
    exact add_le_add_right hcomparison.1 _
  · intro heq
    exact hcomparison.2 (by
      rw [directionalIntervalPathHarmony_eq_reduced h m p winner
          hwinnerNonnegative,
        directionalIntervalPathHarmony_eq_reduced h m p decrease
          hdecrease.1] at heq
      linarith)

/-- Activity after the first `i` decreases, reconstructed from a finite
decrease vector.  Natural `i = 0` is the trigger and `i = N` is the terminal
follower. -/
noncomputable def directionalReconstructedActivity
    {N : ℕ} (decrease : Fin N → ℝ) (i : ℕ) : ℝ :=
  1 - ∑ j : Fin N, if j.1 < i then decrease j else 0

theorem directionalReconstructedActivity_eq_mass_tail
    {N i : ℕ} (decrease : Fin N → ℝ) :
    directionalReconstructedActivity decrease i =
      1 - (∑ j : Fin N, decrease j) +
        powerProfileFromDecreases decrease i := by
  classical
  unfold directionalReconstructedActivity powerProfileFromDecreases
  have hpartition :
      (∑ j : Fin N, decrease j) =
        (∑ j : Fin N, if j.1 < i then decrease j else 0) +
          ∑ j : Fin N, if i ≤ j.1 then decrease j else 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hji : j.1 < i
    · simp [hji, Nat.not_le_of_lt hji]
    · have hij : i ≤ j.1 := Nat.le_of_not_gt hji
      simp [hji, hij]
  linarith

/-- If the solid-simplex budget is not exhausted, every reconstructed
follower remains strictly positive. -/
theorem directionalReconstructedActivity_positive_of_mass_lt_one
    {N i : ℕ} (decrease : Fin N → ℝ)
    (hnonnegative : ∀ j, 0 ≤ decrease j)
    (hmass : (∑ j : Fin N, decrease j) < 1) :
    0 < directionalReconstructedActivity decrease i := by
  rw [directionalReconstructedActivity_eq_mass_tail]
  have htail : 0 ≤ powerProfileFromDecreases decrease i := by
    unfold powerProfileFromDecreases
    apply Finset.sum_nonneg
    intro j _
    split_ifs
    · exact hnonnegative j
    · exact le_rfl
  linarith

/-- At unit total mass, the reconstructed activity is exactly the optimizer
tail profile used by the general-power first-zero theorem. -/
theorem directionalReconstructedActivity_eq_tail_of_mass_one
    {N i : ℕ} (decrease : Fin N → ℝ)
    (hmass : (∑ j : Fin N, decrease j) = 1) :
    directionalReconstructedActivity decrease i =
      powerProfileFromDecreases decrease i := by
  rw [directionalReconstructedActivity_eq_mass_tail, hmass]
  ring

/-- Every horizon strictly before the first-zero cell has the zero-multiplier
unique optimizer, and all its reconstructed followers are positive. -/
theorem directional_before_firstZero_unique_and_positive
    {h m p : ℝ} {K N : ℕ}
    (hcell : GeneralPowerFirstZeroCell h m p K) (hNK : N < K) :
    IsUniqueMinimizerOn (SolidSimplex : (Fin N → ℝ) → Prop)
      (directionalIntervalPathHarmony h m p)
      (powerPathDecrease h m p 0 N) ∧
    ∀ i : ℕ, 0 < directionalReconstructedActivity
      (powerPathDecrease h m p 0 N) i := by
  rcases hcell with ⟨hK, hh, hm, hp, hprevious, hboundary⟩
  have hNle : N ≤ K - 1 := by omega
  have hmassLe : powerPathMass h m p 0 N ≤
      powerPathMass h m p 0 (K - 1) := by
    rw [powerPathMass_zero_eq_shiftedSum N hh hm hp,
      powerPathMass_zero_eq_shiftedSum (K - 1) hh hm hp]
    exact powerPathShiftedSum_monotone hh hm hp hNle
  have hmassLt : powerPathMass h m p 0 N < 1 :=
    lt_of_le_of_lt hmassLe hprevious
  have hreduced : IsUniqueMinimizerOn
      (SolidSimplex : (Fin N → ℝ) → Prop)
      (powerReducedObjective h m p (powerPathWeight N))
      (powerPathDecrease h m p 0 N) := by
    apply powerKKTDecrease_zero_unique_minimizer (powerPathWeight N) hh hp
    simpa [powerPathMass] using hmassLt.le
  refine ⟨directionalPath_uniqueMinimizer_of_reduced hreduced, ?_⟩
  intro i
  apply directionalReconstructedActivity_positive_of_mass_lt_one
  · exact fun j => powerKKTDecrease_nonnegative (powerPathWeight N) hh hp j
  · simpa only [powerPathMass, powerKKTMass, powerPathDecrease] using hmassLt

/-- At and beyond the first-zero horizon, the unique declared directional
winner has positive reconstructed activity exactly before `K`. -/
theorem directional_atOrAfter_firstZero_unique_and_support
    {h m p : ℝ} {K N : ℕ}
    (hcell : GeneralPowerFirstZeroCell h m p K) (hKN : K ≤ N) :
    ∃ eta : ℝ,
      IsUniqueMinimizerOn (SolidSimplex : (Fin N → ℝ) → Prop)
        (directionalIntervalPathHarmony h m p)
        (powerPathDecrease h m p eta N) ∧
      ∀ i : ℕ,
        0 < directionalReconstructedActivity
          (powerPathDecrease h m p eta N) i ↔ i < K := by
  obtain ⟨boundaryEta, etaNonnegative, _etaBelowM, etaMass,
      _boundaryUnique, _boundarySupport, extensions⟩ :=
    generalPower_all_horizon_finite_persistence hcell
  obtain ⟨R, rfl⟩ := Nat.exists_eq_add_of_le hKN
  let eta := boundaryEta + m * (R : ℝ)
  have cellData := hcell
  rcases cellData with ⟨_hK, hh, hm, hp, _hprevious, _hboundary⟩
  have hmass : powerPathMass h m p eta (K + R) = 1 := by
    dsimp [eta]
    rw [powerPathMass_extension R hh hm hp etaNonnegative, etaMass]
  refine ⟨eta,
    directionalPath_uniqueMinimizer_of_reduced (extensions R).1,
    ?_⟩
  intro i
  have hmassSum :
      (∑ j : Fin (K + R), powerPathDecrease h m p eta (K + R) j) = 1 := by
    simpa only [powerPathMass, powerKKTMass, powerPathDecrease] using hmass
  rw [directionalReconstructedActivity_eq_tail_of_mass_one
    (i := i) _ hmassSum]
  exact generalPower_all_horizon_exact_first_zero
    hcell etaNonnegative etaMass R i

/-- Analytic directional maximum-gap law.  A gap of `L` edges has `L-1`
free followers because its right trigger is inert.  Their unique winner is
all-positive exactly when `L ≤ K`. -/
theorem directional_maximumGap_support_law
    {h m p : ℝ} {K L : ℕ}
    (hcell : GeneralPowerFirstZeroCell h m p K) (hL : 0 < L) :
    (L ≤ K ↔
      ∃ winner : Fin (L - 1) → ℝ,
        IsUniqueMinimizerOn (SolidSimplex : (Fin (L - 1) → ℝ) → Prop)
          (directionalIntervalPathHarmony h m p) winner ∧
        ∀ i, 0 < directionalReconstructedActivity winner i) := by
  constructor
  · intro hLK
    have hbefore : L - 1 < K := by omega
    refine ⟨powerPathDecrease h m p 0 (L - 1), ?_⟩
    exact directional_before_firstZero_unique_and_positive hcell hbefore
  · rintro ⟨winner, hunique, hallPositive⟩
    by_contra hnot
    have hKL : K ≤ L - 1 := by omega
    obtain ⟨eta, hcanonicalUnique, hsupport⟩ :=
      directional_atOrAfter_firstZero_unique_and_support hcell hKL
    have hwinnerEq : winner = powerPathDecrease h m p eta (L - 1) := by
      have hcanonicalToWinner := hcanonicalUnique.2 winner hunique.1
      have hwinnerToCanonical := hunique.2 _ hcanonicalUnique.1
      exact hcanonicalToWinner.2
        (le_antisymm hwinnerToCanonical.1 hcanonicalToWinner.1)
    have hnotPositive : ¬ 0 < directionalReconstructedActivity
        (powerPathDecrease h m p eta (L - 1)) K := by
      intro hpositive
      exact (Nat.lt_irrefl K) ((hsupport K).mp hpositive)
    rw [← hwinnerEq] at hnotPositive
    exact hnotPositive (hallPositive K)

/-! ## Reach--phase coordinate and absolute critical mass -/

/-- The optimizer phase sum and the contextual shifted sum are the same
finite sum after the change of coordinate `u = 1 - tau`. -/
theorem phaseShiftedPowerSum_eq_context
    (q tau : ℝ) (K : ℕ) :
    PhonologicalCalculus.ContinuousHG.shiftedPowerSum q tau K =
      PhonologicalCalculus.Context.shiftedPowerSum K q (1 - tau) := by
  unfold PhonologicalCalculus.ContinuousHG.shiftedPowerSum
    PhonologicalCalculus.Context.shiftedPowerSum
  apply Finset.sum_congr rfl
  intro r _
  congr 1
  push_cast
  ring

/-- Every directional first-zero cell has one and only one within-cell
coordinate `u ∈ (0,1]`, with the exact reach--phase equation used by the
two-trigger calculation. -/
theorem exists_unique_contextPhase_of_firstZeroCell
    {h m p : ℝ} {K : ℕ} (hcell : GeneralPowerFirstZeroCell h m p K) :
    ∃! u : ℝ,
      u ∈ Ioc (0 : ℝ) 1 ∧
      PhonologicalCalculus.Context.shiftedPowerSum K
          (powerShiftExponent p) u =
        (p * (h / m)) ^ powerShiftExponent p := by
  obtain ⟨tau, htau, htauUnique⟩ :=
    exists_unique_phaseOffset_of_firstZeroCell hcell
  let u := 1 - tau
  have hu : u ∈ Ioc (0 : ℝ) 1 := by
    constructor <;> dsimp [u] <;> linarith [htau.1.1, htau.1.2]
  have hequation : PhonologicalCalculus.Context.shiftedPowerSum K
      (powerShiftExponent p) u =
        (p * (h / m)) ^ powerShiftExponent p := by
    rw [← phaseShiftedPowerSum_eq_context]
    exact htau.2
  refine ⟨u, ⟨hu, hequation⟩, ?_⟩
  intro v hv
  have honeMinusV : 1 - v ∈ Ico (0 : ℝ) 1 := by
    constructor <;> linarith [hv.1.1, hv.1.2]
  have hphaseV : PhonologicalCalculus.ContinuousHG.shiftedPowerSum
      (powerShiftExponent p) (1 - v) K =
        (p * (h / m)) ^ powerShiftExponent p := by
    rw [phaseShiftedPowerSum_eq_context]
    simpa using hv.2
  have htauEq : 1 - v = tau := htauUnique (1 - v) ⟨honeMinusV, hphaseV⟩
  dsimp [u]
  linarith

/-- Ascending positive centered loads in an `L`-edge reflected interval.
The parity branch is merely a closed finite enumeration of the positive
entries of `L-1-2i`. -/
noncomputable def absoluteCriticalMass (L : ℕ) (q : ℝ) : ℝ :=
  ∑ r ∈ Finset.range (L / 2),
    (((2 * r + if Even L then 1 else 2 : ℕ) : ℝ) ^ q)

theorem absoluteCriticalMass_before
    {K : ℕ} {q : ℝ} (hK : 0 < K) (hq : 0 < q) :
    absoluteCriticalMass (2 * K - 1) q =
      (2 : ℝ) ^ q *
        PhonologicalCalculus.Context.shiftedPowerSum K q 0 := by
  have hodd : ¬ Even (2 * K - 1) := by
    rintro ⟨r, hr⟩
    omega
  have hhalf : (2 * K - 1) / 2 = K - 1 := by
    have hid : 2 * K - 1 = 2 * (K - 1) + 1 := by omega
    rw [hid, Nat.mul_add_div (by norm_num : 0 < 2)]
    norm_num
  unfold absoluteCriticalMass
  rw [if_neg hodd, hhalf]
  have hfactor :
      (∑ r ∈ Finset.range (K - 1), (((2 * r + 2 : ℕ) : ℝ) ^ q)) =
        (2 : ℝ) ^ q *
          ∑ r ∈ Finset.range (K - 1), ((((r + 1 : ℕ) : ℝ)) ^ q) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    rw [show (2 * r + 2 : ℕ) = 2 * (r + 1) by omega,
      Nat.cast_mul]
    change ((2 : ℝ) * ((r + 1 : ℕ) : ℝ)) ^ q =
      (2 : ℝ) ^ q * (((r + 1 : ℕ) : ℝ) ^ q)
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2)
      (Nat.cast_nonneg (r + 1))]
  rw [hfactor]
  congr 1
  unfold PhonologicalCalculus.Context.shiftedPowerSum
  have hKid : K - 1 + 1 = K := Nat.sub_add_cancel hK
  rw [← hKid, Finset.sum_range_succ']
  simp [Real.rpow_eq_pow, Real.zero_rpow hq.ne']

theorem absoluteCriticalMass_middle
    {K : ℕ} {q : ℝ} (_hq : 0 < q) :
    absoluteCriticalMass (2 * K) q =
      (2 : ℝ) ^ q *
        PhonologicalCalculus.Context.shiftedPowerSum K q (1 / 2) := by
  have heven : Even (2 * K) := ⟨K, by omega⟩
  have hhalf : (2 * K) / 2 = K := by omega
  unfold absoluteCriticalMass
  rw [if_pos heven, hhalf]
  unfold PhonologicalCalculus.Context.shiftedPowerSum
  simp only [Real.rpow_eq_pow]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  have hbase : (0 : ℝ) ≤ (r : ℝ) + 1 / 2 := by positivity
  have hbaseIdentity : (((2 * r + 1 : ℕ) : ℕ) : ℝ) =
      (2 : ℝ) * ((r : ℝ) + 1 / 2) := by
    push_cast
    ring
  rw [hbaseIdentity,
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hbase]

theorem absoluteCriticalMass_after
    {K : ℕ} {q : ℝ} (_hq : 0 < q) :
    absoluteCriticalMass (2 * K + 1) q =
      (2 : ℝ) ^ q *
        PhonologicalCalculus.Context.shiftedPowerSum K q 1 := by
  have hodd : ¬ Even (2 * K + 1) := by
    rintro ⟨r, hr⟩
    omega
  have hhalf : (2 * K + 1) / 2 = K := by
    rw [Nat.mul_add_div (by norm_num : 0 < 2)]
    norm_num
  unfold absoluteCriticalMass
  rw [if_neg hodd, hhalf]
  unfold PhonologicalCalculus.Context.shiftedPowerSum
  simp only [Real.rpow_eq_pow]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  have hbase : (0 : ℝ) ≤ (r : ℝ) + 1 := by positivity
  rw [show (2 * r + 2 : ℕ) = 2 * (r + 1) by omega,
    Nat.cast_mul]
  change ((2 : ℝ) * ((r + 1 : ℕ) : ℝ)) ^ q =
    (2 : ℝ) ^ q * (((r : ℝ) + 1) ^ q)
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2)
    (Nat.cast_nonneg (r + 1))]
  congr 1
  push_cast
  ring

/-- Canonical embedding of the positive half of a reflected edge interval. -/
def absoluteHalfEdgeIndex {L : ℕ} (r : Fin (L / 2)) : Fin L :=
  ⟨r.1, lt_of_lt_of_le r.2 (Nat.div_le_self L 2)⟩

theorem absoluteIntervalCentered_pos_of_lt_half
    {L : ℕ} (i : Fin L) (hi : i.1 < L / 2) :
    0 < absoluteIntervalCentered L i := by
  unfold absoluteIntervalCentered
  have hnat : 2 * i.1 + 1 < L := by omega
  have hreal : 2 * (i.1 : ℝ) + 1 < (L : ℝ) := by exact_mod_cast hnat
  linarith

theorem absoluteIntervalCentered_nonpos_of_half_le
    {L : ℕ} (i : Fin L) (hi : L / 2 ≤ i.1) :
    absoluteIntervalCentered L i ≤ 0 := by
  unfold absoluteIntervalCentered
  have hnat : L ≤ 2 * i.1 + 1 := by omega
  have hreal : (L : ℝ) ≤ 2 * (i.1 : ℝ) + 1 := by exact_mod_cast hnat
  linarith

theorem absoluteIntervalFreeSlope_pos_of_lt_half
    {h m p : ℝ} {L : ℕ} (hh : 0 < h) (hm : 0 < m) (hp : 1 < p)
    (i : Fin L) (hi : i.1 < L / 2) :
    0 < absoluteIntervalFreeSlope h m p L i := by
  have hcenter := absoluteIntervalCentered_pos_of_lt_half i hi
  have hscale : 0 < m / (2 * p * h) := by
    have hp0 : 0 < p := lt_trans zero_lt_one hp
    positivity
  unfold absoluteIntervalFreeSlope signedPowerResponse
  rw [Real.sign_of_pos hcenter, one_mul, abs_of_pos hcenter]
  exact Real.rpow_pos_of_pos (mul_pos hscale hcenter) _

theorem absoluteIntervalFreeSlope_nonpos_of_half_le
    {h m p : ℝ} {L : ℕ} (hh : 0 < h) (hm : 0 < m) (hp : 1 < p)
    (i : Fin L) (hi : L / 2 ≤ i.1) :
    absoluteIntervalFreeSlope h m p L i ≤ 0 := by
  have hcenter := absoluteIntervalCentered_nonpos_of_half_le i hi
  rcases hcenter.eq_or_lt with hzero | hnegative
  · unfold absoluteIntervalFreeSlope signedPowerResponse
    rw [hzero, Real.sign_zero, zero_mul]
  · have hscale : 0 < m / (2 * p * h) := by
      have hp0 : 0 < p := lt_trans zero_lt_one hp
      positivity
    unfold absoluteIntervalFreeSlope signedPowerResponse
    rw [Real.sign_of_neg hnegative, neg_one_mul]
    exact neg_nonpos.mpr (Real.rpow_nonneg
      (mul_nonneg hscale.le (abs_nonneg _)) _)

/-- The actual free depth is the sum of the initial positive slopes. -/
noncomputable def absoluteIntervalFreeDepth
    (h m p : ℝ) (L : ℕ) : ℝ :=
  ∑ r ∈ Finset.range (L / 2),
    signedPowerResponse p (m / (2 * p * h))
      ((L : ℝ) - 1 - 2 * (r : ℝ))

theorem absoluteIntervalFreeDepth_term_eq_slope
    (h m p : ℝ) {L r : ℕ} (hr : r < L / 2) :
    signedPowerResponse p (m / (2 * p * h))
        ((L : ℝ) - 1 - 2 * (r : ℝ)) =
      absoluteIntervalFreeSlope h m p L
        (absoluteHalfEdgeIndex ⟨r, hr⟩) := by
  rfl

/-- The same centered positive-load sum, before multiplication by the
grammar scale. -/
noncomputable def absoluteCenteredMass (L : ℕ) (q : ℝ) : ℝ :=
  ∑ r ∈ Finset.range (L / 2),
    (((L : ℝ) - 1 - 2 * (r : ℝ)) ^ q)

theorem absoluteIntervalFreeDepth_eq_centeredMass
    {h m p : ℝ} (L : ℕ) (hh : 0 < h) (hm : 0 < m) (hp : 1 < p) :
    absoluteIntervalFreeDepth h m p L =
      (m / (2 * p * h)) ^ powerShiftExponent p *
        absoluteCenteredMass L (powerShiftExponent p) := by
  classical
  let scale : ℝ := m / (2 * p * h)
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hscale : 0 < scale := by dsimp [scale]; positivity
  unfold absoluteIntervalFreeDepth absoluteCenteredMass
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  have hrHalf : r < L / 2 := Finset.mem_range.mp hr
  have hnat : 2 * r + 1 < L := by omega
  have hcenter : 0 < (L : ℝ) - 1 - 2 * (r : ℝ) := by
    have hreal : 2 * (r : ℝ) + 1 < (L : ℝ) := by exact_mod_cast hnat
    linarith
  have hcenterNonnegative : 0 ≤ (L : ℝ) - 1 - 2 * (r : ℝ) := hcenter.le
  change signedPowerResponse p scale ((L : ℝ) - 1 - 2 * (r : ℝ)) =
    scale ^ powerShiftExponent p *
      (((L : ℝ) - 1 - 2 * (r : ℝ)) ^ powerShiftExponent p)
  rw [signedPowerResponse, Real.sign_of_pos hcenter, one_mul,
    abs_of_pos hcenter,
    Real.mul_rpow hscale.le hcenterNonnegative]

/-- The descending centered-load enumeration and the ascending parity
enumeration are exactly the same finite multiset. -/
theorem absoluteCenteredMass_eq_criticalMass
    (L : ℕ) (q : ℝ) :
    absoluteCenteredMass L q = absoluteCriticalMass L q := by
  rcases L.even_or_odd' with ⟨K, hEven | hOdd⟩
  · subst L
    have heven : Even (2 * K) := ⟨K, by omega⟩
    have hhalf : (2 * K) / 2 = K := by omega
    unfold absoluteCenteredMass absoluteCriticalMass
    rw [if_pos heven, hhalf]
    rw [← Finset.sum_range_reflect
      (fun r : ℕ => (((2 * r + 1 : ℕ) : ℝ) ^ q)) K]
    apply Finset.sum_congr rfl
    intro r hr
    have hrK : r < K := Finset.mem_range.mp hr
    congr 1
    have hcast : (((K - 1 - r : ℕ) : ℕ) : ℝ) =
        (K : ℝ) - 1 - (r : ℝ) := by
      rw [Nat.cast_sub (by omega : r ≤ K - 1),
        Nat.cast_sub (by omega : 1 ≤ K)]
      norm_num
    push_cast
    rw [hcast]
    ring
  · subst L
    have hnotEven : ¬ Even (2 * K + 1) := by
      rintro ⟨r, hr⟩
      omega
    have hhalf : (2 * K + 1) / 2 = K := by
      rw [Nat.mul_add_div (by norm_num : 0 < 2)]
      norm_num
    unfold absoluteCenteredMass absoluteCriticalMass
    rw [if_neg hnotEven, hhalf]
    rw [← Finset.sum_range_reflect
      (fun r : ℕ => (((2 * r + 2 : ℕ) : ℝ) ^ q)) K]
    apply Finset.sum_congr rfl
    intro r hr
    have hrK : r < K := Finset.mem_range.mp hr
    congr 1
    have hcast : (((K - 1 - r : ℕ) : ℕ) : ℝ) =
        (K : ℝ) - 1 - (r : ℝ) := by
      rw [Nat.cast_sub (by omega : r ≤ K - 1),
        Nat.cast_sub (by omega : 1 ≤ K)]
      norm_num
    push_cast
    rw [hcast]
    ring

theorem absoluteIntervalFreeDepth_eq_criticalMass
    {h m p : ℝ} (L : ℕ) (hh : 0 < h) (hm : 0 < m) (hp : 1 < p) :
    absoluteIntervalFreeDepth h m p L =
      (m / (2 * p * h)) ^ powerShiftExponent p *
        absoluteCriticalMass L (powerShiftExponent p) := by
  rw [absoluteIntervalFreeDepth_eq_centeredMass L hh hm hp,
    absoluteCenteredMass_eq_criticalMass]

/-! ## Prefix geometry and the lower-obstacle support criterion -/

/-- Signed decrease accumulated at a vertex of an `L`-edge interval. -/
noncomputable def absoluteSlopePrefix {L : ℕ} (slope : Fin L → ℝ)
    (vertex : Fin (L + 1)) : ℝ :=
  ∑ i : Fin L, if i.1 < vertex.1 then slope i else 0

/-- Equal endpoints and the phonological box `0 ≤ x ≤ 1`, expressed in
signed-decrease coordinates.  Since `x = 1 - prefix`, the prefix itself
lies in `[0,1]`. -/
def AbsoluteIntervalBox {L : ℕ} (slope : Fin L → ℝ) : Prop :=
  (∑ i, slope i) = 0 ∧
    ∀ vertex : Fin (L + 1),
      0 ≤ absoluteSlopePrefix slope vertex ∧
        absoluteSlopePrefix slope vertex ≤ 1

/-- Every vertex of the reconstructed interval is strictly positive. -/
def AbsoluteIntervalAllPositive {L : ℕ} (slope : Fin L → ℝ) : Prop :=
  ∀ vertex : Fin (L + 1), absoluteSlopePrefix slope vertex < 1

/-- Some reconstructed vertex reaches the lower activity obstacle exactly.
For a boxed path this is the logical complement of strict positivity. -/
def AbsoluteIntervalHasZero {L : ℕ} (slope : Fin L → ℝ) : Prop :=
  ∃ vertex : Fin (L + 1), absoluteSlopePrefix slope vertex = 1

theorem absoluteIntervalBox_hasZero_iff_not_allPositive
    {L : ℕ} {slope : Fin L → ℝ} (hbox : AbsoluteIntervalBox slope) :
    AbsoluteIntervalHasZero slope ↔ ¬ AbsoluteIntervalAllPositive slope := by
  classical
  constructor
  · rintro ⟨vertex, hzero⟩ hallPositive
    have := hallPositive vertex
    linarith
  · intro hnotPositive
    rw [AbsoluteIntervalAllPositive] at hnotPositive
    push Not at hnotPositive
    obtain ⟨vertex, hcontact⟩ := hnotPositive
    exact ⟨vertex, le_antisymm (hbox.2 vertex).2 hcontact⟩

/-- The central vertex after the positive half of the reflected slope
sequence. -/
def absoluteHalfVertex (L : ℕ) : Fin (L + 1) :=
  ⟨L / 2, by omega⟩

theorem absoluteSlopePrefix_half_eq_freeDepth
    (h m p : ℝ) (L : ℕ) :
    absoluteSlopePrefix (absoluteIntervalFreeSlope h m p L)
        (absoluteHalfVertex L) =
      absoluteIntervalFreeDepth h m p L := by
  unfold absoluteSlopePrefix absoluteHalfVertex absoluteIntervalFreeDepth
  let f : ℕ → ℝ := fun r =>
    signedPowerResponse p (m / (2 * p * h))
      ((L : ℝ) - 1 - 2 * (r : ℝ))
  calc
    (∑ i : Fin L,
        if i.1 < L / 2 then
          absoluteIntervalFreeSlope h m p L i else 0) =
        ∑ r ∈ Finset.range L,
          if r < L / 2 then f r else 0 := by
      simpa [f, absoluteIntervalFreeSlope, absoluteIntervalCentered] using
        (Fin.sum_univ_eq_sum_range
          (fun r : ℕ => if r < L / 2 then f r else 0) L)
    _ = ∑ r ∈ Finset.range (L / 2), f r := by
      symm
      calc
        (∑ r ∈ Finset.range (L / 2), f r) =
        ∑ r ∈ Finset.range (L / 2),
          if r < L / 2 then f r else 0 := by
          apply Finset.sum_congr rfl
          intro r hr
          rw [if_pos (Finset.mem_range.mp hr)]
        _ = ∑ r ∈ Finset.range L,
            if r < L / 2 then f r else 0 := by
          apply Finset.sum_subset (Finset.range_mono (Nat.div_le_self L 2))
          intro r hrL hrHalf
          rw [if_neg]
          exact fun hr => hrHalf (Finset.mem_range.mpr hr)

/-- Prefixes of the reflected free path never exceed the central depth and
never become negative.  This is the exact finite path-geometry fact needed
to turn the scalar depth into the box-obstacle criterion. -/
theorem absoluteIntervalFreeSlope_prefix_bounds
    {h m p : ℝ} (L : ℕ) (hh : 0 < h) (hm : 0 < m) (hp : 1 < p)
    (vertex : Fin (L + 1)) :
    0 ≤ absoluteSlopePrefix (absoluteIntervalFreeSlope h m p L) vertex ∧
      absoluteSlopePrefix (absoluteIntervalFreeSlope h m p L) vertex ≤
        absoluteIntervalFreeDepth h m p L := by
  classical
  let slope := absoluteIntervalFreeSlope h m p L
  have htotal : ∑ i : Fin L, slope i = 0 :=
    absoluteIntervalFreeSlope_sum_zero h m p L
  have hdepth :
      (∑ i : Fin L, if i.1 < L / 2 then slope i else 0) =
        absoluteIntervalFreeDepth h m p L := by
    rw [← absoluteSlopePrefix_half_eq_freeDepth h m p L]
    rfl
  unfold absoluteSlopePrefix
  change 0 ≤ ∑ i : Fin L, (if i.1 < vertex.1 then slope i else 0) ∧
    (∑ i : Fin L, if i.1 < vertex.1 then slope i else 0) ≤
      absoluteIntervalFreeDepth h m p L
  have hprefixLe :
      (∑ i : Fin L, if i.1 < vertex.1 then slope i else 0) ≤
        ∑ i : Fin L, if i.1 < L / 2 then slope i else 0 := by
    apply Finset.sum_le_sum
    intro i _
    by_cases hiVertex : i.1 < vertex.1
    · rw [if_pos hiVertex]
      by_cases hiHalf : i.1 < L / 2
      · rw [if_pos hiHalf]
      · rw [if_neg hiHalf]
        exact absoluteIntervalFreeSlope_nonpos_of_half_le hh hm hp i
          (Nat.le_of_not_gt hiHalf)
    · rw [if_neg hiVertex]
      split_ifs with hiHalf
      · exact (absoluteIntervalFreeSlope_pos_of_lt_half hh hm hp i hiHalf).le
      · exact le_rfl
  by_cases hbefore : vertex.1 ≤ L / 2
  · have hprefixNonnegative :
        0 ≤ ∑ i : Fin L, if i.1 < vertex.1 then slope i else 0 := by
      apply Finset.sum_nonneg
      intro i _
      split_ifs with hiVertex
      · exact (absoluteIntervalFreeSlope_pos_of_lt_half hh hm hp i
          (lt_of_lt_of_le hiVertex hbefore)).le
      · exact le_rfl
    exact ⟨hprefixNonnegative, by simpa [hdepth] using hprefixLe⟩
  · have hhalfVertex : L / 2 ≤ vertex.1 := Nat.le_of_not_ge hbefore
    have htailNonpositive :
        ∑ i : Fin L, (if vertex.1 ≤ i.1 then slope i else 0) ≤ 0 := by
      apply Finset.sum_nonpos
      intro i _
      split_ifs with hiTail
      · exact absoluteIntervalFreeSlope_nonpos_of_half_le hh hm hp i
          (hhalfVertex.trans hiTail)
      · exact le_rfl
    have hprefixPlusTail :
        (∑ i : Fin L, if i.1 < vertex.1 then slope i else 0) +
          ∑ i : Fin L, (if vertex.1 ≤ i.1 then slope i else 0) = 0 := by
      calc
        (∑ i : Fin L, if i.1 < vertex.1 then slope i else 0) +
            ∑ i : Fin L, (if vertex.1 ≤ i.1 then slope i else 0) =
            ∑ i : Fin L, slope i := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i _
          by_cases hi : i.1 < vertex.1
          · simp [hi, Nat.not_le_of_lt hi]
          · have hi' : vertex.1 ≤ i.1 := Nat.le_of_not_gt hi
            simp [hi, hi']
        _ = 0 := htotal
    constructor
    · linarith
    · simpa [hdepth] using hprefixLe

theorem absoluteIntervalFreeSlope_box_of_depth_le_one
    {h m p : ℝ} (L : ℕ) (hh : 0 < h) (hm : 0 < m) (hp : 1 < p)
    (hdepth : absoluteIntervalFreeDepth h m p L ≤ 1) :
    AbsoluteIntervalBox (absoluteIntervalFreeSlope h m p L) := by
  refine ⟨absoluteIntervalFreeSlope_sum_zero h m p L, ?_⟩
  intro vertex
  have hb := absoluteIntervalFreeSlope_prefix_bounds L hh hm hp vertex
  exact ⟨hb.1, hb.2.trans hdepth⟩

theorem absoluteIntervalFreeSlope_allPositive_iff_depth_lt_one
    {h m p : ℝ} (L : ℕ) (hh : 0 < h) (hm : 0 < m) (hp : 1 < p) :
    AbsoluteIntervalAllPositive (absoluteIntervalFreeSlope h m p L) ↔
      absoluteIntervalFreeDepth h m p L < 1 := by
  constructor
  · intro hall
    rw [← absoluteSlopePrefix_half_eq_freeDepth h m p L]
    exact hall (absoluteHalfVertex L)
  · intro hdepth vertex
    exact (absoluteIntervalFreeSlope_prefix_bounds L hh hm hp vertex).2.trans_lt
      hdepth

/-- When the free path does not cross the lower obstacle, it is the unique
winner of the actual boxed interval objective. -/
theorem absoluteIntervalFreeSlope_unique_box_minimizer_of_depth_le_one
    {h m p : ℝ} (L : ℕ) (hh : 0 < h) (hm : 0 < m) (hp : 1 < p)
    (hdepth : absoluteIntervalFreeDepth h m p L ≤ 1) :
    IsUniqueMinimizerOn (AbsoluteIntervalBox : (Fin L → ℝ) → Prop)
      (absoluteIntervalPathHarmony h m p)
      (absoluteIntervalFreeSlope h m p L) := by
  have hfree := absoluteIntervalPathHarmony_unique_minimizer L hh hm hp
  refine ⟨absoluteIntervalFreeSlope_box_of_depth_le_one L hh hm hp hdepth, ?_⟩
  intro slope hslope
  exact hfree.2 slope hslope.1

/-! ## Convex descent from an interior boxed path -/

/-- Convexity of the absolute real-power edge penalty on the whole real
line, written in the two-weight form used by the finite path objective. -/
theorem absolutePowerPenalty_convexCombination
    {p a b x y : ℝ} (hp : 1 ≤ p) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) :
    absolutePowerPenalty p (a * x + b * y) ≤
      a * absolutePowerPenalty p x + b * absolutePowerPenalty p y := by
  have habs : |a * x + b * y| ≤ a * |x| + b * |y| := by
    calc
      |a * x + b * y| ≤ |a * x| + |b * y| := abs_add_le _ _
      _ = a * |x| + b * |y| := by
        rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
  have hbaseNonnegative : 0 ≤ a * |x| + b * |y| := by positivity
  have hmono : |a * x + b * y| ^ p ≤
      (a * |x| + b * |y|) ^ p :=
    Real.rpow_le_rpow (abs_nonneg _) habs (zero_le_one.trans hp)
  have hconvex := (convexOn_rpow hp).2 (abs_nonneg x) (abs_nonneg y)
    ha hb hab
  unfold absolutePowerPenalty
  calc
    |a * x + b * y| ^ p ≤ (a * |x| + b * |y|) ^ p := hmono
    _ ≤ a * |x| ^ p + b * |y| ^ p := by simpa using hconvex

/-- The finite signed-slope objective is convex along every segment. -/
theorem absoluteSlopeObjective_convexCombination
    {ι : Type*} [Fintype ι]
    {h m p a b : ℝ} (weight d u : ι → ℝ)
    (hh : 0 ≤ h) (hp : 1 ≤ p) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) :
    absoluteSlopeObjective h m p weight
        (fun i => a * d i + b * u i) ≤
      a * absoluteSlopeObjective h m p weight d +
        b * absoluteSlopeObjective h m p weight u := by
  classical
  unfold absoluteSlopeObjective
  calc
    (∑ i, (h * absolutePowerPenalty p (a * d i + b * u i) -
        m * weight i * (a * d i + b * u i))) ≤
      ∑ i, (a * (h * absolutePowerPenalty p (d i) -
          m * weight i * d i) +
        b * (h * absolutePowerPenalty p (u i) -
          m * weight i * u i)) := by
      apply Finset.sum_le_sum
      intro i _
      have hedge := mul_le_mul_of_nonneg_left
        (absolutePowerPenalty_convexCombination hp ha hb hab
          (x := d i) (y := u i)) hh
      linarith
    _ = a * (∑ i, (h * absolutePowerPenalty p (d i) -
          m * weight i * d i)) +
        b * (∑ i, (h * absolutePowerPenalty p (u i) -
          m * weight i * u i)) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

/-- Strict two-weight convexity of the absolute power penalty. -/
theorem absolutePowerPenalty_strictConvexCombination
    {p a b x y : ℝ} (hp : 1 < p) (ha : 0 < a) (hb : 0 < b)
    (hab : a + b = 1) (hxy : x ≠ y) :
    absolutePowerPenalty p (a * x + b * y) <
      a * absolutePowerPenalty p x + b * absolutePowerPenalty p y := by
  let z := a * x + b * y
  have hxz : x ≠ z := by
    intro hx
    apply hxy
    have haEq : a = 1 - b := by linarith
    have hzero : b * (y - x) = 0 := by
      dsimp [z] at hx
      rw [haEq] at hx
      nlinarith
    exact (sub_eq_zero.mp
      ((mul_eq_zero.mp hzero).resolve_left hb.ne')).symm
  have hyz : y ≠ z := by
    intro hy
    apply hxy
    have hbEq : b = 1 - a := by linarith
    have hzero : a * (x - y) = 0 := by
      dsimp [z] at hy
      rw [hbEq] at hy
      nlinarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left ha.ne')
  have hxSupport := (absolutePower_strict_tangent hp (u := z) (d := x))
  have hySupport := (absolutePower_strict_tangent hp (u := z) (d := y))
  have hxStrict :
      absolutePowerPenalty p z + absolutePowerSlope p z * (x - z) <
        absolutePowerPenalty p x :=
    lt_of_le_of_ne hxSupport.1 (fun heq => hxz (hxSupport.2 heq))
  have hyStrict :
      absolutePowerPenalty p z + absolutePowerSlope p z * (y - z) <
        absolutePowerPenalty p y :=
    lt_of_le_of_ne hySupport.1 (fun heq => hyz (hySupport.2 heq))
  have hxScaled := mul_lt_mul_of_pos_left hxStrict ha
  have hyScaled := mul_lt_mul_of_pos_left hyStrict hb
  change absolutePowerPenalty p z <
    a * absolutePowerPenalty p x + b * absolutePowerPenalty p y
  calc
    absolutePowerPenalty p z =
        a * (absolutePowerPenalty p z +
            absolutePowerSlope p z * (x - z)) +
          b * (absolutePowerPenalty p z +
            absolutePowerSlope p z * (y - z)) := by
      have hbEq : b = 1 - a := by linarith
      dsimp [z]
      rw [hbEq]
      ring
    _ < a * absolutePowerPenalty p x +
        b * absolutePowerPenalty p y := add_lt_add hxScaled hyScaled

/-- Strict midpoint convexity of the finite reduced objective. -/
theorem absoluteSlopeObjective_strict_midpoint
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {h m p : ℝ} (weight d u : ι → ℝ)
    (hh : 0 < h) (hp : 1 < p) (hdu : d ≠ u) :
    absoluteSlopeObjective h m p weight
        (fun i => (d i + u i) / 2) <
      (absoluteSlopeObjective h m p weight d +
        absoluteSlopeObjective h m p weight u) / 2 := by
  classical
  have hcoordinate : ∃ i, d i ≠ u i := by
    by_contra hnot
    apply hdu
    funext i
    exact not_ne_iff.mp (not_exists.mp hnot i)
  obtain ⟨different, hdifferent⟩ := hcoordinate
  unfold absoluteSlopeObjective
  have hpointwise (i : ι) :
      h * absolutePowerPenalty p ((d i + u i) / 2) -
          m * weight i * ((d i + u i) / 2) ≤
        ((h * absolutePowerPenalty p (d i) - m * weight i * d i) +
          (h * absolutePowerPenalty p (u i) - m * weight i * u i)) / 2 := by
    have hpenalty := absolutePowerPenalty_convexCombination hp.le
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
      (x := d i) (y := u i)
    have hscaled := mul_le_mul_of_nonneg_left hpenalty hh.le
    have hmid : (1 / 2 : ℝ) * d i + 1 / 2 * u i =
        (d i + u i) / 2 := by ring
    rw [hmid] at hscaled
    calc
      h * absolutePowerPenalty p ((d i + u i) / 2) -
          m * weight i * ((d i + u i) / 2) ≤
        h * (1 / 2 * absolutePowerPenalty p (d i) +
          1 / 2 * absolutePowerPenalty p (u i)) -
            m * weight i * ((d i + u i) / 2) :=
        sub_le_sub_right hscaled _
      _ = ((h * absolutePowerPenalty p (d i) - m * weight i * d i) +
          (h * absolutePowerPenalty p (u i) - m * weight i * u i)) / 2 := by
        ring
  have hstrict :
      h * absolutePowerPenalty p ((d different + u different) / 2) -
          m * weight different * ((d different + u different) / 2) <
        ((h * absolutePowerPenalty p (d different) -
            m * weight different * d different) +
          (h * absolutePowerPenalty p (u different) -
            m * weight different * u different)) / 2 := by
    have hpenalty := absolutePowerPenalty_strictConvexCombination hp
      (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (0 : ℝ) < 1 / 2)
      (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
      hdifferent
    have hscaled := mul_lt_mul_of_pos_left hpenalty hh
    have hmid : (1 / 2 : ℝ) * d different + 1 / 2 * u different =
        (d different + u different) / 2 := by ring
    rw [hmid] at hscaled
    calc
      h * absolutePowerPenalty p ((d different + u different) / 2) -
          m * weight different * ((d different + u different) / 2) <
        h * (1 / 2 * absolutePowerPenalty p (d different) +
          1 / 2 * absolutePowerPenalty p (u different)) -
            m * weight different * ((d different + u different) / 2) :=
        sub_lt_sub_right hscaled _
      _ = ((h * absolutePowerPenalty p (d different) -
            m * weight different * d different) +
          (h * absolutePowerPenalty p (u different) -
            m * weight different * u different)) / 2 := by
        ring
  have hsum :
      (∑ i, (h * absolutePowerPenalty p ((d i + u i) / 2) -
          m * weight i * ((d i + u i) / 2))) <
        ∑ i, (((h * absolutePowerPenalty p (d i) - m * weight i * d i) +
          (h * absolutePowerPenalty p (u i) - m * weight i * u i)) / 2) := by
    apply Finset.sum_lt_sum
    · intro i _
      exact hpointwise i
    · exact ⟨different, Finset.mem_univ _, hstrict⟩
  calc
    (∑ i, (h * absolutePowerPenalty p ((d i + u i) / 2) -
        m * weight i * ((d i + u i) / 2))) <
      ∑ i, (((h * absolutePowerPenalty p (d i) - m * weight i * d i) +
        (h * absolutePowerPenalty p (u i) - m * weight i * u i)) / 2) :=
      hsum
    _ = ((∑ i, (h * absolutePowerPenalty p (d i) -
          m * weight i * d i)) +
        ∑ i, (h * absolutePowerPenalty p (u i) -
          m * weight i * u i)) / 2 := by
      rw [← Finset.sum_div, Finset.sum_add_distrib]

/-- Prefix formation commutes with affine interpolation. -/
theorem absoluteSlopePrefix_affine
    {L : ℕ} (a b : ℝ) (d u : Fin L → ℝ) (vertex : Fin (L + 1)) :
    absoluteSlopePrefix (fun i => a * d i + b * u i) vertex =
      a * absoluteSlopePrefix d vertex +
        b * absoluteSlopePrefix u vertex := by
  unfold absoluteSlopePrefix
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i.1 < vertex.1 <;> simp [hi]

/-- Consecutive prefixes differ by exactly the intervening signed slope. -/
theorem absoluteSlopePrefix_succ
    {L : ℕ} (slope : Fin L → ℝ) (i : Fin L) :
    absoluteSlopePrefix slope ⟨i.1 + 1, by omega⟩ =
      absoluteSlopePrefix slope ⟨i.1, by omega⟩ + slope i := by
  classical
  unfold absoluteSlopePrefix
  calc
    (∑ j : Fin L, if j.1 < i.1 + 1 then slope j else 0) =
        ∑ j : Fin L,
          ((if j.1 < i.1 then slope j else 0) +
            if j = i then slope j else 0) := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hji : j = i
      · subst j
        simp
      · have hval : j.1 ≠ i.1 := by
          intro heq
          exact hji (Fin.ext heq)
        by_cases hjlt : j.1 < i.1
        · have hjltSucc : j.1 < i.1 + 1 := by omega
          simp [hji, hjlt, hjltSucc]
        · have hnotSucc : ¬ j.1 < i.1 + 1 := by omega
          simp [hji, hjlt, hnotSucc]
    _ = (∑ j : Fin L, if j.1 < i.1 then slope j else 0) +
        ∑ j : Fin L, if j = i then slope j else 0 :=
      Finset.sum_add_distrib
    _ = (∑ j : Fin L, if j.1 < i.1 then slope j else 0) + slope i := by
      congr 1
      simp

theorem continuous_absoluteSlopePrefix
    {L : ℕ} (vertex : Fin (L + 1)) :
    Continuous (fun slope : Fin L → ℝ =>
      absoluteSlopePrefix slope vertex) := by
  unfold absoluteSlopePrefix
  apply continuous_finsetSum
  intro i _
  by_cases hi : i.1 < vertex.1
  · simpa [hi] using (continuous_apply i :
      Continuous (fun slope : Fin L → ℝ => slope i))
  · simpa [hi] using (continuous_const :
      Continuous (fun _ : Fin L → ℝ => (0 : ℝ)))

theorem isClosed_absoluteIntervalBox (L : ℕ) :
    IsClosed {slope : Fin L → ℝ | AbsoluteIntervalBox slope} := by
  have hsumContinuous : Continuous (fun slope : Fin L → ℝ => ∑ i, slope i) := by
    apply continuous_finsetSum
    intro i _
    exact continuous_apply i
  have hmassClosed : IsClosed {slope : Fin L → ℝ | (∑ i, slope i) = 0} :=
    isClosed_eq hsumContinuous continuous_const
  have hprefixClosed : IsClosed {slope : Fin L → ℝ |
      ∀ vertex : Fin (L + 1),
        0 ≤ absoluteSlopePrefix slope vertex ∧
          absoluteSlopePrefix slope vertex ≤ 1} := by
    rw [show {slope : Fin L → ℝ |
        ∀ vertex : Fin (L + 1),
          0 ≤ absoluteSlopePrefix slope vertex ∧
            absoluteSlopePrefix slope vertex ≤ 1} =
        ⋂ vertex : Fin (L + 1),
          {slope : Fin L → ℝ |
            0 ≤ absoluteSlopePrefix slope vertex ∧
              absoluteSlopePrefix slope vertex ≤ 1} by
      ext slope
      simp]
    apply isClosed_iInter
    intro vertex
    exact (isClosed_le continuous_const
      (continuous_absoluteSlopePrefix vertex)).and
      (isClosed_le (continuous_absoluteSlopePrefix vertex) continuous_const)
  simpa [AbsoluteIntervalBox] using hmassClosed.and hprefixClosed

theorem absoluteIntervalBox_subset_slopeCube (L : ℕ) :
    {slope : Fin L → ℝ | AbsoluteIntervalBox slope} ⊆
      Set.Icc (fun _ : Fin L => (-1 : ℝ)) (fun _ => (1 : ℝ)) := by
  intro slope hslope
  change (∀ i, (-1 : ℝ) ≤ slope i) ∧ ∀ i, slope i ≤ 1
  constructor <;> intro i
  · have hleft := hslope.2 (⟨i.1, by omega⟩ : Fin (L + 1))
    have hright := hslope.2 (⟨i.1 + 1, by omega⟩ : Fin (L + 1))
    have hadjacent := absoluteSlopePrefix_succ slope i
    linarith
  · have hleft := hslope.2 (⟨i.1, by omega⟩ : Fin (L + 1))
    have hright := hslope.2 (⟨i.1 + 1, by omega⟩ : Fin (L + 1))
    have hadjacent := absoluteSlopePrefix_succ slope i
    linarith

theorem isCompact_absoluteIntervalBox (L : ℕ) :
    IsCompact {slope : Fin L → ℝ | AbsoluteIntervalBox slope} :=
  IsCompact.of_isClosed_subset isCompact_Icc
    (isClosed_absoluteIntervalBox L)
    (absoluteIntervalBox_subset_slopeCube L)

theorem absoluteIntervalBox_zero (L : ℕ) :
    AbsoluteIntervalBox (fun _ : Fin L => (0 : ℝ)) := by
  constructor
  · simp
  · intro vertex
    simp [absoluteSlopePrefix]

theorem absoluteIntervalBox_midpoint
    {L : ℕ} {d u : Fin L → ℝ}
    (hd : AbsoluteIntervalBox d) (hu : AbsoluteIntervalBox u) :
    AbsoluteIntervalBox (fun i => (d i + u i) / 2) := by
  constructor
  · rw [show (fun i => (d i + u i) / 2) =
        (fun i => (1 / 2 : ℝ) * d i + 1 / 2 * u i) by
      funext i
      ring]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      hd.1, hu.1]
    ring
  · intro vertex
    have hdv := hd.2 vertex
    have huv := hu.2 vertex
    rw [show (fun i => (d i + u i) / 2) =
        (fun i => (1 / 2 : ℝ) * d i + 1 / 2 * u i) by
      funext i
      ring,
      absoluteSlopePrefix_affine]
    constructor <;> nlinarith

theorem continuous_absoluteSlopeObjective
    {ι : Type*} [Fintype ι]
    (h m p : ℝ) (weight : ι → ℝ) (hp : 0 ≤ p) :
    Continuous (absoluteSlopeObjective h m p weight) := by
  unfold absoluteSlopeObjective
  apply continuous_finsetSum
  intro i _
  have hcoordinate : Continuous (fun slope : ι → ℝ => slope i) :=
    continuous_apply i
  have hpenalty : Continuous (fun slope : ι → ℝ =>
      absolutePowerPenalty p (slope i)) := by
    unfold absolutePowerPenalty
    exact hcoordinate.abs.rpow_const (fun _ => Or.inr hp)
  exact (continuous_const.mul hpenalty).sub
    ((continuous_const.mul continuous_const).mul hcoordinate)

theorem continuous_absoluteIntervalPathHarmony
    {h m p : ℝ} {L : ℕ} (hp : 0 ≤ p) :
    Continuous (absoluteIntervalPathHarmony h m p : (Fin L → ℝ) → ℝ) := by
  have hreduced := continuous_absoluteSlopeObjective h m p
    (absoluteIntervalWeight L) hp
  have heq : (absoluteIntervalPathHarmony h m p : (Fin L → ℝ) → ℝ) =
      fun slope => m * (L : ℝ) +
        absoluteSlopeObjective h m p (absoluteIntervalWeight L) slope := by
    funext slope
    exact absoluteIntervalPathHarmony_eq_reduced h m p slope
  rw [heq]
  exact continuous_const.add hreduced

/-- Every declared boxed reflected interval has an attained unique winner.
Compactness supplies attainment and strict power convexity supplies
uniqueness, including after obstacle contact. -/
theorem exists_unique_absoluteIntervalBox_minimizer
    {h m p : ℝ} (L : ℕ) (hh : 0 < h) (hp : 1 < p) :
    ∃ winner : Fin L → ℝ,
      IsUniqueMinimizerOn
        (AbsoluteIntervalBox : (Fin L → ℝ) → Prop)
        (absoluteIntervalPathHarmony h m p) winner := by
  let carrier : Set (Fin L → ℝ) :=
    {slope | AbsoluteIntervalBox slope}
  have hcarrierCompact : IsCompact carrier := isCompact_absoluteIntervalBox L
  have hcarrierNonempty : carrier.Nonempty :=
    ⟨fun _ => 0, absoluteIntervalBox_zero L⟩
  obtain ⟨winner, hwinnerCarrier, hwinnerMinimum⟩ :=
    hcarrierCompact.exists_isMinOn hcarrierNonempty
      (continuous_absoluteIntervalPathHarmony
        (h := h) (m := m) (p := p) (zero_le_one.trans hp.le)).continuousOn
  refine ⟨winner, hwinnerCarrier, ?_⟩
  intro candidate hcandidate
  have hminimum := hwinnerMinimum hcandidate
  constructor
  · exact hminimum
  · intro hequal
    by_contra hne
    have hLpositive : 0 < L := by
      by_contra hnot
      have hLzero : L = 0 := Nat.eq_zero_of_not_pos hnot
      apply hne
      funext i
      exact Fin.elim0 (hLzero ▸ i)
    letI : Nonempty (Fin L) := Fin.pos_iff_nonempty.mp hLpositive
    let midpoint : Fin L → ℝ := fun i => (candidate i + winner i) / 2
    have hmidpointCarrier : AbsoluteIntervalBox midpoint :=
      absoluteIntervalBox_midpoint hcandidate hwinnerCarrier
    have hstrictReduced := absoluteSlopeObjective_strict_midpoint
      (h := h) (m := m) (p := p)
      (absoluteIntervalWeight L) candidate winner hh hp hne
    have hstrictHarmony :
        absoluteIntervalPathHarmony h m p midpoint <
          (absoluteIntervalPathHarmony h m p candidate +
            absoluteIntervalPathHarmony h m p winner) / 2 := by
      dsimp [midpoint]
      rw [absoluteIntervalPathHarmony_eq_reduced,
        absoluteIntervalPathHarmony_eq_reduced,
        absoluteIntervalPathHarmony_eq_reduced]
      nlinarith
    have hmidpointMinimum := hwinnerMinimum hmidpointCarrier
    change absoluteIntervalPathHarmony h m p winner ≤
      absoluteIntervalPathHarmony h m p midpoint at hmidpointMinimum
    rw [hequal] at hstrictHarmony
    nlinarith

/-- Exact lower-obstacle criterion for the actual boxed interval objective.
The forward implication includes the load-bearing obstacle argument: if a
boxed winner were everywhere positive while the free depth were at least
one, a sufficiently short segment toward the free optimizer would remain in
the box and strictly lower Harmony. -/
theorem absoluteInterval_allPositiveWinner_iff_depth_lt_one
    {h m p : ℝ} (L : ℕ) (hh : 0 < h) (hm : 0 < m) (hp : 1 < p) :
    (∃ winner : Fin L → ℝ,
      IsUniqueMinimizerOn (AbsoluteIntervalBox : (Fin L → ℝ) → Prop)
        (absoluteIntervalPathHarmony h m p) winner ∧
      AbsoluteIntervalAllPositive winner) ↔
    absoluteIntervalFreeDepth h m p L < 1 := by
  classical
  let free := absoluteIntervalFreeSlope h m p L
  let depth := absoluteIntervalFreeDepth h m p L
  constructor
  · rintro ⟨winner, hwinner, hallPositive⟩
    by_contra hnotDepth
    have hdepth : 1 ≤ depth := le_of_not_gt hnotDepth
    have hfreeGlobal := absoluteIntervalPathHarmony_unique_minimizer
      L hh hm hp
    by_cases hwinnerFree : winner = free
    · subst winner
      have hfreePositive : AbsoluteIntervalAllPositive free := hallPositive
      have : depth < 1 := by
        simpa [free, depth] using
          (absoluteIntervalFreeSlope_allPositive_iff_depth_lt_one
            L hh hm hp).mp hfreePositive
      linarith
    · have hfreeMass : (∑ i : Fin L, free i) = 0 := by
        exact absoluteIntervalFreeSlope_sum_zero h m p L
      have hfreeLeWinner :
          absoluteIntervalPathHarmony h m p free ≤
            absoluteIntervalPathHarmony h m p winner :=
        (hfreeGlobal.2 winner hwinner.1.1).1
      have hfreeLtWinner :
          absoluteIntervalPathHarmony h m p free <
            absoluteIntervalPathHarmony h m p winner := by
        apply lt_of_le_of_ne hfreeLeWinner
        intro heq
        apply hwinnerFree
        exact (hfreeGlobal.2 winner hwinner.1.1).2 heq.symm
      let activity : Fin (L + 1) → ℝ := fun vertex =>
        1 - absoluteSlopePrefix winner vertex
      let delta : ℝ := Finset.univ.inf' Finset.univ_nonempty activity
      obtain ⟨minimumVertex, _, hdeltaEq⟩ :=
        Finset.exists_mem_eq_inf' (s := Finset.univ)
          Finset.univ_nonempty activity
      have hdeltaPositive : 0 < delta := by
        change 0 < Finset.univ.inf' Finset.univ_nonempty activity
        rw [hdeltaEq]
        exact sub_pos.mpr (hallPositive minimumVertex)
      have hdeltaLe (vertex : Fin (L + 1)) :
          delta ≤ 1 - absoluteSlopePrefix winner vertex := by
        exact Finset.inf'_le activity (Finset.mem_univ vertex)
      let start : Fin (L + 1) := ⟨0, by omega⟩
      have hdeltaLeOne : delta ≤ 1 := by
        have := hdeltaLe start
        simpa [start, absoluteSlopePrefix] using this
      let denominator : ℝ := 2 * (depth + 1)
      have hdenominatorPositive : 0 < denominator := by
        dsimp [denominator]
        nlinarith
      let t : ℝ := delta / denominator
      have htPositive : 0 < t := by
        dsimp [t]
        exact div_pos hdeltaPositive hdenominatorPositive
      have htLessOne : t < 1 := by
        dsimp [t]
        rw [div_lt_one hdenominatorPositive]
        dsimp [denominator]
        nlinarith
      have htNonnegative : 0 ≤ t := htPositive.le
      have honeMinusTNonnegative : 0 ≤ 1 - t := by linarith
      have hweights : (1 - t) + t = 1 := by ring
      have hdepthRatio : depth / denominator < 1 := by
        rw [div_lt_one hdenominatorPositive]
        dsimp [denominator]
        linarith
      have htDepth : t * depth < delta := by
        calc
          t * depth = delta * (depth / denominator) := by
            dsimp [t]
            ring
          _ < delta * 1 :=
            mul_lt_mul_of_pos_left hdepthRatio hdeltaPositive
          _ = delta := by ring
      let moved : Fin L → ℝ := fun i =>
        (1 - t) * winner i + t * free i
      have hmovedMass : (∑ i : Fin L, moved i) = 0 := by
        dsimp [moved]
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
          hwinner.1.1, hfreeMass]
        ring
      have hmovedBox : AbsoluteIntervalBox moved := by
        refine ⟨hmovedMass, ?_⟩
        intro vertex
        have hwinnerPrefix := hwinner.1.2 vertex
        have hfreePrefix := absoluteIntervalFreeSlope_prefix_bounds
          L hh hm hp vertex
        have hdeltaAt := hdeltaLe vertex
        have hprefixAffine := absoluteSlopePrefix_affine
          (1 - t) t winner free vertex
        have hlower : 0 ≤ absoluteSlopePrefix moved vertex := by
          rw [show moved = fun i =>
              (1 - t) * winner i + t * free i by rfl,
            hprefixAffine]
          exact add_nonneg
            (mul_nonneg honeMinusTNonnegative hwinnerPrefix.1)
            (mul_nonneg htNonnegative hfreePrefix.1)
        have hdifference :
            absoluteSlopePrefix free vertex -
                absoluteSlopePrefix winner vertex ≤ depth := by
          linarith
        have hscaledDifference :
            t * (absoluteSlopePrefix free vertex -
                absoluteSlopePrefix winner vertex) ≤ t * depth :=
          mul_le_mul_of_nonneg_left hdifference htNonnegative
        have hupper : absoluteSlopePrefix moved vertex ≤ 1 := by
          rw [show moved = fun i =>
              (1 - t) * winner i + t * free i by rfl,
            hprefixAffine]
          nlinarith
        exact ⟨hlower, hupper⟩
      have hreducedFreeLtWinner :
          absoluteSlopeObjective h m p (absoluteIntervalWeight L) free <
            absoluteSlopeObjective h m p (absoluteIntervalWeight L) winner := by
        rw [absoluteIntervalPathHarmony_eq_reduced,
          absoluteIntervalPathHarmony_eq_reduced] at hfreeLtWinner
        linarith
      have hconvexReduced :
          absoluteSlopeObjective h m p (absoluteIntervalWeight L) moved ≤
            (1 - t) *
                absoluteSlopeObjective h m p (absoluteIntervalWeight L) winner +
              t * absoluteSlopeObjective h m p
                (absoluteIntervalWeight L) free := by
        exact absoluteSlopeObjective_convexCombination
          (absoluteIntervalWeight L) winner free hh.le hp.le
            honeMinusTNonnegative htNonnegative hweights
      have hmovedReducedLtWinner :
          absoluteSlopeObjective h m p (absoluteIntervalWeight L) moved <
            absoluteSlopeObjective h m p (absoluteIntervalWeight L) winner := by
        calc
          absoluteSlopeObjective h m p (absoluteIntervalWeight L) moved ≤
              (1 - t) *
                  absoluteSlopeObjective h m p (absoluteIntervalWeight L) winner +
                t * absoluteSlopeObjective h m p
                  (absoluteIntervalWeight L) free := hconvexReduced
          _ < absoluteSlopeObjective h m p
                (absoluteIntervalWeight L) winner := by
            nlinarith
      have hmovedHarmonyLtWinner :
          absoluteIntervalPathHarmony h m p moved <
            absoluteIntervalPathHarmony h m p winner := by
        rw [absoluteIntervalPathHarmony_eq_reduced,
          absoluteIntervalPathHarmony_eq_reduced]
        linarith
      exact (not_lt_of_ge (hwinner.2 moved hmovedBox).1)
        hmovedHarmonyLtWinner
  · intro hdepth
    refine ⟨absoluteIntervalFreeSlope h m p L, ?_, ?_⟩
    · exact absoluteIntervalFreeSlope_unique_box_minimizer_of_depth_le_one
        L hh hm hp hdepth.le
    · exact (absoluteIntervalFreeSlope_allPositive_iff_depth_lt_one
        L hh hm hp).mpr hdepth

/-- The actual boxed interval always has one unique winner, and its support
status is completely determined by whether the unconstrained central depth is
strictly below the obstacle.  This strengthens the support test from an
existence statement to an exact property of the attained winner. -/
theorem exists_unique_absoluteIntervalBox_minimizer_with_support
    {h m p : ℝ} (L : ℕ) (hh : 0 < h) (hm : 0 < m) (hp : 1 < p) :
    ∃ winner : Fin L → ℝ,
      IsUniqueMinimizerOn
          (AbsoluteIntervalBox : (Fin L → ℝ) → Prop)
          (absoluteIntervalPathHarmony h m p) winner ∧
      (AbsoluteIntervalAllPositive winner ↔
        absoluteIntervalFreeDepth h m p L < 1) ∧
      (AbsoluteIntervalHasZero winner ↔
        1 ≤ absoluteIntervalFreeDepth h m p L) := by
  obtain ⟨winner, hwinner⟩ :=
    exists_unique_absoluteIntervalBox_minimizer L hh hp
  have hallPositiveIff :
      AbsoluteIntervalAllPositive winner ↔
        absoluteIntervalFreeDepth h m p L < 1 := by
    constructor
    · intro hallPositive
      exact (absoluteInterval_allPositiveWinner_iff_depth_lt_one
        L hh hm hp).mp ⟨winner, hwinner, hallPositive⟩
    · intro hdepth
      obtain ⟨positiveWinner, hpositiveWinner, hallPositive⟩ :=
        (absoluteInterval_allPositiveWinner_iff_depth_lt_one
          L hh hm hp).mpr hdepth
      have hwinnerLe := (hwinner.2 positiveWinner hpositiveWinner.1).1
      have hpositiveLe := (hpositiveWinner.2 winner hwinner.1).1
      have hequal :
          absoluteIntervalPathHarmony h m p positiveWinner =
            absoluteIntervalPathHarmony h m p winner :=
        le_antisymm hpositiveLe hwinnerLe
      have hwinnersEqual : positiveWinner = winner :=
        (hwinner.2 positiveWinner hpositiveWinner.1).2 hequal
      rwa [← hwinnersEqual]
  have hzeroIff :
      AbsoluteIntervalHasZero winner ↔
        1 ≤ absoluteIntervalFreeDepth h m p L := by
    rw [absoluteIntervalBox_hasZero_iff_not_allPositive hwinner.1,
      hallPositiveIff]
    exact not_lt
  exact ⟨winner, hwinner, hallPositiveIff, hzeroIff⟩

/-! ## Reach--phase comparison at the three critical spans -/

/-- The factor `2^q` in the centered critical mass exactly cancels the two
in the reflected KKT load. -/
theorem absoluteIntervalFreeDepth_eq_scaledShifted_of_criticalMass
    {h m p : ℝ} {L : ℕ} {shifted : ℝ}
    (hh : 0 < h) (hm : 0 < m) (hp : 1 < p)
    (hmass : absoluteCriticalMass L (powerShiftExponent p) =
      (2 : ℝ) ^ powerShiftExponent p * shifted) :
    absoluteIntervalFreeDepth h m p L =
      (m / (p * h)) ^ powerShiftExponent p * shifted := by
  have hpPositive : 0 < p := lt_trans zero_lt_one hp
  have hscaleNonnegative : 0 ≤ m / (2 * p * h) := by positivity
  have hfactor :
      (m / (2 * p * h)) ^ powerShiftExponent p *
          (2 : ℝ) ^ powerShiftExponent p =
        (m / (p * h)) ^ powerShiftExponent p := by
    rw [← Real.mul_rpow hscaleNonnegative (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    field_simp [hpPositive.ne', hh.ne']
  rw [absoluteIntervalFreeDepth_eq_criticalMass L hh hm hp, hmass]
  calc
    (m / (2 * p * h)) ^ powerShiftExponent p *
        ((2 : ℝ) ^ powerShiftExponent p * shifted) =
      ((m / (2 * p * h)) ^ powerShiftExponent p *
        (2 : ℝ) ^ powerShiftExponent p) * shifted := by ring
    _ = (m / (p * h)) ^ powerShiftExponent p * shifted := by
      rw [hfactor]

theorem absoluteIntervalFreeDepth_before_eq_scaled
    {h m p : ℝ} {K : ℕ} (hK : 0 < K)
    (hh : 0 < h) (hm : 0 < m) (hp : 1 < p) :
    absoluteIntervalFreeDepth h m p (2 * K - 1) =
      (m / (p * h)) ^ powerShiftExponent p *
        PhonologicalCalculus.Context.shiftedPowerSum K
          (powerShiftExponent p) 0 := by
  apply absoluteIntervalFreeDepth_eq_scaledShifted_of_criticalMass
    hh hm hp
  exact absoluteCriticalMass_before hK (powerShiftExponent_positive hp)

theorem absoluteIntervalFreeDepth_middle_eq_scaled
    {h m p : ℝ} {K : ℕ} (hh : 0 < h) (hm : 0 < m) (hp : 1 < p) :
    absoluteIntervalFreeDepth h m p (2 * K) =
      (m / (p * h)) ^ powerShiftExponent p *
        PhonologicalCalculus.Context.shiftedPowerSum K
          (powerShiftExponent p) (1 / 2) := by
  apply absoluteIntervalFreeDepth_eq_scaledShifted_of_criticalMass
    hh hm hp
  exact absoluteCriticalMass_middle (powerShiftExponent_positive hp)

theorem absoluteIntervalFreeDepth_after_eq_scaled
    {h m p : ℝ} {K : ℕ} (hh : 0 < h) (hm : 0 < m) (hp : 1 < p) :
    absoluteIntervalFreeDepth h m p (2 * K + 1) =
      (m / (p * h)) ^ powerShiftExponent p *
        PhonologicalCalculus.Context.shiftedPowerSum K
          (powerShiftExponent p) 1 := by
  apply absoluteIntervalFreeDepth_eq_scaledShifted_of_criticalMass
    hh hm hp
  exact absoluteCriticalMass_after (powerShiftExponent_positive hp)

/-- The directional reach--phase mass is reciprocal to the reflected
interval scale. -/
theorem reachPhase_scale_mul_sum_eq_one
    {h m p phaseMass : ℝ} (hh : 0 < h) (hm : 0 < m) (hp : 1 < p)
    (hphase : phaseMass = (p * (h / m)) ^ powerShiftExponent p) :
    (m / (p * h)) ^ powerShiftExponent p * phaseMass = 1 := by
  have hpPositive : 0 < p := lt_trans zero_lt_one hp
  have hleftNonnegative : 0 ≤ m / (p * h) := by positivity
  have hrightNonnegative : 0 ≤ p * (h / m) := by positivity
  rw [hphase, ← Real.mul_rpow hleftNonnegative hrightNonnegative]
  have hproduct : (m / (p * h)) * (p * (h / m)) = 1 := by
    field_simp [hpPositive.ne', hh.ne', hm.ne']
  rw [hproduct, Real.one_rpow]

/-- Multiplication by the positive reciprocal phase scale transports the
strict support comparison without changing its order. -/
theorem scaledShifted_lt_one_iff
    {h m p phaseMass shifted : ℝ}
    (hh : 0 < h) (hm : 0 < m) (hp : 1 < p)
    (hphase : phaseMass = (p * (h / m)) ^ powerShiftExponent p) :
    (m / (p * h)) ^ powerShiftExponent p * shifted < 1 ↔
      shifted < phaseMass := by
  have hpPositive : 0 < p := lt_trans zero_lt_one hp
  have hscalePositive :
      0 < (m / (p * h)) ^ powerShiftExponent p := by
    exact Real.rpow_pos_of_pos (by positivity) _
  have hone := reachPhase_scale_mul_sum_eq_one hh hm hp hphase
  constructor
  · intro hscaled
    by_contra hnot
    have hle : phaseMass ≤ shifted := le_of_not_gt hnot
    have := mul_le_mul_of_nonneg_left hle hscalePositive.le
    linarith
  · intro hshifted
    have := mul_lt_mul_of_pos_left hshifted hscalePositive
    linarith

theorem one_le_scaledShifted_iff
    {h m p phaseMass shifted : ℝ}
    (hh : 0 < h) (hm : 0 < m) (hp : 1 < p)
    (hphase : phaseMass = (p * (h / m)) ^ powerShiftExponent p) :
    1 ≤ (m / (p * h)) ^ powerShiftExponent p * shifted ↔
      phaseMass ≤ shifted := by
  rw [← not_lt, ← not_lt,
    scaledShifted_lt_one_iff hh hm hp hphase]

theorem absoluteIntervalFreeDepth_before_lt_one_of_phase
    {h m p u : ℝ} {K : ℕ} (hK : 0 < K)
    (hh : 0 < h) (hm : 0 < m) (hp : 1 < p) (hu : 0 < u)
    (hphase : PhonologicalCalculus.Context.shiftedPowerSum K
        (powerShiftExponent p) u =
      (p * (h / m)) ^ powerShiftExponent p) :
    absoluteIntervalFreeDepth h m p (2 * K - 1) < 1 := by
  rw [absoluteIntervalFreeDepth_before_eq_scaled hK hh hm hp,
    scaledShifted_lt_one_iff hh hm hp hphase]
  exact PhonologicalCalculus.Context.shiftedPowerSum_strictMono
    hK (powerShiftExponent_positive hp) (le_refl 0) hu

theorem absoluteIntervalFreeDepth_middle_lt_one_iff_phase_gt_half
    {h m p u : ℝ} {K : ℕ} (hK : 0 < K)
    (hh : 0 < h) (hm : 0 < m) (hp : 1 < p) (hu : 0 ≤ u)
    (hphase : PhonologicalCalculus.Context.shiftedPowerSum K
        (powerShiftExponent p) u =
      (p * (h / m)) ^ powerShiftExponent p) :
    absoluteIntervalFreeDepth h m p (2 * K) < 1 ↔ 1 / 2 < u := by
  rw [absoluteIntervalFreeDepth_middle_eq_scaled hh hm hp,
    scaledShifted_lt_one_iff hh hm hp hphase]
  constructor
  · intro hmass
    by_contra hnot
    have huHalf : u ≤ 1 / 2 := le_of_not_gt hnot
    have := PhonologicalCalculus.Context.shiftedPowerSum_mono
      (K := K) (powerShiftExponent_positive hp) hu huHalf
    exact (not_lt_of_ge this) hmass
  · intro hhalf
    exact PhonologicalCalculus.Context.shiftedPowerSum_strictMono
      hK (powerShiftExponent_positive hp) (by norm_num) hhalf

theorem one_le_absoluteIntervalFreeDepth_after_of_phase
    {h m p u : ℝ} {K : ℕ}
    (hh : 0 < h) (hm : 0 < m) (hp : 1 < p)
    (hu : 0 ≤ u) (huOne : u ≤ 1)
    (hphase : PhonologicalCalculus.Context.shiftedPowerSum K
        (powerShiftExponent p) u =
      (p * (h / m)) ^ powerShiftExponent p) :
    1 ≤ absoluteIntervalFreeDepth h m p (2 * K + 1) := by
  rw [absoluteIntervalFreeDepth_after_eq_scaled hh hm hp,
    one_le_scaledShifted_iff hh hm hp hphase]
  exact PhonologicalCalculus.Context.shiftedPowerSum_mono
    (powerShiftExponent_positive hp) hu huOne

/-! ## Monotonicity in opposite-trigger span -/

theorem absoluteCriticalMass_succ_le
    {q : ℝ} (hq : 0 < q) (L : ℕ) :
    absoluteCriticalMass L q ≤ absoluteCriticalMass (L + 1) q := by
  rcases L.even_or_odd' with ⟨K, hEven | hOdd⟩
  · subst L
    have heven : Even (2 * K) := ⟨K, by omega⟩
    have hodd : ¬ Even (2 * K + 1) := by
      rintro ⟨r, hr⟩
      omega
    have hhalfEven : (2 * K) / 2 = K := by omega
    have hhalfOdd : (2 * K + 1) / 2 = K := by omega
    unfold absoluteCriticalMass
    rw [if_pos heven, if_neg hodd, hhalfEven, hhalfOdd]
    apply Finset.sum_le_sum
    intro r _
    apply Real.rpow_le_rpow (Nat.cast_nonneg _) _ hq.le
    norm_cast
    omega
  · subst L
    have hodd : ¬ Even (2 * K + 1) := by
      rintro ⟨r, hr⟩
      omega
    have heven : Even (2 * K + 1 + 1) := ⟨K + 1, by omega⟩
    have hhalfOdd : (2 * K + 1) / 2 = K := by omega
    have hhalfEven : (2 * K + 1 + 1) / 2 = K + 1 := by omega
    unfold absoluteCriticalMass
    rw [if_neg hodd, if_pos heven, hhalfOdd, hhalfEven]
    let oldTerm : ℕ → ℝ := fun r => (((2 * r + 2 : ℕ) : ℝ) ^ q)
    let newTerm : ℕ → ℝ := fun r => (((2 * r + 1 : ℕ) : ℝ) ^ q)
    change (∑ r ∈ Finset.range K, oldTerm r) ≤
      ∑ r ∈ Finset.range (K + 1), newTerm r
    have htail : (∑ r ∈ Finset.range K, oldTerm r) ≤
        ∑ r ∈ Finset.range K, newTerm (r + 1) := by
      apply Finset.sum_le_sum
      intro r _
      apply Real.rpow_le_rpow (Nat.cast_nonneg _) _ hq.le
      norm_cast
      omega
    have hzero : 0 ≤ newTerm 0 := Real.rpow_nonneg (Nat.cast_nonneg _) _
    calc
      (∑ r ∈ Finset.range K, oldTerm r) ≤
          ∑ r ∈ Finset.range K, newTerm (r + 1) := htail
      _ ≤ (∑ r ∈ Finset.range K, newTerm (r + 1)) + newTerm 0 :=
        le_add_of_nonneg_right hzero
      _ = ∑ r ∈ Finset.range (K + 1), newTerm r :=
        (Finset.sum_range_succ' newTerm K).symm

theorem absoluteCriticalMass_monotone {q : ℝ} (hq : 0 < q) :
    Monotone (fun L => absoluteCriticalMass L q) :=
  monotone_nat_of_le_succ (absoluteCriticalMass_succ_le hq)

theorem absoluteIntervalFreeDepth_monotone
    {h m p : ℝ} (hh : 0 < h) (hm : 0 < m) (hp : 1 < p) :
    Monotone (fun L => absoluteIntervalFreeDepth h m p L) := by
  intro L R hLR
  change absoluteIntervalFreeDepth h m p L ≤
    absoluteIntervalFreeDepth h m p R
  rw [absoluteIntervalFreeDepth_eq_criticalMass L hh hm hp,
    absoluteIntervalFreeDepth_eq_criticalMass R hh hm hp]
  exact mul_le_mul_of_nonneg_left
    (absoluteCriticalMass_monotone (powerShiftExponent_positive hp) hLR)
    (Real.rpow_nonneg (by positivity) _)

/-! ## Actual maximum-gap law and CTX-C2 composition -/

/-- The phase-selected bidirectional support class. -/
noncomputable def absoluteEdgeSupportClass (u : ℝ) : EdgeSupportClass :=
  if u ≤ 1 / 2 then .absoluteLowPhase else .absoluteHighPhase

/-- Analytic maximum-gap law for the actual equal-endpoint absolute-edge
objective.  The proposition on the right quantifies over a genuine unique
boxed winner; it is not an assumed support table. -/
theorem absolute_maximumGap_support_law
    {h m p u : ℝ} {K L : ℕ}
    (hcell : GeneralPowerFirstZeroCell h m p K)
    (hu : u ∈ Ioc (0 : ℝ) 1)
    (hphase : PhonologicalCalculus.Context.shiftedPowerSum K
        (powerShiftExponent p) u =
      (p * (h / m)) ^ powerShiftExponent p) :
    (L ≤ maximumPositiveGap K (absoluteEdgeSupportClass u) ↔
      ∃ winner : Fin L → ℝ,
        IsUniqueMinimizerOn
          (AbsoluteIntervalBox : (Fin L → ℝ) → Prop)
          (absoluteIntervalPathHarmony h m p) winner ∧
        AbsoluteIntervalAllPositive winner) := by
  have hcellData := hcell
  rcases hcellData with ⟨hK, hh, hm, hp, _hprevious, _hboundary⟩
  rw [absoluteInterval_allPositiveWinner_iff_depth_lt_one L hh hm hp]
  have hmono := absoluteIntervalFreeDepth_monotone hh hm hp
  by_cases hlow : u ≤ 1 / 2
  · simp only [absoluteEdgeSupportClass, if_pos hlow, maximumPositiveGap]
    constructor
    · intro hL
      have hbefore := absoluteIntervalFreeDepth_before_lt_one_of_phase
        hK hh hm hp hu.1 hphase
      exact lt_of_le_of_lt (hmono hL) hbefore
    · intro hdepth
      by_contra hnot
      have hmiddleLe : 2 * K ≤ L := by omega
      have hnotMiddleLt :
          ¬ absoluteIntervalFreeDepth h m p (2 * K) < 1 := by
        rw [absoluteIntervalFreeDepth_middle_lt_one_iff_phase_gt_half
          hK hh hm hp hu.1.le hphase]
        exact not_lt_of_ge hlow
      have hmiddleOne :
          1 ≤ absoluteIntervalFreeDepth h m p (2 * K) :=
        le_of_not_gt hnotMiddleLt
      have := hmono hmiddleLe
      linarith
  · have hhigh : 1 / 2 < u := lt_of_not_ge hlow
    simp only [absoluteEdgeSupportClass, if_neg hlow, maximumPositiveGap]
    constructor
    · intro hL
      have hmiddle : absoluteIntervalFreeDepth h m p (2 * K) < 1 :=
        (absoluteIntervalFreeDepth_middle_lt_one_iff_phase_gt_half
          hK hh hm hp hu.1.le hphase).mpr hhigh
      exact lt_of_le_of_lt (hmono hL) hmiddle
    · intro hdepth
      by_contra hnot
      have hafterLe : 2 * K + 1 ≤ L := by omega
      have hafterOne := one_le_absoluteIntervalFreeDepth_after_of_phase
        hh hm hp hu.1.le hu.2 hphase
      have := hmono hafterLe
      linarith

/-- Attained-winner form of the maximum-gap law.  At every span there is a
unique boxed winner; it is strictly positive exactly up to the registered
maximum gap, and it has an exact zero at every longer span. -/
theorem absolute_maximumGap_uniqueWinner_law
    {h m p u : ℝ} {K L : ℕ}
    (hcell : GeneralPowerFirstZeroCell h m p K)
    (hu : u ∈ Ioc (0 : ℝ) 1)
    (hphase : PhonologicalCalculus.Context.shiftedPowerSum K
        (powerShiftExponent p) u =
      (p * (h / m)) ^ powerShiftExponent p) :
    ∃ winner : Fin L → ℝ,
      IsUniqueMinimizerOn
          (AbsoluteIntervalBox : (Fin L → ℝ) → Prop)
          (absoluteIntervalPathHarmony h m p) winner ∧
      (AbsoluteIntervalAllPositive winner ↔
        L ≤ maximumPositiveGap K (absoluteEdgeSupportClass u)) ∧
      (AbsoluteIntervalHasZero winner ↔
        maximumPositiveGap K (absoluteEdgeSupportClass u) < L) := by
  rcases hcell with ⟨hK, hh, hm, hp, hprevious, hboundary⟩
  have hcellRestored : GeneralPowerFirstZeroCell h m p K :=
    ⟨hK, hh, hm, hp, hprevious, hboundary⟩
  obtain ⟨winner, hwinner, hallDepth, hzeroDepth⟩ :=
    exists_unique_absoluteIntervalBox_minimizer_with_support
      L hh hm hp
  have hregistered := absolute_maximumGap_support_law
    (L := L) hcellRestored hu hphase
  have hallRegistered :
      AbsoluteIntervalAllPositive winner ↔
        L ≤ maximumPositiveGap K (absoluteEdgeSupportClass u) := by
    constructor
    · intro hallPositive
      exact hregistered.mpr ⟨winner, hwinner, hallPositive⟩
    · intro hgap
      obtain ⟨positiveWinner, hpositiveWinner, hallPositive⟩ :=
        hregistered.mp hgap
      have hwinnerLe := (hwinner.2 positiveWinner hpositiveWinner.1).1
      have hpositiveLe := (hpositiveWinner.2 winner hwinner.1).1
      have hequal :
          absoluteIntervalPathHarmony h m p positiveWinner =
            absoluteIntervalPathHarmony h m p winner :=
        le_antisymm hpositiveLe hwinnerLe
      have hwinnersEqual : positiveWinner = winner :=
        (hwinner.2 positiveWinner hpositiveWinner.1).2 hequal
      rwa [← hwinnersEqual]
  have hzeroRegistered :
      AbsoluteIntervalHasZero winner ↔
        maximumPositiveGap K (absoluteEdgeSupportClass u) < L := by
    rw [absoluteIntervalBox_hasZero_iff_not_allPositive hwinner.1,
      hallRegistered]
    exact Nat.not_le
  exact ⟨winner, hwinner, hallRegistered, hzeroRegistered⟩

/-- Equality of the registered half-phase bit preserves the complete
absolute-edge support class, hence every binary support answer. -/
theorem absoluteEdgeSupportClass_eq_low
    {u : ℝ} (hu : u ≤ 1 / 2) :
    absoluteEdgeSupportClass u = .absoluteLowPhase := by
  unfold absoluteEdgeSupportClass
  rw [if_pos (by simpa only [one_div] using hu)]

theorem absoluteEdgeSupportClass_eq_high
    {u : ℝ} (hu : 1 / 2 < u) :
    absoluteEdgeSupportClass u = .absoluteHighPhase := by
  unfold absoluteEdgeSupportClass
  rw [if_neg (by simpa only [one_div] using not_le.mpr hu)]

theorem phaseBit_preserves_absoluteEdgeSupportClass
    {u v : ℝ} (hbit : phaseBit u = phaseBit v) :
    absoluteEdgeSupportClass u = absoluteEdgeSupportClass v := by
  by_cases hu : u ≤ 1 / 2
  · have huBit : phaseBit u = 0 := (phaseBit_eq_zero_iff u).mpr hu
    have hvBit : phaseBit v = 0 := hbit ▸ huBit
    have hv : v ≤ 1 / 2 := (phaseBit_eq_zero_iff v).mp hvBit
    rw [absoluteEdgeSupportClass_eq_low hu,
      absoluteEdgeSupportClass_eq_low hv]
  · have huHigh : 1 / 2 < u := lt_of_not_ge hu
    have huBit : phaseBit u = 1 := (phaseBit_eq_one_iff u).mpr huHigh
    have hvBit : phaseBit v = 1 := hbit ▸ huBit
    have hvHigh : 1 / 2 < v := (phaseBit_eq_one_iff v).mp hvBit
    rw [absoluteEdgeSupportClass_eq_high huHigh,
      absoluteEdgeSupportClass_eq_high hvHigh]

/-- Objective-level necessity witness for the half-phase bit.  Two quadratic
grammars have the same one-trigger first-zero cell `K = 4`, but their unique
eight-edge equal-endpoint winners have opposite exact support verdicts. -/
theorem ctx_c1_actual_carrier_witness :
    (∃ winner : Fin 8 → ℝ,
      IsUniqueMinimizerOn
          (AbsoluteIntervalBox : (Fin 8 → ℝ) → Prop)
          (absoluteIntervalPathHarmony (7 / 2) 1 2) winner ∧
      AbsoluteIntervalHasZero winner) ∧
    (∃ winner : Fin 8 → ℝ,
      IsUniqueMinimizerOn
          (AbsoluteIntervalBox : (Fin 8 → ℝ) → Prop)
          (absoluteIntervalPathHarmony (9 / 2) 1 2) winner ∧
      AbsoluteIntervalAllPositive winner) := by
  have hlowCell : GeneralPowerFirstZeroCell (7 / 2) 1 2 4 := by
    rw [generalPowerFirstZeroCell_iff_shiftedSum]
    norm_num [powerPathShiftedSum_eq_range, powerPathScale,
      powerShiftExponent]
  have hhighCell : GeneralPowerFirstZeroCell (9 / 2) 1 2 4 := by
    rw [generalPowerFirstZeroCell_iff_shiftedSum]
    norm_num [powerPathShiftedSum_eq_range, powerPathScale,
      powerShiftExponent]
  have hlowPhase : PhonologicalCalculus.Context.shiftedPowerSum 4
      (powerShiftExponent 2) (1 / 4) =
        (2 * ((7 / 2) / 1)) ^ powerShiftExponent 2 := by
    norm_num [PhonologicalCalculus.Context.shiftedPowerSum,
      powerShiftExponent]
  have hhighPhase : PhonologicalCalculus.Context.shiftedPowerSum 4
      (powerShiftExponent 2) (3 / 4) =
        (2 * ((9 / 2) / 1)) ^ powerShiftExponent 2 := by
    norm_num [PhonologicalCalculus.Context.shiftedPowerSum,
      powerShiftExponent]
  obtain ⟨lowWinner, hlowWinner, _hlowPositive, hlowZero⟩ :=
    absolute_maximumGap_uniqueWinner_law
      (L := 8) hlowCell (by norm_num) hlowPhase
  obtain ⟨highWinner, hhighWinner, hhighPositive, _hhighZero⟩ :=
    absolute_maximumGap_uniqueWinner_law
      (L := 8) hhighCell (by norm_num) hhighPhase
  constructor
  · exact ⟨lowWinner, hlowWinner, hlowZero.mpr (by
      norm_num [absoluteEdgeSupportClass, maximumPositiveGap])⟩
  · exact ⟨highWinner, hhighWinner, hhighPositive.mpr (by
      norm_num [absoluteEdgeSupportClass, maximumPositiveGap])⟩

/-- `CTX-C1.GENERAL.04`, objective-level analytic closure.  The unique phase
coordinate determines an attained unique boxed winner at every span; the
winner is positive through `2K-1`, contacts the lower obstacle at `2K`
exactly in the low half-phase, and has a zero from `2K+1` onward.  Equality
of the registered phase bit preserves every binary support answer. -/
theorem ctx_c1_general_04_analytic
    {h m p : ℝ} {K : ℕ}
    (hcell : GeneralPowerFirstZeroCell h m p K) :
    ∃! u : ℝ,
      u ∈ Ioc (0 : ℝ) 1 ∧
      PhonologicalCalculus.Context.shiftedPowerSum K
          (powerShiftExponent p) u =
        (p * (h / m)) ^ powerShiftExponent p ∧
      (∀ L : ℕ,
        ∃ winner : Fin L → ℝ,
          IsUniqueMinimizerOn
              (AbsoluteIntervalBox : (Fin L → ℝ) → Prop)
              (absoluteIntervalPathHarmony h m p) winner ∧
          (AbsoluteIntervalAllPositive winner ↔
            L ≤ maximumPositiveGap K (absoluteEdgeSupportClass u)) ∧
          (AbsoluteIntervalHasZero winner ↔
            maximumPositiveGap K (absoluteEdgeSupportClass u) < L)) ∧
      (∀ L : ℕ, L ≤ 2 * K - 1 →
        ∃ winner : Fin L → ℝ,
          IsUniqueMinimizerOn
              (AbsoluteIntervalBox : (Fin L → ℝ) → Prop)
              (absoluteIntervalPathHarmony h m p) winner ∧
          AbsoluteIntervalAllPositive winner) ∧
      (∃ winner : Fin (2 * K) → ℝ,
        IsUniqueMinimizerOn
            (AbsoluteIntervalBox : (Fin (2 * K) → ℝ) → Prop)
            (absoluteIntervalPathHarmony h m p) winner ∧
        (AbsoluteIntervalHasZero winner ↔ u ≤ 1 / 2)) ∧
      (∀ L : ℕ, 2 * K + 1 ≤ L →
        ∃ winner : Fin L → ℝ,
          IsUniqueMinimizerOn
              (AbsoluteIntervalBox : (Fin L → ℝ) → Prop)
              (absoluteIntervalPathHarmony h m p) winner ∧
          AbsoluteIntervalHasZero winner) ∧
      (∀ v : ℝ, phaseBit u = phaseBit v →
        ∀ L : ℕ,
          positiveAtGap K L (absoluteEdgeSupportClass u) =
            positiveAtGap K L (absoluteEdgeSupportClass v)) := by
  obtain ⟨u, huData, huUnique⟩ :=
    exists_unique_contextPhase_of_firstZeroCell hcell
  have hK : 0 < K := hcell.1
  have hWinnerLaw (L : ℕ) :=
    absolute_maximumGap_uniqueWinner_law
      (L := L) hcell huData.1 huData.2
  refine ⟨u, ⟨huData.1, huData.2, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro L
    exact hWinnerLaw L
  · intro L hbefore
    obtain ⟨winner, hwinner, hallPositive, _hzero⟩ := hWinnerLaw L
    refine ⟨winner, hwinner, hallPositive.mpr ?_⟩
    by_cases hlow : u ≤ 1 / 2
    · rw [absoluteEdgeSupportClass_eq_low hlow]
      simp only [maximumPositiveGap]
      exact hbefore
    · rw [absoluteEdgeSupportClass_eq_high (lt_of_not_ge hlow)]
      simp only [maximumPositiveGap]
      omega
  · obtain ⟨winner, hwinner, _hallPositive, hzero⟩ :=
      hWinnerLaw (2 * K)
    refine ⟨winner, hwinner, ?_⟩
    rw [hzero]
    by_cases hlow : u ≤ 1 / 2
    · constructor
      · intro _
        exact hlow
      · intro _
        rw [absoluteEdgeSupportClass_eq_low hlow]
        simp only [maximumPositiveGap]
        omega
    · constructor
      · intro hcontact
        have hmax :
            maximumPositiveGap K (absoluteEdgeSupportClass u) = 2 * K := by
          rw [absoluteEdgeSupportClass_eq_high (lt_of_not_ge hlow)]
          rfl
        rw [hmax] at hcontact
        omega
      · exact fun huLow => (hlow huLow).elim
  · intro L hafter
    obtain ⟨winner, hwinner, _hallPositive, hzero⟩ := hWinnerLaw L
    refine ⟨winner, hwinner, hzero.mpr ?_⟩
    have hmaximum :
        maximumPositiveGap K (absoluteEdgeSupportClass u) ≤ 2 * K := by
      by_cases hlow : u ≤ 1 / 2
      · rw [absoluteEdgeSupportClass_eq_low hlow]
        simp only [maximumPositiveGap]
        omega
      · rw [absoluteEdgeSupportClass_eq_high (lt_of_not_ge hlow)]
        simp only [maximumPositiveGap]
        exact le_rfl
    omega
  · intro v hbit L
    rw [phaseBit_preserves_absoluteEdgeSupportClass hbit]
  · intro v hv
    exact huUnique v ⟨hv.1, hv.2.1⟩

/-- The registered directional and absolute support predicates are now
connected to the two exact maximum-gap codes used by the finite diagnostic. -/
theorem directional_actual_support_iff_positiveAtGap
    {h m p : ℝ} {K L : ℕ}
    (hcell : GeneralPowerFirstZeroCell h m p K) (hL : 0 < L) :
    (∃ winner : Fin (L - 1) → ℝ,
      IsUniqueMinimizerOn (SolidSimplex : (Fin (L - 1) → ℝ) → Prop)
        (directionalIntervalPathHarmony h m p) winner ∧
      ∀ i, 0 < directionalReconstructedActivity winner i) ↔
      positiveAtGap K L .forward = true := by
  rw [← directional_maximumGap_support_law hcell hL]
  simp [positiveAtGap, maximumPositiveGap]

theorem absolute_actual_support_iff_positiveAtGap
    {h m p u : ℝ} {K L : ℕ}
    (hcell : GeneralPowerFirstZeroCell h m p K)
    (hu : u ∈ Ioc (0 : ℝ) 1)
    (hphase : PhonologicalCalculus.Context.shiftedPowerSum K
        (powerShiftExponent p) u =
      (p * (h / m)) ^ powerShiftExponent p) :
    (∃ winner : Fin L → ℝ,
      IsUniqueMinimizerOn
        (AbsoluteIntervalBox : (Fin L → ℝ) → Prop)
        (absoluteIntervalPathHarmony h m p) winner ∧
      AbsoluteIntervalAllPositive winner) ↔
      positiveAtGap K L (absoluteEdgeSupportClass u) = true := by
  rw [← absolute_maximumGap_support_law hcell hu hphase]
  simp [positiveAtGap]

/-- Objective-level directional all-positive support at a declared gap. -/
noncomputable def DirectionalGapPositive
    (h m p : ℝ) (L : ℕ) : Prop :=
  ∃ winner : Fin (L - 1) → ℝ,
    IsUniqueMinimizerOn (SolidSimplex : (Fin (L - 1) → ℝ) → Prop)
      (directionalIntervalPathHarmony h m p) winner ∧
    ∀ i, 0 < directionalReconstructedActivity winner i

/-- Objective-level absolute-edge all-positive support at a declared gap. -/
noncomputable def AbsoluteGapPositive
    (h m p : ℝ) (L : ℕ) : Prop :=
  ∃ winner : Fin L → ℝ,
    IsUniqueMinimizerOn
      (AbsoluteIntervalBox : (Fin L → ℝ) → Prop)
      (absoluteIntervalPathHarmony h m p) winner ∧
    AbsoluteIntervalAllPositive winner

/-- The finite shortest-separator statement after replacing both Boolean
support classes by their actual objective-level unique-winner semantics. -/
theorem actual_opposite_trigger_shortest_separator
    {h m p u : ℝ} {K : ℕ}
    (hcell : GeneralPowerFirstZeroCell h m p K) (hKtwo : 2 ≤ K)
    (hu : u ∈ Ioc (0 : ℝ) 1)
    (hphase : PhonologicalCalculus.Context.shiftedPowerSum K
        (powerShiftExponent p) u =
      (p * (h / m)) ^ powerShiftExponent p) :
    (∀ L : ℕ, 0 < L → L < K + 1 →
      DirectionalGapPositive h m p L ∧
        AbsoluteGapPositive h m p L) ∧
    ¬ DirectionalGapPositive h m p (K + 1) ∧
      AbsoluteGapPositive h m p (K + 1) := by
  constructor
  · intro L hL hshort
    have hcodes := no_shorter_binary_separator hKtwo hshort
    constructor
    · unfold DirectionalGapPositive
      exact (directional_actual_support_iff_positiveAtGap hcell hL).mpr
        hcodes.1
    · unfold AbsoluteGapPositive
      apply (absolute_actual_support_iff_positiveAtGap
        hcell hu hphase).mpr
      by_cases hlow : u ≤ 1 / 2
      · rw [show absoluteEdgeSupportClass u = .absoluteLowPhase by
          unfold absoluteEdgeSupportClass
          rw [if_pos hlow]]
        exact hcodes.2.1
      · rw [show absoluteEdgeSupportClass u = .absoluteHighPhase by
          unfold absoluteEdgeSupportClass
          rw [if_neg hlow]]
        exact hcodes.2.2
  · have hcodes := opposite_trigger_separates_at_K_add_one hKtwo
    constructor
    · unfold DirectionalGapPositive
      intro hdirectional
      have htrue := (directional_actual_support_iff_positiveAtGap
        hcell (by omega : 0 < K + 1)).mp hdirectional
      rw [hcodes.1] at htrue
      contradiction
    · unfold AbsoluteGapPositive
      apply (absolute_actual_support_iff_positiveAtGap
        hcell hu hphase).mpr
      by_cases hlow : u ≤ 1 / 2
      · rw [show absoluteEdgeSupportClass u = .absoluteLowPhase by
          unfold absoluteEdgeSupportClass
          rw [if_pos hlow]]
        exact hcodes.2.1
      · rw [show absoluteEdgeSupportClass u = .absoluteHighPhase by
          unfold absoluteEdgeSupportClass
          rw [if_neg hlow]]
        exact hcodes.2.2

/-- `CTX-C2.GENERAL.03`, objective-level analytic closure.  The unique
directional reach phase exists; the declared objectives realize their exact
maximum-gap laws; and the already proved finite diagnostic is therefore a
result about those objective-level support responses rather than a detached
integer fixture. -/
theorem ctx_c2_general_03_analytic
    {h m p : ℝ} {K : ℕ}
    (hcell : GeneralPowerFirstZeroCell h m p K) (hKtwo : 2 ≤ K) :
    (∀ profile : List ℝ,
      IsGlobalWinner (pathHarmony (powerPenalty p) h m) profile ↔
        IsGlobalWinner (absolutePathHarmony (powerPenalty p) h m) profile) ∧
    (∀ L : ℕ, 0 < L →
      ((∃ winner : Fin (L - 1) → ℝ,
          IsUniqueMinimizerOn
            (SolidSimplex : (Fin (L - 1) → ℝ) → Prop)
            (directionalIntervalPathHarmony h m p) winner ∧
          ∀ i, 0 < directionalReconstructedActivity winner i) ↔
        positiveAtGap K L .forward = true)) ∧
    ∃! u : ℝ,
      u ∈ Ioc (0 : ℝ) 1 ∧
      PhonologicalCalculus.Context.shiftedPowerSum K
          (powerShiftExponent p) u =
        (p * (h / m)) ^ powerShiftExponent p ∧
      (∀ L : ℕ,
        ((∃ winner : Fin L → ℝ,
            IsUniqueMinimizerOn
              (AbsoluteIntervalBox : (Fin L → ℝ) → Prop)
              (absoluteIntervalPathHarmony h m p) winner ∧
            AbsoluteIntervalAllPositive winner) ↔
          positiveAtGap K L (absoluteEdgeSupportClass u) = true)) ∧
      ((∀ L : ℕ, 0 < L → L < K + 1 →
          DirectionalGapPositive h m p L ∧
            AbsoluteGapPositive h m p L) ∧
        ¬ DirectionalGapPositive h m p (K + 1) ∧
          AbsoluteGapPositive h m p (K + 1)) := by
  have hcellData := hcell
  rcases hcellData with ⟨_hK, hh, hm, hp, _hprevious, _hboundary⟩
  refine ⟨fun profile => oneTrigger_power_globalWinner_iff hp hh.le hm profile,
    ?_, ?_⟩
  · intro L hL
    exact directional_actual_support_iff_positiveAtGap hcell hL
  · obtain ⟨u, huData, huUnique⟩ :=
      exists_unique_contextPhase_of_firstZeroCell hcell
    refine ⟨u, ⟨huData.1, huData.2, ?_, ?_⟩, ?_⟩
    · intro L
      exact absolute_actual_support_iff_positiveAtGap hcell huData.1 huData.2
    · exact actual_opposite_trigger_shortest_separator
        hcell hKtwo huData.1 huData.2
    · intro v hv
      exact huUnique v ⟨hv.1, hv.2.1⟩


end PhonologicalCalculus.Context
