import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Two-trigger phase and support calculations

This module formalizes the finite phase fixtures and the power-sum comparison
at the heart of the equal-endpoint two-trigger calculation.  For a positive
exponent `q`, `shiftedPowerSum K q u` is the phase mass

`sum (r + u)^q`, for `r = 0, ..., K - 1`.

The three critical path spans use shifts `0`, `1 / 2`, and `1`.  Their exact
ordering supplies the strict pre-critical regime, the half-phase boundary,
and the post-critical regime.  The analytic step connecting these masses to
the optimizer of the absolute-edge obstacle problem is intentionally not
encoded here.
-/

namespace PhonologicalCalculus.Context

/-- The shifted power sum in reach--phase coordinates. -/
noncomputable def shiftedPowerSum (K : ℕ) (q u : ℝ) : ℝ :=
  ∑ r ∈ Finset.range K, Real.rpow ((r : ℝ) + u) q

theorem shiftedPowerSum_mono {K : ℕ} {q u v : ℝ}
    (hq : 0 < q) (hu : 0 ≤ u) (huv : u ≤ v) :
    shiftedPowerSum K q u ≤ shiftedPowerSum K q v := by
  unfold shiftedPowerSum
  apply Finset.sum_le_sum
  intro r hr
  exact Real.rpow_le_rpow (by positivity)
    (by linarith) hq.le

theorem shiftedPowerSum_strictMono {K : ℕ} {q u v : ℝ}
    (hK : 0 < K) (hq : 0 < q) (hu : 0 ≤ u) (huv : u < v) :
    shiftedPowerSum K q u < shiftedPowerSum K q v := by
  unfold shiftedPowerSum
  apply Finset.sum_lt_sum_of_nonempty
  · exact Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hK)
  · intro r hr
    exact Real.rpow_lt_rpow (by positivity)
      (by linarith) hq

/-- The three masses associated with spans `2K-1`, `2K`, and `2K+1`,
after their common positive factor has been removed. -/
inductive CriticalSpan where
  | before
  | middle
  | after
  deriving DecidableEq

noncomputable def criticalMass (K : ℕ) (q : ℝ) : CriticalSpan → ℝ
  | .before => shiftedPowerSum K q 0
  | .middle => shiftedPowerSum K q (1 / 2)
  | .after => shiftedPowerSum K q 1

/-- The algebraic contact test at a critical span.  The free depth reaches
the lower obstacle exactly when the phase mass does not exceed the span mass. -/
def criticalContact (K : ℕ) (q u : ℝ) (span : CriticalSpan) : Prop :=
  shiftedPowerSum K q u ≤ criticalMass K q span

theorem before_critical_no_contact {K : ℕ} {q u : ℝ}
    (hK : 0 < K) (hq : 0 < q) (hu : 0 < u) :
    ¬ criticalContact K q u .before := by
  intro hcontact
  have hstrict : shiftedPowerSum K q 0 < shiftedPowerSum K q u :=
    shiftedPowerSum_strictMono hK hq (le_refl 0) hu
  exact (not_lt_of_ge hcontact) hstrict

theorem middle_critical_contact_iff {K : ℕ} {q u : ℝ}
    (hK : 0 < K) (hq : 0 < q) (hu : 0 ≤ u) :
    criticalContact K q u .middle ↔ u ≤ 1 / 2 := by
  constructor
  · intro hcontact
    by_contra hnot
    have hhalf : (1 / 2 : ℝ) < u := lt_of_not_ge hnot
    have hstrict := shiftedPowerSum_strictMono hK hq (by norm_num) hhalf
    exact (not_lt_of_ge hcontact) hstrict
  · intro hhalf
    exact shiftedPowerSum_mono hq hu hhalf

theorem after_critical_contact {K : ℕ} {q u : ℝ}
    (hq : 0 < q) (hu : 0 ≤ u) (huOne : u ≤ 1) :
    criticalContact K q u .after :=
  shiftedPowerSum_mono hq hu huOne

/-- The three exact support comparisons for every positive integer `K` and
positive powered-path exponent `q`. -/
theorem critical_support_regimes {K : ℕ} {q u : ℝ}
    (hK : 0 < K) (hq : 0 < q) (hu : 0 < u) (huOne : u ≤ 1) :
    ¬ criticalContact K q u .before ∧
      (criticalContact K q u .middle ↔ u ≤ 1 / 2) ∧
      criticalContact K q u .after := by
  exact ⟨before_critical_no_contact hK hq hu,
    middle_critical_contact_iff hK hq hu.le,
    after_critical_contact hq hu.le huOne⟩

/-- The quadratic (`p = 2`, hence `q = 1`) edge/site ratio determined by a
reach `K` and phase `u`. -/
noncomputable def quadraticPhaseRatio (K : ℕ) (u : ℝ) : ℝ :=
  shiftedPowerSum K 1 u / 2

/-- `CTX-C1.PHASE.01`: the two registered phase coordinates at reach four
give ratios `7/2` and `9/2`. -/
theorem ctx_c1_phase_01 :
    [quadraticPhaseRatio 4 (1 / 4), quadraticPhaseRatio 4 (3 / 4)] =
      [7 / 2, 9 / 2] := by
  norm_num [quadraticPhaseRatio, shiftedPowerSum]

/-- The center value at the quadratic critical span, obtained by truncating
the free center value at the lower obstacle. -/
noncomputable def quadraticCriticalCenter (K : ℕ) (u : ℝ) : ℝ :=
  max (1 - shiftedPowerSum K 1 (1 / 2) / shiftedPowerSum K 1 u) 0

/-- `CTX-C1.CENTER.02`: at span eight the low-phase fixture contacts the
obstacle, while the high-phase fixture has center value `1/9`. -/
theorem ctx_c1_center_02 :
    [quadraticCriticalCenter 4 (1 / 4),
      quadraticCriticalCenter 4 (3 / 4)] = [0, 1 / 9] := by
  norm_num [quadraticCriticalCenter, shiftedPowerSum, max_eq_left, max_eq_right]

/-- The binary carrier retained for the two-trigger support consumer. -/
noncomputable def phaseBit (u : ℝ) : ℕ :=
  if 1 / 2 < u then 1 else 0

noncomputable def binarySupportCarrier (K : ℕ) (u : ℝ) : ℕ × ℕ :=
  (K, phaseBit u)

theorem phaseBit_eq_zero_iff (u : ℝ) :
    phaseBit u = 0 ↔ u ≤ 1 / 2 := by
  simp [phaseBit, not_lt]

theorem phaseBit_eq_one_iff (u : ℝ) :
    phaseBit u = 1 ↔ 1 / 2 < u := by
  simp [phaseBit]

/-- `CTX-C1.CARRIER.03`: the registered equal-reach phases occupy the two
distinct carrier cells and give opposite middle-span support verdicts. -/
theorem ctx_c1_carrier_03 :
    [binarySupportCarrier 4 (1 / 4), binarySupportCarrier 4 (3 / 4)] =
        [(4, 0), (4, 1)] ∧
      criticalContact 4 1 (1 / 4) .middle ∧
      ¬ criticalContact 4 1 (3 / 4) .middle := by
  norm_num [binarySupportCarrier, phaseBit, criticalContact, criticalMass,
    shiftedPowerSum]

/-- Within a fixed reach cell, equality of the phase bit preserves the
critical binary support answer. -/
theorem phaseBit_preserves_middle_contact {K : ℕ} {q u v : ℝ}
    (hK : 0 < K) (hq : 0 < q) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hbit : phaseBit u = phaseBit v) :
    criticalContact K q u .middle ↔ criticalContact K q v .middle := by
  rw [middle_critical_contact_iff hK hq hu,
    middle_critical_contact_iff hK hq hv]
  rw [← phaseBit_eq_zero_iff u, ← phaseBit_eq_zero_iff v, hbit]

end PhonologicalCalculus.Context
