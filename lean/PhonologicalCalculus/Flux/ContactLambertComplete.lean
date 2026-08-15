import PhonologicalCalculus.Flux.ContactResponseComplete
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Topology.Order.IntermediateValue

/-!
# Positive Lambert branch and corrected contact balance

This module removes the remaining witness parameter from the scalar
Lambert inversion used by `FLUX-D4`.  It proves directly that, for every
positive real `z`, there is exactly one positive real `w` satisfying
`w * exp w = z`, and packages that solution as a noncomputable canonical
branch.

It also records the exact leading-balance consequence of the normalized
contact remainder.  The recovered-coefficient equation

`epsilon * (-log (t epsilon)) / (t epsilon)^Gamma -> C`

is equivalent to

`(t epsilon)^Gamma / (-log (t epsilon)) ~ epsilon / C`.

The product expression `(t epsilon)^Gamma * (-log (t epsilon)) ~ epsilon / C`
does not follow from that equation and is therefore not asserted here.
-/

namespace PhonologicalCalculus.Flux

open Asymptotics Filter Set
open scoped Topology

private theorem lambertKernel_strictMonoOn :
    StrictMonoOn (fun w : ℝ => w * Real.exp w) (Ici 0) := by
  intro a ha b _hb hab
  have hfirst : a * Real.exp a < b * Real.exp a :=
    mul_lt_mul_of_pos_right hab (Real.exp_pos a)
  have hbNonnegative : 0 ≤ b := le_trans ha hab.le
  have hsecond : b * Real.exp a ≤ b * Real.exp b :=
    mul_le_mul_of_nonneg_left (Real.exp_monotone hab.le) hbNonnegative
  exact lt_of_lt_of_le hfirst hsecond

/-- Every positive real has a unique positive preimage under `w ↦ w * exp w`.
This is the positive-real Lambert branch required by the contact-response
normal form. -/
theorem existsUnique_positive_lambertWitness {z : ℝ} (hz : 0 < z) :
    ∃! w : ℝ, 0 < w ∧ LambertWitness z w := by
  let f : ℝ → ℝ := fun w => w * Real.exp w
  have hzNonnegative : 0 ≤ z := hz.le
  have hfContinuous : Continuous f := by
    exact continuous_id.mul Real.continuous_exp
  have hUpper : z ≤ f z := by
    have hExp : 1 ≤ Real.exp z := by
      simpa only [Real.exp_zero] using Real.exp_monotone hzNonnegative
    dsimp [f]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hExp hzNonnegative
  have hzBetween : z ∈ Icc (f 0) (f z) := by
    constructor
    · simpa [f] using hzNonnegative
    · exact hUpper
  obtain ⟨w, hwInterval, hwEquation⟩ :=
    intermediate_value_Icc hzNonnegative hfContinuous.continuousOn hzBetween
  have hwPositive : 0 < w := by
    have hwNonnegative : 0 ≤ w := hwInterval.1
    have hwNonzero : w ≠ 0 := by
      intro hwZero
      subst w
      simp [f] at hwEquation
      linarith
    exact lt_of_le_of_ne hwNonnegative (Ne.symm hwNonzero)
  refine ⟨w, ⟨hwPositive, ?_⟩, ?_⟩
  · simpa [f, LambertWitness] using hwEquation
  · intro v hv
    apply lambertKernel_strictMonoOn.injOn
    · exact mem_Ici.mpr hv.1.le
    · exact mem_Ici.mpr hwPositive.le
    · have hwLambert : LambertWitness z w := by
        simpa [f, LambertWitness] using hwEquation
      simpa [LambertWitness] using hv.2.trans hwLambert.symm

/-- The canonical positive solution of `w * exp w = z` for positive `z`.
The value outside the positive domain is set to zero and is never used by
the contact-response theorem. -/
noncomputable def positiveLambertWitness (z : ℝ) : ℝ :=
  if hz : 0 < z then Classical.choose (existsUnique_positive_lambertWitness hz) else 0

theorem positiveLambertWitness_pos {z : ℝ} (hz : 0 < z) :
    0 < positiveLambertWitness z := by
  rw [positiveLambertWitness, dif_pos hz]
  exact (Classical.choose_spec (existsUnique_positive_lambertWitness hz)).1.1

theorem positiveLambertWitness_equation {z : ℝ} (hz : 0 < z) :
    LambertWitness z (positiveLambertWitness z) := by
  rw [positiveLambertWitness, dif_pos hz]
  exact (Classical.choose_spec (existsUnique_positive_lambertWitness hz)).1.2

theorem positiveLambertWitness_unique {z w : ℝ}
    (hz : 0 < z) (hw : 0 < w) (hEquation : LambertWitness z w) :
    w = positiveLambertWitness z := by
  rw [positiveLambertWitness, dif_pos hz]
  exact (Classical.choose_spec (existsUnique_positive_lambertWitness hz)).2
    w ⟨hw, hEquation⟩

/-- The canonical positive Lambert branch for the contact normal form. -/
noncomputable def contactLambertBranch (Gamma C epsilon : ℝ) : ℝ :=
  positiveLambertWitness (Gamma * C / epsilon)

theorem contactLambertBranch_pos
    {Gamma C epsilon : ℝ}
    (hGamma : 0 < Gamma) (hC : 0 < C) (hepsilon : 0 < epsilon) :
    0 < contactLambertBranch Gamma C epsilon := by
  apply positiveLambertWitness_pos
  exact div_pos (mul_pos hGamma hC) hepsilon

theorem contactLambertBranch_equation
    {Gamma C epsilon : ℝ}
    (hGamma : 0 < Gamma) (hC : 0 < C) (hepsilon : 0 < epsilon) :
    LambertWitness (Gamma * C / epsilon)
      (contactLambertBranch Gamma C epsilon) := by
  apply positiveLambertWitness_equation
  exact div_pos (mul_pos hGamma hC) hepsilon

/-! ## Correct leading-balance ratio -/

/-- The ratio whose convergence to one expresses the contact leading balance.
Its numerator is the contact scale and its denominator is the perturbation
scale. -/
noncomputable def contactLeadingBalanceRatio
    (Gamma C : ℝ) (t : ℝ → ℝ) (epsilon : ℝ) : ℝ :=
  ((t epsilon) ^ Gamma / (-Real.log (t epsilon))) / (epsilon / C)

/-- Pointwise algebra connecting the corrected leading-balance ratio to the
reciprocal recovered coefficient. -/
theorem contactLeadingBalanceRatio_eq_coefficientRatio
    {Gamma C epsilon : ℝ} {t : ℝ → ℝ}
    (hC : C ≠ 0) (hepsilon : 0 < epsilon)
    (ht : 0 < t epsilon) (htOne : t epsilon < 1) :
    contactLeadingBalanceRatio Gamma C t epsilon =
      C / contactRecoveredCoefficient Gamma t epsilon := by
  have hepsilon0 : epsilon ≠ 0 := hepsilon.ne'
  have hpow : (t epsilon) ^ Gamma ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos ht Gamma)
  have hlog : -Real.log (t epsilon) ≠ 0 := by
    exact neg_ne_zero.mpr (Real.log_neg ht htOne).ne
  unfold contactLeadingBalanceRatio contactRecoveredCoefficient
  field_simp [hC, hepsilon0, hpow, hlog]

/-- The normalized remainder yields the exact, algebraically correct
leading-balance ratio. -/
theorem contact_remainder_implies_leading_balance_ratio
    {Gamma C : ℝ} {t : ℝ → ℝ}
    (hC : 0 < C)
    (htPos : ∀ᶠ epsilon in 𝓝[>] (0 : ℝ), 0 < t epsilon)
    (htZero : Tendsto t (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hRemainder : Tendsto (contactNormalizedRemainder Gamma C t)
      (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    Tendsto (contactLeadingBalanceRatio Gamma C t)
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have hCoefficient : Tendsto (contactRecoveredCoefficient Gamma t)
      (𝓝[>] (0 : ℝ)) (𝓝 C) :=
    contact_remainder_implies_coefficient htPos hRemainder
  have hRatio : Tendsto
      (fun epsilon => C / contactRecoveredCoefficient Gamma t epsilon)
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have h := (tendsto_const_nhds : Tendsto (fun _ : ℝ => C)
      (𝓝[>] (0 : ℝ)) (𝓝 C)).div hCoefficient hC.ne'
    change Tendsto
      (fun epsilon => C / contactRecoveredCoefficient Gamma t epsilon)
      (𝓝[>] (0 : ℝ)) (𝓝 (C / C)) at h
    simpa only [div_self hC.ne'] using h
  refine hRatio.congr' ?_
  filter_upwards [self_mem_nhdsWithin, htPos,
    htZero.eventually_lt_const zero_lt_one] with epsilon hepsilon ht htOne
  exact (contactLeadingBalanceRatio_eq_coefficientRatio
    hC.ne' hepsilon ht htOne).symm

/-- Asymptotic-equivalence form of the corrected contact balance:
`t^Gamma / (-log t) ~ epsilon / C`. -/
theorem contact_remainder_implies_leading_balance
    {Gamma C : ℝ} {t : ℝ → ℝ}
    (hC : 0 < C)
    (htPos : ∀ᶠ epsilon in 𝓝[>] (0 : ℝ), 0 < t epsilon)
    (htZero : Tendsto t (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hRemainder : Tendsto (contactNormalizedRemainder Gamma C t)
      (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    (fun epsilon => (t epsilon) ^ Gamma / (-Real.log (t epsilon)))
      ~[𝓝[>] (0 : ℝ)] (fun epsilon => epsilon / C) := by
  apply isEquivalent_of_tendsto_one
  exact contact_remainder_implies_leading_balance_ratio
    hC htPos htZero hRemainder

/-! ## Integrated FLUX-D4 wrapper -/

/-- The complete declared odd-contact response with the positive Lambert
branch constructed internally rather than supplied as a theorem premise. -/
theorem flux_d4_complete_with_canonical_lambert
    {lambda p C : ℝ} {t : ℝ → ℝ}
    (hlambda : lambda ≠ 0) (hp : 1 < p) (hC : 0 < C) (r : ℕ)
    (htPos : ∀ᶠ epsilon in 𝓝[>] (0 : ℝ), 0 < t epsilon)
    (htZero : Tendsto t (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hRemainder : Tendsto
      (contactNormalizedRemainder (oddContactResponseExponent r p) C t)
      (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    (oddContactGauge lambda r 0 = 0 ∧
      ShiftEquivariant (oddContactGauge lambda r) lambda ∧
      StrictMono (oddContactGauge lambda r) ∧
      deriv (oddContactGauge lambda r) = raisedCosineMarginal lambda r ∧
      analyticOrderAt
          (fun z => oddContactGauge lambda r z - oddContactGauge lambda r 0) 0 =
        (2 * r + 1 : ℕ)) ∧
    Tendsto
        (contactRecoveredCoefficient (oddContactResponseExponent r p) t)
        (𝓝[>] (0 : ℝ)) (𝓝 C) ∧
    Tendsto
        (fun epsilon => Real.log (t epsilon) / Real.log epsilon)
        (𝓝[>] (0 : ℝ))
        (𝓝 (1 / oddContactResponseExponent r p)) ∧
    Tendsto
        (fun epsilon =>
          t epsilon /
            lambertNormalT epsilon (oddContactResponseExponent r p) C
              (contactLambertBranch
                (oddContactResponseExponent r p) C epsilon))
        (𝓝[>] (0 : ℝ)) (𝓝 1) ∧
    (fun epsilon =>
        (t epsilon) ^ (oddContactResponseExponent r p) /
          (-Real.log (t epsilon)))
      ~[𝓝[>] (0 : ℝ)] (fun epsilon => epsilon / C) := by
  have hGamma : 0 < oddContactResponseExponent r p :=
    oddContactResponseExponent_pos hp r
  have hwPos : ∀ᶠ epsilon in 𝓝[>] (0 : ℝ),
      0 < contactLambertBranch (oddContactResponseExponent r p) C epsilon := by
    filter_upwards [self_mem_nhdsWithin] with epsilon hepsilon
    exact contactLambertBranch_pos hGamma hC hepsilon
  have hLambert : ∀ᶠ epsilon in 𝓝[>] (0 : ℝ),
      LambertWitness
        (oddContactResponseExponent r p * C / epsilon)
        (contactLambertBranch
          (oddContactResponseExponent r p) C epsilon) := by
    filter_upwards [self_mem_nhdsWithin] with epsilon hepsilon
    exact contactLambertBranch_equation hGamma hC hepsilon
  have hComplete := flux_d4_complete_declared_response
    hlambda hp hC r htPos htZero hRemainder hwPos hLambert
  have hBalance := contact_remainder_implies_leading_balance
    hC htPos htZero hRemainder
  exact ⟨hComplete.1, hComplete.2.1, hComplete.2.2.1,
    hComplete.2.2.2, hBalance⟩

end PhonologicalCalculus.Flux
