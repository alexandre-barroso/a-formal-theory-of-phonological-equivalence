import PhonologicalCalculus.Flux.ContactResponse
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Scalar closure of the support-contact asymptotic

This module isolates the analytic scalar consequence used by `FLUX-D4`.
The normalized remainder is a registered explicit hypothesis. From that
hypothesis, positivity, and
support entry `t(epsilon) -> 0`, Lean derives both the recovered leading
coefficient and the logarithmic support-birth exponent.  The proof does not
postulate either reported limit.

No KKT/contact-germ derivation of the normalized remainder is asserted.
Keeping that boundary explicit prevents an asymptotic normal form from being
confused with an assumption-free theorem about every continuous HG grammar.
-/

namespace PhonologicalCalculus.Flux

open Filter Set
open scoped Topology

/-- The normalized remainder registered as an explicit analytic premise. -/
noncomputable def contactNormalizedRemainder
    (Gamma C : ℝ) (t : ℝ → ℝ) (epsilon : ℝ) : ℝ :=
  (C * (t epsilon) ^ Gamma + epsilon * Real.log (t epsilon)) /
    (t epsilon) ^ Gamma

/-- The coefficient read directly from the support-entry response. -/
noncomputable def contactRecoveredCoefficient
    (Gamma : ℝ) (t : ℝ → ℝ) (epsilon : ℝ) : ℝ :=
  epsilon * (-Real.log (t epsilon)) / (t epsilon) ^ Gamma

/-- Exact algebra relating the registered normalized remainder to the response
coefficient at every positive support value. -/
theorem contactRecoveredCoefficient_eq_sub_remainder
    {Gamma C epsilon : ℝ} {t : ℝ → ℝ}
    (ht : 0 < t epsilon) :
    contactRecoveredCoefficient Gamma t epsilon =
      C - contactNormalizedRemainder Gamma C t epsilon := by
  unfold contactRecoveredCoefficient contactNormalizedRemainder
  have hpow : (t epsilon) ^ Gamma ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos ht Gamma)
  field_simp [hpow]
  ring

/-- The normalized remainder equation implies the exact coefficient limit
`-epsilon log(t(epsilon)) / t(epsilon)^Gamma -> C`. -/
theorem contact_remainder_implies_coefficient
    {Gamma C : ℝ} {t : ℝ → ℝ}
    (htPos : ∀ᶠ epsilon in 𝓝[>] (0 : ℝ), 0 < t epsilon)
    (hRemainder : Tendsto (contactNormalizedRemainder Gamma C t)
      (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    Tendsto (contactRecoveredCoefficient Gamma t)
      (𝓝[>] (0 : ℝ)) (𝓝 C) := by
  have hLimit : Tendsto
      (fun epsilon : ℝ => C - contactNormalizedRemainder Gamma C t epsilon)
      (𝓝[>] (0 : ℝ)) (𝓝 C) := by
    simpa using (tendsto_const_nhds.sub hRemainder)
  refine hLimit.congr' ?_
  filter_upwards [htPos] with epsilon ht
  exact (contactRecoveredCoefficient_eq_sub_remainder ht).symm

/-- Along a positive response tending to zero, the logarithm tends to
negative infinity and its negation tends to positive infinity. -/
theorem contact_log_scales
    {t : ℝ → ℝ}
    (htPos : ∀ᶠ epsilon in 𝓝[>] (0 : ℝ), 0 < t epsilon)
    (htZero : Tendsto t (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    Tendsto (fun epsilon => Real.log (t epsilon))
        (𝓝[>] (0 : ℝ)) atBot ∧
      Tendsto (fun epsilon => -Real.log (t epsilon))
        (𝓝[>] (0 : ℝ)) atTop := by
  have htWithin : Tendsto t (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨htZero, htPos⟩
  have hlog : Tendsto (fun epsilon => Real.log (t epsilon))
      (𝓝[>] (0 : ℝ)) atBot :=
    Real.tendsto_log_nhdsGT_zero.comp htWithin
  exact ⟨hlog, tendsto_neg_atBot_atTop.comp hlog⟩

/-- The nested logarithm is negligible compared with the diverging support
logarithm.  This is the analytic step that makes the coefficient-insensitive
logarithmic exponent exact. -/
theorem contact_log_negLog_div_log_tendsto_zero
    {t : ℝ → ℝ}
    (htPos : ∀ᶠ epsilon in 𝓝[>] (0 : ℝ), 0 < t epsilon)
    (htZero : Tendsto t (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    Tendsto
      (fun epsilon =>
        Real.log (-Real.log (t epsilon)) / Real.log (t epsilon))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hscales := contact_log_scales htPos htZero
  have hsmall : Tendsto
      (fun epsilon =>
        Real.log (-Real.log (t epsilon)) /
          (-Real.log (t epsilon)))
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hscales.2
  have hneg := hsmall.neg
  simpa only [neg_zero] using hneg.congr' (by
    filter_upwards [htZero.eventually_lt_const zero_lt_one, htPos]
        with epsilon htOne ht
    have hlogNeg : Real.log (t epsilon) < 0 := Real.log_neg ht htOne
    field_simp [hlogNeg.ne])

/-- If the recovered coefficient has a positive finite limit, its logarithm
is negligible relative to the support logarithm. -/
theorem contact_log_coefficient_div_log_tendsto_zero
    {Gamma C : ℝ} {t : ℝ → ℝ}
    (hC : 0 < C)
    (htPos : ∀ᶠ epsilon in 𝓝[>] (0 : ℝ), 0 < t epsilon)
    (htZero : Tendsto t (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hCoefficient : Tendsto (contactRecoveredCoefficient Gamma t)
      (𝓝[>] (0 : ℝ)) (𝓝 C)) :
    Tendsto
      (fun epsilon =>
        Real.log (contactRecoveredCoefficient Gamma t epsilon) /
          Real.log (t epsilon))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hlogCoefficient : Tendsto
      (fun epsilon => Real.log
        (contactRecoveredCoefficient Gamma t epsilon))
      (𝓝[>] (0 : ℝ)) (𝓝 (Real.log C)) :=
    (Real.continuousAt_log hC.ne').tendsto.comp hCoefficient
  have hlogT := (contact_log_scales htPos htZero).1
  have hinv : Tendsto (fun epsilon => (Real.log (t epsilon))⁻¹)
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_inv_atBot_zero.comp hlogT
  simpa [div_eq_mul_inv] using hlogCoefficient.mul hinv

/-- Exact logarithmic decomposition of the response coefficient. -/
theorem log_contactRecoveredCoefficient
    {Gamma epsilon : ℝ} {t : ℝ → ℝ}
    (hepsilon : 0 < epsilon) (ht : 0 < t epsilon)
    (htOne : t epsilon < 1) :
    Real.log (contactRecoveredCoefficient Gamma t epsilon) =
      Real.log epsilon + Real.log (-Real.log (t epsilon)) -
        Gamma * Real.log (t epsilon) := by
  have hlogNeg : Real.log (t epsilon) < 0 := Real.log_neg ht htOne
  have hnegLog : 0 < -Real.log (t epsilon) := neg_pos.mpr hlogNeg
  have hpow : 0 < (t epsilon) ^ Gamma :=
    Real.rpow_pos_of_pos ht Gamma
  unfold contactRecoveredCoefficient
  rw [Real.log_div (mul_ne_zero hepsilon.ne' hnegLog.ne') hpow.ne',
    Real.log_mul hepsilon.ne' hnegLog.ne', Real.log_rpow ht]

/-- A positive finite coefficient limit forces the registered logarithmic
support-birth exponent.  This theorem derives the exponent from the response;
it does not assume it as a field of a KKT contract. -/
theorem contact_coefficient_implies_log_slope
    {Gamma C : ℝ} {t : ℝ → ℝ}
    (hGamma : 0 < Gamma) (hC : 0 < C)
    (htPos : ∀ᶠ epsilon in 𝓝[>] (0 : ℝ), 0 < t epsilon)
    (htZero : Tendsto t (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hCoefficient : Tendsto (contactRecoveredCoefficient Gamma t)
      (𝓝[>] (0 : ℝ)) (𝓝 C)) :
    Tendsto
      (fun epsilon => Real.log (t epsilon) / Real.log epsilon)
      (𝓝[>] (0 : ℝ)) (𝓝 (1 / Gamma)) := by
  have hlogCoeffDiv := contact_log_coefficient_div_log_tendsto_zero
    hC htPos htZero hCoefficient
  have hlogNegDiv := contact_log_negLog_div_log_tendsto_zero htPos htZero
  have hforward : Tendsto
      (fun epsilon => Real.log epsilon / Real.log (t epsilon))
      (𝓝[>] (0 : ℝ)) (𝓝 Gamma) := by
    have hcalc := (hlogCoeffDiv.sub hlogNegDiv).add
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => Gamma)
        (𝓝[>] (0 : ℝ)) (𝓝 Gamma))
    simpa only [sub_zero, zero_add] using hcalc.congr' (by
      filter_upwards [self_mem_nhdsWithin,
        htZero.eventually_lt_const zero_lt_one, htPos,
        hCoefficient.eventually_const_lt hC]
          with epsilon hepsilon htOne ht hcoeffPos
      have hlogTNeg : Real.log (t epsilon) < 0 := Real.log_neg ht htOne
      have hlogTNe : Real.log (t epsilon) ≠ 0 := hlogTNeg.ne
      have hidentity := log_contactRecoveredCoefficient
        (Gamma := Gamma) hepsilon ht htOne
      field_simp [hlogTNe]
      linarith)
  have hinverse : Tendsto
      (fun epsilon =>
        (Real.log epsilon / Real.log (t epsilon))⁻¹)
      (𝓝[>] (0 : ℝ)) (𝓝 Gamma⁻¹) :=
    hforward.inv₀ hGamma.ne'
  simpa only [one_div] using hinverse.congr' (by
    filter_upwards [self_mem_nhdsWithin,
      ((tendsto_id : Tendsto (fun x : ℝ => x) (𝓝 0) (𝓝 0)).mono_left
        inf_le_left).eventually_lt_const zero_lt_one,
      htZero.eventually_lt_const zero_lt_one, htPos]
        with epsilon hepsilon hepsilonOne htOne ht
    have hlogEpsNeg : Real.log epsilon < 0 :=
      Real.log_neg hepsilon hepsilonOne
    have hlogTNeg : Real.log (t epsilon) < 0 := Real.log_neg ht htOne
    field_simp [hlogEpsNeg.ne, hlogTNeg.ne])

/-- **FLUX-D4.PERTURBATION.04, scalar consequence.** Once the normalized
remainder is assumed explicitly, the two reported response limits follow
jointly and mechanically. -/
theorem flux_d4_scalar_contact_response
    {Gamma C : ℝ} {t : ℝ → ℝ}
    (hGamma : 0 < Gamma) (hC : 0 < C)
    (htPos : ∀ᶠ epsilon in 𝓝[>] (0 : ℝ), 0 < t epsilon)
    (htZero : Tendsto t (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hRemainder : Tendsto (contactNormalizedRemainder Gamma C t)
      (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    Tendsto (contactRecoveredCoefficient Gamma t)
        (𝓝[>] (0 : ℝ)) (𝓝 C) ∧
      Tendsto (fun epsilon => Real.log (t epsilon) / Real.log epsilon)
        (𝓝[>] (0 : ℝ)) (𝓝 (1 / Gamma)) := by
  have hCoefficient := contact_remainder_implies_coefficient htPos hRemainder
  exact ⟨hCoefficient,
    contact_coefficient_implies_log_slope hGamma hC htPos htZero hCoefficient⟩

/-! ## Lambert representative equivalence -/

/-- The positive logarithmic coordinate in which the contact equation has
the elementary form `u * exp u`. -/
noncomputable def contactLogCoordinate
    (Gamma : ℝ) (t : ℝ → ℝ) (epsilon : ℝ) : ℝ :=
  Gamma * (-Real.log (t epsilon))

/-- The response coefficient ratio is exactly the ratio of two elementary
Lambert products when `w` satisfies its defining equation. -/
theorem contactCoefficientRatio_eq_lambertProductRatio
    {Gamma C epsilon w : ℝ} {t : ℝ → ℝ}
    (hGamma : 0 < Gamma) (hC : 0 < C) (hepsilon : 0 < epsilon)
    (ht : 0 < t epsilon) (hw : 0 < w)
    (hLambert : LambertWitness (Gamma * C / epsilon) w) :
    contactRecoveredCoefficient Gamma t epsilon / C =
      (contactLogCoordinate Gamma t epsilon *
          Real.exp (contactLogCoordinate Gamma t epsilon)) /
        (w * Real.exp w) := by
  let u := contactLogCoordinate Gamma t epsilon
  have hGamma0 : Gamma ≠ 0 := hGamma.ne'
  have hC0 : C ≠ 0 := hC.ne'
  have hepsilon0 : epsilon ≠ 0 := hepsilon.ne'
  have ht0 : t epsilon ≠ 0 := ht.ne'
  have hpow : (t epsilon) ^ Gamma = Real.exp (-u) := by
    rw [Real.rpow_def_of_pos ht]
    congr 1
    dsimp [u, contactLogCoordinate]
    ring
  have hLambertMul : w * Real.exp w * epsilon = Gamma * C :=
    (eq_div_iff hepsilon0).mp hLambert
  unfold contactRecoveredCoefficient
  rw [hpow, Real.exp_neg]
  dsimp [u, contactLogCoordinate]
  field_simp [hGamma0, hC0, hepsilon0, Real.exp_ne_zero]
  linear_combination (-Real.log (t epsilon)) * hLambertMul

/-- Taking logarithms turns the Lambert-product ratio into the sum of a
linear gap and a monotone logarithmic correction. -/
theorem log_contactCoefficientRatio_eq_gap_add_logRatio
    {Gamma C epsilon w : ℝ} {t : ℝ → ℝ}
    (hGamma : 0 < Gamma) (hC : 0 < C) (hepsilon : 0 < epsilon)
    (ht : 0 < t epsilon) (htOne : t epsilon < 1) (hw : 0 < w)
    (hLambert : LambertWitness (Gamma * C / epsilon) w) :
    Real.log (contactRecoveredCoefficient Gamma t epsilon / C) =
      (contactLogCoordinate Gamma t epsilon - w) +
        Real.log (contactLogCoordinate Gamma t epsilon / w) := by
  have hlogT : Real.log (t epsilon) < 0 := Real.log_neg ht htOne
  have hu : 0 < contactLogCoordinate Gamma t epsilon := by
    unfold contactLogCoordinate
    exact mul_pos hGamma (neg_pos.mpr hlogT)
  rw [contactCoefficientRatio_eq_lambertProductRatio
    hGamma hC hepsilon ht hw hLambert]
  rw [Real.log_div
      (mul_ne_zero hu.ne' (Real.exp_ne_zero _))
      (mul_ne_zero hw.ne' (Real.exp_ne_zero _)),
    Real.log_mul hu.ne' (Real.exp_ne_zero _),
    Real.log_mul hw.ne' (Real.exp_ne_zero _),
    Real.log_exp, Real.log_exp,
    Real.log_div hu.ne' hw.ne']
  ring

/-- The logarithmic correction has the same sign as its linear gap, so it
cannot cancel that gap.  This elementary inequality is the rigidity step in
the asymptotic inversion. -/
theorem abs_gap_le_abs_gap_add_logRatio
    {u w : ℝ} (hu : 0 < u) (hw : 0 < w) :
    |u - w| ≤ |(u - w) + Real.log (u / w)| := by
  by_cases hwu : w ≤ u
  · have hgap : 0 ≤ u - w := sub_nonneg.mpr hwu
    have hratio : 1 ≤ u / w := (le_div_iff₀ hw).2 (by simpa using hwu)
    have hlog : 0 ≤ Real.log (u / w) := Real.log_nonneg hratio
    rw [abs_of_nonneg hgap, abs_of_nonneg (add_nonneg hgap hlog)]
    linarith
  · have huw : u < w := lt_of_not_ge hwu
    have hgap : u - w < 0 := sub_neg.mpr huw
    have hratioPos : 0 < u / w := div_pos hu hw
    have hratioOne : u / w < 1 := (div_lt_one hw).2 huw
    have hlog : Real.log (u / w) < 0 :=
      Real.log_neg hratioPos hratioOne
    rw [abs_of_neg hgap, abs_of_neg (add_neg hgap hlog)]
    linarith

/-- A coefficient-equivalent response and its exact positive Lambert
representative have asymptotically identical logarithmic coordinates. -/
theorem contact_lambert_logCoordinate_gap_tendsto_zero
    {Gamma C : ℝ} {t w : ℝ → ℝ}
    (hGamma : 0 < Gamma) (hC : 0 < C)
    (htPos : ∀ᶠ epsilon in 𝓝[>] (0 : ℝ), 0 < t epsilon)
    (htZero : Tendsto t (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hCoefficient : Tendsto (contactRecoveredCoefficient Gamma t)
      (𝓝[>] (0 : ℝ)) (𝓝 C))
    (hwPos : ∀ᶠ epsilon in 𝓝[>] (0 : ℝ), 0 < w epsilon)
    (hLambert : ∀ᶠ epsilon in 𝓝[>] (0 : ℝ),
      LambertWitness (Gamma * C / epsilon) (w epsilon)) :
    Tendsto
      (fun epsilon => contactLogCoordinate Gamma t epsilon - w epsilon)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hRatio : Tendsto
      (fun epsilon => contactRecoveredCoefficient Gamma t epsilon / C)
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have h := hCoefficient.div_const C
    simpa [hC.ne'] using h
  have hLogRatio : Tendsto
      (fun epsilon => Real.log
        (contactRecoveredCoefficient Gamma t epsilon / C))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := (Real.continuousAt_log one_ne_zero).tendsto.comp hRatio
    simpa only [Function.comp_def, Real.log_one] using h
  have hSum : Tendsto
      (fun epsilon =>
        (contactLogCoordinate Gamma t epsilon - w epsilon) +
          Real.log (contactLogCoordinate Gamma t epsilon / w epsilon))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    refine hLogRatio.congr' ?_
    filter_upwards [self_mem_nhdsWithin,
      ((tendsto_id : Tendsto (fun x : ℝ => x) (𝓝 0) (𝓝 0)).mono_left
        inf_le_left).eventually_lt_const zero_lt_one,
      htPos, htZero.eventually_lt_const zero_lt_one, hwPos, hLambert]
        with epsilon hepsilon hepsilonOne ht htOne hw hLam
    exact log_contactCoefficientRatio_eq_gap_add_logRatio
      hGamma hC hepsilon ht htOne hw hLam
  have hAbsSum : Tendsto
      (fun epsilon =>
        |(contactLogCoordinate Gamma t epsilon - w epsilon) +
          Real.log (contactLogCoordinate Gamma t epsilon / w epsilon)|)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using hSum.abs
  have hAbsGap : Tendsto
      (fun epsilon => |contactLogCoordinate Gamma t epsilon - w epsilon|)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    apply squeeze_zero'
    · exact Eventually.of_forall (fun _ => abs_nonneg _)
    · filter_upwards [htPos, htZero.eventually_lt_const zero_lt_one, hwPos]
          with epsilon ht htOne hw
      have hlogT : Real.log (t epsilon) < 0 := Real.log_neg ht htOne
      have hu : 0 < contactLogCoordinate Gamma t epsilon := by
        unfold contactLogCoordinate
        exact mul_pos hGamma (neg_pos.mpr hlogT)
      exact abs_gap_le_abs_gap_add_logRatio hu hw
    · exact hAbsSum
  exact (tendsto_zero_iff_abs_tendsto_zero _).2 hAbsGap

/-- **FLUX-D4.NORMALFORM.03, Lambert equivalence.**  The normalized response
remainder determines not only the coefficient and log slope but the full
ratio-one Lambert representative, for any positive branch satisfying the
defining Lambert equation. -/
theorem contact_remainder_implies_lambert_equivalence
    {Gamma C : ℝ} {t w : ℝ → ℝ}
    (hGamma : 0 < Gamma) (hC : 0 < C)
    (htPos : ∀ᶠ epsilon in 𝓝[>] (0 : ℝ), 0 < t epsilon)
    (htZero : Tendsto t (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hRemainder : Tendsto (contactNormalizedRemainder Gamma C t)
      (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hwPos : ∀ᶠ epsilon in 𝓝[>] (0 : ℝ), 0 < w epsilon)
    (hLambert : ∀ᶠ epsilon in 𝓝[>] (0 : ℝ),
      LambertWitness (Gamma * C / epsilon) (w epsilon)) :
    Tendsto
      (fun epsilon =>
        t epsilon / lambertNormalT epsilon Gamma C (w epsilon))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have hCoefficient := contact_remainder_implies_coefficient htPos hRemainder
  have hGap := contact_lambert_logCoordinate_gap_tendsto_zero
    hGamma hC htPos htZero hCoefficient hwPos hLambert
  have hExponent : Tendsto
      (fun epsilon =>
        (w epsilon - contactLogCoordinate Gamma t epsilon) / Gamma)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := hGap.neg.div_const Gamma
    simpa only [neg_sub, neg_zero, zero_div] using h
  have hExp : Tendsto
      (fun epsilon => Real.exp
        ((w epsilon - contactLogCoordinate Gamma t epsilon) / Gamma))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have h := (Real.continuous_exp.tendsto 0).comp hExponent
    change Tendsto
      (fun epsilon => Real.exp
        ((w epsilon - contactLogCoordinate Gamma t epsilon) / Gamma))
      (𝓝[>] (0 : ℝ)) (𝓝 (Real.exp 0)) at h
    simpa only [Real.exp_zero] using h
  refine hExp.congr' ?_
  filter_upwards [self_mem_nhdsWithin, htPos,
    htZero.eventually_lt_const zero_lt_one, hwPos, hLambert]
      with epsilon hepsilon ht htOne hw hLam
  have htExp : t epsilon = Real.exp
      (-contactLogCoordinate Gamma t epsilon / Gamma) := by
    unfold contactLogCoordinate
    have hGamma0 := hGamma.ne'
    have harg : -(Gamma * -Real.log (t epsilon)) / Gamma =
        Real.log (t epsilon) := by
      field_simp [hGamma0]
    rw [harg, Real.exp_log ht]
  rw [htExp,
    lambertNormalT_eq_exp hepsilon hGamma hC hw hLam,
    ← Real.exp_sub]
  congr 1
  ring

end PhonologicalCalculus.Flux
