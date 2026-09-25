import PhonologicalCalculus.Support.EndpointSlope
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Shift

namespace PhonologicalCalculus.Support

open Set

theorem exists_positive_improvement_of_hasDerivAt_neg
    {f : ℝ → ℝ} {slope : ℝ}
    (hderiv : HasDerivAt f slope 0) (hslope : slope < 0) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ f epsilon < f 0 := by
  by_contra hnone
  push Not at hnone
  have hminimum : IsMinOn f (Ici (0 : ℝ)) 0 := by
    intro epsilon hepsilon
    have hepsilonNonnegative : 0 ≤ epsilon := by
      simpa only [mem_Ici] using hepsilon
    rcases eq_or_lt_of_le hepsilonNonnegative with rfl | hpositive
    · exact le_refl (f 0)
    · exact hnone epsilon hpositive
  have hlocal : IsLocalMinOn f (Ici (0 : ℝ)) 0 := hminimum.localize
  have hone : (1 : ℝ) ∈ posTangentConeAt (Ici (0 : ℝ)) 0 := by
    rw [one_mem_posTangentConeAt_iff_mem_closure]
    rw [inter_eq_left.mpr Ioi_subset_Ici_self, closure_Ioi]
    exact Set.mem_Ici.mpr le_rfl
  have hnonnegative := hlocal.hasFDerivWithinAt_nonneg
    hderiv.hasFDerivAt.hasFDerivWithinAt hone
  have hslopeNonnegative : 0 ≤ slope := by
    simpa [ContinuousLinearMap.toSpanSingleton_apply] using hnonnegative
  exact (not_lt_of_ge hslopeNonnegative) hslope

def zeroSiteLiftObjective
    (edge site : ℝ → ℝ) (previous epsilon : ℝ) : ℝ :=
  edge (previous - epsilon) + edge epsilon + site epsilon

theorem zeroSiteLiftObjective_hasDerivAt
    {edge site : ℝ → ℝ}
    {previous edgeSlopeAtZero edgeSlopeAtPrevious siteSlopeAtZero : ℝ}
    (hedgeZero : HasDerivAt edge edgeSlopeAtZero 0)
    (hedgePrevious : HasDerivAt edge edgeSlopeAtPrevious previous)
    (hsiteZero : HasDerivAt site siteSlopeAtZero 0) :
    HasDerivAt (zeroSiteLiftObjective edge site previous)
      (zeroLiftingRightDerivative edgeSlopeAtZero edgeSlopeAtPrevious
        siteSlopeAtZero) 0 := by
  have hedgePreviousAtInnerValue :
      HasDerivAt edge edgeSlopeAtPrevious (previous - 0) := by
    simpa using hedgePrevious
  have hincoming : HasDerivAt
      (fun epsilon : ℝ => edge (previous - epsilon))
      (-edgeSlopeAtPrevious) 0 := by
    exact hedgePreviousAtInnerValue.comp_const_sub previous 0
  change HasDerivAt
    (fun epsilon : ℝ =>
      edge (previous - epsilon) + edge epsilon + site epsilon)
    (edgeSlopeAtZero - edgeSlopeAtPrevious + siteSlopeAtZero) 0
  have hsum := (hincoming.add hedgeZero).add hsiteZero
  have hfunction : HasDerivAt
      (fun epsilon : ℝ =>
        edge (previous - epsilon) + edge epsilon + site epsilon)
      (-edgeSlopeAtPrevious + edgeSlopeAtZero + siteSlopeAtZero) 0 := by
    apply hsum.congr_of_eventuallyEq
    filter_upwards with epsilon
    rfl
  exact hfunction.congr_deriv (by ring)

theorem zeroSiteLift_exists_strict_improvement
    {edge site : ℝ → ℝ} {previous incomingSlope : ℝ}
    (hedgeZero : HasDerivAt edge 0 0)
    (hedgePrevious : HasDerivAt edge incomingSlope previous)
    (hsiteZero : HasDerivAt site 0 0)
    (hincoming : 0 < incomingSlope) :
    ∃ epsilon : ℝ, 0 < epsilon ∧
      zeroSiteLiftObjective edge site previous epsilon <
        zeroSiteLiftObjective edge site previous 0 := by
  have hderiv := zeroSiteLiftObjective_hasDerivAt
    hedgeZero hedgePrevious hsiteZero
  have hslope :
      zeroLiftingRightDerivative 0 incomingSlope 0 < 0 :=
    zeroLiftingRightDerivative_negative hincoming
  exact exists_positive_improvement_of_hasDerivAt_neg hderiv hslope

theorem flux_drop_telescope
    (flux : ℕ → ℝ) (siteSlope : ℝ) :
    ∀ K : ℕ,
      (∀ i : ℕ, i < K → flux (i + 1) + siteSlope ≤ flux i) →
      flux K + (K : ℝ) * siteSlope ≤ flux 0 := by
  intro K
  induction K with
  | zero =>
      intro _
      norm_num
  | succ K ih =>
      intro hdrop
      have hprefix : ∀ i : ℕ, i < K →
          flux (i + 1) + siteSlope ≤ flux i := by
        intro i hi
        exact hdrop i (Nat.lt_succ_of_lt hi)
      have htelescope := ih hprefix
      have hlast := hdrop K (Nat.lt_succ_self K)
      push_cast
      nlinarith

theorem flux_drop_strict_prefix_bound
    {flux : ℕ → ℝ} {siteSlope edgeSlopeAtOne : ℝ} {K : ℕ}
    (hdrop : ∀ i : ℕ, i < K →
      flux (i + 1) + siteSlope ≤ flux i)
    (hterminal : 0 < flux K)
    (hinitial : flux 0 ≤ edgeSlopeAtOne) :
    (K : ℝ) * siteSlope < edgeSlopeAtOne := by
  have htelescope := flux_drop_telescope flux siteSlope K hdrop
  linarith

         
theorem sup_e1_endpoint_classification_core :
    (∀ (edge site : ℝ → ℝ) (previous incomingSlope : ℝ),
      HasDerivAt edge 0 0 →
      HasDerivAt edge incomingSlope previous →
      HasDerivAt site 0 0 → 0 < incomingSlope →
      ∃ epsilon : ℝ, 0 < epsilon ∧
        zeroSiteLiftObjective edge site previous epsilon <
          zeroSiteLiftObjective edge site previous 0) ∧
    (∀ (flux : ℕ → ℝ) (siteSlope edgeSlopeAtOne : ℝ) (K : ℕ),
      (∀ i : ℕ, i < K → flux (i + 1) + siteSlope ≤ flux i) →
      0 < flux K → flux 0 ≤ edgeSlopeAtOne →
      (K : ℝ) * siteSlope < edgeSlopeAtOne) := by
  constructor
  · intro edge site previous incomingSlope hedgeZero hedgePrevious
      hsiteZero hincoming
    exact zeroSiteLift_exists_strict_improvement
      hedgeZero hedgePrevious hsiteZero hincoming
  · intro flux siteSlope edgeSlopeAtOne K hdrop hterminal hinitial
    exact flux_drop_strict_prefix_bound hdrop hterminal hinitial

end PhonologicalCalculus.Support
