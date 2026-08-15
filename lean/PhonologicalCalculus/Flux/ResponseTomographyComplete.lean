import PhonologicalCalculus.Flux.Tomography
import Mathlib.Tactic

/-!
# Complete accumulating-response tomography

This module connects the terminal KKT recurrence to the analytic identity
theorem.  A declared optimizer response reads the constitutive flux at each
sampled powered drop.  If two analytic laws generate the same complete
response and those sampled drops accumulate at an interior point of their
common connected domain, the laws coincide throughout that domain.
-/

namespace PhonologicalCalculus.Flux

open Filter Finset Set
open scoped Topology

/-- Tail statistic appearing on the right-hand side of the terminal KKT
recurrence. -/
noncomputable def poweredTailResponse {Theta : Type*}
    (profile : Theta → ℕ → ℝ) (mu epsilon : ℝ)
    (first last : ℕ) (parameter : Theta) : ℝ :=
  mu * (1 + epsilon) *
    ∑ j ∈ Icc first last, (profile parameter j) ^ epsilon

/-- A response is an exact reader of a constitutive law on the sampled
powered-drop coordinates. -/
def ExactConstitutiveResponse {Theta : Type*}
    (law : ℝ → ℝ) (sample : Theta → ℝ)
    (response : Theta → ℝ) : Prop :=
  ∀ parameter, law (sample parameter) = response parameter

/-- The terminal recurrence produces the exact response reader, with the
bridge from the recurrence coordinate to the constitutive-law argument kept
explicit. -/
theorem exactConstitutiveResponse_of_terminalRecurrence
    {Theta : Type*} {law : ℝ → ℝ}
    {flux profile : Theta → ℕ → ℝ} {sample : Theta → ℝ}
    {mu epsilon : ℝ} {first last : ℕ}
    (hfirst : first ≤ last)
    (hstep : ∀ parameter index,
      flux parameter index - flux parameter (index + 1) =
        mu * (1 + epsilon) * (profile parameter index) ^ epsilon)
    (hterminal : ∀ parameter, flux parameter (last + 1) = 0)
    (hsample : ∀ parameter,
      flux parameter first = law (sample parameter)) :
    ExactConstitutiveResponse law sample
      (poweredTailResponse profile mu epsilon first last) := by
  intro parameter
  rw [← hsample parameter]
  exact flux_d5_recurrence_02 hfirst (hstep parameter)
    (hterminal parameter)

/-- Equality of two complete exact responses gives equality of the two laws
at every sampled constitutive coordinate. -/
theorem eqOn_sampleRange_of_exactResponses
    {Theta : Type*} {leftLaw rightLaw : ℝ → ℝ}
    {sample : Theta → ℝ} {leftResponse rightResponse : Theta → ℝ}
    (hleft : ExactConstitutiveResponse leftLaw sample leftResponse)
    (hright : ExactConstitutiveResponse rightLaw sample rightResponse)
    (hresponse : leftResponse = rightResponse) :
    ∀ parameter, leftLaw (sample parameter) = rightLaw (sample parameter) := by
  intro parameter
  rw [hleft parameter, hright parameter, hresponse]

/-- An accumulating sampled range converts equality of complete exact
responses into equality on a punctured-neighbourhood frequency set. -/
theorem frequently_eq_of_accumulating_exactResponses
    {Theta : Type*} {leftLaw rightLaw : ℝ → ℝ}
    {sample : Theta → ℝ} {leftResponse rightResponse : Theta → ℝ}
    {base : ℝ}
    (hleft : ExactConstitutiveResponse leftLaw sample leftResponse)
    (hright : ExactConstitutiveResponse rightLaw sample rightResponse)
    (hresponse : leftResponse = rightResponse)
    (haccumulation : ∃ᶠ point in 𝓝[≠] base,
      ∃ parameter, sample parameter = point) :
    ∃ᶠ point in 𝓝[≠] base, leftLaw point = rightLaw point := by
  apply haccumulation.mono
  intro point hpoint
  obtain ⟨parameter, rfl⟩ := hpoint
  exact eqOn_sampleRange_of_exactResponses hleft hright hresponse parameter

/-- **FLUX-D5.IDENTITY.03**, semantic closure.  Complete response equality on
an interior accumulating sample identifies the two analytic constitutive laws
throughout their common preconnected domain. -/
theorem accumulatingExactResponses_identify
    {Theta : Type*} {domain : Set ℝ}
    {leftLaw rightLaw : ℝ → ℝ} {sample : Theta → ℝ}
    {leftResponse rightResponse : Theta → ℝ} {base : ℝ}
    (hleftAnalytic : AnalyticOnNhd ℝ leftLaw domain)
    (hrightAnalytic : AnalyticOnNhd ℝ rightLaw domain)
    (hdomain : IsPreconnected domain) (hbase : base ∈ domain)
    (hleft : ExactConstitutiveResponse leftLaw sample leftResponse)
    (hright : ExactConstitutiveResponse rightLaw sample rightResponse)
    (hresponse : leftResponse = rightResponse)
    (haccumulation : ∃ᶠ point in 𝓝[≠] base,
      ∃ parameter, sample parameter = point) :
    EqOn leftLaw rightLaw domain := by
  apply flux_d5_identity_03 hleftAnalytic hrightAnalytic hdomain hbase
  exact frequently_eq_of_accumulating_exactResponses
    hleft hright hresponse haccumulation

/-- Full KKT-to-tomography chain for two laws evaluated on one shared exact
optimizer profile.  The theorem exposes each recurrence, terminal, sample,
analyticity, connectedness, and accumulation premise separately. -/
theorem terminalKKT_accumulatingResponse_identifies
    {Theta : Type*} {domain : Set ℝ}
    {leftLaw rightLaw : ℝ → ℝ}
    {leftFlux rightFlux profile : Theta → ℕ → ℝ}
    {sample : Theta → ℝ} {mu epsilon : ℝ}
    {first last : ℕ} {base : ℝ}
    (hfirst : first ≤ last)
    (hleftStep : ∀ parameter index,
      leftFlux parameter index - leftFlux parameter (index + 1) =
        mu * (1 + epsilon) * (profile parameter index) ^ epsilon)
    (hrightStep : ∀ parameter index,
      rightFlux parameter index - rightFlux parameter (index + 1) =
        mu * (1 + epsilon) * (profile parameter index) ^ epsilon)
    (hleftTerminal : ∀ parameter, leftFlux parameter (last + 1) = 0)
    (hrightTerminal : ∀ parameter, rightFlux parameter (last + 1) = 0)
    (hleftSample : ∀ parameter,
      leftFlux parameter first = leftLaw (sample parameter))
    (hrightSample : ∀ parameter,
      rightFlux parameter first = rightLaw (sample parameter))
    (hleftAnalytic : AnalyticOnNhd ℝ leftLaw domain)
    (hrightAnalytic : AnalyticOnNhd ℝ rightLaw domain)
    (hdomain : IsPreconnected domain) (hbase : base ∈ domain)
    (haccumulation : ∃ᶠ point in 𝓝[≠] base,
      ∃ parameter, sample parameter = point) :
    EqOn leftLaw rightLaw domain := by
  let response : Theta → ℝ :=
    poweredTailResponse profile mu epsilon first last
  have hleft : ExactConstitutiveResponse leftLaw sample response :=
    exactConstitutiveResponse_of_terminalRecurrence hfirst hleftStep
      hleftTerminal hleftSample
  have hright : ExactConstitutiveResponse rightLaw sample response :=
    exactConstitutiveResponse_of_terminalRecurrence hfirst hrightStep
      hrightTerminal hrightSample
  exact accumulatingExactResponses_identify
    hleftAnalytic hrightAnalytic hdomain hbase hleft hright rfl haccumulation

end PhonologicalCalculus.Flux
