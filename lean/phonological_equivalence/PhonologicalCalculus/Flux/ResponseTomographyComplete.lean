import PhonologicalCalculus.Flux.Tomography
import Mathlib.Tactic

namespace PhonologicalCalculus.Flux

open Filter Finset Set
open scoped Topology

noncomputable def poweredTailResponse {Theta : Type*}
    (profile : Theta → ℕ → ℝ) (mu epsilon : ℝ)
    (first last : ℕ) (parameter : Theta) : ℝ :=
  mu * (1 + epsilon) *
    ∑ j ∈ Icc first last, (profile parameter j) ^ epsilon

def ExactConstitutiveResponse {Theta : Type*}
    (law : ℝ → ℝ) (sample : Theta → ℝ)
    (response : Theta → ℝ) : Prop :=
  ∀ parameter, law (sample parameter) = response parameter

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

theorem eqOn_sampleRange_of_exactResponses
    {Theta : Type*} {leftLaw rightLaw : ℝ → ℝ}
    {sample : Theta → ℝ} {leftResponse rightResponse : Theta → ℝ}
    (hleft : ExactConstitutiveResponse leftLaw sample leftResponse)
    (hright : ExactConstitutiveResponse rightLaw sample rightResponse)
    (hresponse : leftResponse = rightResponse) :
    ∀ parameter, leftLaw (sample parameter) = rightLaw (sample parameter) := by
  intro parameter
  rw [hleft parameter, hright parameter, hresponse]

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
