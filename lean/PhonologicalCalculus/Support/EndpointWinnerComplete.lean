import PhonologicalCalculus.Support.EndpointSlopeComplete
import Mathlib.Tactic

/-!
# Complete endpoint-support winner contract

This module exposes the exact KKT data consumed by the endpoint-support
classification.  The contract records the positive-prefix length, the local
zero-site optimality condition, and the flux inequalities supplied by the
declared smooth convex path objective.  From that one contract, zero endpoint
site slope forces a full positive prefix, while positive endpoint site slope
forces the strict finite ceiling.
-/

namespace PhonologicalCalculus.Support

/-- KKT data for the endpoint-support query of one finite local path winner.
`positiveLength` is the number of positive follower coordinates.  The
derivative and local-minimum fields are used only when a first zero lies
inside the horizon; the flux fields are the positive-prefix KKT recurrence. -/
structure EndpointPathKKT
    (edge site : ℝ → ℝ) (horizon positiveLength : ℕ)
    (flux : ℕ → ℝ)
    (siteSlope edgeSlopeAtOne boundaryPrevious boundaryIncomingSlope : ℝ) : Prop where
  positiveLength_le_horizon : positiveLength ≤ horizon
  edgeSlope_zero : HasDerivAt edge 0 0
  siteSlope_zero : HasDerivAt site siteSlope 0
  edgeSlope_boundary :
    HasDerivAt edge boundaryIncomingSlope boundaryPrevious
  boundaryIncomingSlope_pos :
    positiveLength < horizon → 0 < boundaryIncomingSlope
  boundary_local_minimum : positiveLength < horizon →
    ∀ epsilon, 0 < epsilon →
      zeroSiteLiftObjective edge site boundaryPrevious 0 ≤
        zeroSiteLiftObjective edge site boundaryPrevious epsilon
  flux_drop : ∀ index, index < positiveLength →
    flux (index + 1) + siteSlope ≤ flux index
  terminal_flux_pos : 0 < flux positiveLength
  initial_flux_le : flux 0 ≤ edgeSlopeAtOne

/-- A declared winner predicate is represented exactly by its endpoint KKT
proof.  Strict convexity and KKT necessity/sufficiency belong to the
instantiating local path objective. -/
def ExactEndpointWinnerKKT {Candidate : Type*}
    (winner proofPredicate : Candidate → Prop) : Prop :=
  ∀ candidate, winner candidate ↔ proofPredicate candidate

/-- With zero endpoint site slope, an internal first zero contradicts the
local optimality condition.  Hence the positive prefix fills the horizon. -/
theorem zeroEndpointSlope_forces_fullPositivePrefix
    {edge site : ℝ → ℝ} {horizon positiveLength : ℕ}
    {flux : ℕ → ℝ}
    {edgeSlopeAtOne boundaryPrevious boundaryIncomingSlope : ℝ}
    (hkkt : EndpointPathKKT edge site horizon positiveLength flux 0
      edgeSlopeAtOne boundaryPrevious boundaryIncomingSlope) :
    positiveLength = horizon := by
  apply Nat.le_antisymm hkkt.positiveLength_le_horizon
  by_contra hnot
  have hfirstZero : positiveLength < horizon := Nat.lt_of_not_ge hnot
  have himprovement := zeroSiteLift_exists_strict_improvement
    hkkt.edgeSlope_zero hkkt.edgeSlope_boundary hkkt.siteSlope_zero
    (hkkt.boundaryIncomingSlope_pos hfirstZero)
  obtain ⟨epsilon, hepsilon, hlower⟩ := himprovement
  have hminimum := hkkt.boundary_local_minimum hfirstZero epsilon hepsilon
  exact (not_lt_of_ge hminimum) hlower

/-- Positive endpoint site slope and finite initial edge slope impose the
strict real-valued support ceiling. -/
theorem positiveEndpointSlope_forces_strictPrefixBound
    {edge site : ℝ → ℝ} {horizon positiveLength : ℕ}
    {flux : ℕ → ℝ}
    {siteSlope edgeSlopeAtOne boundaryPrevious boundaryIncomingSlope : ℝ}
    (hkkt : EndpointPathKKT edge site horizon positiveLength flux siteSlope
      edgeSlopeAtOne boundaryPrevious boundaryIncomingSlope) :
    (positiveLength : ℝ) * siteSlope < edgeSlopeAtOne := by
  exact flux_drop_strict_prefix_bound hkkt.flux_drop
    hkkt.terminal_flux_pos hkkt.initial_flux_le

/-- Exact integer ceiling implied by the strict real-valued endpoint bound. -/
theorem positiveEndpointSlope_forces_integerPrefixBound
    {edge site : ℝ → ℝ} {horizon positiveLength : ℕ}
    {flux : ℕ → ℝ}
    {siteSlope edgeSlopeAtOne boundaryPrevious boundaryIncomingSlope : ℝ}
    (hkkt : EndpointPathKKT edge site horizon positiveLength flux siteSlope
      edgeSlopeAtOne boundaryPrevious boundaryIncomingSlope)
    (hsiteSlope : 0 < siteSlope) :
    positiveLength ≤ Nat.ceil (edgeSlopeAtOne / siteSlope) - 1 := by
  apply strictPositivePrefix_le_ceil_sub_one positiveLength hsiteSlope
  exact positiveEndpointSlope_forces_strictPrefixBound hkkt

/-- Winner-level transport of the endpoint classification through an exact
KKT contract. -/
theorem endpointWinner_supportClassification
    {Candidate : Type*} {edge site : ℝ → ℝ}
    {horizon : Candidate → ℕ} {positiveLength : Candidate → ℕ}
    {flux : Candidate → ℕ → ℝ}
    {boundaryPrevious boundaryIncomingSlope : Candidate → ℝ}
    {siteSlope edgeSlopeAtOne : ℝ}
    (winner : Candidate → Prop)
    (hProof : ExactEndpointWinnerKKT winner
      (fun candidate ↦ EndpointPathKKT edge site
        (horizon candidate) (positiveLength candidate)
        (flux candidate) siteSlope edgeSlopeAtOne
        (boundaryPrevious candidate) (boundaryIncomingSlope candidate))) :
    (siteSlope = 0 → ∀ candidate, winner candidate →
      positiveLength candidate = horizon candidate) ∧
    (0 < siteSlope → ∀ candidate, winner candidate →
      (positiveLength candidate : ℝ) * siteSlope < edgeSlopeAtOne ∧
      positiveLength candidate ≤
        Nat.ceil (edgeSlopeAtOne / siteSlope) - 1) := by
  constructor
  · intro hzero candidate hwinner
    have hkkt := (hProof candidate).1 hwinner
    subst siteSlope
    exact zeroEndpointSlope_forces_fullPositivePrefix hkkt
  · intro hpositive candidate hwinner
    have hkkt := (hProof candidate).1 hwinner
    exact ⟨positiveEndpointSlope_forces_strictPrefixBound hkkt,
      positiveEndpointSlope_forces_integerPrefixBound hkkt hpositive⟩

/-- **SUP-E1.GENERAL.03**, complete typed endpoint-support package relative
to the explicit smooth-convex KKT-to-winner contract. -/
theorem sup_e1_completeEndpointWinnerBridge :
    ∀ {Candidate : Type*} {edge site : ℝ → ℝ}
      {horizon : Candidate → ℕ} {positiveLength : Candidate → ℕ}
      {flux : Candidate → ℕ → ℝ}
      {boundaryPrevious boundaryIncomingSlope : Candidate → ℝ}
      {siteSlope edgeSlopeAtOne : ℝ}
      (winner : Candidate → Prop),
      ExactEndpointWinnerKKT winner
        (fun candidate ↦ EndpointPathKKT edge site
          (horizon candidate) (positiveLength candidate)
          (flux candidate) siteSlope edgeSlopeAtOne
          (boundaryPrevious candidate) (boundaryIncomingSlope candidate)) →
      (siteSlope = 0 → ∀ candidate, winner candidate →
        positiveLength candidate = horizon candidate) ∧
      (0 < siteSlope → ∀ candidate, winner candidate →
        (positiveLength candidate : ℝ) * siteSlope < edgeSlopeAtOne ∧
        positiveLength candidate ≤
          Nat.ceil (edgeSlopeAtOne / siteSlope) - 1) := by
  intro Candidate edge site horizon positiveLength flux boundaryPrevious
    boundaryIncomingSlope siteSlope edgeSlopeAtOne winner hProof
  exact endpointWinner_supportClassification winner hProof

end PhonologicalCalculus.Support
