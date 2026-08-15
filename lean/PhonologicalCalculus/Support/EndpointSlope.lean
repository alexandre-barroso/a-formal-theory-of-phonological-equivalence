import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Convex.Deriv

/-!
# Endpoint-slope support lemmas

This module isolates the exact local derivative and integer-conversion steps
used by the endpoint-slope support classification.  The final section records
the order-theoretic implication from a strictly improving zero-site lift to
strict positivity of a minimizing profile.  Deriving the improving lift from
the full differentiability and convexity hypotheses remains a separate
analytic proof requirement.
-/

namespace PhonologicalCalculus.Support

/-- The right derivative contributed by lifting a zero coordinate while its
left neighbour remains fixed. -/
def zeroLiftingRightDerivative
    (edgeSlopeAtZero edgeSlopeAtPrevious siteSlopeAtZero : ℝ) : ℝ :=
  edgeSlopeAtZero - edgeSlopeAtPrevious + siteSlopeAtZero

/-- Exact local derivative identity for the endpoint lift. -/
theorem zeroLiftingRightDerivative_eq
    (edgeSlopeAtZero edgeSlopeAtPrevious siteSlopeAtZero : ℝ) :
    zeroLiftingRightDerivative edgeSlopeAtZero edgeSlopeAtPrevious
        siteSlopeAtZero =
      edgeSlopeAtZero - edgeSlopeAtPrevious + siteSlopeAtZero := by
  rfl

/-- When the edge and site slopes at zero vanish, lifting a zero site has
derivative equal to the negative incoming edge slope. -/
theorem zeroLiftingRightDerivative_zero_slopes
    (edgeSlopeAtPrevious : ℝ) :
    zeroLiftingRightDerivative 0 edgeSlopeAtPrevious 0 =
      -edgeSlopeAtPrevious := by
  simp [zeroLiftingRightDerivative]

/-- A positive incoming edge slope therefore makes the zero-site lift a
strict descent direction. -/
theorem zeroLiftingRightDerivative_negative
    {edgeSlopeAtPrevious : ℝ} (hEdge : 0 < edgeSlopeAtPrevious) :
    zeroLiftingRightDerivative 0 edgeSlopeAtPrevious 0 < 0 := by
  simpa [zeroLiftingRightDerivative] using neg_lt_zero.mpr hEdge

/-- A strict telescoped flux inequality gives the registered ceiling bound on
the number of positive coordinates. -/
theorem strictPositivePrefix_le_ceil_sub_one
    (positiveCount : ℕ) {endpointSiteSlope edgeSlopeAtOne : ℝ}
    (hSite : 0 < endpointSiteSlope)
    (hFlux : (positiveCount : ℝ) * endpointSiteSlope < edgeSlopeAtOne) :
    positiveCount ≤ Nat.ceil (edgeSlopeAtOne / endpointSiteSlope) - 1 := by
  have hRatio : (positiveCount : ℝ) < edgeSlopeAtOne / endpointSiteSlope :=
    (lt_div_iff₀ hSite).2 hFlux
  exact Nat.le_sub_one_of_lt ((Nat.lt_ceil).2 hRatio)

/-- Exact registered integer instance: a strict bound below four permits at
most three positive coordinates. -/
theorem strictPositivePrefix_registered_bound
    (positiveCount : ℕ) (hFlux : (positiveCount : ℝ) < 4) :
    positiveCount ≤ 3 := by
  have hNat : positiveCount < 4 := by
    exact_mod_cast hFlux
  omega

/-- An abstract minimizer cannot contain a zero coordinate whenever every
zero coordinate admits a strictly improving lift. -/
theorem minimizer_has_no_zero_of_improving_lift
    {ι : Type*} {Profile : Type*} (coordinate : Profile → ι → ℝ)
    (objective : Profile → ℝ) (winner : Profile)
    (isMinimizer : ∀ competitor, objective winner ≤ objective competitor)
    (improvingLift :
      ∀ index, coordinate winner index = 0 →
        ∃ competitor, objective competitor < objective winner) :
    ∀ index, coordinate winner index ≠ 0 := by
  intro index hZero
  obtain ⟨competitor, hImproves⟩ := improvingLift index hZero
  exact (not_lt_of_ge (isMinimizer competitor)) hImproves

/-- Nonnegativity converts exclusion of zero into strict positivity. -/
theorem minimizer_strictly_positive_of_improving_lift
    {ι : Type*} {Profile : Type*} (coordinate : Profile → ι → ℝ)
    (objective : Profile → ℝ) (winner : Profile)
    (isMinimizer : ∀ competitor, objective winner ≤ objective competitor)
    (nonnegative : ∀ index, 0 ≤ coordinate winner index)
    (improvingLift :
      ∀ index, coordinate winner index = 0 →
        ∃ competitor, objective competitor < objective winner) :
    ∀ index, 0 < coordinate winner index := by
  intro index
  exact lt_of_le_of_ne (nonnegative index)
    (Ne.symm (minimizer_has_no_zero_of_improving_lift coordinate objective winner
      isMinimizer improvingLift index))

/-- Exact declaration for the registered derivative proof goal. -/
theorem sup_e1_derivative_01 :
    zeroLiftingRightDerivative 0 1 0 = -1 ∧
      zeroLiftingRightDerivative 0 1 0 < 0 := by
  constructor <;> norm_num [zeroLiftingRightDerivative]

/-- Exact declaration for the registered strict-prefix bound proof goal. -/
theorem sup_e1_bound_02 :
    Nat.ceil ((4 : ℝ) / 1) - 1 = 3 ∧
      (3 : ℝ) * 1 < 4 ∧
      ¬((4 : ℝ) * 1 < 4) := by
  norm_num

end PhonologicalCalculus.Support
