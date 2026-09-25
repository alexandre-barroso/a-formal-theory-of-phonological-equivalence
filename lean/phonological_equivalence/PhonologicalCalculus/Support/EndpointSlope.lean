                              
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Convex.Deriv

namespace PhonologicalCalculus.Support

def zeroLiftingRightDerivative
    (edgeSlopeAtZero edgeSlopeAtPrevious siteSlopeAtZero : ℝ) : ℝ :=
  edgeSlopeAtZero - edgeSlopeAtPrevious + siteSlopeAtZero

theorem zeroLiftingRightDerivative_eq
    (edgeSlopeAtZero edgeSlopeAtPrevious siteSlopeAtZero : ℝ) :
    zeroLiftingRightDerivative edgeSlopeAtZero edgeSlopeAtPrevious
        siteSlopeAtZero =
      edgeSlopeAtZero - edgeSlopeAtPrevious + siteSlopeAtZero := by
  rfl

theorem zeroLiftingRightDerivative_zero_slopes
    (edgeSlopeAtPrevious : ℝ) :
    zeroLiftingRightDerivative 0 edgeSlopeAtPrevious 0 =
      -edgeSlopeAtPrevious := by
  simp [zeroLiftingRightDerivative]

theorem zeroLiftingRightDerivative_negative
    {edgeSlopeAtPrevious : ℝ} (hEdge : 0 < edgeSlopeAtPrevious) :
    zeroLiftingRightDerivative 0 edgeSlopeAtPrevious 0 < 0 := by
  simpa [zeroLiftingRightDerivative] using neg_lt_zero.mpr hEdge

theorem strictPositivePrefix_le_ceil_sub_one
    (positiveCount : ℕ) {endpointSiteSlope edgeSlopeAtOne : ℝ}
    (hSite : 0 < endpointSiteSlope)
    (hFlux : (positiveCount : ℝ) * endpointSiteSlope < edgeSlopeAtOne) :
    positiveCount ≤ Nat.ceil (edgeSlopeAtOne / endpointSiteSlope) - 1 := by
  have hRatio : (positiveCount : ℝ) < edgeSlopeAtOne / endpointSiteSlope :=
    (lt_div_iff₀ hSite).2 hFlux
  exact Nat.le_sub_one_of_lt ((Nat.lt_ceil).2 hRatio)

theorem strictPositivePrefix_registered_bound
    (positiveCount : ℕ) (hFlux : (positiveCount : ℝ) < 4) :
    positiveCount ≤ 3 := by
  have hNat : positiveCount < 4 := by
    exact_mod_cast hFlux
  omega

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

theorem sup_e1_derivative_01 :
    zeroLiftingRightDerivative 0 1 0 = -1 ∧
      zeroLiftingRightDerivative 0 1 0 < 0 := by
  constructor <;> norm_num [zeroLiftingRightDerivative]

theorem sup_e1_bound_02 :
    Nat.ceil ((4 : ℝ) / 1) - 1 = 3 ∧
      (3 : ℝ) * 1 < 4 ∧
      ¬((4 : ℝ) * 1 < 4) := by
  norm_num

end PhonologicalCalculus.Support
