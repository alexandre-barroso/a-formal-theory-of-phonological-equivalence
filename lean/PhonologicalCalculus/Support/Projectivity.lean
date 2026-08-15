import PhonologicalCalculus.MaxEnt.ExactCore
import Mathlib.Data.Real.Basic

/-!
# Free-end projectivity and exact-zero extension

This module isolates the support-theoretic distinction between an all-positive
free endpoint and an attained exact zero.  The universal obstruction is proved
from the terminal and interior stationarity equations.  Two explicit convex
objectives then exhibit the prefix change, while a closed quadratic profile
exhibits stability after extinction.
-/

namespace PhonologicalCalculus.Support

section StationarityObstruction

/-- If an old positive terminal coordinate were preserved as an interior
coordinate after extension, its old terminal equation and new interior
equation would force the new terminal flux to vanish.  The new positive
terminal equation forces the same flux to be positive, a contradiction. -/
theorem positiveFreeEndpoint_not_projective
    (oldFlux newFlux oldSiteSlope newSiteSlope : ℝ)
    (oldTerminal : oldFlux = oldSiteSlope)
    (newInterior : oldFlux - newFlux = oldSiteSlope)
    (newTerminal : newFlux = newSiteSlope)
    (newSiteSlopePositive : 0 < newSiteSlope) : False := by
  linarith

/-- **SUP-E2.CONTRADICTION.01**.  The stationarity equations derive zero new
drop flux while the positive-site terminal equation requires positive flux. -/
theorem sup_e2_contradiction_01
    (oldFlux newFlux oldSiteSlope newSiteSlope : ℝ)
    (oldTerminal : oldFlux = oldSiteSlope)
    (newInterior : oldFlux - newFlux = oldSiteSlope)
    (newTerminal : newFlux = newSiteSlope)
    (newSiteSlopePositive : 0 < newSiteSlope) :
    newFlux = 0 ∧ 0 < newFlux ∧ False := by
  have hzero : newFlux = 0 := by linarith
  have hpositive : 0 < newFlux := by linarith
  exact ⟨hzero, hpositive,
    positiveFreeEndpoint_not_projective oldFlux newFlux oldSiteSlope
      newSiteSlope oldTerminal newInterior newTerminal newSiteSlopePositive⟩

end StationarityObstruction

section MatchedPowerWitness

/-- The one-follower matched-square free-end objective. -/
def matchedSquareOne (x : ℝ) : ℝ :=
  (1 - x) ^ 2 + x ^ 2

/-- The two-follower matched-square free-end objective. -/
def matchedSquareTwo (x y : ℝ) : ℝ :=
  (1 - x) ^ 2 + (x - y) ^ 2 + x ^ 2 + y ^ 2

/-- Completion of the square at the one-follower winner. -/
theorem matchedSquareOne_decomposition (x : ℝ) :
    matchedSquareOne x = 1 / 2 + 2 * (x - 1 / 2) ^ 2 := by
  unfold matchedSquareOne
  ring

/-- Completion of the positive-definite quadratic form at the two-follower
winner. -/
theorem matchedSquareTwo_decomposition (x y : ℝ) :
    matchedSquareTwo x y = 3 / 5 +
      (5 / 2) * (x - 2 / 5) ^ 2 +
      2 * (y - 1 / 5 - (x - 2 / 5) / 2) ^ 2 := by
  unfold matchedSquareTwo
  ring

/-- The one-follower objective has the unique winner `1/2`. -/
theorem matchedSquareOne_uniqueMinimum (x : ℝ) :
    matchedSquareOne (1 / 2) ≤ matchedSquareOne x ∧
      (matchedSquareOne x = matchedSquareOne (1 / 2) → x = 1 / 2) := by
  rw [matchedSquareOne_decomposition, matchedSquareOne_decomposition]
  constructor
  · nlinarith [sq_nonneg (x - 1 / 2)]
  · intro h
    nlinarith [sq_nonneg (x - 1 / 2)]

/-- The two-follower objective has the unique winner `(2/5,1/5)`. -/
theorem matchedSquareTwo_uniqueMinimum (x y : ℝ) :
    matchedSquareTwo (2 / 5) (1 / 5) ≤ matchedSquareTwo x y ∧
      (matchedSquareTwo x y = matchedSquareTwo (2 / 5) (1 / 5) →
        x = 2 / 5 ∧ y = 1 / 5) := by
  rw [matchedSquareTwo_decomposition, matchedSquareTwo_decomposition]
  constructor
  · nlinarith [sq_nonneg (x - 2 / 5),
      sq_nonneg (y - 1 / 5 - (x - 2 / 5) / 2)]
  · intro h
    have hx : x = 2 / 5 := by
      nlinarith [sq_nonneg (x - 2 / 5),
        sq_nonneg (y - 1 / 5 - (x - 2 / 5) / 2)]
    subst x
    have hy : y = 1 / 5 := by
      nlinarith [sq_nonneg (y - 1 / 5)]
    exact ⟨rfl, hy⟩

/-- **SUP-E2.QUADRATIC.02**.  Extending the matched-square objective from one
to two followers changes the preserved first follower from `1/2` to `2/5`. -/
theorem sup_e2_quadratic_02 :
    matchedSquareOne (1 / 2) = 1 / 2 ∧
    matchedSquareTwo (2 / 5) (1 / 5) = 3 / 5 ∧
    (1 / 2 : ℝ) ≠ 2 / 5 := by
  norm_num [matchedSquareOne, matchedSquareTwo]

end MatchedPowerWitness

section ExactZeroExtension

/-- Closed saturated coordinate for the quadratic linear-site family. -/
def stableQuadraticCoordinate (h m : ℚ) (firstZero position : ℕ) : ℚ :=
  if position ≤ firstZero then
    1 - (position : ℚ) / firstZero -
      m * position * (firstZero - position : ℕ) / (4 * h)
  else
    0

/-- A saturated profile through a declared finite horizon. -/
def stableQuadraticProfile (h m : ℚ) (firstZero horizon : ℕ) : List ℚ :=
  (List.range (horizon + 1)).map
    (stableQuadraticCoordinate h m firstZero)

/-- Every coordinate after the first-zero position is exactly zero. -/
theorem stableQuadraticCoordinate_zeroTail
    (h m : ℚ) (firstZero position : ℕ)
    (hpos : firstZero < position) :
    stableQuadraticCoordinate h m firstZero position = 0 := by
  simp [stableQuadraticCoordinate, Nat.not_le.mpr hpos]

/-- **SUP-E2.ZEROEXTEND.03**.  The registered quadratic prefix is unchanged
after extending the horizon beyond its exact first zero. -/
theorem sup_e2_zeroextend_03 :
    stableQuadraticProfile 5 1 4 4 = [1, 3 / 5, 3 / 10, 1 / 10, 0] ∧
    (stableQuadraticProfile 5 1 4 7).take 5 =
      [1, 3 / 5, 3 / 10, 1 / 10, 0] := by
  norm_num [stableQuadraticProfile, stableQuadraticCoordinate,
    List.range_succ]

end ExactZeroExtension

end PhonologicalCalculus.Support
