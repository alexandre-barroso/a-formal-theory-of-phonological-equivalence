import PhonologicalCalculus.MaxEnt.ExactCore
import Mathlib.Data.Real.Basic

namespace PhonologicalCalculus.Support

section StationarityObstruction

theorem positiveFreeEndpoint_not_projective
    (oldFlux newFlux oldSiteSlope newSiteSlope : ℝ)
    (oldTerminal : oldFlux = oldSiteSlope)
    (newInterior : oldFlux - newFlux = oldSiteSlope)
    (newTerminal : newFlux = newSiteSlope)
    (newSiteSlopePositive : 0 < newSiteSlope) : False := by
  linarith

                          
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

def matchedSquareOne (x : ℝ) : ℝ :=
  (1 - x) ^ 2 + x ^ 2

def matchedSquareTwo (x y : ℝ) : ℝ :=
  (1 - x) ^ 2 + (x - y) ^ 2 + x ^ 2 + y ^ 2

theorem matchedSquareOne_decomposition (x : ℝ) :
    matchedSquareOne x = 1 / 2 + 2 * (x - 1 / 2) ^ 2 := by
  unfold matchedSquareOne
  ring

theorem matchedSquareTwo_decomposition (x y : ℝ) :
    matchedSquareTwo x y = 3 / 5 +
      (5 / 2) * (x - 2 / 5) ^ 2 +
      2 * (y - 1 / 5 - (x - 2 / 5) / 2) ^ 2 := by
  unfold matchedSquareTwo
  ring

theorem matchedSquareOne_uniqueMinimum (x : ℝ) :
    matchedSquareOne (1 / 2) ≤ matchedSquareOne x ∧
      (matchedSquareOne x = matchedSquareOne (1 / 2) → x = 1 / 2) := by
  rw [matchedSquareOne_decomposition, matchedSquareOne_decomposition]
  constructor
  · nlinarith [sq_nonneg (x - 1 / 2)]
  · intro h
    nlinarith [sq_nonneg (x - 1 / 2)]

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

                      
theorem sup_e2_quadratic_02 :
    matchedSquareOne (1 / 2) = 1 / 2 ∧
    matchedSquareTwo (2 / 5) (1 / 5) = 3 / 5 ∧
    (1 / 2 : ℝ) ≠ 2 / 5 := by
  norm_num [matchedSquareOne, matchedSquareTwo]

end MatchedPowerWitness

section ExactZeroExtension

def stableQuadraticCoordinate (h m : ℚ) (firstZero position : ℕ) : ℚ :=
  if position ≤ firstZero then
    1 - (position : ℚ) / firstZero -
      m * position * (firstZero - position : ℕ) / (4 * h)
  else
    0

def stableQuadraticProfile (h m : ℚ) (firstZero horizon : ℕ) : List ℚ :=
  (List.range (horizon + 1)).map
    (stableQuadraticCoordinate h m firstZero)

theorem stableQuadraticCoordinate_zeroTail
    (h m : ℚ) (firstZero position : ℕ)
    (hpos : firstZero < position) :
    stableQuadraticCoordinate h m firstZero position = 0 := by
  simp [stableQuadraticCoordinate, Nat.not_le.mpr hpos]

                       
theorem sup_e2_zeroextend_03 :
    stableQuadraticProfile 5 1 4 4 = [1, 3 / 5, 3 / 10, 1 / 10, 0] ∧
    (stableQuadraticProfile 5 1 4 7).take 5 =
      [1, 3 / 5, 3 / 10, 1 / 10, 0] := by
  norm_num [stableQuadraticProfile, stableQuadraticCoordinate,
    List.range_succ]

end ExactZeroExtension

end PhonologicalCalculus.Support
