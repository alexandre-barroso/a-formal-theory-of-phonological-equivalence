import PhonologicalCalculus.Support.Projectivity
import Mathlib.Analysis.Real.Sqrt

/-!
# Matched-power decay and exact continuation algebra

The power-law terms are represented by their positive values at a declared
decay ratio.  This isolates the field algebra shared by every real exponent
from the separate analytic existence and uniqueness argument.  The quadratic
specializations are then evaluated exactly.
-/

namespace PhonologicalCalculus.Support

section DecayEquation

/-- Quadratic matched-power decay residual. -/
noncomputable def quadraticDecayResidual (h m lambda : ℝ) : ℝ :=
  (h / m) * (1 - lambda) * (1 - lambda) - lambda

/-- The golden-ratio conjugate solves the unit-weight quadratic decay
equation exactly. -/
theorem sup_e3_root_01 :
    quadraticDecayResidual 1 1 ((3 - Real.sqrt 5) / 2) = 0 := by
  have hsqrt : (Real.sqrt 5) ^ 2 = 5 := by
    norm_num
  unfold quadraticDecayResidual
  nlinarith

/-- The registered quadratic root lies strictly between zero and one. -/
theorem quadraticDecayRoot_mem_unitInterval :
    0 < (3 - Real.sqrt 5) / 2 ∧ (3 - Real.sqrt 5) / 2 < 1 := by
  have hsqrt : (Real.sqrt 5) ^ 2 = 5 := by
    norm_num
  have hsqrt_nonneg : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  constructor <;> nlinarith

/-- Complete isolating-interval and uniqueness proof for
`SUP-E3.ROOT.01`.  The displayed root is the only zero of its registered
minimal polynomial on `[0,1/2]`. -/
theorem sup_e3_root_01_complete :
    let root : ℝ := (3 - Real.sqrt 5) / 2
    0 < root ∧ root ≤ 1 / 2 ∧
      root ^ 2 - 3 * root + 1 = 0 ∧
      ∀ x : ℝ, 0 ≤ x → x ≤ 1 / 2 →
        x ^ 2 - 3 * x + 1 = 0 → x = root := by
  dsimp
  have hsqrt : (Real.sqrt 5) ^ 2 = 5 := by
    norm_num
  have hsqrtNonnegative : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have hsqrtAtLeastTwo : 2 ≤ Real.sqrt 5 := by
    nlinarith
  have hrootPositive := quadraticDecayRoot_mem_unitInterval.1
  have hrootUpper : (3 - Real.sqrt 5) / 2 ≤ (1 / 2 : ℝ) := by
    linarith
  have hrootPolynomial :
      ((3 - Real.sqrt 5) / 2) ^ 2 -
        3 * ((3 - Real.sqrt 5) / 2) + 1 = 0 := by
    nlinarith
  refine ⟨hrootPositive, hrootUpper, hrootPolynomial, ?_⟩
  intro x hxLower hxUpper hxPolynomial
  have hfactor :
      (x - (3 - Real.sqrt 5) / 2) *
        (x + (3 - Real.sqrt 5) / 2 - 3) = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hfactor with hroot | himpossible
  · linarith
  · nlinarith

end DecayEquation

section ContinuationIdentities

/-- Algebraic form of the matched-power decay equation, where `edgePower`
denotes `(1-λ)^(p-1)` and `sitePower` denotes `λ^(p-1)`. -/
def SatisfiesMatchedDecay
    (h m edgePower sitePower : ℝ) : Prop :=
  m * sitePower = h * edgePower * (1 - sitePower)

/-- **SUP-E3.ENERGY.02**.  Under the decay equation, the geometric energy
quotient reduces to the continuation coefficient.  The proof is pure field
algebra and therefore does not assume an integer exponent. -/
theorem sup_e3_energy_02
    (h m lambda edgePower sitePower : ℝ)
    (hDecay : SatisfiesMatchedDecay h m edgePower sitePower)
    (hDenominator : 1 - lambda * sitePower ≠ 0) :
    (h * (1 - lambda) * edgePower +
        m * lambda * sitePower) /
      (1 - lambda * sitePower) = h * edgePower := by
  unfold SatisfiesMatchedDecay at hDecay
  apply (div_eq_iff hDenominator).2
  calc
    h * (1 - lambda) * edgePower + m * lambda * sitePower =
        h * edgePower * (1 - lambda) + lambda * (m * sitePower) := by ring
    _ = h * edgePower * (1 - lambda) +
        lambda * (h * edgePower * (1 - sitePower)) := by rw [hDecay]
    _ = h * edgePower * (1 - lambda * sitePower) := by ring

/-- **SUP-E4.COEFFICIENT.01**.  Terminal stationarity identifies the exact
continuation coefficient `h*edgePower`. -/
theorem sup_e4_coefficient_01
    (h m edgePower sitePower : ℝ)
    (hSitePower : sitePower ≠ 0)
    (hDecay : SatisfiesMatchedDecay h m edgePower sitePower) :
    h * edgePower / sitePower - m = h * edgePower := by
  unfold SatisfiesMatchedDecay at hDecay
  rw [sub_eq_iff_eq_add]
  apply (div_eq_iff hSitePower).2
  calc
    h * edgePower = h * edgePower * sitePower +
        h * edgePower * (1 - sitePower) := by ring
    _ = h * edgePower * sitePower + m * sitePower := by rw [hDecay]
    _ = (h * edgePower + m) * sitePower := by ring

/-- Complete uniqueness form of `SUP-E4.COEFFICIENT.01` within the declared
terminal-monomial comparison class. -/
theorem sup_e4_coefficient_01_unique
    (h m edgePower sitePower : ℝ)
    (hSitePower : sitePower ≠ 0)
    (hDecay : SatisfiesMatchedDecay h m edgePower sitePower) :
    ∃! coefficient : ℝ,
      coefficient = h * edgePower ∧
      coefficient = h * edgePower / sitePower - m := by
  have hcoefficient :=
    sup_e4_coefficient_01 h m edgePower sitePower hSitePower hDecay
  refine ⟨h * edgePower, ⟨rfl, hcoefficient.symm⟩, ?_⟩
  intro coefficient hcoefficientProperties
  exact hcoefficientProperties.1

end ContinuationIdentities

section ExactRepair

/-- Exact finite geometric prefix at decay ratio `lambda`. -/
def geometricProfile (lambda : ℚ) (horizon : ℕ) : List ℚ :=
  (List.range (horizon + 1)).map fun index => lambda ^ index

/-- Every shorter geometric profile is literally the corresponding prefix of
every longer geometric profile. -/
theorem geometricProfile_take_of_le (lambda : ℚ) {short long : ℕ}
    (horizonOrder : short ≤ long) :
    (geometricProfile lambda long).take (short + 1) =
      geometricProfile lambda short := by
  unfold geometricProfile
  rw [← List.map_take]
  simp [List.take_range, Nat.min_eq_left (Nat.add_le_add_right horizonOrder 1)]

/-- Replacing an optimized tail by its exact value function preserves the
complete set of global minimizers of the finite prefix problem. -/
theorem exactTailReplacement_minimizer_iff
    {State : Type*} (prefixCost tailCost terminalCost : State → ℝ)
    (tailIdentity : ∀ state, tailCost state = terminalCost state)
    (candidate : State) :
    (∀ rival, prefixCost candidate + tailCost candidate ≤
        prefixCost rival + tailCost rival) ↔
      (∀ rival, prefixCost candidate + terminalCost candidate ≤
        prefixCost rival + terminalCost rival) := by
  simp only [tailIdentity]

/-- The repaired Kazakh parameter tuple satisfies the quadratic decay
equation and has continuation coefficient `3/2`. -/
theorem kazakhMatchedPower_parameters :
    quadraticDecayResidual (15 / 4) 1 (3 / 5) = 0 ∧
    (15 / 4 : ℝ) * (1 - 3 / 5) = 3 / 2 := by
  norm_num [quadraticDecayResidual]

/-- **SUP-E4.REPAIR.02**.  The exact repaired five-follower profile is the
geometric prefix with ratio `3/5`. -/
theorem sup_e4_repair_02 :
    geometricProfile (3 / 5) 5 =
      [1, 3 / 5, 9 / 25, 27 / 125, 81 / 625, 243 / 3125] := by
  norm_num [geometricProfile, List.range_succ]

/-- **SUP-E4.TRILEMMA.03**.  The linear-site quadratic profile reaches exact
zero, while the matched-power profile remains strictly positive at the same
five-follower horizon. -/
theorem sup_e4_trilemma_03 :
    stableQuadraticProfile 5 1 4 5 =
      [1, 3 / 5, 3 / 10, 1 / 10, 0, 0] ∧
    geometricProfile (3 / 5) 5 =
      [1, 3 / 5, 9 / 25, 27 / 125, 81 / 625, 243 / 3125] := by
  constructor
  · norm_num [stableQuadraticProfile, stableQuadraticCoordinate,
      List.range_succ]
  · exact sup_e4_repair_02

/-- Universal projectivity and monomial-coefficient uniqueness after the
exact infinite-tail value has been identified. -/
theorem sup_e4_exact_continuation
    (h m edgePower sitePower : ℝ)
    (sitePowerNonzero : sitePower ≠ 0)
    (decay : SatisfiesMatchedDecay h m edgePower sitePower) :
    (∀ (lambda : ℚ) (short long : ℕ), short ≤ long →
      (geometricProfile lambda long).take (short + 1) =
        geometricProfile lambda short) ∧
      ∃! coefficient : ℝ,
        coefficient = h * edgePower ∧
        coefficient = h * edgePower / sitePower - m := by
  constructor
  · intro lambda short long horizonOrder
    exact geometricProfile_take_of_le lambda horizonOrder
  · exact sup_e4_coefficient_01_unique h m edgePower sitePower
      sitePowerNonzero decay

end ExactRepair

end PhonologicalCalculus.Support
