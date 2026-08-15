import PhonologicalCalculus.MaxEnt.ExactCore
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FinCases

/-!
# Exact quadratic directional-HG applications

This module reconstructs the registered McCollum application calculations
from explicit quadratic objectives and profile formulas.  The declarations
separate continuum optimization, finite-grid optimization, saturated
all-horizon profiles, horizon-specific profiles, and carrier type.  This
separation makes the nonconservativity claim depend on two independently
proved winner statements rather than on rounded numerical output.
-/

namespace PhonologicalCalculus.Application

section OneFollowerGrid

/-- The one-follower directional-HG objective with harmony weight `21` and
markedness weight `1`. -/
def oneFollowerObjective (x : ℝ) : ℝ :=
  21 * (1 - x) ^ 2 + x

/-- Exact completion of the square for the one-follower objective. -/
theorem oneFollowerObjective_square (x : ℝ) :
    oneFollowerObjective x = 83 / 84 + 21 * (x - 41 / 42) ^ 2 := by
  unfold oneFollowerObjective
  ring

/-- The exact continuum candidate has objective value `83/84`. -/
theorem oneFollowerObjective_at_continuumWinner :
    oneFollowerObjective (41 / 42) = 83 / 84 := by
  rw [oneFollowerObjective_square]
  norm_num

/-- The continuum candidate `41/42` is a global minimizer. -/
theorem oneFollower_continuum_minimum (x : ℝ) :
    oneFollowerObjective (41 / 42) ≤ oneFollowerObjective x := by
  rw [oneFollowerObjective_at_continuumWinner, oneFollowerObjective_square]
  nlinarith [sq_nonneg (x - 41 / 42)]

/-- Equality at the continuum minimum uniquely determines the candidate. -/
theorem oneFollower_continuum_unique (x : ℝ)
    (h : oneFollowerObjective x = oneFollowerObjective (41 / 42)) :
    x = 41 / 42 := by
  rw [oneFollowerObjective_square, oneFollowerObjective_at_continuumWinner] at h
  nlinarith [sq_nonneg (x - 41 / 42)]

/-- The exact rational objective used for exhaustive tenths-grid evaluation. -/
def oneFollowerObjectiveRat (x : ℚ) : ℚ :=
  21 * (1 - x) ^ 2 + x

/-- The eleven-point tenths lattice, represented without floating-point
rounding. -/
def tenthsCandidate (k : Fin 11) : ℚ :=
  (k : ℕ) / 10

/-- Every tenths-grid objective value is at least the value at `1`. -/
theorem oneFollower_tenths_minimum (k : Fin 11) :
    oneFollowerObjectiveRat 1 ≤ oneFollowerObjectiveRat (tenthsCandidate k) := by
  fin_cases k <;> norm_num [oneFollowerObjectiveRat, tenthsCandidate]

/-- Equality on the tenths grid occurs only at its final point. -/
theorem oneFollower_tenths_unique (k : Fin 11)
    (h : oneFollowerObjectiveRat (tenthsCandidate k) =
      oneFollowerObjectiveRat 1) :
    k = ⟨10, by decide⟩ := by
  fin_cases k
  all_goals norm_num [oneFollowerObjectiveRat, tenthsCandidate] at h
  rfl

/-- The exact continuum and tenths-grid winners are distinct. -/
theorem oneFollower_exactWinner_nonconservative :
    (41 / 42 : ℝ) ≠ 1 := by
  norm_num

/-- **APP-MCC-GRID**.  The continuum objective has the unique winner
`41/42`, the complete tenths lattice has the unique winner `1`, and exact
winner identity is therefore not preserved by discretization. -/
theorem app_mcc_grid :
    (∀ x : ℝ,
      oneFollowerObjective (41 / 42) ≤ oneFollowerObjective x ∧
      (oneFollowerObjective x = oneFollowerObjective (41 / 42) →
        x = 41 / 42)) ∧
    (∀ k : Fin 11,
      oneFollowerObjectiveRat 1 ≤ oneFollowerObjectiveRat (tenthsCandidate k) ∧
      (oneFollowerObjectiveRat (tenthsCandidate k) = oneFollowerObjectiveRat 1 →
        k = ⟨10, by decide⟩)) ∧
    (41 / 42 : ℝ) ≠ 1 := by
  refine ⟨?_, ?_, oneFollower_exactWinner_nonconservative⟩
  · intro x
    exact ⟨oneFollower_continuum_minimum x, oneFollower_continuum_unique x⟩
  · intro k
    exact ⟨oneFollower_tenths_minimum k, oneFollower_tenths_unique k⟩

end OneFollowerGrid

section QuadraticProfiles

/-- The first-zero boundary condition for the quadratic family.  The first
inequality keeps the previous follower positive; the second places the stated
index on the zero side, including equality. -/
def IsQuadraticFirstZero (h m : ℚ) (K : ℕ) : Prop :=
  m * (K - 1 : ℕ) * K < 4 * h ∧ 4 * h ≤ m * K * (K + 1)

/-- A coordinate of the extension-stable saturated quadratic profile. -/
def quadraticSaturatedCoordinate (h m : ℚ) (K j : ℕ) : ℚ :=
  if j ≤ K then
    1 - (j : ℚ) / K - m * j * (K - j : ℕ) / (4 * h)
  else
    0

/-- The saturated profile through a declared horizon. -/
def quadraticSaturatedProfile (h m : ℚ) (K horizon : ℕ) : List ℚ :=
  (List.range (horizon + 1)).map (quadraticSaturatedCoordinate h m K)

/-- A coordinate of the unsaturated, horizon-specific quadratic profile. -/
def quadraticUnsaturatedCoordinate (h m : ℚ) (horizon j : ℕ) : ℚ :=
  if j ≤ horizon then
    1 - m * j * (2 * horizon - j + 1 : ℕ) / (4 * h)
  else
    0

/-- The unsaturated profile at a fixed finite horizon. -/
def quadraticUnsaturatedProfile (h m : ℚ) (horizon : ℕ) : List ℚ :=
  (List.range (horizon + 1)).map
    (quadraticUnsaturatedCoordinate h m horizon)

/-- The three registered parameter pairs satisfy their exact first-zero
boundary conditions. -/
theorem mccollum_firstZero_boundaries :
    IsQuadraticFirstZero 20 3 5 ∧
    IsQuadraticFirstZero 5 1 4 ∧
    IsQuadraticFirstZero 21 1 9 := by
  norm_num [IsQuadraticFirstZero]

/-- The first registered saturated profile is reconstructed from its closed
coordinate formula. -/
theorem mccollum_profile_20_3 :
    quadraticSaturatedProfile 20 3 5 5 =
      [1, 13 / 20, 3 / 8, 7 / 40, 1 / 20, 0] := by
  norm_num [quadraticSaturatedProfile, quadraticSaturatedCoordinate,
    List.range_succ]

/-- The second registered saturated profile is reconstructed from its closed
coordinate formula. -/
theorem mccollum_profile_5_1 :
    quadraticSaturatedProfile 5 1 4 4 =
      [1, 3 / 5, 3 / 10, 1 / 10, 0] := by
  norm_num [quadraticSaturatedProfile, quadraticSaturatedCoordinate,
    List.range_succ]

/-- The third registered saturated profile is reconstructed from its closed
coordinate formula. -/
theorem mccollum_profile_21_1 :
    quadraticSaturatedProfile 21 1 9 9 =
      [1, 50 / 63, 11 / 18, 19 / 42, 20 / 63, 13 / 63,
        5 / 42, 1 / 18, 1 / 63, 0] := by
  norm_num [quadraticSaturatedProfile, quadraticSaturatedCoordinate,
    List.range_succ]

/-- At the printed one-follower horizon, the exact unsaturated profile is
`[1,41/42]`. -/
theorem mccollum_oneFollower_profile :
    quadraticUnsaturatedProfile 21 1 1 = [1, 41 / 42] := by
  norm_num [quadraticUnsaturatedProfile, quadraticUnsaturatedCoordinate,
    List.range_succ]

/-- **APP-MCC-LENGTH.ANCHORS.01** and
**APP-MCC-LENGTH.ONEFOLLOWER.02**.  The registered exact profiles are a single
consequence of the saturated and horizon-specific closed formulas. -/
theorem app_mcc_length_registeredProfiles :
    quadraticSaturatedProfile 20 3 5 5 =
      [1, 13 / 20, 3 / 8, 7 / 40, 1 / 20, 0] ∧
    quadraticSaturatedProfile 5 1 4 4 =
      [1, 3 / 5, 3 / 10, 1 / 10, 0] ∧
    quadraticSaturatedProfile 21 1 9 9 =
      [1, 50 / 63, 11 / 18, 19 / 42, 20 / 63, 13 / 63,
        5 / 42, 1 / 18, 1 / 63, 0] ∧
    quadraticUnsaturatedProfile 21 1 1 = [1, 41 / 42] := by
  exact ⟨mccollum_profile_20_3, mccollum_profile_5_1,
    mccollum_profile_21_1, mccollum_oneFollower_profile⟩

/-- The finite response compiler uses one trigger label and one label for
every position of every horizon through the first-zero index. -/
def quadraticCompilerLabelCount (K : ℕ) : ℕ :=
  1 + K * (K + 1) / 2

/-- The three exact finite carrier sizes. -/
theorem app_mcc_comp_counts :
    [quadraticCompilerLabelCount 5, quadraticCompilerLabelCount 4,
      quadraticCompilerLabelCount 9] = [16, 11, 46] := by
  norm_num [quadraticCompilerLabelCount]

/-- A fixed one-follower parameter change changes the exact winner coordinate
by `1/60`. -/
theorem app_mcc_comp_parameter :
    quadraticUnsaturatedCoordinate 5 1 1 1 = 9 / 10 ∧
    quadraticUnsaturatedCoordinate 6 1 1 1 = 11 / 12 ∧
    quadraticUnsaturatedCoordinate 6 1 1 1 -
      quadraticUnsaturatedCoordinate 5 1 1 1 = 1 / 60 := by
  norm_num [quadraticUnsaturatedCoordinate]

end QuadraticProfiles

section CarrierGuard

/-- The exact eleven-point lattice carrier. -/
abbrev TenthsCarrier := Fin 11

/-- The two carrier kinds distinguished by the registered type guard. -/
inductive CandidateCarrierKind
  | finite (size : ℕ)
  | realInterval
  deriving DecidableEq

/-- The exact tenths-lattice carrier kind. -/
def tenthsCarrierKind : CandidateCarrierKind :=
  .finite 11

/-- The closed-real-interval carrier kind. -/
def unitContinuumCarrierKind : CandidateCarrierKind :=
  .realInterval

/-- **APP-MCC-COMP.TYPE.03**.  The lattice has exactly eleven elements and
its finite carrier tag is distinct from the real-interval carrier tag. -/
theorem app_mcc_comp_carrierGuard :
    Fintype.card TenthsCarrier = 11 ∧
      tenthsCarrierKind ≠ unitContinuumCarrierKind := by
  constructor
  · simp
  · decide

end CarrierGuard

end PhonologicalCalculus.Application
