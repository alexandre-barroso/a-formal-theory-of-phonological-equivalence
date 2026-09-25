import PhonologicalCalculus.MaxEnt.ExactCore
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FinCases

namespace PhonologicalCalculus.Application

section OneFollowerGrid

def oneFollowerObjective (x : ℝ) : ℝ :=
  21 * (1 - x) ^ 2 + x

theorem oneFollowerObjective_square (x : ℝ) :
    oneFollowerObjective x = 83 / 84 + 21 * (x - 41 / 42) ^ 2 := by
  unfold oneFollowerObjective
  ring

theorem oneFollowerObjective_at_continuumWinner :
    oneFollowerObjective (41 / 42) = 83 / 84 := by
  rw [oneFollowerObjective_square]
  norm_num

theorem oneFollower_continuum_minimum (x : ℝ) :
    oneFollowerObjective (41 / 42) ≤ oneFollowerObjective x := by
  rw [oneFollowerObjective_at_continuumWinner, oneFollowerObjective_square]
  nlinarith [sq_nonneg (x - 41 / 42)]

theorem oneFollower_continuum_unique (x : ℝ)
    (h : oneFollowerObjective x = oneFollowerObjective (41 / 42)) :
    x = 41 / 42 := by
  rw [oneFollowerObjective_square, oneFollowerObjective_at_continuumWinner] at h
  nlinarith [sq_nonneg (x - 41 / 42)]

def oneFollowerObjectiveRat (x : ℚ) : ℚ :=
  21 * (1 - x) ^ 2 + x

def tenthsCandidate (k : Fin 11) : ℚ :=
  (k : ℕ) / 10

theorem oneFollower_tenths_minimum (k : Fin 11) :
    oneFollowerObjectiveRat 1 ≤ oneFollowerObjectiveRat (tenthsCandidate k) := by
  fin_cases k <;> norm_num [oneFollowerObjectiveRat, tenthsCandidate]

theorem oneFollower_tenths_unique (k : Fin 11)
    (h : oneFollowerObjectiveRat (tenthsCandidate k) =
      oneFollowerObjectiveRat 1) :
    k = ⟨10, by decide⟩ := by
  fin_cases k
  all_goals norm_num [oneFollowerObjectiveRat, tenthsCandidate] at h
  rfl

theorem oneFollower_exactWinner_nonconservative :
    (41 / 42 : ℝ) ≠ 1 := by
  norm_num

               
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

def IsQuadraticFirstZero (h m : ℚ) (K : ℕ) : Prop :=
  m * (K - 1 : ℕ) * K < 4 * h ∧ 4 * h ≤ m * K * (K + 1)

def quadraticSaturatedCoordinate (h m : ℚ) (K j : ℕ) : ℚ :=
  if j ≤ K then
    1 - (j : ℚ) / K - m * j * (K - j : ℕ) / (4 * h)
  else
    0

def quadraticSaturatedProfile (h m : ℚ) (K horizon : ℕ) : List ℚ :=
  (List.range (horizon + 1)).map (quadraticSaturatedCoordinate h m K)

def quadraticUnsaturatedCoordinate (h m : ℚ) (horizon j : ℕ) : ℚ :=
  if j ≤ horizon then
    1 - m * j * (2 * horizon - j + 1 : ℕ) / (4 * h)
  else
    0

def quadraticUnsaturatedProfile (h m : ℚ) (horizon : ℕ) : List ℚ :=
  (List.range (horizon + 1)).map
    (quadraticUnsaturatedCoordinate h m horizon)

theorem mccollum_firstZero_boundaries :
    IsQuadraticFirstZero 20 3 5 ∧
    IsQuadraticFirstZero 5 1 4 ∧
    IsQuadraticFirstZero 21 1 9 := by
  norm_num [IsQuadraticFirstZero]

theorem mccollum_profile_20_3 :
    quadraticSaturatedProfile 20 3 5 5 =
      [1, 13 / 20, 3 / 8, 7 / 40, 1 / 20, 0] := by
  norm_num [quadraticSaturatedProfile, quadraticSaturatedCoordinate,
    List.range_succ]

theorem mccollum_profile_5_1 :
    quadraticSaturatedProfile 5 1 4 4 =
      [1, 3 / 5, 3 / 10, 1 / 10, 0] := by
  norm_num [quadraticSaturatedProfile, quadraticSaturatedCoordinate,
    List.range_succ]

theorem mccollum_profile_21_1 :
    quadraticSaturatedProfile 21 1 9 9 =
      [1, 50 / 63, 11 / 18, 19 / 42, 20 / 63, 13 / 63,
        5 / 42, 1 / 18, 1 / 63, 0] := by
  norm_num [quadraticSaturatedProfile, quadraticSaturatedCoordinate,
    List.range_succ]

theorem mccollum_oneFollower_profile :
    quadraticUnsaturatedProfile 21 1 1 = [1, 41 / 42] := by
  norm_num [quadraticUnsaturatedProfile, quadraticUnsaturatedCoordinate,
    List.range_succ]

                                                          
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

def quadraticCompilerLabelCount (K : ℕ) : ℕ :=
  1 + K * (K + 1) / 2

theorem app_mcc_comp_counts :
    [quadraticCompilerLabelCount 5, quadraticCompilerLabelCount 4,
      quadraticCompilerLabelCount 9] = [16, 11, 46] := by
  norm_num [quadraticCompilerLabelCount]

theorem app_mcc_comp_parameter :
    quadraticUnsaturatedCoordinate 5 1 1 1 = 9 / 10 ∧
    quadraticUnsaturatedCoordinate 6 1 1 1 = 11 / 12 ∧
    quadraticUnsaturatedCoordinate 6 1 1 1 -
      quadraticUnsaturatedCoordinate 5 1 1 1 = 1 / 60 := by
  norm_num [quadraticUnsaturatedCoordinate]

end QuadraticProfiles

section CarrierGuard

abbrev TenthsCarrier := Fin 11

inductive CandidateCarrierKind
  | finite (size : ℕ)
  | realInterval
  deriving DecidableEq

def tenthsCarrierKind : CandidateCarrierKind :=
  .finite 11

def unitContinuumCarrierKind : CandidateCarrierKind :=
  .realInterval

                       
theorem app_mcc_comp_carrierGuard :
    Fintype.card TenthsCarrier = 11 ∧
      tenthsCarrierKind ≠ unitContinuumCarrierKind := by
  constructor
  · simp
  · decide

end CarrierGuard

end PhonologicalCalculus.Application
