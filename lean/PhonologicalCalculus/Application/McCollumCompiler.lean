import PhonologicalCalculus.Application.McCollum
import PhonologicalCalculus.ContinuousHG.Quadratic
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Finite all-horizon compiler for a fixed quadratic grammar

For a fixed quadratic phase with first-zero index `K`, every horizon below
`K` has its own unsaturated optimizer, while every horizon at or above `K`
is the same saturated positive prefix followed by exact zeros.  Consequently
the complete zero-extended winner-profile query factors through the finite
carrier `Fin (K + 1)`: horizons `0, ..., K - 1` retain their own code and all
later horizons share code `K`.

This phase carrier is distinct from the registered nonminimal inventory that
counts one trigger label plus every follower-position label through `K`.
-/

namespace PhonologicalCalculus.Application

open PhonologicalCalculus.ContinuousHG

/-- The finite carrier for complete zero-extended horizon profiles. -/
abbrev QuadraticHorizonCode (K : ℕ) := Fin (K + 1)

/-- Every horizon is truncated at the first-zero phase boundary. -/
def quadraticHorizonEncode (K horizon : ℕ) : QuadraticHorizonCode K :=
  ⟨min horizon K, by omega⟩

/-- The unsaturated finite profile, extended by exact zeros after its declared
horizon. -/
noncomputable def quadraticZeroExtendedUnsaturatedProfile
    (h m : ℝ) (horizon position : ℕ) : ℝ :=
  if position ≤ horizon then
    ContinuousHG.quadraticUnsaturatedProfile h m horizon position
  else
    0

/-- The exact complete profile at a horizon, represented on the common
zero-extended coordinate domain `ℕ`. -/
noncomputable def quadraticDeclaredHorizonProfile
    (h m : ℝ) (K horizon : ℕ) : ℕ → ℝ :=
  if horizon < K then
    quadraticZeroExtendedUnsaturatedProfile h m horizon
  else
    ContinuousHG.quadraticSaturatedProfile h m K

/-- Reader for the finite horizon code.  The final code denotes the saturated
profile and therefore also every extension-stable longer horizon. -/
noncomputable def quadraticHorizonDecode
    (h m : ℝ) (K : ℕ) (code : QuadraticHorizonCode K) : ℕ → ℝ :=
  if code.1 < K then
    quadraticZeroExtendedUnsaturatedProfile h m code.1
  else
    ContinuousHG.quadraticSaturatedProfile h m K

/-- Encoding and decoding recover the declared zero-extended profile at every
horizon. -/
theorem quadraticHorizonDecode_encode
    (h m : ℝ) (K horizon : ℕ) :
    quadraticHorizonDecode h m K (quadraticHorizonEncode K horizon) =
      quadraticDeclaredHorizonProfile h m K horizon := by
  funext position
  by_cases horizonBefore : horizon < K
  · have minimumIdentity : min horizon K = horizon :=
      Nat.min_eq_left (Nat.le_of_lt horizonBefore)
    simp [quadraticHorizonDecode, quadraticHorizonEncode,
      quadraticDeclaredHorizonProfile, horizonBefore, minimumIdentity]
  · have boundaryBefore : K ≤ horizon := Nat.le_of_not_gt horizonBefore
    have minimumIdentity : min horizon K = K := Nat.min_eq_right boundaryBefore
    simp [quadraticHorizonDecode, quadraticHorizonEncode,
      quadraticDeclaredHorizonProfile, horizonBefore, minimumIdentity]

/-- The finite phase carrier has exactly one code per preboundary horizon and
one shared saturated code. -/
theorem quadraticHorizonCode_card (K : ℕ) :
    Fintype.card (QuadraticHorizonCode K) = K + 1 := by
  simp [QuadraticHorizonCode]

/-- Every positive quadratic weight pair reaches the triangular threshold at
some finite horizon. -/
theorem exists_quadraticThresholdReached
    {h m : ℝ} (hPositive : 0 < h) (mPositive : 0 < m) :
    ∃ K : ℕ, ContinuousHG.QuadraticThresholdReached h m K := by
  obtain ⟨K, KAbove⟩ := exists_nat_gt (4 * h / m)
  have ratioPositive : 0 < 4 * h / m := by positivity
  have KPositiveReal : 0 < (K : ℝ) := lt_trans ratioPositive KAbove
  have baseBound : 4 * h < m * (K : ℝ) := by
    have := (div_lt_iff₀ mPositive).1 KAbove
    nlinarith
  have multiplierAtLeastOne : (1 : ℝ) ≤ ((K + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le K)
  have productBound :
      m * (K : ℝ) ≤ m * (K : ℝ) * ((K + 1 : ℕ) : ℝ) := by
    exact le_mul_of_one_le_right
      (mul_nonneg mPositive.le (Nat.cast_nonneg K)) multiplierAtLeastOne
  refine ⟨K, ?_⟩
  unfold ContinuousHG.QuadraticThresholdReached
  exact le_trans baseBound.le productBound

/-- Every positive quadratic weight pair lies in one exact strict/weak
first-zero phase cell. -/
theorem exists_quadraticPhaseCell
    {h m : ℝ} (hPositive : 0 < h) (mPositive : 0 < m) :
    ∃ K : ℕ, ContinuousHG.QuadraticPhaseCell h m K := by
  classical
  let thresholdExists :
      ∃ K : ℕ, ContinuousHG.QuadraticThresholdReached h m K :=
    exists_quadraticThresholdReached hPositive mPositive
  let K := Nat.find thresholdExists
  have reachedAtK : ContinuousHG.QuadraticThresholdReached h m K :=
    Nat.find_spec thresholdExists
  have KPositive : 0 < K := by
    by_contra notPositive
    have KZero : K = 0 := Nat.eq_zero_of_not_pos notPositive
    rw [KZero] at reachedAtK
    unfold ContinuousHG.QuadraticThresholdReached at reachedAtK
    norm_num at reachedAtK
    linarith
  have previousBefore : K - 1 < K := by omega
  have previousNotReached :
      ¬ ContinuousHG.QuadraticThresholdReached h m (K - 1) :=
    Nat.find_min thresholdExists previousBefore
  have previousSuccessor : K - 1 + 1 = K := by omega
  have lowerBoundary :
      m * (((K - 1 : ℕ) : ℝ)) * (K : ℝ) < 4 * h := by
    unfold ContinuousHG.QuadraticThresholdReached at previousNotReached
    rw [previousSuccessor] at previousNotReached
    exact lt_of_not_ge previousNotReached
  refine ⟨K, KPositive, hPositive, mPositive, lowerBoundary, ?_⟩
  exact reachedAtK

/-- Every horizon strictly before a quadratic first-zero phase is in the
unsaturated optimizer cell. -/
theorem quadraticPhaseCell_unsaturatedCell_of_lt
    {h m : ℝ} {K horizon : ℕ}
    (phase : ContinuousHG.QuadraticPhaseCell h m K)
    (horizonBefore : horizon < K) :
    ContinuousHG.QuadraticUnsaturatedCell h m horizon := by
  rcases phase with ⟨phasePositive, hPositive, mPositive,
    lowerBoundary, upperBoundary⟩
  have phaseAgain : ContinuousHG.QuadraticPhaseCell h m K :=
    ⟨phasePositive, hPositive, mPositive, lowerBoundary, upperBoundary⟩
  have notReached :=
    (ContinuousHG.quadraticPhaseCell_least_threshold phaseAgain).2
      horizon horizonBefore
  refine ⟨hPositive, mPositive, ?_⟩
  simpa [ContinuousHG.QuadraticThresholdReached] using
    (lt_of_not_ge notReached)

/-- The zero-extended unsaturated profile has exactly the unique-minimizer
decrease vector on every retained edge. -/
theorem quadraticZeroExtendedUnsaturatedProfile_step
    {h m : ℝ} {horizon : ℕ} (index : Fin horizon) :
    quadraticZeroExtendedUnsaturatedProfile h m horizon index.1 -
        quadraticZeroExtendedUnsaturatedProfile h m horizon (index.1 + 1) =
      ContinuousHG.quadraticUnsaturatedDecrease h m horizon index := by
  have indexWithin : index.1 ≤ horizon := Nat.le_of_lt index.2
  have successorWithin : index.1 + 1 ≤ horizon := index.2
  simpa [quadraticZeroExtendedUnsaturatedProfile, indexWithin,
    successorWithin] using
      (ContinuousHG.quadraticUnsaturatedProfile_step
        (h := h) (m := m) index)

/-- The saturated zero-tail profile has exactly the extension-stable
unique-minimizer decrease vector at every longer horizon. -/
theorem quadraticSaturatedProfile_extended_step
    {h m : ℝ} {K extension : ℕ} (index : Fin (K + extension)) :
    ContinuousHG.quadraticSaturatedProfile h m K index.1 -
        ContinuousHG.quadraticSaturatedProfile h m K (index.1 + 1) =
      ContinuousHG.quadraticExtendedDecrease h m K extension index := by
  by_cases active : index.1 < K
  · simpa [ContinuousHG.quadraticExtendedDecrease, active] using
      (ContinuousHG.quadraticSaturatedProfile_step
        (h := h) (m := m) (K := K) ⟨index.1, active⟩)
  · have atOrAfter : K ≤ index.1 := Nat.le_of_not_gt active
    have successorAtOrAfter : K ≤ index.1 + 1 :=
      le_trans atOrAfter (Nat.le_succ index.1)
    rw [ContinuousHG.quadraticSaturatedProfile_zero_tail atOrAfter,
      ContinuousHG.quadraticSaturatedProfile_zero_tail successorAtOrAfter]
    simp [ContinuousHG.quadraticExtendedDecrease, active]

/-- Exact optimizer proof selected by a horizon code.  Before the
boundary it contains the unsaturated unique minimizer; at and after the
boundary it contains the unique zero-extended saturated minimizer. -/
def QuadraticHorizonOptimizerProof
    (h m : ℝ) (K horizon : ℕ) : Prop :=
  (horizon < K ∧
    ContinuousHG.IsUniqueMinimizerOn
      (ContinuousHG.SolidSimplex : (Fin horizon → ℝ) → Prop)
      (ContinuousHG.quadraticReducedObjective h m
        (ContinuousHG.quadraticPathWeight horizon))
      (ContinuousHG.quadraticUnsaturatedDecrease h m horizon)) ∨
  (K ≤ horizon ∧ ∃ extension : ℕ,
    horizon = K + extension ∧
    ContinuousHG.IsUniqueMinimizerOn
      (ContinuousHG.SolidSimplex : (Fin (K + extension) → ℝ) → Prop)
      (ContinuousHG.quadraticReducedObjective h m
        (ContinuousHG.quadraticPathWeight (K + extension)))
      (ContinuousHG.quadraticExtendedDecrease h m K extension))

/-- A first-zero phase supplies the appropriate exact unique optimizer at
every finite horizon. -/
theorem quadraticHorizonOptimizerProof_of_phase
    {h m : ℝ} {K : ℕ}
    (phase : ContinuousHG.QuadraticPhaseCell h m K)
    (horizon : ℕ) :
    QuadraticHorizonOptimizerProof h m K horizon := by
  by_cases horizonBefore : horizon < K
  · left
    exact ⟨horizonBefore,
      ContinuousHG.quadraticUnsaturatedDecrease_unique_minimizer
        (quadraticPhaseCell_unsaturatedCell_of_lt phase horizonBefore)⟩
  · right
    have atOrAfter : K ≤ horizon := Nat.le_of_not_gt horizonBefore
    refine ⟨atOrAfter, horizon - K, ?_, ?_⟩
    · exact (Nat.add_sub_of_le atOrAfter).symm
    · exact ContinuousHG.quadraticExtension_stable_unique_minimizer phase

/-- The decoded profile is tied to the unique-minimizer decrease vector on
every finite horizon. -/
def QuadraticHorizonProfileProof
    (h m : ℝ) (K horizon : ℕ) : Prop :=
  (horizon < K ∧ ∀ index : Fin horizon,
    quadraticDeclaredHorizonProfile h m K horizon index.1 -
        quadraticDeclaredHorizonProfile h m K horizon (index.1 + 1) =
      ContinuousHG.quadraticUnsaturatedDecrease h m horizon index) ∨
  (K ≤ horizon ∧ ∃ extension : ℕ,
    horizon = K + extension ∧
    ∀ index : Fin (K + extension),
      quadraticDeclaredHorizonProfile h m K horizon index.1 -
          quadraticDeclaredHorizonProfile h m K horizon (index.1 + 1) =
        ContinuousHG.quadraticExtendedDecrease h m K extension index)

/-- The profile/decrease correspondence is definitionally valid for every
boundary index; unlike optimizer proof verification, it does not require the
weights to inhabit that boundary's phase cell. -/
theorem quadraticHorizonProfileProof_for_horizon
    (h m : ℝ) (K horizon : ℕ) :
    QuadraticHorizonProfileProof h m K horizon := by
  by_cases horizonBefore : horizon < K
  · left
    refine ⟨horizonBefore, ?_⟩
    intro index
    simpa [quadraticDeclaredHorizonProfile, horizonBefore] using
      (quadraticZeroExtendedUnsaturatedProfile_step
        (h := h) (m := m) index)
  · right
    have atOrAfter : K ≤ horizon := Nat.le_of_not_gt horizonBefore
    refine ⟨atOrAfter, horizon - K, ?_, ?_⟩
    · exact (Nat.add_sub_of_le atOrAfter).symm
    · intro index
      simpa [quadraticDeclaredHorizonProfile, horizonBefore] using
        (quadraticSaturatedProfile_extended_step
          (h := h) (m := m) index)

/-- **APP-MCC-COMP**, exact all-horizon closure.  A fixed first-zero phase has
a finite profile code; decoding commutes with horizon encoding; and every
decoded profile is proved equal to the corresponding unique reduced
optimizer. -/
theorem app_mcc_comp_allHorizon
    {h m : ℝ} (hPositive : 0 < h) (mPositive : 0 < m) :
    ∃ K : ℕ,
      ContinuousHG.QuadraticPhaseCell h m K ∧
      Fintype.card (QuadraticHorizonCode K) = K + 1 ∧
      (∀ horizon,
        quadraticHorizonDecode h m K (quadraticHorizonEncode K horizon) =
          quadraticDeclaredHorizonProfile h m K horizon) ∧
      (∀ horizon,
        QuadraticHorizonOptimizerProof h m K horizon) ∧
      (∀ horizon,
        QuadraticHorizonProfileProof h m K horizon) := by
  obtain ⟨K, phase⟩ := exists_quadraticPhaseCell hPositive mPositive
  exact ⟨K, phase, quadraticHorizonCode_card K,
    quadraticHorizonDecode_encode h m K,
    quadraticHorizonOptimizerProof_of_phase phase,
    quadraticHorizonProfileProof_for_horizon h m K⟩

end PhonologicalCalculus.Application
