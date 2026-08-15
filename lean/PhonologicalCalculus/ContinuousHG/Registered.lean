import PhonologicalCalculus.ContinuousHG.Quadratic
import Mathlib.Tactic.NormNum

/-!
# Registered continuous-HG proof goals

This module connects the reusable continuous-HG theory to the exact finite
records carried by six registered proof goals. The declarations are
mathematical propositions, not identifier-only proxies: they state the
profile, decrease, mass, boundary, and support facts that the corresponding
records require.
-/

namespace PhonologicalCalculus.ContinuousHG

/-- Decrease vector used by the registered solid-simplex identity. -/
noncomputable def chgB1FixtureDecreases : List ℝ := [1 / 5, 1 / 4, 1 / 10]

/-- Profile reconstructed from the registered solid-simplex fixture. -/
noncomputable def chgB1FixtureProfile : List ℝ :=
  profileFromDecreases 1 chgB1FixtureDecreases

/-- `CHG-B1.SIMPLEX.02`: the registered decrease vector is in the solid
simplex, reconstructs an admissible profile, and gives exactly the same
quadratic directional objective in profile and decrease coordinates. -/
theorem chg_b1_simplex_02 :
    SolidSimplexFrom 1 chgB1FixtureDecreases ∧
    AdmissibleProfileFrom 1 chgB1FixtureProfile ∧
    decreasesFrom 1 chgB1FixtureProfile = chgB1FixtureDecreases ∧
    pathHarmony quadraticPenalty (7 / 3) (5 / 4) chgB1FixtureProfile =
      (7 / 3) * ((chgB1FixtureDecreases.map quadraticPenalty).sum) +
        (5 / 4) * chgB1FixtureProfile.sum := by
  norm_num [chgB1FixtureDecreases, chgB1FixtureProfile,
    SolidSimplexFrom, AdmissibleProfileFrom, profileFromDecreases,
    decreasesFrom, pathHarmony, directionalDrops, directionalDropsFrom,
    directionalDrop, quadraticPenalty]

/-- `CHG-B2.BOUNDARY.04`: equality is on the zero side at the registered
`h = 5`, `m = 1`, `K = 4` boundary. The displayed tail is exactly zero and
the support statement excludes every coordinate at or beyond four. -/
theorem chg_b2_boundary_04 :
    QuadraticPhaseCell 5 1 4 ∧
    [quadraticSaturatedProfile 5 1 4 0,
      quadraticSaturatedProfile 5 1 4 1,
      quadraticSaturatedProfile 5 1 4 2,
      quadraticSaturatedProfile 5 1 4 3,
      quadraticSaturatedProfile 5 1 4 4,
      quadraticSaturatedProfile 5 1 4 5,
      quadraticSaturatedProfile 5 1 4 6] =
        [1, 3 / 5, 3 / 10, 1 / 10, 0, 0, 0] ∧
    (∀ i, 0 < quadraticSaturatedProfile 5 1 4 i ↔ i < 4) ∧
    quadraticSaturatedProfile 5 1 4 4 = 0 := by
  have hphase : QuadraticPhaseCell 5 1 4 := by
    norm_num [QuadraticPhaseCell]
  exact ⟨hphase,
    by norm_num [quadraticSaturatedProfile],
    fun i => quadraticSaturatedProfile_support_iff hphase,
    by norm_num [quadraticSaturatedProfile]⟩

/-- `CHG-B2.ANCHORS.05`: the three registered support indices and exact
profiles, including the stable zero following the `h = 5`, `m = 1` boundary. -/
theorem chg_b2_anchors_05 :
    QuadraticPhaseCell 20 3 5 ∧
    [quadraticSaturatedProfile 20 3 5 0,
      quadraticSaturatedProfile 20 3 5 1,
      quadraticSaturatedProfile 20 3 5 2,
      quadraticSaturatedProfile 20 3 5 3,
      quadraticSaturatedProfile 20 3 5 4,
      quadraticSaturatedProfile 20 3 5 5] =
        [1, 13 / 20, 3 / 8, 7 / 40, 1 / 20, 0] ∧
    QuadraticPhaseCell 5 1 4 ∧
    [quadraticSaturatedProfile 5 1 4 0,
      quadraticSaturatedProfile 5 1 4 1,
      quadraticSaturatedProfile 5 1 4 2,
      quadraticSaturatedProfile 5 1 4 3,
      quadraticSaturatedProfile 5 1 4 4,
      quadraticSaturatedProfile 5 1 4 5] =
        [1, 3 / 5, 3 / 10, 1 / 10, 0, 0] ∧
    QuadraticPhaseCell 21 1 9 ∧
    [quadraticUnsaturatedProfile 21 1 1 0,
      quadraticUnsaturatedProfile 21 1 1 1] = [1, 41 / 42] := by
  norm_num [QuadraticPhaseCell, quadraticSaturatedProfile,
    quadraticUnsaturatedProfile]

/-- `CHG-B3.UNSATURATED.01`: exact unconstrained decreases, reconstructed
profile, and strict slack of the unit decrease budget. -/
theorem chg_b3_unsaturated_01 :
    [quadraticUnsaturatedDecrease 21 1 3 ⟨0, by decide⟩,
      quadraticUnsaturatedDecrease 21 1 3 ⟨1, by decide⟩,
      quadraticUnsaturatedDecrease 21 1 3 ⟨2, by decide⟩] =
        [1 / 14, 1 / 21, 1 / 42] ∧
    [quadraticUnsaturatedProfile 21 1 3 0,
      quadraticUnsaturatedProfile 21 1 3 1,
      quadraticUnsaturatedProfile 21 1 3 2,
      quadraticUnsaturatedProfile 21 1 3 3] =
        [1, 13 / 14, 37 / 42, 6 / 7] ∧
    ([1 / 14, 1 / 21, 1 / 42] : List ℝ).sum < 1 := by
  norm_num [quadraticUnsaturatedDecrease, quadraticPathWeight,
    quadraticUnsaturatedProfile]

/-- `CHG-B3.SATURATED.02`: exact active decreases, unit mass, and profile at
the registered saturated boundary. -/
theorem chg_b3_saturated_02 :
    [quadraticSaturatedDecrease 5 1 4 ⟨0, by decide⟩,
      quadraticSaturatedDecrease 5 1 4 ⟨1, by decide⟩,
      quadraticSaturatedDecrease 5 1 4 ⟨2, by decide⟩,
      quadraticSaturatedDecrease 5 1 4 ⟨3, by decide⟩] =
        [2 / 5, 3 / 10, 1 / 5, 1 / 10] ∧
    ([2 / 5, 3 / 10, 1 / 5, 1 / 10] : List ℝ).sum = 1 ∧
    [quadraticSaturatedProfile 5 1 4 0,
      quadraticSaturatedProfile 5 1 4 1,
      quadraticSaturatedProfile 5 1 4 2,
      quadraticSaturatedProfile 5 1 4 3,
      quadraticSaturatedProfile 5 1 4 4] =
        [1, 3 / 5, 3 / 10, 1 / 10, 0] := by
  norm_num [quadraticSaturatedDecrease, quadraticSaturatedProfile]

/-- Exact strict/weak condition saying that `L` followers are positive in the
quadratic family: the `L` threshold is still strict and the next one is on the
zero side. -/
def QuadraticPositiveFollowerCount (h m : ℝ) (L : ℕ) : Prop :=
  0 < h ∧ 0 < m ∧
    m * (L : ℝ) * ((L + 1 : ℕ) : ℝ) < 4 * h ∧
    4 * h ≤ m * ((L + 1 : ℕ) : ℝ) * ((L + 2 : ℕ) : ℝ)

theorem quadraticPositiveFollowerCount_iff_phaseCell
    (h m : ℝ) (L : ℕ) :
    QuadraticPositiveFollowerCount h m L ↔
      QuadraticPhaseCell h m (L + 1) := by
  simp only [QuadraticPositiveFollowerCount, QuadraticPhaseCell,
    Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, Nat.succ_pos, true_and]
  ring_nf

/-- A positive-follower count determines the complete strict support of its
closed profile. -/
theorem quadraticPositiveFollowerCount_support_iff
    {h m : ℝ} {L i : ℕ}
    (hcount : QuadraticPositiveFollowerCount h m L) :
    0 < quadraticSaturatedProfile h m (L + 1) i ↔ i < L + 1 := by
  apply quadraticSaturatedProfile_support_iff
  exact (quadraticPositiveFollowerCount_iff_phaseCell h m L).1 hcount

/-- `CHG-B3.SUPPORT.03`: complete replay of the six registered strict support
cells. In each row the final natural is both the positive-follower count and
the greatest strict triangular index. -/
theorem chg_b3_support_03 :
    QuadraticPositiveFollowerCount 5 1 3 ∧
    QuadraticPositiveFollowerCount 5 3 2 ∧
    QuadraticPositiveFollowerCount 20 1 8 ∧
    QuadraticPositiveFollowerCount 20 3 4 ∧
    QuadraticPositiveFollowerCount 21 1 8 ∧
    QuadraticPositiveFollowerCount 21 3 4 := by
  norm_num [QuadraticPositiveFollowerCount]

end PhonologicalCalculus.ContinuousHG
