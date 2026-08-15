import PhonologicalCalculus.Flux.PathWinnerComplete
import PhonologicalCalculus.Flux.Rigidity
import Mathlib.Tactic

/-!
# Complete star-winner rigidity bridge

This module derives the complete degree-three star functional equation from
winner predicates rather than assuming it as an untyped algebraic response.
Exact KKT-to-winner contracts are retained as explicit project-specific
concrete-objective premises.
The resulting equation composes with continuous additive rigidity to identify
the constitutive recoding.
-/

namespace PhonologicalCalculus.Flux

/-- Baseline free-center residual of a degree-three star. -/
def baselineStarResidual (lambda first second third : ℝ) : ℝ :=
  first + second + third + lambda

/-- Recoded free-center residual of the same degree-three star. -/
def transformedStarResidual
    (F : ℝ → ℝ) (lambda first second third : ℝ) : ℝ :=
  F first + F second + F third + lambda

/-- Exact KKT characterization of the free-center winner event for every
three-edge star probe. -/
def ExactStarWinnerKKT
    (winner : ℝ → ℝ → ℝ → Prop)
    (residual : ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∀ first second third,
    winner first second third ↔ residual first second third = 0

/-- Complete star-winner equality, together with exact KKT contracts, forces
the recoded stationarity equation at every baseline-balanced star. -/
theorem completeStarEquation_of_completeWinnerEquality
    (F : ℝ → ℝ) (lambda : ℝ)
    (baselineWinner transformedWinner : ℝ → ℝ → ℝ → Prop)
    (hbaseline : ExactStarWinnerKKT baselineWinner
      (baselineStarResidual lambda))
    (htransformed : ExactStarWinnerKKT transformedWinner
      (transformedStarResidual F lambda))
    (hwinner : baselineWinner = transformedWinner) :
    CompleteStarEquation F lambda := by
  intro first second
  let third := -lambda - first - second
  have hbaselineResidual :
      baselineStarResidual lambda first second third = 0 := by
    dsimp only [third, baselineStarResidual]
    ring
  have hbaselineWinner : baselineWinner first second third :=
    (hbaseline first second third).2 hbaselineResidual
  have htransformedWinner : transformedWinner first second third := by
    rw [← hwinner]
    exact hbaselineWinner
  exact (htransformed first second third).1 htransformedWinner

/-- Complete equality of degree-three star winners identifies every
continuous odd constitutive recoding at a nonzero load. -/
theorem identity_of_completeStarWinnerEquality
    (F : ℝ → ℝ) (lambda : ℝ)
    (baselineWinner transformedWinner : ℝ → ℝ → ℝ → Prop)
    (hbaseline : ExactStarWinnerKKT baselineWinner
      (baselineStarResidual lambda))
    (htransformed : ExactStarWinnerKKT transformedWinner
      (transformedStarResidual F lambda))
    (hwinner : baselineWinner = transformedWinner)
    (hcontinuous : Continuous F) (hodd : Function.Odd F)
    (hload : lambda ≠ 0) :
    F = id := by
  apply complete_star_rigidity hcontinuous hodd hload
  exact completeStarEquation_of_completeWinnerEquality
    F lambda baselineWinner transformedWinner
    hbaseline htransformed hwinner

/-- Complete one-site free path probes at two incommensurate loads identify a
continuous normalized constitutive recoding.  Each load-to-shift step is
obtained from actual winner equality through its exact KKT contract. -/
theorem identity_of_two_completePathWinnerProbeFamilies
    (F : ℝ → ℝ) (firstLoad secondLoad : ℝ)
    (baselineWinnerFirst transformedWinnerFirst : ℝ → Unit → Prop)
    (baselineWinnerSecond transformedWinnerSecond : ℝ → Unit → Prop)
    (hbaselineFirst : ∀ y, ExactWinnerKKT (baselineWinnerFirst y)
      (baselineFreeTwoEdgeProbeKKT firstLoad y))
    (htransformedFirst : ∀ y, ExactWinnerKKT (transformedWinnerFirst y)
      (transformedFreeTwoEdgeProbeKKT F firstLoad y))
    (hwinnerFirst : ∀ y,
      baselineWinnerFirst y = transformedWinnerFirst y)
    (hbaselineSecond : ∀ y, ExactWinnerKKT (baselineWinnerSecond y)
      (baselineFreeTwoEdgeProbeKKT secondLoad y))
    (htransformedSecond : ∀ y, ExactWinnerKKT (transformedWinnerSecond y)
      (transformedFreeTwoEdgeProbeKKT F secondLoad y))
    (hwinnerSecond : ∀ y,
      baselineWinnerSecond y = transformedWinnerSecond y)
    (hcontinuous : Continuous F) (hnormalized : F 0 = 0)
    (hincommensurate : Irrational (firstLoad / secondLoad)) :
    F = id := by
  have hfirst : ShiftEquivariant F firstLoad :=
    shiftEquivariant_of_completeFreeProbeWinnerEquivalence
      F firstLoad baselineWinnerFirst transformedWinnerFirst
      hbaselineFirst htransformedFirst hwinnerFirst
  have hsecond : ShiftEquivariant F secondLoad :=
    shiftEquivariant_of_completeFreeProbeWinnerEquivalence
      F secondLoad baselineWinnerSecond transformedWinnerSecond
      hbaselineSecond htransformedSecond hwinnerSecond
  exact incommensurate_shift_rigidity hcontinuous hnormalized
    hfirst hsecond hincommensurate

/-- **FLUX-D2.RIGIDITY.03**, complete semantic closure.  Incommensurate
complete path probes and complete degree-three star probes are two distinct
winner-level routes to constitutive identity. -/
theorem flux_d2_completeWinnerRigidity :
    (∀ (F : ℝ → ℝ) (firstLoad secondLoad : ℝ)
      (baselineWinnerFirst transformedWinnerFirst : ℝ → Unit → Prop)
      (baselineWinnerSecond transformedWinnerSecond : ℝ → Unit → Prop),
      (∀ y, ExactWinnerKKT (baselineWinnerFirst y)
        (baselineFreeTwoEdgeProbeKKT firstLoad y)) →
      (∀ y, ExactWinnerKKT (transformedWinnerFirst y)
        (transformedFreeTwoEdgeProbeKKT F firstLoad y)) →
      (∀ y, baselineWinnerFirst y = transformedWinnerFirst y) →
      (∀ y, ExactWinnerKKT (baselineWinnerSecond y)
        (baselineFreeTwoEdgeProbeKKT secondLoad y)) →
      (∀ y, ExactWinnerKKT (transformedWinnerSecond y)
        (transformedFreeTwoEdgeProbeKKT F secondLoad y)) →
      (∀ y, baselineWinnerSecond y = transformedWinnerSecond y) →
      Continuous F → F 0 = 0 →
      Irrational (firstLoad / secondLoad) → F = id) ∧
    (∀ (F : ℝ → ℝ) (lambda : ℝ)
      (baselineWinner transformedWinner : ℝ → ℝ → ℝ → Prop),
      ExactStarWinnerKKT baselineWinner (baselineStarResidual lambda) →
      ExactStarWinnerKKT transformedWinner
        (transformedStarResidual F lambda) →
      baselineWinner = transformedWinner →
      Continuous F → Function.Odd F → lambda ≠ 0 → F = id) := by
  constructor
  · exact identity_of_two_completePathWinnerProbeFamilies
  · exact identity_of_completeStarWinnerEquality

end PhonologicalCalculus.Flux
