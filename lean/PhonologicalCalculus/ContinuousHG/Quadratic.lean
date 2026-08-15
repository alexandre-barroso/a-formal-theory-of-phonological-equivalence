import PhonologicalCalculus.ContinuousHG.Core
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Exact quadratic directional-HG kernel

This module formalizes the quadratic member of the reduced directional path
family.  It first proves an exact objective-gap identity and a finite-simplex
Karush--Kuhn--Tucker sufficiency and uniqueness theorem.  It then gives the
closed saturated and unsaturated profiles, the strict/weak triangular phase
cell, the exact first-zero property, the stable zero tail, and the registered
rational anchor calculations.

The general real-power optimizer theorem requires additional real-power and
convex-analysis infrastructure.  Nothing below represents that unformalized
part as already proved.
-/

namespace PhonologicalCalculus.ContinuousHG

open scoped BigOperators

section FiniteQuadraticObjective

variable {ι : Type*} [Fintype ι]

/-- Solid simplex of finite nonnegative decrease vectors. -/
def SolidSimplex (d : ι → ℝ) : Prop :=
  (∀ i, 0 ≤ d i) ∧ (∑ i, d i) ≤ 1

/-- Quadratic reduced objective with an arbitrary finite positive-direction
weight field. -/
def quadraticReducedObjective (h m : ℝ) (weight d : ι → ℝ) : ℝ :=
  ∑ i, (h * (d i) ^ 2 - m * weight i * d i)

/-- Coordinate gradient of the quadratic reduced objective. -/
def quadraticGradient (h m : ℝ) (weight d : ι → ℝ) (i : ι) : ℝ :=
  2 * h * d i - m * weight i

/-- A point is the unique minimizer of `objective` on `carrier`. -/
def IsUniqueMinimizerOn (carrier : (ι → ℝ) → Prop)
    (objective : (ι → ℝ) → ℝ) (u : ι → ℝ) : Prop :=
  carrier u ∧
    ∀ d, carrier d →
      objective u ≤ objective d ∧
      (objective d = objective u → d = u)

/-- Exact completion-of-squares identity around an arbitrary reference
vector.  The second term is the first-order residual. -/
theorem quadraticObjective_gap_identity (h m : ℝ) (weight d u : ι → ℝ) :
    quadraticReducedObjective h m weight d -
        quadraticReducedObjective h m weight u =
      h * ∑ i, (d i - u i) ^ 2 +
        ∑ i, quadraticGradient h m weight u i * (d i - u i) := by
  classical
  unfold quadraticReducedObjective quadraticGradient
  rw [← Finset.sum_sub_distrib]
  calc
    (∑ i, ((h * d i ^ 2 - m * weight i * d i) -
        (h * u i ^ 2 - m * weight i * u i))) =
        ∑ i, (h * (d i - u i) ^ 2 +
          (2 * h * u i - m * weight i) * (d i - u i)) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
    _ = h * ∑ i, (d i - u i) ^ 2 +
        ∑ i, (2 * h * u i - m * weight i) * (d i - u i) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]

/-- Finite-simplex KKT sufficiency for the quadratic family.  A common
multiplier acts on positive coordinates; inactive coordinates have no smaller
gradient.  A nonpositive multiplier handles the slack direction of the solid
simplex.  Strict convexity supplied by `h > 0` makes the minimizer unique. -/
theorem quadratic_unique_minimizer_of_simplex_kkt
    {h m lambda : ℝ} (weight u : ι → ℝ)
    (hh : 0 < h) (hu : SolidSimplex u)
    (humass : (∑ i, u i) = 1) (hlambda : lambda ≤ 0)
    (hgradient : ∀ i, lambda ≤ quadraticGradient h m weight u i)
    (hactive : ∀ i, 0 < u i → quadraticGradient h m weight u i = lambda) :
    IsUniqueMinimizerOn (SolidSimplex : (ι → ℝ) → Prop)
      (quadraticReducedObjective h m weight) u := by
  classical
  refine ⟨hu, ?_⟩
  intro d hd
  let gradient : ι → ℝ := quadraticGradient h m weight u
  have hcorrectionPointwise :
      ∀ i, 0 ≤ (gradient i - lambda) * (d i - u i) := by
    intro i
    by_cases hui : u i = 0
    · rw [hui, sub_zero]
      exact mul_nonneg (sub_nonneg.mpr (hgradient i)) (hd.1 i)
    · have huiPos : 0 < u i := lt_of_le_of_ne (hu.1 i) (Ne.symm hui)
      have hgi : gradient i = lambda := hactive i huiPos
      simp [hgi]
  have hcorrection :
      0 ≤ ∑ i, (gradient i - lambda) * (d i - u i) :=
    Finset.sum_nonneg fun i _ => hcorrectionPointwise i
  have hmassDifference : (∑ i, d i) - ∑ i, u i ≤ 0 := by
    rw [humass]
    linarith [hd.2]
  have hlambdaMass :
      0 ≤ lambda * ((∑ i, d i) - ∑ i, u i) :=
    mul_nonneg_of_nonpos_of_nonpos hlambda hmassDifference
  have hlinearIdentity :
      (∑ i, gradient i * (d i - u i)) =
        lambda * ((∑ i, d i) - ∑ i, u i) +
          ∑ i, (gradient i - lambda) * (d i - u i) := by
    calc
      (∑ i, gradient i * (d i - u i)) =
          ∑ i, (lambda * (d i - u i) +
            (gradient i - lambda) * (d i - u i)) := by
              apply Finset.sum_congr rfl
              intro i _
              ring
      _ = (∑ i, lambda * (d i - u i)) +
          ∑ i, (gradient i - lambda) * (d i - u i) :=
            Finset.sum_add_distrib
      _ = lambda * (∑ i, (d i - u i)) +
          ∑ i, (gradient i - lambda) * (d i - u i) := by
            rw [Finset.mul_sum]
      _ = lambda * ((∑ i, d i) - ∑ i, u i) +
          ∑ i, (gradient i - lambda) * (d i - u i) := by
            rw [Finset.sum_sub_distrib]
  have hlinear : 0 ≤ ∑ i, gradient i * (d i - u i) := by
    rw [hlinearIdentity]
    exact add_nonneg hlambdaMass hcorrection
  have hsquares : 0 ≤ ∑ i, (d i - u i) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg (d i - u i)
  have hgap :
      0 ≤ quadraticReducedObjective h m weight d -
        quadraticReducedObjective h m weight u := by
    rw [quadraticObjective_gap_identity]
    exact add_nonneg (mul_nonneg hh.le hsquares) hlinear
  constructor
  · linarith
  · intro hequal
    have hgapZero :
        quadraticReducedObjective h m weight d -
          quadraticReducedObjective h m weight u = 0 := by
      linarith
    have hsquareProductNonpositive :
        h * ∑ i, (d i - u i) ^ 2 ≤ 0 := by
      rw [quadraticObjective_gap_identity] at hgapZero
      linarith
    have hsquaresZero : ∑ i, (d i - u i) ^ 2 = 0 := by
      have hsquareProductNonnegative :
          0 ≤ h * ∑ i, (d i - u i) ^ 2 :=
        mul_nonneg hh.le hsquares
      nlinarith
    funext i
    have hterm : (d i - u i) ^ 2 = 0 := by
      exact (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => sq_nonneg (d j - u j))).1 hsquaresZero i
        (Finset.mem_univ i)
    nlinarith

/-- Unconstrained coordinatewise stationarity gives an exact square gap. -/
theorem quadratic_unconstrained_gap
    {h m : ℝ} (hh : h ≠ 0) (weight d : ι → ℝ) :
    let u := fun i => m * weight i / (2 * h)
    quadraticReducedObjective h m weight d -
        quadraticReducedObjective h m weight u =
      h * ∑ i, (d i - u i) ^ 2 := by
  classical
  dsimp
  rw [quadraticObjective_gap_identity]
  have hstationary :
      ∀ i, quadraticGradient h m weight
        (fun j => m * weight j / (2 * h)) i = 0 := by
    intro i
    simp only [quadraticGradient]
    field_simp [hh]
    ring
  simp [hstationary]

/-- When the unconstrained stationary point lies in the solid simplex, it is
also the unique simplex minimizer. -/
theorem quadratic_unconstrained_unique_minimizer
    {h m : ℝ} (hh : 0 < h) (weight : ι → ℝ)
    (hu : SolidSimplex (fun i => m * weight i / (2 * h))) :
    IsUniqueMinimizerOn (SolidSimplex : (ι → ℝ) → Prop)
      (quadraticReducedObjective h m weight)
      (fun i => m * weight i / (2 * h)) := by
  classical
  let u : ι → ℝ := fun i => m * weight i / (2 * h)
  refine ⟨hu, ?_⟩
  intro d _hd
  have hgap :
      quadraticReducedObjective h m weight d -
          quadraticReducedObjective h m weight u =
        h * ∑ i, (d i - u i) ^ 2 := by
    simpa [u] using quadratic_unconstrained_gap (ι := ι) hh.ne' weight d
  have hsquares : 0 ≤ ∑ i, (d i - u i) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg (d i - u i)
  constructor
  · nlinarith
  · intro hequal
    have hsquaresZero : ∑ i, (d i - u i) ^ 2 = 0 := by
      have hgapZero :
          quadraticReducedObjective h m weight d -
            quadraticReducedObjective h m weight u = 0 := by
        linarith
      nlinarith
    funext i
    have hterm : (d i - u i) ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => sq_nonneg (d j - u j))).1 hsquaresZero i
        (Finset.mem_univ i)
    nlinarith

end FiniteQuadraticObjective

section ClosedProfiles

theorem sum_fin_index_real (K : ℕ) :
    (∑ i : Fin K, (i.1 : ℝ)) =
      (K : ℝ) * (((K - 1 : ℕ) : ℝ)) / 2 := by
  rw [Fin.sum_univ_eq_sum_range]
  have hNat : (∑ i ∈ Finset.range K, i) * 2 = K * (K - 1) :=
    Finset.sum_range_id_mul_two K
  have hReal : (∑ i ∈ Finset.range K, (i : ℝ)) * 2 =
      (K : ℝ) * ((K - 1 : ℕ) : ℝ) := by
    calc
      (∑ i ∈ Finset.range K, (i : ℝ)) * 2 =
          (((∑ i ∈ Finset.range K, i) * 2 : ℕ) : ℝ) := by
            norm_num [Nat.cast_sum]
      _ = ((K * (K - 1) : ℕ) : ℝ) := by rw [hNat]
      _ = (K : ℝ) * ((K - 1 : ℕ) : ℝ) := by norm_num
  linarith

/-- Strict/weak phase cell selecting `K` as the first zero in the quadratic
family.  The lower boundary is strict; the upper boundary is weak. -/
def QuadraticPhaseCell (h m : ℝ) (K : ℕ) : Prop :=
  0 < K ∧ 0 < h ∧ 0 < m ∧
    m * ((K - 1 : ℕ) : ℝ) * (K : ℝ) < 4 * h ∧
    4 * h ≤ m * (K : ℝ) * ((K + 1 : ℕ) : ℝ)

/-- Threshold predicate equivalent to exhaustion of the unit decrease budget
at a quadratic triangular boundary. -/
def QuadraticThresholdReached (h m : ℝ) (k : ℕ) : Prop :=
  4 * h ≤ m * (k : ℝ) * ((k + 1 : ℕ) : ℝ)

/-- Saturated quadratic optimizer profile.  Natural subtraction makes every
coordinate at and beyond `K` exactly zero. -/
noncomputable def quadraticSaturatedProfile (h m : ℝ) (K i : ℕ) : ℝ :=
  ((K - i : ℕ) : ℝ) *
    (1 / (K : ℝ) - m * (i : ℝ) / (4 * h))

/-- Unsaturated quadratic optimizer profile at a declared horizon. -/
noncomputable def quadraticUnsaturatedProfile (h m : ℝ) (N i : ℕ) : ℝ :=
  1 - m * (i : ℝ) * ((2 * N + 1 - i : ℕ) : ℝ) / (4 * h)

/-- Positional coefficient in the reduced directional objective at horizon
`N`; the first decrease has coefficient `N` and the last coefficient one. -/
def quadraticPathWeight (N : ℕ) (i : Fin N) : ℝ :=
  ((N - i.1 : ℕ) : ℝ)

theorem quadraticPathWeight_sum (N : ℕ) :
    (∑ i : Fin N, quadraticPathWeight N i) =
      (N : ℝ) * ((N + 1 : ℕ) : ℝ) / 2 := by
  cases N with
  | zero => simp [quadraticPathWeight]
  | succ n =>
      have hpoint : ∀ i : Fin (n + 1),
          quadraticPathWeight (n + 1) i =
            ((n + 1 : ℕ) : ℝ) - (i.1 : ℝ) := by
        intro i
        unfold quadraticPathWeight
        have hNat : n + 1 - i.1 + i.1 = n + 1 :=
          Nat.sub_add_cancel (Nat.le_of_lt i.2)
        have hReal : ((n + 1 - i.1 : ℕ) : ℝ) + (i.1 : ℝ) =
            ((n + 1 : ℕ) : ℝ) := by
          exact_mod_cast hNat
        linarith
      simp_rw [hpoint]
      rw [Finset.sum_sub_distrib, sum_fin_index_real]
      simp
      ring

/-- Unconstrained quadratic decrease vector before the unit budget becomes
active. -/
noncomputable def quadraticUnsaturatedDecrease (h m : ℝ) (N : ℕ)
    (i : Fin N) : ℝ :=
  m * quadraticPathWeight N i / (2 * h)

/-- Strict pre-threshold cell at a finite horizon. -/
def QuadraticUnsaturatedCell (h m : ℝ) (N : ℕ) : Prop :=
  0 < h ∧ 0 < m ∧
    m * (N : ℝ) * ((N + 1 : ℕ) : ℝ) < 4 * h

theorem quadraticUnsaturatedDecrease_sum
    {h m : ℝ} {N : ℕ} (hh : h ≠ 0) :
    (∑ i : Fin N, quadraticUnsaturatedDecrease h m N i) =
      m * (N : ℝ) * ((N + 1 : ℕ) : ℝ) / (4 * h) := by
  classical
  unfold quadraticUnsaturatedDecrease
  calc
    (∑ i : Fin N, m * quadraticPathWeight N i / (2 * h)) =
        (m / (2 * h)) * ∑ i : Fin N, quadraticPathWeight N i := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
    _ = m * (N : ℝ) * ((N + 1 : ℕ) : ℝ) / (4 * h) := by
      rw [quadraticPathWeight_sum]
      field_simp [hh]
      ring

theorem quadraticUnsaturatedDecrease_solidSimplex
    {h m : ℝ} {N : ℕ} (hcell : QuadraticUnsaturatedCell h m N) :
    SolidSimplex (quadraticUnsaturatedDecrease h m N) := by
  rcases hcell with ⟨hh, hm, hstrict⟩
  constructor
  · intro i
    unfold quadraticUnsaturatedDecrease quadraticPathWeight
    exact div_nonneg (mul_nonneg hm.le (Nat.cast_nonneg _))
      (mul_nonneg (by norm_num) hh.le)
  · rw [quadraticUnsaturatedDecrease_sum hh.ne']
    have hdenom : 0 < 4 * h := by positivity
    exact (div_lt_one hdenom).2 hstrict |>.le

/-- Before the strict triangular threshold, the unconstrained stationary
vector is feasible and is therefore the unique reduced-objective minimizer. -/
theorem quadraticUnsaturatedDecrease_unique_minimizer
    {h m : ℝ} {N : ℕ} (hcell : QuadraticUnsaturatedCell h m N) :
    IsUniqueMinimizerOn (SolidSimplex : (Fin N → ℝ) → Prop)
      (quadraticReducedObjective h m (quadraticPathWeight N))
      (quadraticUnsaturatedDecrease h m N) := by
  rcases hcell with ⟨hh, hm, hstrict⟩
  have hcell' : QuadraticUnsaturatedCell h m N := ⟨hh, hm, hstrict⟩
  have hsimplex := quadraticUnsaturatedDecrease_solidSimplex hcell'
  change IsUniqueMinimizerOn (SolidSimplex : (Fin N → ℝ) → Prop)
    (quadraticReducedObjective h m (quadraticPathWeight N))
    (fun i => m * quadraticPathWeight N i / (2 * h))
  exact quadratic_unconstrained_unique_minimizer
    (ι := Fin N) (m := m) hh (quadraticPathWeight N) hsimplex

/-- The unconstrained decrease vector is exactly the consecutive difference
of the unsaturated profile. -/
theorem quadraticUnsaturatedProfile_step
    {h m : ℝ} {N : ℕ} (i : Fin N) :
    quadraticUnsaturatedProfile h m N i.1 -
        quadraticUnsaturatedProfile h m N (i.1 + 1) =
      quadraticUnsaturatedDecrease h m N i := by
  have hFirstNat :
      2 * N + 1 - i.1 + i.1 = 2 * N + 1 := by omega
  have hSecondNat :
      2 * N + 1 - (i.1 + 1) + (i.1 + 1) = 2 * N + 1 := by omega
  have hWeightNat : N - i.1 + i.1 = N :=
    Nat.sub_add_cancel (Nat.le_of_lt i.2)
  have hFirstReal : ((2 * N + 1 - i.1 : ℕ) : ℝ) =
      2 * (N : ℝ) + 1 - (i.1 : ℝ) := by
    have hcast : ((2 * N + 1 - i.1 : ℕ) : ℝ) + (i.1 : ℝ) =
        2 * (N : ℝ) + 1 := by exact_mod_cast hFirstNat
    linarith
  have hSecondReal : ((2 * N + 1 - (i.1 + 1) : ℕ) : ℝ) =
      2 * (N : ℝ) - (i.1 : ℝ) := by
    have hcast : ((2 * N + 1 - (i.1 + 1) : ℕ) : ℝ) +
        ((i.1 : ℝ) + 1) = 2 * (N : ℝ) + 1 := by
      exact_mod_cast hSecondNat
    linarith
  have hWeightReal : ((N - i.1 : ℕ) : ℝ) =
      (N : ℝ) - (i.1 : ℝ) := by
    have hcast : ((N - i.1 : ℕ) : ℝ) + (i.1 : ℝ) = (N : ℝ) := by
      exact_mod_cast hWeightNat
    linarith
  unfold quadraticUnsaturatedProfile quadraticUnsaturatedDecrease
    quadraticPathWeight
  rw [hFirstReal, hSecondReal, hWeightReal]
  push_cast
  ring

/-- Closed saturated decrease vector at its first-zero horizon. -/
noncomputable def quadraticSaturatedDecrease (h m : ℝ) (K : ℕ)
    (i : Fin K) : ℝ :=
  1 / (K : ℝ) +
    m * (((K - 1 : ℕ) : ℝ) - 2 * (i.1 : ℝ)) / (4 * h)

/-- Common active-set multiplier for the saturated quadratic vector. -/
noncomputable def quadraticSaturatedMultiplier (h m : ℝ) (K : ℕ) : ℝ :=
  2 * h / (K : ℝ) - m * ((K + 1 : ℕ) : ℝ) / 2

theorem quadraticSaturatedDecrease_sum {h m : ℝ} {K : ℕ}
    (hK : 0 < K) :
    ∑ i, quadraticSaturatedDecrease h m K i = 1 := by
  classical
  have hK0 : (K : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hK
  have hshapeSum :
      (∑ i : Fin K,
        (((K - 1 : ℕ) : ℝ) - 2 * (i.1 : ℝ))) = 0 := by
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    rw [← Finset.mul_sum, sum_fin_index_real]
    ring
  calc
    (∑ i : Fin K, quadraticSaturatedDecrease h m K i) =
        ∑ i : Fin K, (1 / (K : ℝ) +
          (m / (4 * h)) *
            (((K - 1 : ℕ) : ℝ) - 2 * (i.1 : ℝ))) := by
              apply Finset.sum_congr rfl
              intro i _
              unfold quadraticSaturatedDecrease
              ring
    _ = (∑ _i : Fin K, 1 / (K : ℝ)) +
        (m / (4 * h)) *
          ∑ i : Fin K, (((K - 1 : ℕ) : ℝ) - 2 * (i.1 : ℝ)) := by
            rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ = (K : ℝ) * (1 / (K : ℝ)) := by
      rw [hshapeSum]
      simp
    _ = 1 := by
      field_simp [hK0]

theorem quadraticSaturatedDecrease_positive
    {h m : ℝ} {K : ℕ} (hphase : QuadraticPhaseCell h m K)
    (i : Fin K) : 0 < quadraticSaturatedDecrease h m K i := by
  rcases hphase with ⟨hK, hh, hm, hlower, _⟩
  have hKreal : 0 < (K : ℝ) := by exact_mod_cast hK
  have hi : i.1 ≤ K - 1 := Nat.le_sub_one_of_lt i.2
  have hiReal : (i.1 : ℝ) ≤ ((K - 1 : ℕ) : ℝ) := by exact_mod_cast hi
  have hdenom : 0 < 4 * h := by positivity
  have hlastFraction :
      m * ((K - 1 : ℕ) : ℝ) / (4 * h) < 1 / (K : ℝ) := by
    exact (div_lt_div_iff₀ hdenom hKreal).2 (by simpa using hlower)
  have hshape : -((K - 1 : ℕ) : ℝ) ≤
      ((K - 1 : ℕ) : ℝ) - 2 * (i.1 : ℝ) := by
    linarith
  have hscale : 0 ≤ m / (4 * h) := div_nonneg hm.le hdenom.le
  have hscaled := mul_le_mul_of_nonneg_left hshape hscale
  have hscaled' :
      -m * ((K - 1 : ℕ) : ℝ) / (4 * h) ≤
        m * (((K - 1 : ℕ) : ℝ) - 2 * (i.1 : ℝ)) / (4 * h) := by
    calc
      -m * ((K - 1 : ℕ) : ℝ) / (4 * h) =
          (m / (4 * h)) * -((K - 1 : ℕ) : ℝ) := by ring
      _ ≤ (m / (4 * h)) *
          (((K - 1 : ℕ) : ℝ) - 2 * (i.1 : ℝ)) := hscaled
      _ = m * (((K - 1 : ℕ) : ℝ) - 2 * (i.1 : ℝ)) /
          (4 * h) := by ring
  have hscaled'' :
      -(m * ((K - 1 : ℕ) : ℝ) / (4 * h)) ≤
        m * (((K - 1 : ℕ) : ℝ) - 2 * (i.1 : ℝ)) / (4 * h) := by
    calc
      -(m * ((K - 1 : ℕ) : ℝ) / (4 * h)) =
          -m * ((K - 1 : ℕ) : ℝ) / (4 * h) := by ring
      _ ≤ _ := hscaled'
  unfold quadraticSaturatedDecrease
  have hlastPositive :
      0 < 1 / (K : ℝ) - m * ((K - 1 : ℕ) : ℝ) / (4 * h) :=
    sub_pos.mpr hlastFraction
  have hcandidateLower :
      1 / (K : ℝ) - m * ((K - 1 : ℕ) : ℝ) / (4 * h) ≤
        1 / (K : ℝ) +
          m * (((K - 1 : ℕ) : ℝ) - 2 * (i.1 : ℝ)) / (4 * h) := by
    simpa [sub_eq_add_neg] using
      add_le_add_left hscaled'' (1 / (K : ℝ))
  exact lt_of_lt_of_le hlastPositive hcandidateLower

theorem quadraticSaturatedDecrease_gradient
    {h m : ℝ} {K : ℕ} (hh : h ≠ 0) (i : Fin K) :
    quadraticGradient h m (quadraticPathWeight K)
        (quadraticSaturatedDecrease h m K) i =
      quadraticSaturatedMultiplier h m K := by
  unfold quadraticGradient quadraticPathWeight quadraticSaturatedDecrease
    quadraticSaturatedMultiplier
  have hdecomp : K - i.1 + i.1 = K := Nat.sub_add_cancel (Nat.le_of_lt i.2)
  have hcast : ((K - i.1 : ℕ) : ℝ) + (i.1 : ℝ) = (K : ℝ) := by
    exact_mod_cast hdecomp
  have hKpos : 0 < K := Nat.zero_lt_of_lt i.2
  have hK0 : (K : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hKpos
  have hpredNat : K - 1 + 1 = K := Nat.sub_add_cancel hKpos
  have hpredCast : ((K - 1 : ℕ) : ℝ) + 1 = (K : ℝ) := by
    exact_mod_cast hpredNat
  have hweightReal : ((K - i.1 : ℕ) : ℝ) = (K : ℝ) - (i.1 : ℝ) := by
    linarith [hcast]
  have hpredReal : ((K - 1 : ℕ) : ℝ) = (K : ℝ) - 1 := by
    linarith [hpredCast]
  have hsuccReal : ((K + 1 : ℕ) : ℝ) = (K : ℝ) + 1 := by
    norm_num
  rw [hweightReal, hpredReal, hsuccReal]
  field_simp [hh, hK0]
  ring

theorem quadraticSaturatedMultiplier_nonpositive
    {h m : ℝ} {K : ℕ} (hphase : QuadraticPhaseCell h m K) :
    quadraticSaturatedMultiplier h m K ≤ 0 := by
  rcases hphase with ⟨hK, hh, hm, _, hupper⟩
  have hKreal : 0 < (K : ℝ) := by exact_mod_cast hK
  have hhalf : 0 < (2 : ℝ) := by norm_num
  have hquotient : 2 * h / (K : ℝ) ≤
      m * ((K + 1 : ℕ) : ℝ) / 2 := by
    exact (div_le_div_iff₀ hKreal hhalf).2 (by nlinarith)
  exact sub_nonpos.mpr hquotient

/-- At the phase-selected first-zero horizon, the closed saturated decrease
vector is the unique minimizer of the reduced quadratic path objective. -/
theorem quadraticSaturatedDecrease_unique_minimizer
    {h m : ℝ} {K : ℕ} (hphase : QuadraticPhaseCell h m K) :
    IsUniqueMinimizerOn (SolidSimplex : (Fin K → ℝ) → Prop)
      (quadraticReducedObjective h m (quadraticPathWeight K))
      (quadraticSaturatedDecrease h m K) := by
  rcases hphase with ⟨hK, hh, hm, hlower, hupper⟩
  have hphase' : QuadraticPhaseCell h m K :=
    ⟨hK, hh, hm, hlower, hupper⟩
  have hpositive : ∀ i : Fin K,
      0 < quadraticSaturatedDecrease h m K i :=
    quadraticSaturatedDecrease_positive hphase'
  have hsum : ∑ i, quadraticSaturatedDecrease h m K i = 1 :=
    quadraticSaturatedDecrease_sum hK
  apply quadratic_unique_minimizer_of_simplex_kkt
    (weight := quadraticPathWeight K)
    (u := quadraticSaturatedDecrease h m K)
    (lambda := quadraticSaturatedMultiplier h m K)
  · exact hh
  · exact ⟨fun i => (hpositive i).le, by linarith⟩
  · exact hsum
  · exact quadraticSaturatedMultiplier_nonpositive hphase'
  · intro i
    rw [quadraticSaturatedDecrease_gradient hh.ne' i]
  · intro i _
    exact quadraticSaturatedDecrease_gradient hh.ne' i

/-- The closed decrease vector is exactly the consecutive difference of the
closed saturated profile. -/
theorem quadraticSaturatedProfile_step
    {h m : ℝ} {K : ℕ} (i : Fin K) :
    quadraticSaturatedProfile h m K i.1 -
        quadraticSaturatedProfile h m K (i.1 + 1) =
      quadraticSaturatedDecrease h m K i := by
  have hsuccLe : i.1 + 1 ≤ K := i.2
  have hremainNat :
      K - i.1 = (K - (i.1 + 1)) + 1 := by omega
  have hdecompNat :
      K = (K - (i.1 + 1)) + (i.1 + 1) := by omega
  have hpredNat :
      K - 1 = (K - (i.1 + 1)) + i.1 := by omega
  have hremainReal : ((K - i.1 : ℕ) : ℝ) =
      ((K - (i.1 + 1) : ℕ) : ℝ) + 1 := by
    exact_mod_cast hremainNat
  have hdecompReal : (K : ℝ) =
      ((K - (i.1 + 1) : ℕ) : ℝ) + ((i.1 : ℝ) + 1) := by
    exact_mod_cast hdecompNat
  have hpredReal : ((K - 1 : ℕ) : ℝ) =
      ((K - (i.1 + 1) : ℕ) : ℝ) + (i.1 : ℝ) := by
    exact_mod_cast hpredNat
  unfold quadraticSaturatedProfile quadraticSaturatedDecrease
  rw [hremainReal, hdecompReal, hpredReal]
  push_cast
  ring

/-- Extension of the first-zero decrease vector by exact zeros to a longer
horizon. -/
noncomputable def quadraticExtendedDecrease (h m : ℝ) (K R : ℕ)
    (i : Fin (K + R)) : ℝ :=
  if hi : i.1 < K then
    quadraticSaturatedDecrease h m K ⟨i.1, hi⟩
  else 0

/-- Multiplier shift induced by appending `R` zero coordinates. -/
noncomputable def quadraticExtendedMultiplier (h m : ℝ) (K R : ℕ) : ℝ :=
  quadraticSaturatedMultiplier h m K - m * (R : ℝ)

theorem quadraticExtendedDecrease_sum
    {h m : ℝ} {K R : ℕ} (hK : 0 < K) :
    ∑ i, quadraticExtendedDecrease h m K R i = 1 := by
  classical
  rw [Fin.sum_univ_add]
  have hfirst :
      (∑ i : Fin K,
        quadraticExtendedDecrease h m K R (Fin.castAdd R i)) =
        ∑ i : Fin K, quadraticSaturatedDecrease h m K i := by
    apply Finset.sum_congr rfl
    intro i _
    simp [quadraticExtendedDecrease, i.2]
  have htail :
      (∑ i : Fin R,
        quadraticExtendedDecrease h m K R (Fin.natAdd K i)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    simp [quadraticExtendedDecrease]
  rw [hfirst, htail, add_zero, quadraticSaturatedDecrease_sum hK]

theorem quadraticExtendedDecrease_nonnegative
    {h m : ℝ} {K R : ℕ} (hphase : QuadraticPhaseCell h m K)
    (i : Fin (K + R)) : 0 ≤ quadraticExtendedDecrease h m K R i := by
  classical
  by_cases hi : i.1 < K
  · simp only [quadraticExtendedDecrease, dif_pos hi]
    exact (quadraticSaturatedDecrease_positive hphase ⟨i.1, hi⟩).le
  · simp [quadraticExtendedDecrease, hi]

theorem quadraticExtendedDecrease_active_gradient
    {h m : ℝ} {K R : ℕ} (hh : h ≠ 0)
    (i : Fin (K + R)) (hi : i.1 < K) :
    quadraticGradient h m (quadraticPathWeight (K + R))
        (quadraticExtendedDecrease h m K R) i =
      quadraticExtendedMultiplier h m K R := by
  let j : Fin K := ⟨i.1, hi⟩
  have hbase := quadraticSaturatedDecrease_gradient (h := h) (m := m) hh j
  have hWeightNat : K + R - i.1 = (K - i.1) + R := by omega
  have hWeightReal : ((K + R - i.1 : ℕ) : ℝ) =
      ((K - i.1 : ℕ) : ℝ) + (R : ℝ) := by
    exact_mod_cast hWeightNat
  simp only [quadraticGradient, quadraticPathWeight,
    quadraticExtendedDecrease, dif_pos hi,
    quadraticExtendedMultiplier]
  rw [hWeightReal]
  change 2 * h * quadraticSaturatedDecrease h m K j -
      m * (((K - i.1 : ℕ) : ℝ) + (R : ℝ)) =
    quadraticSaturatedMultiplier h m K - m * (R : ℝ)
  unfold quadraticGradient quadraticPathWeight at hbase
  nlinarith

theorem quadraticExtendedDecrease_gradient_lower_bound
    {h m : ℝ} {K R : ℕ} (hphase : QuadraticPhaseCell h m K)
    (i : Fin (K + R)) :
    quadraticExtendedMultiplier h m K R ≤
      quadraticGradient h m (quadraticPathWeight (K + R))
        (quadraticExtendedDecrease h m K R) i := by
  rcases hphase with ⟨hK, hh, hm, hlower, hupper⟩
  have hphase' : QuadraticPhaseCell h m K :=
    ⟨hK, hh, hm, hlower, hupper⟩
  by_cases hi : i.1 < K
  · rw [quadraticExtendedDecrease_active_gradient hh.ne' i hi]
  · have hKi : K ≤ i.1 := Nat.le_of_not_gt hi
    have htailNat : K + R - i.1 ≤ R := by omega
    have htailReal : ((K + R - i.1 : ℕ) : ℝ) ≤ (R : ℝ) := by
      exact_mod_cast htailNat
    have hscaled :
        m * ((K + R - i.1 : ℕ) : ℝ) ≤ m * (R : ℝ) :=
      mul_le_mul_of_nonneg_left htailReal hm.le
    have hlambda := quadraticSaturatedMultiplier_nonpositive hphase'
    simp only [quadraticExtendedMultiplier, quadraticGradient,
      quadraticPathWeight, quadraticExtendedDecrease, dif_neg hi, mul_zero,
      zero_sub]
    linarith

/-- The first-zero prefix remains the unique optimizer after any finite number
of zero coordinates is appended. -/
theorem quadraticExtension_stable_unique_minimizer
    {h m : ℝ} {K R : ℕ} (hphase : QuadraticPhaseCell h m K) :
    IsUniqueMinimizerOn (SolidSimplex : (Fin (K + R) → ℝ) → Prop)
      (quadraticReducedObjective h m (quadraticPathWeight (K + R)))
      (quadraticExtendedDecrease h m K R) := by
  rcases hphase with ⟨hK, hh, hm, hlower, hupper⟩
  have hphase' : QuadraticPhaseCell h m K :=
    ⟨hK, hh, hm, hlower, hupper⟩
  have hsum : ∑ i, quadraticExtendedDecrease h m K R i = 1 :=
    quadraticExtendedDecrease_sum hK
  apply quadratic_unique_minimizer_of_simplex_kkt
    (weight := quadraticPathWeight (K + R))
    (u := quadraticExtendedDecrease h m K R)
    (lambda := quadraticExtendedMultiplier h m K R)
  · exact hh
  · exact ⟨quadraticExtendedDecrease_nonnegative hphase', by linarith⟩
  · exact hsum
  · unfold quadraticExtendedMultiplier
    have hlambda := quadraticSaturatedMultiplier_nonpositive hphase'
    have hmR : 0 ≤ m * (R : ℝ) := mul_nonneg hm.le (Nat.cast_nonneg R)
    linarith
  · exact quadraticExtendedDecrease_gradient_lower_bound hphase'
  · intro i hpositive
    by_cases hi : i.1 < K
    · exact quadraticExtendedDecrease_active_gradient hh.ne' i hi
    · simp [quadraticExtendedDecrease, hi] at hpositive

theorem quadraticSaturatedProfile_trigger {h m : ℝ} {K : ℕ}
    (hK : 0 < K) : quadraticSaturatedProfile h m K 0 = 1 := by
  simp [quadraticSaturatedProfile, Nat.ne_of_gt hK]

theorem quadraticSaturatedProfile_first_zero (h m : ℝ) (K : ℕ) :
    quadraticSaturatedProfile h m K K = 0 := by
  simp [quadraticSaturatedProfile]

theorem quadraticSaturatedProfile_zero_tail {h m : ℝ} {K i : ℕ}
    (hKi : K ≤ i) : quadraticSaturatedProfile h m K i = 0 := by
  simp [quadraticSaturatedProfile, Nat.sub_eq_zero_of_le hKi]

theorem quadraticSaturatedProfile_positive_before_boundary
    {h m : ℝ} {K i : ℕ} (hphase : QuadraticPhaseCell h m K)
    (hiK : i < K) : 0 < quadraticSaturatedProfile h m K i := by
  rcases hphase with ⟨hK, hh, hm, hlower, _⟩
  have hKreal : 0 < (K : ℝ) := by exact_mod_cast hK
  have hiSub : i ≤ K - 1 := Nat.le_sub_one_of_lt hiK
  have hiReal : (i : ℝ) ≤ ((K - 1 : ℕ) : ℝ) := by exact_mod_cast hiSub
  have hmi : m * (i : ℝ) ≤ m * ((K - 1 : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_left hiReal hm.le
  have hmiK : m * (i : ℝ) * (K : ℝ) ≤
      m * ((K - 1 : ℕ) : ℝ) * (K : ℝ) :=
    mul_le_mul_of_nonneg_right hmi hKreal.le
  have hcross : m * (i : ℝ) * (K : ℝ) < 4 * h :=
    lt_of_le_of_lt hmiK hlower
  have hdenom : 0 < 4 * h := by positivity
  have hfraction : m * (i : ℝ) / (4 * h) < 1 / (K : ℝ) := by
    exact (div_lt_div_iff₀ hdenom hKreal).2 (by simpa using hcross)
  have hprefix : 0 < ((K - i : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_pos_of_lt hiK
  exact mul_pos hprefix (sub_pos.mpr hfraction)

/-- The phase cell gives the complete strict-support classification: a
coordinate is positive exactly before `K`, and `K` begins a stable zero tail. -/
theorem quadraticSaturatedProfile_support_iff
    {h m : ℝ} {K i : ℕ} (hphase : QuadraticPhaseCell h m K) :
    0 < quadraticSaturatedProfile h m K i ↔ i < K := by
  constructor
  · intro hpositive
    by_contra hnot
    have hKi : K ≤ i := Nat.le_of_not_gt hnot
    rw [quadraticSaturatedProfile_zero_tail hKi] at hpositive
    exact lt_irrefl 0 hpositive
  · exact quadraticSaturatedProfile_positive_before_boundary hphase

/-- The strict/weak phase inequalities make `K` the least triangular
threshold. -/
theorem quadraticPhaseCell_least_threshold
    {h m : ℝ} {K : ℕ} (hphase : QuadraticPhaseCell h m K) :
    QuadraticThresholdReached h m K ∧
      ∀ j, j < K → ¬ QuadraticThresholdReached h m j := by
  rcases hphase with ⟨hK, hh, hm, hlower, hupper⟩
  constructor
  · exact hupper
  · intro j hjK hjReached
    have hjFirst : j ≤ K - 1 := Nat.le_sub_one_of_lt hjK
    have hjSecond : j + 1 ≤ K := Nat.succ_le_of_lt hjK
    have hjFirstReal : (j : ℝ) ≤ ((K - 1 : ℕ) : ℝ) := by
      exact_mod_cast hjFirst
    have hjSecondReal : ((j + 1 : ℕ) : ℝ) ≤ (K : ℝ) := by
      exact_mod_cast hjSecond
    have hjNonnegative : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
    have hKminusNonnegative : 0 ≤ ((K - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    have hproduct : (j : ℝ) * ((j + 1 : ℕ) : ℝ) ≤
        ((K - 1 : ℕ) : ℝ) * (K : ℝ) :=
      mul_le_mul hjFirstReal hjSecondReal (by positivity) hKminusNonnegative
    have hmproduct : m * ((j : ℝ) * ((j + 1 : ℕ) : ℝ)) ≤
        m * (((K - 1 : ℕ) : ℝ) * (K : ℝ)) :=
      mul_le_mul_of_nonneg_left hproduct hm.le
    unfold QuadraticThresholdReached at hjReached
    nlinarith

/-- A phase cell therefore supplies an exact first zero and an
extension-stable zero tail. -/
theorem quadraticProfile_exact_first_zero
    {h m : ℝ} {K : ℕ} (hphase : QuadraticPhaseCell h m K) :
    quadraticSaturatedProfile h m K K = 0 ∧
      (∀ i, i < K → 0 < quadraticSaturatedProfile h m K i) ∧
      (∀ i, K ≤ i → quadraticSaturatedProfile h m K i = 0) := by
  exact ⟨quadraticSaturatedProfile_first_zero h m K,
    fun i hi => quadraticSaturatedProfile_positive_before_boundary hphase hi,
    fun i hi => quadraticSaturatedProfile_zero_tail hi⟩

theorem quadraticUnsaturatedProfile_terminal (h m : ℝ) (N : ℕ) :
    quadraticUnsaturatedProfile h m N N =
      1 - m * (N : ℝ) * ((N + 1 : ℕ) : ℝ) / (4 * h) := by
  have hNat : 2 * N + 1 - N = N + 1 := by omega
  simp [quadraticUnsaturatedProfile, hNat]

/-- The unsaturated terminal coordinate is positive exactly below the strict
quadratic threshold. -/
theorem quadraticUnsaturated_terminal_positive_iff
    {h m : ℝ} {N : ℕ} (hh : 0 < h) :
    0 < quadraticUnsaturatedProfile h m N N ↔
      m * (N : ℝ) * ((N + 1 : ℕ) : ℝ) < 4 * h := by
  rw [quadraticUnsaturatedProfile_terminal]
  have hdenom : 0 < 4 * h := by positivity
  constructor
  · intro hpositive
    have hratio :
        m * (N : ℝ) * ((N + 1 : ℕ) : ℝ) / (4 * h) < 1 := by
      linarith
    exact (div_lt_one hdenom).1 hratio
  · intro hstrict
    have hratio :
        m * (N : ℝ) * ((N + 1 : ℕ) : ℝ) / (4 * h) < 1 :=
      (div_lt_one hdenom).2 hstrict
    linarith

/-- Exact saturated profile and decrease values at the equality-boundary
anchor `h = 5`, `m = 1`, `K = 4`. -/
theorem quadratic_anchor_saturated_five_one :
    [quadraticSaturatedProfile 5 1 4 0,
      quadraticSaturatedProfile 5 1 4 1,
      quadraticSaturatedProfile 5 1 4 2,
      quadraticSaturatedProfile 5 1 4 3,
      quadraticSaturatedProfile 5 1 4 4] =
        [1, 3 / 5, 3 / 10, 1 / 10, 0] ∧
    [quadraticSaturatedProfile 5 1 4 0 -
        quadraticSaturatedProfile 5 1 4 1,
      quadraticSaturatedProfile 5 1 4 1 -
        quadraticSaturatedProfile 5 1 4 2,
      quadraticSaturatedProfile 5 1 4 2 -
        quadraticSaturatedProfile 5 1 4 3,
      quadraticSaturatedProfile 5 1 4 3 -
        quadraticSaturatedProfile 5 1 4 4] =
        [2 / 5, 3 / 10, 1 / 5, 1 / 10] := by
  norm_num [quadraticSaturatedProfile]

/-- Exact unsaturated profile and decrease values at `h = 21`, `m = 1`,
`N = 3`. -/
theorem quadratic_anchor_unsaturated_twenty_one_one :
    [quadraticUnsaturatedProfile 21 1 3 0,
      quadraticUnsaturatedProfile 21 1 3 1,
      quadraticUnsaturatedProfile 21 1 3 2,
      quadraticUnsaturatedProfile 21 1 3 3] =
        [1, 13 / 14, 37 / 42, 6 / 7] ∧
    [quadraticUnsaturatedProfile 21 1 3 0 -
        quadraticUnsaturatedProfile 21 1 3 1,
      quadraticUnsaturatedProfile 21 1 3 1 -
        quadraticUnsaturatedProfile 21 1 3 2,
      quadraticUnsaturatedProfile 21 1 3 2 -
        quadraticUnsaturatedProfile 21 1 3 3] =
        [1 / 14, 1 / 21, 1 / 42] := by
  norm_num [quadraticUnsaturatedProfile]

/-- Exact replay of the three quadratic first-zero/profile anchors used in
the all-horizon theorem record. -/
theorem quadratic_all_horizon_registered_anchors :
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
      quadraticSaturatedProfile 5 1 4 4] =
        [1, 3 / 5, 3 / 10, 1 / 10, 0] ∧
    QuadraticPhaseCell 21 1 9 ∧
    [quadraticUnsaturatedProfile 21 1 1 0,
      quadraticUnsaturatedProfile 21 1 1 1] = [1, 41 / 42] := by
  norm_num [QuadraticPhaseCell, quadraticSaturatedProfile,
    quadraticUnsaturatedProfile]

/-- Exact replay of the six registered quadratic support cells.  Each natural
number is the first-zero index, one greater than the positive-follower count. -/
theorem quadratic_registered_support_cells :
    QuadraticPhaseCell 5 1 4 ∧
    QuadraticPhaseCell 5 3 3 ∧
    QuadraticPhaseCell 20 1 9 ∧
    QuadraticPhaseCell 20 3 5 ∧
    QuadraticPhaseCell 21 1 9 ∧
    QuadraticPhaseCell 21 3 5 := by
  norm_num [QuadraticPhaseCell]

end ClosedProfiles

end PhonologicalCalculus.ContinuousHG
