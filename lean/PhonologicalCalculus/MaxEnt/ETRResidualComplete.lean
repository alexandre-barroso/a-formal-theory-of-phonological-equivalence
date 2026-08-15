import PhonologicalCalculus.MaxEnt.ExactCore
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Tactic

/-!
# Bounded ETR-INV residual objective

This module formalizes the exact affine cube substitution and sum-of-squares
semantics used by `MAX-G3.RESIDUAL.01`.  Every allowed ETR-INV equation is
mapped to its integer-coefficient scaled residual.  The residual sum is
nonnegative and has a cube zero exactly when every source equation holds.
-/

namespace PhonologicalCalculus.MaxEnt

open Finset
open scoped BigOperators

noncomputable section

/-- The three equation forms of bounded ETR-INV. -/
inductive BoundedETRINVEquation (N : ℕ)
  | unit (x : Fin N)
  | add (x y z : Fin N)
  | inverse (x y : Fin N)
  deriving DecidableEq

/-- Affine transport from the closed unit cube to `[1/2,2]`. -/
def etrInvVariableValue {N : ℕ} (u : Fin N → ℝ) (i : Fin N) : ℝ :=
  1 / 2 + (3 / 2) * u i

/-- Exact semantics of one source equation after affine transport. -/
def BoundedETRINVEquation.Holds {N : ℕ}
    (equation : BoundedETRINVEquation N) (u : Fin N → ℝ) : Prop :=
  match equation with
  | .unit x => etrInvVariableValue u x = 1
  | .add x y z =>
      etrInvVariableValue u x + etrInvVariableValue u y =
        etrInvVariableValue u z
  | .inverse x y => etrInvVariableValue u x * etrInvVariableValue u y = 1

/-- Integer-coefficient scaled residual after the cube substitution.  Its
square is exactly one of the three summands displayed in the registered
derivation. -/
def BoundedETRINVEquation.scaledResidual {N : ℕ}
    (equation : BoundedETRINVEquation N) (u : Fin N → ℝ) : ℝ :=
  match equation with
  | .unit x => 2 * (-1 + 3 * u x)
  | .add x y z => 2 * (1 + 3 * u x + 3 * u y - 3 * u z)
  | .inverse x y => -3 + 3 * u x + 3 * u y + 9 * u x * u y

/-- The scaled residual vanishes exactly when its source equation holds. -/
theorem scaledResidual_eq_zero_iff_holds {N : ℕ}
    (equation : BoundedETRINVEquation N) (u : Fin N → ℝ) :
    equation.scaledResidual u = 0 ↔ equation.Holds u := by
  cases equation with
  | unit x =>
      simp only [BoundedETRINVEquation.scaledResidual,
        BoundedETRINVEquation.Holds, etrInvVariableValue]
      constructor <;> intro h <;> linarith
  | add x y z =>
      simp only [BoundedETRINVEquation.scaledResidual,
        BoundedETRINVEquation.Holds, etrInvVariableValue]
      constructor <;> intro h <;> linarith
  | inverse x y =>
      simp only [BoundedETRINVEquation.scaledResidual,
        BoundedETRINVEquation.Holds, etrInvVariableValue]
      constructor <;> intro h
      · nlinarith
      · nlinarith

/-- One bounded ETR-INV instance with explicit variables and equations. -/
structure BoundedETRINVInstance where
  variableCount : ℕ
  equationCount : ℕ
  equation : Fin equationCount → BoundedETRINVEquation variableCount

/-- Closed unit-cube domain of the transformed instance. -/
def BoundedETRINVInstance.IsCubePoint
    (problem : BoundedETRINVInstance)
    (u : Fin problem.variableCount → ℝ) : Prop :=
  ∀ i, 0 ≤ u i ∧ u i ≤ 1

/-- Source satisfiability under the declared bounded domain. -/
def BoundedETRINVInstance.Satisfiable
    (problem : BoundedETRINVInstance) : Prop :=
  ∃ u : Fin problem.variableCount → ℝ,
    problem.IsCubePoint u ∧ ∀ e, (problem.equation e).Holds u

/-- Integer sum-of-squared-residual objective. -/
def BoundedETRINVInstance.sourceResidualSum
    (problem : BoundedETRINVInstance)
    (u : Fin problem.variableCount → ℝ) : ℝ :=
  ∑ e, ((problem.equation e).scaledResidual u) ^ 2

/-- The source residual objective is nonnegative everywhere. -/
theorem sourceResidualSum_nonneg
    (problem : BoundedETRINVInstance)
    (u : Fin problem.variableCount → ℝ) :
    0 ≤ problem.sourceResidualSum u := by
  unfold BoundedETRINVInstance.sourceResidualSum
  exact Finset.sum_nonneg fun e _ => sq_nonneg _

/-- The sum of squares vanishes exactly when every transformed equation
holds. -/
theorem sourceResidualSum_eq_zero_iff
    (problem : BoundedETRINVInstance)
    (u : Fin problem.variableCount → ℝ) :
    problem.sourceResidualSum u = 0 ↔
      ∀ e, (problem.equation e).Holds u := by
  unfold BoundedETRINVInstance.sourceResidualSum
  rw [show (∑ e, ((problem.equation e).scaledResidual u) ^ 2) =
      ∑ e ∈ Finset.univ,
        ((problem.equation e).scaledResidual u) ^ 2 by rfl]
  rw [sum_sq_eq_zero_iff]
  constructor
  · intro h e
    exact (scaledResidual_eq_zero_iff_holds (problem.equation e) u).1
      (h e (Finset.mem_univ e))
  · intro h e _
    exact (scaledResidual_eq_zero_iff_holds (problem.equation e) u).2 (h e)

/-- **MAX-G3.RESIDUAL.01**, semantic closure.  Bounded ETR-INV is
satisfiable exactly when the integer residual sum has a zero on the closed
unit cube. -/
theorem boundedETRINV_satisfiable_iff_residual_zero
    (problem : BoundedETRINVInstance) :
    problem.Satisfiable ↔
      ∃ u : Fin problem.variableCount → ℝ,
        problem.IsCubePoint u ∧ problem.sourceResidualSum u = 0 := by
  constructor
  · rintro ⟨u, hu, hequations⟩
    exact ⟨u, hu, (sourceResidualSum_eq_zero_iff problem u).2 hequations⟩
  · rintro ⟨u, hu, hzero⟩
    exact ⟨u, hu, (sourceResidualSum_eq_zero_iff problem u).1 hzero⟩

/-- Exact displayed residual square for a unit equation. -/
theorem unit_residual_square_formula {N : ℕ} (x : Fin N) (u : Fin N → ℝ) :
    ((BoundedETRINVEquation.unit x).scaledResidual u) ^ 2 =
      4 * (-1 + 3 * u x) ^ 2 := by
  simp [BoundedETRINVEquation.scaledResidual]
  ring

/-- Exact displayed residual square for an addition equation. -/
theorem add_residual_square_formula {N : ℕ}
    (x y z : Fin N) (u : Fin N → ℝ) :
    ((BoundedETRINVEquation.add x y z).scaledResidual u) ^ 2 =
      4 * (1 + 3 * u x + 3 * u y - 3 * u z) ^ 2 := by
  simp [BoundedETRINVEquation.scaledResidual]
  ring

/-- Exact displayed residual square for an inverse equation. -/
theorem inverse_residual_square_formula {N : ℕ}
    (x y : Fin N) (u : Fin N → ℝ) :
    ((BoundedETRINVEquation.inverse x y).scaledResidual u) ^ 2 =
      (-3 + 3 * u x + 3 * u y + 9 * u x * u y) ^ 2 := by
  rfl

/-! ## Canonical integer polynomial witness and degree bound -/

open MvPolynomial

/-- Integer multivariate polynomial whose real evaluation is the scaled
residual. -/
def BoundedETRINVEquation.scaledResidualPolynomial {N : ℕ}
    (equation : BoundedETRINVEquation N) : MvPolynomial (Fin N) ℤ :=
  match equation with
  | .unit x => 2 * (-1 + 3 * X x)
  | .add x y z => 2 * (1 + 3 * X x + 3 * X y - 3 * X z)
  | .inverse x y => -3 + 3 * X x + 3 * X y + 9 * X x * X y

/-- Canonical collected integer polynomial for the source sum of squares. -/
def BoundedETRINVInstance.sourceResidualPolynomial
    (problem : BoundedETRINVInstance) :
    MvPolynomial (Fin problem.variableCount) ℤ :=
  ∑ e, (problem.equation e).scaledResidualPolynomial ^ 2

/-- Real evaluation of the integer residual polynomial equals the analytic
sum-of-squares objective definitionally used above. -/
theorem eval_sourceResidualPolynomial
    (problem : BoundedETRINVInstance)
    (u : Fin problem.variableCount → ℝ) :
    MvPolynomial.eval₂ (Int.castRingHom ℝ) u problem.sourceResidualPolynomial =
      problem.sourceResidualSum u := by
  classical
  unfold BoundedETRINVInstance.sourceResidualPolynomial
    BoundedETRINVInstance.sourceResidualSum
  rw [MvPolynomial.eval₂_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [MvPolynomial.eval₂_pow]
  congr 1
  cases hequation : problem.equation e with
  | unit x =>
      simp [BoundedETRINVEquation.scaledResidualPolynomial,
        BoundedETRINVEquation.scaledResidual]
  | add x y z =>
      simp [BoundedETRINVEquation.scaledResidualPolynomial,
        BoundedETRINVEquation.scaledResidual]
  | inverse x y =>
      simp [BoundedETRINVEquation.scaledResidualPolynomial,
        BoundedETRINVEquation.scaledResidual]

theorem totalDegree_add_le {N : ℕ} {p q : MvPolynomial (Fin N) ℤ}
    {degree : ℕ} (hp : p.totalDegree ≤ degree)
    (hq : q.totalDegree ≤ degree) :
    (p + q).totalDegree ≤ degree :=
  (MvPolynomial.totalDegree_add p q).trans (max_le hp hq)

theorem totalDegree_sub_le {N : ℕ} {p q : MvPolynomial (Fin N) ℤ}
    {degree : ℕ} (hp : p.totalDegree ≤ degree)
    (hq : q.totalDegree ≤ degree) :
    (p - q).totalDegree ≤ degree := by
  rw [sub_eq_add_neg]
  apply totalDegree_add_le hp
  simpa using hq

theorem totalDegree_natCast_mul_le {N : ℕ}
    (coefficient degree : ℕ) (p : MvPolynomial (Fin N) ℤ)
    (hp : p.totalDegree ≤ degree) :
    ((coefficient : MvPolynomial (Fin N) ℤ) * p).totalDegree ≤ degree := by
  calc
    ((coefficient : MvPolynomial (Fin N) ℤ) * p).totalDegree ≤
        (coefficient : MvPolynomial (Fin N) ℤ).totalDegree +
          p.totalDegree := MvPolynomial.totalDegree_mul _ _
    _ = p.totalDegree := by
      rw [← MvPolynomial.C_eq_coe_nat coefficient,
        MvPolynomial.totalDegree_C, Nat.zero_add]
    _ ≤ degree := hp

theorem totalDegree_intCast_le {N : ℕ}
    (coefficient : ℤ) (degree : ℕ) :
    (coefficient : MvPolynomial (Fin N) ℤ).totalDegree ≤ degree := by
  have hCast :
      (coefficient : MvPolynomial (Fin N) ℤ) =
        MvPolynomial.C coefficient :=
    (map_intCast (MvPolynomial.C :
      ℤ →+* MvPolynomial (Fin N) ℤ) coefficient).symm
  rw [hCast, MvPolynomial.totalDegree_C]
  exact Nat.zero_le degree

/-- Every scaled residual polynomial has total degree at most two. -/
theorem scaledResidualPolynomial_totalDegree_le_two {N : ℕ}
    (equation : BoundedETRINVEquation N) :
    equation.scaledResidualPolynomial.totalDegree ≤ 2 := by
  cases equation with
  | unit x =>
      unfold BoundedETRINVEquation.scaledResidualPolynomial
      apply totalDegree_natCast_mul_le 2 2
      apply totalDegree_add_le
      · simp
      · exact totalDegree_natCast_mul_le 3 2 (X x) (by simp)
  | add x y z =>
      unfold BoundedETRINVEquation.scaledResidualPolynomial
      apply totalDegree_natCast_mul_le 2 2
      apply totalDegree_sub_le
      · apply totalDegree_add_le
        · apply totalDegree_add_le
          · exact totalDegree_intCast_le 1 2
          · exact totalDegree_natCast_mul_le 3 2 (X x) (by simp)
        · exact totalDegree_natCast_mul_le 3 2 (X y) (by simp)
      · exact totalDegree_natCast_mul_le 3 2 (X z) (by simp)
  | inverse x y =>
      unfold BoundedETRINVEquation.scaledResidualPolynomial
      apply totalDegree_add_le
      · apply totalDegree_add_le
        · apply totalDegree_add_le
          · change (-(3 : MvPolynomial (Fin N) ℤ)).totalDegree ≤ 2
            rw [MvPolynomial.totalDegree_neg]
            norm_num [MvPolynomial.totalDegree, MvPolynomial.support]
          · exact totalDegree_natCast_mul_le 3 2 (X x) (by simp)
        · exact totalDegree_natCast_mul_le 3 2 (X y) (by simp)
      · rw [mul_assoc]
        apply totalDegree_natCast_mul_le 9 2
        calc
          (X x * X y : MvPolynomial (Fin N) ℤ).totalDegree ≤
              (X x : MvPolynomial (Fin N) ℤ).totalDegree +
                (X y : MvPolynomial (Fin N) ℤ).totalDegree :=
            MvPolynomial.totalDegree_mul _ _
          _ = 2 := by simp

/-- **MAX-G3.RESIDUAL.01**, exact quartic-degree clause. -/
theorem sourceResidualPolynomial_totalDegree_le_four
    (problem : BoundedETRINVInstance) :
    problem.sourceResidualPolynomial.totalDegree ≤ 4 := by
  classical
  unfold BoundedETRINVInstance.sourceResidualPolynomial
  apply MvPolynomial.totalDegree_finsetSum_le
  intro e _
  calc
    ((problem.equation e).scaledResidualPolynomial ^ 2).totalDegree ≤
        2 * (problem.equation e).scaledResidualPolynomial.totalDegree :=
      MvPolynomial.totalDegree_pow _ 2
    _ ≤ 2 * 2 := Nat.mul_le_mul_left 2
      (scaledResidualPolynomial_totalDegree_le_two (problem.equation e))
    _ = 4 := by norm_num

/-! ## Canonical coefficient ℓ¹ bound -/

/-- The exact coefficient ℓ¹ norm of an integer multivariate polynomial.
Unlike a syntactic expression-size bound, this definition is applied after
like monomials have been collected, so cancellation can only decrease it. -/
def coefficientL1 {N : ℕ} (p : MvPolynomial (Fin N) ℤ) : ℕ :=
  ∑ monomial ∈ p.support, Int.natAbs (p.coeff monomial)

/-- Enlarging the summation set beyond the support does not change the
coefficient ℓ¹ norm. -/
theorem coefficientL1_eq_sum_of_support_subset {N : ℕ}
    (p : MvPolynomial (Fin N) ℤ)
    (supportSet : Finset (Fin N →₀ ℕ))
    (hSupport : p.support ⊆ supportSet) :
    coefficientL1 p =
      ∑ monomial ∈ supportSet, Int.natAbs (p.coeff monomial) := by
  classical
  unfold coefficientL1
  apply Finset.sum_subset hSupport
  intro monomial _ hOutside
  rw [MvPolynomial.notMem_support_iff.mp hOutside]
  simp

/-- The coefficient ℓ¹ norm is subadditive. -/
theorem coefficientL1_add_le {N : ℕ}
    (p q : MvPolynomial (Fin N) ℤ) :
    coefficientL1 (p + q) ≤ coefficientL1 p + coefficientL1 q := by
  classical
  let supportUnion := p.support ∪ q.support
  rw [coefficientL1_eq_sum_of_support_subset (p + q) supportUnion
    (MvPolynomial.support_add)]
  calc
    ∑ monomial ∈ supportUnion, Int.natAbs ((p + q).coeff monomial) ≤
        ∑ monomial ∈ supportUnion,
          (Int.natAbs (p.coeff monomial) + Int.natAbs (q.coeff monomial)) := by
      apply Finset.sum_le_sum
      intro monomial _
      simpa using Int.natAbs_add_le (p.coeff monomial) (q.coeff monomial)
    _ = (∑ monomial ∈ supportUnion, Int.natAbs (p.coeff monomial)) +
        (∑ monomial ∈ supportUnion, Int.natAbs (q.coeff monomial)) := by
      exact Finset.sum_add_distrib
    _ = coefficientL1 p + coefficientL1 q := by
      rw [← coefficientL1_eq_sum_of_support_subset p supportUnion
          Finset.subset_union_left,
        ← coefficientL1_eq_sum_of_support_subset q supportUnion
          Finset.subset_union_right]

/-- Negation leaves the exact coefficient ℓ¹ norm unchanged. -/
theorem coefficientL1_neg {N : ℕ}
    (p : MvPolynomial (Fin N) ℤ) :
    coefficientL1 (-p) = coefficientL1 p := by
  classical
  unfold coefficientL1
  simp

/-- A finite sum is bounded by the sum of the coefficient ℓ¹ norms of its
summands. -/
theorem coefficientL1_finset_sum_le {N : ℕ} {I : Type*}
    (indexSet : Finset I) (f : I → MvPolynomial (Fin N) ℤ) :
    coefficientL1 (∑ i ∈ indexSet, f i) ≤
      ∑ i ∈ indexSet, coefficientL1 (f i) := by
  classical
  induction indexSet using Finset.induction_on with
  | empty => simp [coefficientL1]
  | @insert i indexSet hi inductionHypothesis =>
      simp only [Finset.sum_insert hi]
      exact (coefficientL1_add_le (f i) (∑ j ∈ indexSet, f j)).trans
        (Nat.add_le_add_left inductionHypothesis _)

/-- A single monomial has coefficient ℓ¹ norm equal to the absolute value of
its coefficient. -/
theorem coefficientL1_monomial {N : ℕ}
    (monomial : Fin N →₀ ℕ) (coefficient : ℤ) :
    coefficientL1 (MvPolynomial.monomial monomial coefficient) =
      Int.natAbs coefficient := by
  classical
  by_cases hCoefficient : coefficient = 0
  · simp [hCoefficient, coefficientL1]
  · simp [coefficientL1, MvPolynomial.support_monomial, hCoefficient]

/-- Left multiplication by one monomial is bounded by multiplication of the
coefficient ℓ¹ norms. -/
theorem coefficientL1_monomial_mul_le {N : ℕ}
    (exponent : Fin N →₀ ℕ) (coefficient : ℤ)
    (p : MvPolynomial (Fin N) ℤ) :
    coefficientL1 (MvPolynomial.monomial exponent coefficient * p) ≤
      Int.natAbs coefficient * coefficientL1 p := by
  classical
  conv_lhs => rw [p.as_sum, Finset.mul_sum]
  calc
    coefficientL1
        (∑ monomial ∈ p.support,
          MvPolynomial.monomial exponent coefficient *
            MvPolynomial.monomial monomial (p.coeff monomial)) ≤
        ∑ monomial ∈ p.support,
          coefficientL1
            (MvPolynomial.monomial exponent coefficient *
              MvPolynomial.monomial monomial (p.coeff monomial)) :=
      coefficientL1_finset_sum_le p.support _
    _ = ∑ monomial ∈ p.support,
        Int.natAbs coefficient * Int.natAbs (p.coeff monomial) := by
      apply Finset.sum_congr rfl
      intro monomial _
      rw [MvPolynomial.monomial_mul, coefficientL1_monomial,
        Int.natAbs_mul]
    _ = Int.natAbs coefficient * coefficientL1 p := by
      unfold coefficientL1
      rw [Finset.mul_sum]

/-- The coefficient ℓ¹ norm is submultiplicative. -/
theorem coefficientL1_mul_le {N : ℕ}
    (p q : MvPolynomial (Fin N) ℤ) :
    coefficientL1 (p * q) ≤ coefficientL1 p * coefficientL1 q := by
  classical
  conv_lhs => rw [p.as_sum, Finset.sum_mul]
  calc
    coefficientL1
        (∑ monomial ∈ p.support,
          MvPolynomial.monomial monomial (p.coeff monomial) * q) ≤
        ∑ monomial ∈ p.support,
          coefficientL1
            (MvPolynomial.monomial monomial (p.coeff monomial) * q) :=
      coefficientL1_finset_sum_le p.support _
    _ ≤ ∑ monomial ∈ p.support,
        Int.natAbs (p.coeff monomial) * coefficientL1 q := by
      apply Finset.sum_le_sum
      intro monomial _
      exact coefficientL1_monomial_mul_le monomial (p.coeff monomial) q
    _ = coefficientL1 p * coefficientL1 q := by
      unfold coefficientL1
      rw [Finset.sum_mul]

/-- Squaring at most squares the coefficient ℓ¹ norm. -/
theorem coefficientL1_sq_le {N : ℕ}
    (p : MvPolynomial (Fin N) ℤ) :
    coefficientL1 (p ^ 2) ≤ coefficientL1 p ^ 2 := by
  simpa [pow_two] using coefficientL1_mul_le p p

/-- Exact coefficient ℓ¹ norm of an integer constant polynomial. -/
theorem coefficientL1_intCast {N : ℕ} (coefficient : ℤ) :
    coefficientL1
        (coefficient : MvPolynomial (Fin N) ℤ) =
      Int.natAbs coefficient := by
  have hCast :
      (coefficient : MvPolynomial (Fin N) ℤ) =
        MvPolynomial.C coefficient :=
    (map_intCast (MvPolynomial.C :
      ℤ →+* MvPolynomial (Fin N) ℤ) coefficient).symm
  rw [hCast, MvPolynomial.C_apply, coefficientL1_monomial]

/-- Exact coefficient ℓ¹ norm of a natural-number constant polynomial. -/
theorem coefficientL1_natCast {N : ℕ} (coefficient : ℕ) :
    coefficientL1
        (coefficient : MvPolynomial (Fin N) ℤ) = coefficient := by
  rw [← MvPolynomial.C_eq_coe_nat coefficient,
    MvPolynomial.C_apply, coefficientL1_monomial]
  simp

/-- Every variable monomial has coefficient ℓ¹ norm one. -/
theorem coefficientL1_X {N : ℕ} (coordinate : Fin N) :
    coefficientL1 (MvPolynomial.X coordinate :
      MvPolynomial (Fin N) ℤ) = 1 := by
  rw [MvPolynomial.X, coefficientL1_monomial]
  norm_num

/-- Multiplication by a natural-number constant scales the coefficient ℓ¹
upper bound by that number. -/
theorem coefficientL1_natCast_mul_le {N : ℕ}
    (coefficient : ℕ) (p : MvPolynomial (Fin N) ℤ) :
    coefficientL1
        ((coefficient : MvPolynomial (Fin N) ℤ) * p) ≤
      coefficient * coefficientL1 p := by
  exact (coefficientL1_mul_le
    (coefficient : MvPolynomial (Fin N) ℤ) p).trans_eq
      (by rw [coefficientL1_natCast])

/-- The coefficient ℓ¹ norm obeys the triangle inequality for subtraction. -/
theorem coefficientL1_sub_le {N : ℕ}
    (p q : MvPolynomial (Fin N) ℤ) :
    coefficientL1 (p - q) ≤ coefficientL1 p + coefficientL1 q := by
  rw [sub_eq_add_neg]
  simpa only [coefficientL1_neg] using coefficientL1_add_le p (-q)

/-- A natural scalar times one variable has coefficient ℓ¹ norm at most the
scalar.  Equality can fail only through degenerate coefficient arithmetic,
which is harmless for the registered upper bound. -/
theorem coefficientL1_natCast_mul_X_le {N : ℕ}
    (coefficient : ℕ) (coordinate : Fin N) :
    coefficientL1
        ((coefficient : MvPolynomial (Fin N) ℤ) * X coordinate) ≤
      coefficient := by
  simpa only [coefficientL1_X, Nat.mul_one] using
    coefficientL1_natCast_mul_le coefficient
      (X coordinate : MvPolynomial (Fin N) ℤ)

theorem coefficientL1_one {N : ℕ} :
    coefficientL1 (1 : MvPolynomial (Fin N) ℤ) = 1 := by
  have hCast : (1 : MvPolynomial (Fin N) ℤ) =
      ((1 : ℤ) : MvPolynomial (Fin N) ℤ) := by norm_num
  rw [hCast, coefficientL1_intCast]
  norm_num

theorem coefficientL1_two {N : ℕ} :
    coefficientL1 (2 : MvPolynomial (Fin N) ℤ) = 2 := by
  have hCast : (2 : MvPolynomial (Fin N) ℤ) =
      ((2 : ℤ) : MvPolynomial (Fin N) ℤ) := by norm_num
  rw [hCast, coefficientL1_intCast]
  norm_num

theorem coefficientL1_three {N : ℕ} :
    coefficientL1 (3 : MvPolynomial (Fin N) ℤ) = 3 := by
  have hCast : (3 : MvPolynomial (Fin N) ℤ) =
      ((3 : ℤ) : MvPolynomial (Fin N) ℤ) := by norm_num
  rw [hCast, coefficientL1_intCast]
  norm_num

theorem coefficientL1_nine {N : ℕ} :
    coefficientL1 (9 : MvPolynomial (Fin N) ℤ) = 9 := by
  have hCast : (9 : MvPolynomial (Fin N) ℤ) =
      ((9 : ℤ) : MvPolynomial (Fin N) ℤ) := by norm_num
  rw [hCast, coefficientL1_intCast]
  norm_num

/-- Every one-equation scaled residual has coefficient ℓ¹ norm at most 20.
The three sharper branch bounds are 8, 20, and 18. -/
theorem scaledResidualPolynomial_coefficientL1_le_twenty {N : ℕ}
    (equation : BoundedETRINVEquation N) :
    coefficientL1 equation.scaledResidualPolynomial ≤ 20 := by
  cases equation with
  | unit x =>
      change coefficientL1
        (2 * (-1 + 3 * X x) : MvPolynomial (Fin N) ℤ) ≤ 20
      have hOuter := coefficientL1_mul_le
        (2 : MvPolynomial (Fin N) ℤ) (-1 + 3 * X x)
      have hInner := coefficientL1_add_le
        (-1 : MvPolynomial (Fin N) ℤ) (3 * X x)
      have hMinusOne : coefficientL1
          (-1 : MvPolynomial (Fin N) ℤ) = 1 := by
        rw [coefficientL1_neg, coefficientL1_one]
      have hThreeX := coefficientL1_mul_le
        (3 : MvPolynomial (Fin N) ℤ) (X x)
      have hTwo : coefficientL1
          (2 : MvPolynomial (Fin N) ℤ) = 2 := coefficientL1_two
      have hThree : coefficientL1
          (3 : MvPolynomial (Fin N) ℤ) = 3 := coefficientL1_three
      have hX : coefficientL1
          (X x : MvPolynomial (Fin N) ℤ) = 1 := coefficientL1_X x
      rw [hTwo] at hOuter
      rw [hThree, hX] at hThreeX
      omega
  | add x y z =>
      change coefficientL1
        (2 * (1 + 3 * X x + 3 * X y - 3 * X z) :
          MvPolynomial (Fin N) ℤ) ≤ 20
      have hOuter := coefficientL1_mul_le
        (2 : MvPolynomial (Fin N) ℤ)
        (1 + 3 * X x + 3 * X y - 3 * X z)
      have hFirst := coefficientL1_add_le
        (1 : MvPolynomial (Fin N) ℤ) (3 * X x)
      have hSecond := coefficientL1_add_le
        (1 + 3 * X x : MvPolynomial (Fin N) ℤ) (3 * X y)
      have hThird := coefficientL1_sub_le
        (1 + 3 * X x + 3 * X y : MvPolynomial (Fin N) ℤ) (3 * X z)
      have hThreeX := coefficientL1_mul_le
        (3 : MvPolynomial (Fin N) ℤ) (X x)
      have hThreeY := coefficientL1_mul_le
        (3 : MvPolynomial (Fin N) ℤ) (X y)
      have hThreeZ := coefficientL1_mul_le
        (3 : MvPolynomial (Fin N) ℤ) (X z)
      have hOne : coefficientL1
          (1 : MvPolynomial (Fin N) ℤ) = 1 := coefficientL1_one
      have hTwo : coefficientL1
          (2 : MvPolynomial (Fin N) ℤ) = 2 := coefficientL1_two
      have hThree : coefficientL1
          (3 : MvPolynomial (Fin N) ℤ) = 3 := coefficientL1_three
      have hX : coefficientL1
          (X x : MvPolynomial (Fin N) ℤ) = 1 := coefficientL1_X x
      have hY : coefficientL1
          (X y : MvPolynomial (Fin N) ℤ) = 1 := coefficientL1_X y
      have hZ : coefficientL1
          (X z : MvPolynomial (Fin N) ℤ) = 1 := coefficientL1_X z
      rw [hTwo] at hOuter
      rw [hThree, hX] at hThreeX
      rw [hThree, hY] at hThreeY
      rw [hThree, hZ] at hThreeZ
      omega
  | inverse x y =>
      change coefficientL1
        (-3 + 3 * X x + 3 * X y + 9 * X x * X y :
          MvPolynomial (Fin N) ℤ) ≤ 20
      have hFirst := coefficientL1_add_le
        (-3 : MvPolynomial (Fin N) ℤ) (3 * X x)
      have hSecond := coefficientL1_add_le
        (-3 + 3 * X x : MvPolynomial (Fin N) ℤ) (3 * X y)
      have hThird := coefficientL1_add_le
        (-3 + 3 * X x + 3 * X y : MvPolynomial (Fin N) ℤ)
        (9 * X x * X y)
      have hMinusThree : coefficientL1
          (-3 : MvPolynomial (Fin N) ℤ) = 3 := by
        rw [coefficientL1_neg, coefficientL1_three]
      have hThreeX := coefficientL1_mul_le
        (3 : MvPolynomial (Fin N) ℤ) (X x)
      have hThreeY := coefficientL1_mul_le
        (3 : MvPolynomial (Fin N) ℤ) (X y)
      have hNineX := coefficientL1_mul_le
        (9 : MvPolynomial (Fin N) ℤ) (X x)
      have hNineXY := coefficientL1_mul_le
        (9 * X x : MvPolynomial (Fin N) ℤ) (X y)
      have hXy : coefficientL1
          (X y : MvPolynomial (Fin N) ℤ) = 1 := coefficientL1_X y
      have hThree : coefficientL1
          (3 : MvPolynomial (Fin N) ℤ) = 3 := coefficientL1_three
      have hNine : coefficientL1
          (9 : MvPolynomial (Fin N) ℤ) = 9 := coefficientL1_nine
      have hX : coefficientL1
          (X x : MvPolynomial (Fin N) ℤ) = 1 := coefficientL1_X x
      rw [hThree, hX] at hThreeX
      rw [hThree, hXy] at hThreeY
      rw [hNine, hX] at hNineX
      rw [hXy] at hNineXY
      omega

/-- Every squared equation residual contributes coefficient ℓ¹ norm at most
400 to the canonical collected source polynomial. -/
theorem scaledResidualPolynomial_sq_coefficientL1_le_four_hundred {N : ℕ}
    (equation : BoundedETRINVEquation N) :
    coefficientL1 (equation.scaledResidualPolynomial ^ 2) ≤ 400 := by
  exact (coefficientL1_sq_le equation.scaledResidualPolynomial).trans
    ((Nat.pow_le_pow_left
      (scaledResidualPolynomial_coefficientL1_le_twenty equation) 2).trans_eq
        (by norm_num))

/-- **MAX-G3.RESIDUAL.01**, canonical coefficient-mass clause.  The collected
integer quartic has coefficient ℓ¹ norm at most `400 q`, where `q` is the
number of source equations. -/
theorem sourceResidualPolynomial_coefficientL1_le
    (problem : BoundedETRINVInstance) :
    coefficientL1 problem.sourceResidualPolynomial ≤
      400 * problem.equationCount := by
  classical
  unfold BoundedETRINVInstance.sourceResidualPolynomial
  calc
    coefficientL1
        (∑ e, (problem.equation e).scaledResidualPolynomial ^ 2) ≤
        ∑ e, coefficientL1
          ((problem.equation e).scaledResidualPolynomial ^ 2) :=
      coefficientL1_finset_sum_le Finset.univ _
    _ ≤ ∑ _e : Fin problem.equationCount, 400 := by
      apply Finset.sum_le_sum
      intro e _
      exact scaledResidualPolynomial_sq_coefficientL1_le_four_hundred
        (problem.equation e)
    _ = 400 * problem.equationCount := by
      simp [Nat.mul_comm]

end

end PhonologicalCalculus.MaxEnt
