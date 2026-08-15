import PhonologicalCalculus.MaxEnt.ETRResidualComplete
import PhonologicalCalculus.MaxEnt.ContractionStrictifierComplete
import PhonologicalCalculus.MaxEnt.FiniteLaw
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Tactic

/-!
# Polynomial realization of the bounded-ETR strictifier

This module constructs the integer quartic whose real evaluation is the
analytic contraction strictifier used by `MAX-G3.CHAIN.02`.  Source variables
and the positive contraction tail occupy disjoint coordinates; the fixed
initial chain value is the constant one, not a free target coordinate.

The construction proves the exact evaluation identity, the quartic degree
bound, the coefficient-mass bound used by the finite-size analysis, and the
strict-negative-witness equivalence relative only to the declared compact-cube
gap.  No compiled code or target witness is postulated.
-/

namespace PhonologicalCalculus.MaxEnt

open Finset MvPolynomial
open scoped BigOperators

noncomputable section

/-- Disjoint source and contraction-tail coordinates. -/
abbrev ETRStrictifierIndex (problem : BoundedETRINVInstance) (m : ℕ) :=
  Sum (Fin problem.variableCount) (Fin m)

/-- Source coordinates projected from a combined strictifier point. -/
def strictifierSourceActivity (problem : BoundedETRINVInstance) (m : ℕ)
    (point : ETRStrictifierIndex problem m → ℝ) :
    Fin problem.variableCount → ℝ :=
  fun coordinate => point (.inl coordinate)

/-- Contraction-tail coordinates projected from a combined point. -/
def strictifierTailActivity (problem : BoundedETRINVInstance) (m : ℕ)
    (point : ETRStrictifierIndex problem m → ℝ) : Fin m → ℝ :=
  fun coordinate => point (.inr coordinate)

/-- Total analytic chain with fixed initial value one and a finite free tail.
Values beyond the represented tail are irrelevant and are set to zero. -/
def strictifierChainFromTail {m : ℕ} (tail : Fin m → ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => if hn : n < m then tail ⟨n, hn⟩ else 0

@[simp]
theorem strictifierChainFromTail_zero {m : ℕ} (tail : Fin m → ℝ) :
    strictifierChainFromTail tail 0 = 1 := rfl

@[simp]
theorem strictifierChainFromTail_succ {m : ℕ} (tail : Fin m → ℝ)
    (coordinate : Fin m) :
    strictifierChainFromTail tail (coordinate.val + 1) = tail coordinate := by
  simp [strictifierChainFromTail, coordinate.isLt]

/-- Polynomial value of chain coordinate `0,...,m`: coordinate zero is the
constant one and coordinate `i+1` is the `i`th free tail variable. -/
def strictifierChainValuePolynomial
    (problem : BoundedETRINVInstance) (m : ℕ) (coordinate : Fin (m + 1)) :
    MvPolynomial (ETRStrictifierIndex problem m) ℤ :=
  Fin.cases 1 (fun tailCoordinate => X (.inr tailCoordinate)) coordinate

@[simp]
theorem eval_strictifierChainValuePolynomial
    (problem : BoundedETRINVInstance) (m : ℕ)
    (point : ETRStrictifierIndex problem m → ℝ)
    (coordinate : Fin (m + 1)) :
    (strictifierChainValuePolynomial problem m coordinate).eval₂
        (Int.castRingHom ℝ) point =
      strictifierChainFromTail
        (strictifierTailActivity problem m point) coordinate.val := by
  refine Fin.cases ?_ (fun tailCoordinate => ?_) coordinate
  · simp [strictifierChainValuePolynomial]
  · simp [strictifierChainValuePolynomial, strictifierChainFromTail,
      strictifierTailActivity, tailCoordinate.isLt]

/-- Polynomial residual of contraction step `i`: `2 r_(i+1)-r_i^2`. -/
def contractionResidualPolynomial
    (problem : BoundedETRINVInstance) (m : ℕ) (step : Fin m) :
    MvPolynomial (ETRStrictifierIndex problem m) ℤ :=
  2 * strictifierChainValuePolynomial problem m step.succ -
    strictifierChainValuePolynomial problem m step.castSucc ^ 2

@[simp]
theorem eval_contractionResidualPolynomial
    (problem : BoundedETRINVInstance) (m : ℕ)
    (point : ETRStrictifierIndex problem m → ℝ) (step : Fin m) :
    (contractionResidualPolynomial problem m step).eval₂
        (Int.castRingHom ℝ) point =
      contractionResidual
        (strictifierChainFromTail
          (strictifierTailActivity problem m point)) step.val := by
  simp [contractionResidualPolynomial, contractionResidual]

/-- Source residual polynomial embedded into the combined coordinate space. -/
def liftedSourceResidualPolynomial
    (problem : BoundedETRINVInstance) (m : ℕ) :
    MvPolynomial (ETRStrictifierIndex problem m) ℤ :=
  MvPolynomial.rename Sum.inl problem.sourceResidualPolynomial

@[simp]
theorem eval_liftedSourceResidualPolynomial
    (problem : BoundedETRINVInstance) (m : ℕ)
    (point : ETRStrictifierIndex problem m → ℝ) :
    (liftedSourceResidualPolynomial problem m).eval₂
        (Int.castRingHom ℝ) point =
      problem.sourceResidualSum
        (strictifierSourceActivity problem m point) := by
  rw [liftedSourceResidualPolynomial, MvPolynomial.eval₂_rename,
    eval_sourceResidualPolynomial]
  rfl

/-- Canonical integer strictifier polynomial. -/
def etrStrictifierPolynomial
    (problem : BoundedETRINVInstance) (m : ℕ) :
    MvPolynomial (ETRStrictifierIndex problem m) ℤ :=
  2 * liftedSourceResidualPolynomial problem m +
    (m : ℤ) * (∑ step : Fin m,
      contractionResidualPolynomial problem m step ^ 2) -
    2 * strictifierChainValuePolynomial problem m (Fin.last m) ^ 2

/-- The constructed polynomial evaluates exactly to the analytic strictifier.
This identity includes every source, recurrence, and terminal coefficient. -/
theorem eval_etrStrictifierPolynomial
    (problem : BoundedETRINVInstance) (m : ℕ)
    (point : ETRStrictifierIndex problem m → ℝ) :
    (etrStrictifierPolynomial problem m).eval₂
        (Int.castRingHom ℝ) point =
      contractionStrictifier problem.sourceResidualSum m
        (strictifierSourceActivity problem m point)
        (strictifierChainFromTail
          (strictifierTailActivity problem m point)) := by
  classical
  let chain := strictifierChainFromTail
    (strictifierTailActivity problem m point)
  calc
    (etrStrictifierPolynomial problem m).eval₂
        (Int.castRingHom ℝ) point =
      2 * problem.sourceResidualSum
          (strictifierSourceActivity problem m point) +
        (m : ℝ) * (∑ step : Fin m,
          contractionResidual chain step.val ^ 2) -
        2 * chain m ^ 2 := by
          simp [etrStrictifierPolynomial, chain,
            eval_liftedSourceResidualPolynomial,
            eval_contractionResidualPolynomial,
            eval_strictifierChainValuePolynomial]
    _ = contractionStrictifier problem.sourceResidualSum m
        (strictifierSourceActivity problem m point) chain := by
          unfold contractionStrictifier
          have hsum :
              (∑ step : Fin m, contractionResidual chain step.val ^ 2) =
                ∑ i ∈ Finset.range m, contractionResidual chain i ^ 2 :=
            Fin.sum_univ_eq_sum_range
              (fun i => contractionResidual chain i ^ 2) m
          rw [hsum]

/-! ## Quartic degree bound -/

theorem strictifier_totalDegree_add_le {J : Type*}
    {p q : MvPolynomial J ℤ} {degree : ℕ}
    (hp : p.totalDegree ≤ degree) (hq : q.totalDegree ≤ degree) :
    (p + q).totalDegree ≤ degree :=
  (MvPolynomial.totalDegree_add p q).trans (max_le hp hq)

theorem strictifier_totalDegree_sub_le {J : Type*}
    {p q : MvPolynomial J ℤ} {degree : ℕ}
    (hp : p.totalDegree ≤ degree) (hq : q.totalDegree ≤ degree) :
    (p - q).totalDegree ≤ degree := by
  rw [sub_eq_add_neg]
  apply strictifier_totalDegree_add_le hp
  simpa using hq

theorem strictifier_totalDegree_intCast_mul_le {J : Type*}
    (coefficient : ℤ) {p : MvPolynomial J ℤ} {degree : ℕ}
    (hp : p.totalDegree ≤ degree) :
    ((coefficient : MvPolynomial J ℤ) * p).totalDegree ≤ degree := by
  have hCast :
      (coefficient : MvPolynomial J ℤ) = MvPolynomial.C coefficient :=
    (map_intCast (MvPolynomial.C : ℤ →+* MvPolynomial J ℤ)
      coefficient).symm
  calc
    ((coefficient : MvPolynomial J ℤ) * p).totalDegree ≤
        (coefficient : MvPolynomial J ℤ).totalDegree + p.totalDegree :=
      MvPolynomial.totalDegree_mul _ _
    _ = p.totalDegree := by
      rw [hCast, MvPolynomial.totalDegree_C, Nat.zero_add]
    _ ≤ degree := hp

theorem strictifierChainValuePolynomial_totalDegree_le_one
    (problem : BoundedETRINVInstance) (m : ℕ)
    (coordinate : Fin (m + 1)) :
    (strictifierChainValuePolynomial problem m coordinate).totalDegree ≤ 1 := by
  refine Fin.cases ?_ (fun tailCoordinate => ?_) coordinate
  · simp [strictifierChainValuePolynomial]
  · simp [strictifierChainValuePolynomial]

theorem contractionResidualPolynomial_totalDegree_le_two
    (problem : BoundedETRINVInstance) (m : ℕ) (step : Fin m) :
    (contractionResidualPolynomial problem m step).totalDegree ≤ 2 := by
  unfold contractionResidualPolynomial
  apply strictifier_totalDegree_sub_le
  · exact strictifier_totalDegree_intCast_mul_le 2
      ((strictifierChainValuePolynomial_totalDegree_le_one
        problem m step.succ).trans (by omega))
  · calc
      (strictifierChainValuePolynomial problem m step.castSucc ^ 2).totalDegree ≤
          2 * (strictifierChainValuePolynomial
            problem m step.castSucc).totalDegree :=
        MvPolynomial.totalDegree_pow _ 2
      _ ≤ 2 := by
        have h := strictifierChainValuePolynomial_totalDegree_le_one
          problem m step.castSucc
        omega

theorem contractionPenaltyPolynomial_totalDegree_le_four
    (problem : BoundedETRINVInstance) (m : ℕ) :
    (∑ step : Fin m,
      contractionResidualPolynomial problem m step ^ 2).totalDegree ≤ 4 := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro step _
  calc
    (contractionResidualPolynomial problem m step ^ 2).totalDegree ≤
        2 * (contractionResidualPolynomial problem m step).totalDegree :=
      MvPolynomial.totalDegree_pow _ 2
    _ ≤ 4 := by
      have h := contractionResidualPolynomial_totalDegree_le_two
        problem m step
      omega

theorem liftedSourceResidualPolynomial_totalDegree_le_four
    (problem : BoundedETRINVInstance) (m : ℕ) :
    (liftedSourceResidualPolynomial problem m).totalDegree ≤ 4 := by
  exact (MvPolynomial.totalDegree_rename_le Sum.inl
      problem.sourceResidualPolynomial).trans
    (sourceResidualPolynomial_totalDegree_le_four problem)

/-- The constructed strictifier is a genuine integer polynomial of total
degree at most four. -/
theorem etrStrictifierPolynomial_totalDegree_le_four
    (problem : BoundedETRINVInstance) (m : ℕ) :
    (etrStrictifierPolynomial problem m).totalDegree ≤ 4 := by
  unfold etrStrictifierPolynomial
  apply strictifier_totalDegree_sub_le
  · apply strictifier_totalDegree_add_le
    · exact strictifier_totalDegree_intCast_mul_le 2
        (liftedSourceResidualPolynomial_totalDegree_le_four problem m)
    · exact strictifier_totalDegree_intCast_mul_le (m : ℤ)
        (contractionPenaltyPolynomial_totalDegree_le_four problem m)
  · exact strictifier_totalDegree_intCast_mul_le 2
      ((MvPolynomial.totalDegree_pow
        (strictifierChainValuePolynomial problem m (Fin.last m)) 2).trans
        (by
          have h := strictifierChainValuePolynomial_totalDegree_le_one
            problem m (Fin.last m)
          omega))

/-! ## Canonical finite-index presentation and coefficient mass -/

/-- Finite-index presentation of one chain value. -/
def strictifierChainValuePolynomialFin
    (problem : BoundedETRINVInstance) (m : ℕ) (coordinate : Fin (m + 1)) :
    MvPolynomial (Fin (problem.variableCount + m)) ℤ :=
  Fin.cases 1
    (fun tailCoordinate => X (finSumFinEquiv (.inr tailCoordinate)))
    coordinate

/-- Finite-index presentation of one contraction residual. -/
def contractionResidualPolynomialFin
    (problem : BoundedETRINVInstance) (m : ℕ) (step : Fin m) :
    MvPolynomial (Fin (problem.variableCount + m)) ℤ :=
  2 * strictifierChainValuePolynomialFin problem m step.succ -
    strictifierChainValuePolynomialFin problem m step.castSucc ^ 2

/-- Finite-index embedding of the source residual polynomial. -/
def liftedSourceResidualPolynomialFin
    (problem : BoundedETRINVInstance) (m : ℕ) :
    MvPolynomial (Fin (problem.variableCount + m)) ℤ :=
  MvPolynomial.rename
    (fun coordinate => finSumFinEquiv (.inl coordinate))
    problem.sourceResidualPolynomial

/-- Canonical `Fin`-indexed strictifier used by the finite target compiler. -/
def etrStrictifierPolynomialFin
    (problem : BoundedETRINVInstance) (m : ℕ) :
    MvPolynomial (Fin (problem.variableCount + m)) ℤ :=
  2 * liftedSourceResidualPolynomialFin problem m +
    (m : ℤ) * (∑ step : Fin m,
      contractionResidualPolynomialFin problem m step ^ 2) -
    2 * strictifierChainValuePolynomialFin problem m (Fin.last m) ^ 2

theorem strictifierChainValuePolynomialFin_eq_rename
    (problem : BoundedETRINVInstance) (m : ℕ)
    (coordinate : Fin (m + 1)) :
    strictifierChainValuePolynomialFin problem m coordinate =
      MvPolynomial.rename finSumFinEquiv
        (strictifierChainValuePolynomial problem m coordinate) := by
  refine Fin.cases ?_ (fun tailCoordinate => ?_) coordinate <;>
    simp [strictifierChainValuePolynomialFin,
      strictifierChainValuePolynomial]

theorem contractionResidualPolynomialFin_eq_rename
    (problem : BoundedETRINVInstance) (m : ℕ) (step : Fin m) :
    contractionResidualPolynomialFin problem m step =
      MvPolynomial.rename finSumFinEquiv
        (contractionResidualPolynomial problem m step) := by
  unfold contractionResidualPolynomialFin contractionResidualPolynomial
  rw [strictifierChainValuePolynomialFin_eq_rename,
    strictifierChainValuePolynomialFin_eq_rename]
  simp only [map_sub, map_mul, map_pow, map_ofNat]

theorem liftedSourceResidualPolynomialFin_eq_rename
    (problem : BoundedETRINVInstance) (m : ℕ) :
    liftedSourceResidualPolynomialFin problem m =
      MvPolynomial.rename finSumFinEquiv
        (liftedSourceResidualPolynomial problem m) := by
  unfold liftedSourceResidualPolynomialFin liftedSourceResidualPolynomial
  rw [MvPolynomial.rename_rename]
  rfl

theorem etrStrictifierPolynomialFin_eq_rename
    (problem : BoundedETRINVInstance) (m : ℕ) :
    etrStrictifierPolynomialFin problem m =
      MvPolynomial.rename finSumFinEquiv
        (etrStrictifierPolynomial problem m) := by
  classical
  unfold etrStrictifierPolynomialFin etrStrictifierPolynomial
  rw [liftedSourceResidualPolynomialFin_eq_rename]
  simp_rw [contractionResidualPolynomialFin_eq_rename]
  rw [strictifierChainValuePolynomialFin_eq_rename]
  simp only [map_sub, map_add, map_mul, map_pow, map_ofNat, map_intCast,
    map_sum]

/-- Reindex a canonical finite point into its disjoint source/tail views. -/
def strictifierSumPointOfFin
    (problem : BoundedETRINVInstance) (m : ℕ)
    (point : Fin (problem.variableCount + m) → ℝ) :
    ETRStrictifierIndex problem m → ℝ :=
  fun coordinate => point (finSumFinEquiv coordinate)

@[simp]
theorem eval_etrStrictifierPolynomialFin
    (problem : BoundedETRINVInstance) (m : ℕ)
    (point : Fin (problem.variableCount + m) → ℝ) :
    (etrStrictifierPolynomialFin problem m).eval₂
        (Int.castRingHom ℝ) point =
      contractionStrictifier problem.sourceResidualSum m
        (strictifierSourceActivity problem m
          (strictifierSumPointOfFin problem m point))
        (strictifierChainFromTail
          (strictifierTailActivity problem m
            (strictifierSumPointOfFin problem m point))) := by
  rw [etrStrictifierPolynomialFin_eq_rename,
    MvPolynomial.eval₂_rename,
    eval_etrStrictifierPolynomial]
  rfl

theorem etrStrictifierPolynomialFin_totalDegree_le_four
    (problem : BoundedETRINVInstance) (m : ℕ) :
    (etrStrictifierPolynomialFin problem m).totalDegree ≤ 4 := by
  rw [etrStrictifierPolynomialFin_eq_rename]
  exact (MvPolynomial.totalDegree_rename_le finSumFinEquiv
      (etrStrictifierPolynomial problem m)).trans
    (etrStrictifierPolynomial_totalDegree_le_four problem m)

/-- Injective coordinate renaming preserves the collected coefficient
`ℓ¹` mass exactly. -/
theorem coefficientL1_rename_injective {N M : ℕ}
    (coordinateMap : Fin N → Fin M)
    (hInjective : Function.Injective coordinateMap)
    (polynomial : MvPolynomial (Fin N) ℤ) :
    coefficientL1 (MvPolynomial.rename coordinateMap polynomial) =
      coefficientL1 polynomial := by
  classical
  unfold coefficientL1
  rw [MvPolynomial.support_rename_of_injective hInjective]
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro exponent hExponent
    rw [MvPolynomial.coeff_rename_mapDomain coordinateMap hInjective]
  · intro first _ second _ hEqual
    exact Finsupp.mapDomain_injective hInjective hEqual

theorem coefficientL1_liftedSourceResidualPolynomialFin
    (problem : BoundedETRINVInstance) (m : ℕ) :
    coefficientL1 (liftedSourceResidualPolynomialFin problem m) =
      coefficientL1 problem.sourceResidualPolynomial := by
  unfold liftedSourceResidualPolynomialFin
  apply coefficientL1_rename_injective
  intro first second hEqual
  exact Sum.inl.inj (finSumFinEquiv.injective hEqual)

theorem coefficientL1_strictifierChainValuePolynomialFin
    (problem : BoundedETRINVInstance) (m : ℕ)
    (coordinate : Fin (m + 1)) :
    coefficientL1
      (strictifierChainValuePolynomialFin problem m coordinate) = 1 := by
  refine Fin.cases ?_ (fun tailCoordinate => ?_) coordinate
  · exact coefficientL1_one
  · exact coefficientL1_X _

theorem coefficientL1_contractionResidualPolynomialFin_le_three
    (problem : BoundedETRINVInstance) (m : ℕ) (step : Fin m) :
    coefficientL1 (contractionResidualPolynomialFin problem m step) ≤ 3 := by
  unfold contractionResidualPolynomialFin
  calc
    coefficientL1
        (2 * strictifierChainValuePolynomialFin problem m step.succ -
          strictifierChainValuePolynomialFin problem m step.castSucc ^ 2) ≤
        coefficientL1
            (2 * strictifierChainValuePolynomialFin problem m step.succ) +
          coefficientL1
            (strictifierChainValuePolynomialFin problem m
              step.castSucc ^ 2) :=
      coefficientL1_sub_le _ _
    _ ≤ 2 * coefficientL1
            (strictifierChainValuePolynomialFin problem m step.succ) +
          coefficientL1
            (strictifierChainValuePolynomialFin problem m
              step.castSucc) ^ 2 :=
      Nat.add_le_add
        (coefficientL1_natCast_mul_le 2
          (strictifierChainValuePolynomialFin problem m step.succ))
        (coefficientL1_sq_le
          (strictifierChainValuePolynomialFin problem m step.castSucc))
    _ = 3 := by
      rw [coefficientL1_strictifierChainValuePolynomialFin,
        coefficientL1_strictifierChainValuePolynomialFin]
      norm_num

theorem coefficientL1_contractionPenaltyPolynomialFin_le
    (problem : BoundedETRINVInstance) (m : ℕ) :
    coefficientL1 (∑ step : Fin m,
        contractionResidualPolynomialFin problem m step ^ 2) ≤
      9 * m := by
  calc
    coefficientL1 (∑ step : Fin m,
        contractionResidualPolynomialFin problem m step ^ 2) ≤
      ∑ step : Fin m,
        coefficientL1 (contractionResidualPolynomialFin problem m step ^ 2) :=
      coefficientL1_finset_sum_le Finset.univ _
    _ ≤ ∑ _step : Fin m, 9 := by
      apply Finset.sum_le_sum
      intro step _
      exact (coefficientL1_sq_le
          (contractionResidualPolynomialFin problem m step)).trans
        ((Nat.pow_le_pow_left
          (coefficientL1_contractionResidualPolynomialFin_le_three
            problem m step) 2).trans_eq (by norm_num))
    _ = 9 * m := by simp [Nat.mul_comm]

/-- Exact polynomial-size bound used by the registered reduction: the source
contributes at most `800q`, the `m` recurrence residuals contribute at most
`9m²`, and the terminal square contributes at most two. -/
theorem etrStrictifierPolynomialFin_coefficientL1_le
    (problem : BoundedETRINVInstance) (m : ℕ) :
    coefficientL1 (etrStrictifierPolynomialFin problem m) ≤
      800 * problem.equationCount + 9 * m ^ 2 + 2 := by
  unfold etrStrictifierPolynomialFin
  calc
    coefficientL1
        (2 * liftedSourceResidualPolynomialFin problem m +
            ((m : ℤ) : MvPolynomial
              (Fin (problem.variableCount + m)) ℤ) * (∑ step : Fin m,
              contractionResidualPolynomialFin problem m step ^ 2) -
          2 * strictifierChainValuePolynomialFin
            problem m (Fin.last m) ^ 2) ≤
        coefficientL1
            (2 * liftedSourceResidualPolynomialFin problem m +
              ((m : ℤ) : MvPolynomial
                (Fin (problem.variableCount + m)) ℤ) * (∑ step : Fin m,
                contractionResidualPolynomialFin problem m step ^ 2)) +
          coefficientL1
            (2 * strictifierChainValuePolynomialFin
              problem m (Fin.last m) ^ 2) :=
      coefficientL1_sub_le _ _
    _ ≤ (coefficientL1
            (2 * liftedSourceResidualPolynomialFin problem m) +
          coefficientL1
            (((m : ℤ) : MvPolynomial
              (Fin (problem.variableCount + m)) ℤ) * (∑ step : Fin m,
              contractionResidualPolynomialFin problem m step ^ 2))) +
          coefficientL1
            (2 * strictifierChainValuePolynomialFin
              problem m (Fin.last m) ^ 2) :=
      Nat.add_le_add_right (coefficientL1_add_le _ _) _
    _ ≤ (2 * coefficientL1
            (liftedSourceResidualPolynomialFin problem m) +
          m * coefficientL1 (∑ step : Fin m,
            contractionResidualPolynomialFin problem m step ^ 2)) +
          2 * coefficientL1
            (strictifierChainValuePolynomialFin
              problem m (Fin.last m) ^ 2) := by
      apply Nat.add_le_add
      · apply Nat.add_le_add
        · exact coefficientL1_natCast_mul_le 2 _
        · simpa using coefficientL1_natCast_mul_le m
            (∑ step : Fin m,
              contractionResidualPolynomialFin problem m step ^ 2)
      · exact coefficientL1_natCast_mul_le 2 _
    _ ≤ (2 * (400 * problem.equationCount) + m * (9 * m)) +
          2 * 1 ^ 2 := by
      apply Nat.add_le_add
      · apply Nat.add_le_add
        · exact Nat.mul_le_mul_left 2 <|
            (coefficientL1_liftedSourceResidualPolynomialFin problem m).le.trans
              (sourceResidualPolynomial_coefficientL1_le problem)
        · exact Nat.mul_le_mul_left m
            (coefficientL1_contractionPenaltyPolynomialFin_le problem m)
      · apply Nat.mul_le_mul_left 2
        exact (coefficientL1_sq_le
          (strictifierChainValuePolynomialFin problem m (Fin.last m))).trans_eq
            (by
              rw [coefficientL1_strictifierChainValuePolynomialFin])
    _ = 800 * problem.equationCount + 9 * m ^ 2 + 2 := by ring

/-! ## Exact semantic reduction -/

/-- Assemble source and contraction-tail coordinates into the canonical
finite index. -/
def strictifierFinPoint
    (problem : BoundedETRINVInstance) (m : ℕ)
    (source : Fin problem.variableCount → ℝ) (tail : Fin m → ℝ) :
    Fin (problem.variableCount + m) → ℝ :=
  fun coordinate =>
    match finSumFinEquiv.symm coordinate with
    | .inl sourceCoordinate => source sourceCoordinate
    | .inr tailCoordinate => tail tailCoordinate

@[simp]
theorem strictifierSourceActivity_sumPoint_finPoint
    (problem : BoundedETRINVInstance) (m : ℕ)
    (source : Fin problem.variableCount → ℝ) (tail : Fin m → ℝ) :
    strictifierSourceActivity problem m
        (strictifierSumPointOfFin problem m
          (strictifierFinPoint problem m source tail)) = source := by
  funext coordinate
  simp [strictifierSourceActivity, strictifierSumPointOfFin,
    strictifierFinPoint]

@[simp]
theorem strictifierTailActivity_sumPoint_finPoint
    (problem : BoundedETRINVInstance) (m : ℕ)
    (source : Fin problem.variableCount → ℝ) (tail : Fin m → ℝ) :
    strictifierTailActivity problem m
        (strictifierSumPointOfFin problem m
          (strictifierFinPoint problem m source tail)) = tail := by
  funext coordinate
  simp [strictifierTailActivity, strictifierSumPointOfFin,
    strictifierFinPoint]

theorem strictifierFinPoint_closedCube
    (problem : BoundedETRINVInstance) (m : ℕ)
    {source : Fin problem.variableCount → ℝ} {tail : Fin m → ℝ}
    (hSource : problem.IsCubePoint source)
    (hTail : ∀ coordinate, 0 ≤ tail coordinate ∧ tail coordinate ≤ 1) :
    strictifierFinPoint problem m source tail ∈
      closedActivityCube (Fin (problem.variableCount + m)) := by
  intro coordinate _
  obtain ⟨coordinate, rfl⟩ := finSumFinEquiv.surjective coordinate
  cases coordinate with
  | inl sourceCoordinate =>
      simpa [strictifierFinPoint] using hSource sourceCoordinate
  | inr tailCoordinate =>
      simpa [strictifierFinPoint] using hTail tailCoordinate

theorem strictifierSourceActivity_closedCube
    (problem : BoundedETRINVInstance) (m : ℕ)
    {point : Fin (problem.variableCount + m) → ℝ}
    (hPoint : point ∈ closedActivityCube
      (Fin (problem.variableCount + m))) :
    problem.IsCubePoint
      (strictifierSourceActivity problem m
        (strictifierSumPointOfFin problem m point)) := by
  intro coordinate
  exact hPoint (finSumFinEquiv (.inl coordinate)) (Set.mem_univ _)

theorem strictifierTailActivity_closedCube
    (problem : BoundedETRINVInstance) (m : ℕ)
    {point : Fin (problem.variableCount + m) → ℝ}
    (hPoint : point ∈ closedActivityCube
      (Fin (problem.variableCount + m))) :
    ∀ coordinate, 0 ≤ strictifierTailActivity problem m
        (strictifierSumPointOfFin problem m point) coordinate ∧
      strictifierTailActivity problem m
        (strictifierSumPointOfFin problem m point) coordinate ≤ 1 := by
  intro coordinate
  exact hPoint (finSumFinEquiv (.inr coordinate)) (Set.mem_univ _)

theorem strictifierChainFromTail_cube
    {m : ℕ} {tail : Fin m → ℝ}
    (hTail : ∀ coordinate, 0 ≤ tail coordinate ∧ tail coordinate ≤ 1) :
    ∀ i, i ≤ m →
      0 ≤ strictifierChainFromTail tail i ∧
        strictifierChainFromTail tail i ≤ 1 := by
  intro i hi
  cases i with
  | zero => simp
  | succ i =>
      have hiTail : i < m := by omega
      simpa [strictifierChainFromTail, hiTail] using hTail ⟨i, hiTail⟩

/-- Tail of the exact contraction orbit. -/
def exactContractionTail (m : ℕ) : Fin m → ℝ :=
  fun coordinate => exactContractionChain (coordinate.val + 1)

theorem exactContractionTail_cube (m : ℕ) :
    ∀ coordinate, 0 ≤ exactContractionTail m coordinate ∧
      exactContractionTail m coordinate ≤ 1 := by
  intro coordinate
  exact ⟨(exactContractionChain_pos _).le,
    exactContractionChain_le_one _⟩

theorem strictifierChainFrom_exactContractionTail
    (m i : ℕ) (hi : i ≤ m) :
    strictifierChainFromTail (exactContractionTail m) i =
      exactContractionChain i := by
  cases i with
  | zero => rfl
  | succ i =>
      have hiTail : i < m := by omega
      simp [strictifierChainFromTail, exactContractionTail, hiTail]

theorem contractionResidual_exactContractionTail_zero
    (m : ℕ) {i : ℕ} (hi : i < m) :
    contractionResidual
      (strictifierChainFromTail (exactContractionTail m)) i = 0 := by
  unfold contractionResidual
  rw [strictifierChainFrom_exactContractionTail m i hi.le,
    strictifierChainFrom_exactContractionTail m (i + 1) (by omega),
    exactContractionChain_succ]
  ring

theorem contractionStrictifier_exactTail_negative_of_source_zero
    (problem : BoundedETRINVInstance) (m : ℕ)
    {source : Fin problem.variableCount → ℝ}
    (hZero : problem.sourceResidualSum source = 0) :
    contractionStrictifier problem.sourceResidualSum m source
      (strictifierChainFromTail (exactContractionTail m)) < 0 := by
  unfold contractionStrictifier
  rw [hZero]
  have hResidualSum :
      (∑ i ∈ Finset.range m,
        contractionResidual
          (strictifierChainFromTail (exactContractionTail m)) i ^ 2) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [contractionResidual_exactContractionTail_zero m
      (Finset.mem_range.mp hi)]
    norm_num
  rw [hResidualSum, strictifierChainFrom_exactContractionTail m m le_rfl]
  nlinarith [exactContractionChain_pos m]

/-- Closed-cube negative witnesses for the constructed polynomial are exactly
bounded-ETR solutions, relative to the declared compact minimum gap. -/
theorem boundedETRINV_satisfiable_iff_strictifier_negative_closedCube
    (problem : BoundedETRINVInstance) (m : ℕ) (gap : ℝ)
    (hGapIfNoZero :
      (¬ ∃ source, problem.IsCubePoint source ∧
          problem.sourceResidualSum source = 0) →
        ∀ source, problem.IsCubePoint source →
          gap ≤ problem.sourceResidualSum source)
    (hTerminal : 2 * exactContractionChain m ^ 2 < gap) :
    problem.Satisfiable ↔
      ∃ point : Fin (problem.variableCount + m) → ℝ,
        point ∈ closedActivityCube
          (Fin (problem.variableCount + m)) ∧
        (etrStrictifierPolynomialFin problem m).eval₂
          (Int.castRingHom ℝ) point < 0 := by
  constructor
  · intro hSatisfiable
    obtain ⟨source, hSource, hZero⟩ :=
      (boundedETRINV_satisfiable_iff_residual_zero problem).1 hSatisfiable
    let tail := exactContractionTail m
    let point := strictifierFinPoint problem m source tail
    refine ⟨point,
      strictifierFinPoint_closedCube problem m hSource
        (exactContractionTail_cube m), ?_⟩
    rw [eval_etrStrictifierPolynomialFin]
    simp only [point, tail,
      strictifierSourceActivity_sumPoint_finPoint,
      strictifierTailActivity_sumPoint_finPoint]
    exact contractionStrictifier_exactTail_negative_of_source_zero
      problem m hZero
  · rintro ⟨point, hPoint, hNegative⟩
    apply (boundedETRINV_satisfiable_iff_residual_zero problem).2
    by_contra hNoZero
    let source := strictifierSourceActivity problem m
      (strictifierSumPointOfFin problem m point)
    let tail := strictifierTailActivity problem m
      (strictifierSumPointOfFin problem m point)
    let chain := strictifierChainFromTail tail
    have hSource : problem.IsCubePoint source :=
      strictifierSourceActivity_closedCube problem m hPoint
    have hTail : ∀ coordinate, 0 ≤ tail coordinate ∧
        tail coordinate ≤ 1 :=
      strictifierTailActivity_closedCube problem m hPoint
    have hChainCube : ∀ i, i ≤ m →
        0 ≤ chain i ∧ chain i ≤ 1 :=
      strictifierChainFromTail_cube hTail
    have hPositive := contractionStrictifier_nonneg_of_gap
      problem.IsCubePoint problem.sourceResidualSum m gap
      (hGapIfNoZero hNoZero) hTerminal source hSource chain rfl hChainCube
    rw [eval_etrStrictifierPolynomialFin] at hNegative
    change contractionStrictifier problem.sourceResidualSum m source chain < 0
      at hNegative
    linarith

/-- Physical MaxEnt activity cube: coordinates are strictly positive and at
most one. -/
def ETRStrictifierPositiveCubePoint {J : Type*}
    (point : J → ℝ) : Prop :=
  ∀ coordinate, 0 < point coordinate ∧ point coordinate ≤ 1

theorem etrStrictifierPositiveCubePoint_mem_openActivityCube
    {J : Type*} {point : J → ℝ}
    (hPoint : point ∈ openActivityCube J) :
    ETRStrictifierPositiveCubePoint point := by
  intro coordinate
  exact ⟨(hPoint coordinate (Set.mem_univ _)).1,
    (hPoint coordinate (Set.mem_univ _)).2.le⟩

theorem etrStrictifierPositiveCubePoint_mem_closedActivityCube
    {J : Type*} {point : J → ℝ}
    (hPoint : ETRStrictifierPositiveCubePoint point) :
    point ∈ closedActivityCube J := by
  intro coordinate _
  exact ⟨(hPoint coordinate).1.le, (hPoint coordinate).2⟩

theorem continuous_eval₂_intPolynomial {J : Type*}
    (polynomial : MvPolynomial J ℤ) :
    Continuous (fun point : J → ℝ =>
      polynomial.eval₂ (Int.castRingHom ℝ) point) := by
  rw [show (fun point : J → ℝ =>
      polynomial.eval₂ (Int.castRingHom ℝ) point) =
      fun point => MvPolynomial.eval point
        (MvPolynomial.map (Int.castRingHom ℝ) polynomial) by
      funext point
      exact MvPolynomial.eval₂_eq_eval_map _ _ _]
  exact MvPolynomial.continuous_eval _

/-- For an integer polynomial, existence of a strict negative witness is the
same on the closed proof cube and on the physical positive activity cube.
Strictness and density perform the boundary-to-physical transport. -/
theorem exists_negative_closedCube_iff_positiveCube
    {J : Type*} (polynomial : MvPolynomial J ℤ) :
    (∃ point : J → ℝ,
      point ∈ closedActivityCube J ∧
      polynomial.eval₂ (Int.castRingHom ℝ) point < 0) ↔
    ∃ point : J → ℝ,
      ETRStrictifierPositiveCubePoint point ∧
      polynomial.eval₂ (Int.castRingHom ℝ) point < 0 := by
  constructor
  · rintro ⟨closedPoint, hClosed, hNegative⟩
    by_contra hNoPhysicalNegative
    have hPhysicalNonnegative :
        ∀ point : J → ℝ,
          ETRStrictifierPositiveCubePoint point →
            0 ≤ polynomial.eval₂ (Int.castRingHom ℝ) point := by
      intro point hPoint
      exact le_of_not_gt fun hNegativePoint =>
        hNoPhysicalNegative ⟨point, hPoint, hNegativePoint⟩
    have hOpenNonnegative :
        ∀ point ∈ openActivityCube J,
          0 ≤ polynomial.eval₂ (Int.castRingHom ℝ) point := by
      intro point hPoint
      exact hPhysicalNonnegative point
        (etrStrictifierPositiveCubePoint_mem_openActivityCube hPoint)
    have hClosedNonnegative :=
      (max_g1_closure_03
        (fun point : J → ℝ =>
          polynomial.eval₂ (Int.castRingHom ℝ) point)
        (continuous_eval₂_intPolynomial polynomial)).1 hOpenNonnegative
    linarith [hClosedNonnegative closedPoint hClosed]
  · rintro ⟨point, hPoint, hNegative⟩
    exact ⟨point,
      etrStrictifierPositiveCubePoint_mem_closedActivityCube hPoint,
      hNegative⟩

/-- Registered physical-cube reduction.  This is the exact constructive
bridge from bounded ETR-INV satisfiability to strict failure of universal
nonnegativity of the canonical integer quartic. -/
theorem boundedETRINV_satisfiable_iff_strictifier_negative_positiveCube
    (problem : BoundedETRINVInstance) (m : ℕ) (gap : ℝ)
    (hGapIfNoZero :
      (¬ ∃ source, problem.IsCubePoint source ∧
          problem.sourceResidualSum source = 0) →
        ∀ source, problem.IsCubePoint source →
          gap ≤ problem.sourceResidualSum source)
    (hTerminal : 2 * exactContractionChain m ^ 2 < gap) :
    problem.Satisfiable ↔
      ∃ point : Fin (problem.variableCount + m) → ℝ,
        ETRStrictifierPositiveCubePoint point ∧
        (etrStrictifierPolynomialFin problem m).eval₂
          (Int.castRingHom ℝ) point < 0 := by
  rw [boundedETRINV_satisfiable_iff_strictifier_negative_closedCube
    problem m gap hGapIfNoZero hTerminal]
  exact exists_negative_closedCube_iff_positiveCube
    (etrStrictifierPolynomialFin problem m)

/-- Polynomial component of **MAX-G3.REDUCTION.03**, in registered
constructive form.
For a bounded ETR-INV instance with the inherited dyadic compact-gap proof
witness and a sufficiently long exact contraction chain, the canonical
integer polynomial is quartic, has the displayed coefficient-mass bound, and
has a strict negative witness on the physical positive unit cube exactly when
the source instance is satisfiable. -/
theorem max_g3_strictifierPolynomial_complete
    (problem : BoundedETRINVInstance) (m bits : ℕ)
    (hGapIfNoZero :
      (¬ ∃ source, problem.IsCubePoint source ∧
          problem.sourceResidualSum source = 0) →
        ∀ source, problem.IsCubePoint source →
          dyadicCompactGap bits ≤ problem.sourceResidualSum source)
    (hLength : bits + 3 < 2 ^ (m + 1)) :
    (etrStrictifierPolynomialFin problem m).totalDegree ≤ 4 ∧
      coefficientL1 (etrStrictifierPolynomialFin problem m) ≤
        800 * problem.equationCount + 9 * m ^ 2 + 2 ∧
      (problem.Satisfiable ↔
        ∃ point : Fin (problem.variableCount + m) → ℝ,
          ETRStrictifierPositiveCubePoint point ∧
          (etrStrictifierPolynomialFin problem m).eval₂
            (Int.castRingHom ℝ) point < 0) := by
  refine ⟨etrStrictifierPolynomialFin_totalDegree_le_four problem m,
    etrStrictifierPolynomialFin_coefficientL1_le problem m, ?_⟩
  exact boundedETRINV_satisfiable_iff_strictifier_negative_positiveCube
    problem m (dyadicCompactGap bits) hGapIfNoZero
      (exactContractionChain_terminal_lt_dyadicGap m bits hLength)

end

end PhonologicalCalculus.MaxEnt
