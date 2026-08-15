import PhonologicalCalculus.MaxEnt.ExecutableComplexity
import Mathlib.Data.List.FinRange
import Mathlib.Tactic

/-!
# Executable quartic expansion for the bounded-ETR strictifier

The semantic formalization represents the strictifier as an `MvPolynomial`.
That representation is ideal for algebraic proofs, but extracting its finite
support uses a choice-based enumeration.  This module gives a separate,
deterministic list expansion of the same polynomial.  It keeps duplicate
monomials rather than collecting them; this is harmless for evaluation and
lets the later tag compiler assign every signed coefficient unit its own row.
-/

namespace PhonologicalCalculus.MaxEnt

open Finset
open scoped BigOperators

/-! ## Raw integer monomials and list polynomials -/

structure ExecutableIntegerMonomial (coordinateCount : ℕ) where
  exponent : Fin coordinateCount → ℕ
  coefficient : ℤ

def ExecutableIntegerMonomial.evaluate
    {coordinateCount : ℕ}
    (term : ExecutableIntegerMonomial coordinateCount)
    (point : Fin coordinateCount → ℝ) : ℝ :=
  (term.coefficient : ℝ) *
    ∏ coordinate, point coordinate ^ term.exponent coordinate

def evaluateExecutablePolynomial
    {coordinateCount : ℕ}
    (terms : List (ExecutableIntegerMonomial coordinateCount))
    (point : Fin coordinateCount → ℝ) : ℝ :=
  (terms.map fun term => term.evaluate point).sum

def zeroExecutableExponent (coordinateCount : ℕ) :
    Fin coordinateCount → ℕ := fun _ => 0

def singleExecutableExponent {coordinateCount : ℕ}
    (selected : Fin coordinateCount) (power : ℕ) :
    Fin coordinateCount → ℕ :=
  fun coordinate => if coordinate = selected then power else 0

def executableConstantMonomial (coordinateCount : ℕ)
    (coefficient : ℤ) : ExecutableIntegerMonomial coordinateCount :=
  ⟨zeroExecutableExponent coordinateCount, coefficient⟩

def executableVariableMonomial {coordinateCount : ℕ}
    (selected : Fin coordinateCount) (power : ℕ) (coefficient : ℤ) :
    ExecutableIntegerMonomial coordinateCount :=
  ⟨singleExecutableExponent selected power, coefficient⟩

def ExecutableIntegerMonomial.scale
    {coordinateCount : ℕ} (coefficient : ℤ)
    (term : ExecutableIntegerMonomial coordinateCount) :
    ExecutableIntegerMonomial coordinateCount :=
  ⟨term.exponent, coefficient * term.coefficient⟩

def ExecutableIntegerMonomial.multiply
    {coordinateCount : ℕ}
    (first second : ExecutableIntegerMonomial coordinateCount) :
    ExecutableIntegerMonomial coordinateCount :=
  ⟨fun coordinate => first.exponent coordinate + second.exponent coordinate,
    first.coefficient * second.coefficient⟩

def scaleExecutablePolynomial {coordinateCount : ℕ}
    (coefficient : ℤ)
    (terms : List (ExecutableIntegerMonomial coordinateCount)) :
    List (ExecutableIntegerMonomial coordinateCount) :=
  terms.map (ExecutableIntegerMonomial.scale coefficient)

def multiplyExecutablePolynomial {coordinateCount : ℕ}
    (first second : List (ExecutableIntegerMonomial coordinateCount)) :
    List (ExecutableIntegerMonomial coordinateCount) :=
  first.flatMap fun left => second.map left.multiply

def squareExecutablePolynomial {coordinateCount : ℕ}
    (terms : List (ExecutableIntegerMonomial coordinateCount)) :
    List (ExecutableIntegerMonomial coordinateCount) :=
  multiplyExecutablePolynomial terms terms

@[simp]
theorem executableConstantMonomial_evaluate
    (coordinateCount : ℕ) (coefficient : ℤ)
    (point : Fin coordinateCount → ℝ) :
    (executableConstantMonomial coordinateCount coefficient).evaluate point =
      coefficient := by
  simp [ExecutableIntegerMonomial.evaluate,
    executableConstantMonomial, zeroExecutableExponent]

@[simp]
theorem executableVariableMonomial_evaluate
    {coordinateCount : ℕ} (selected : Fin coordinateCount)
    (power : ℕ) (coefficient : ℤ)
    (point : Fin coordinateCount → ℝ) :
    (executableVariableMonomial selected power coefficient).evaluate point =
      coefficient * point selected ^ power := by
  classical
  simp [ExecutableIntegerMonomial.evaluate, executableVariableMonomial,
    singleExecutableExponent]

@[simp]
theorem ExecutableIntegerMonomial.scale_evaluate
    {coordinateCount : ℕ} (coefficient : ℤ)
    (term : ExecutableIntegerMonomial coordinateCount)
    (point : Fin coordinateCount → ℝ) :
    (term.scale coefficient).evaluate point =
      coefficient * term.evaluate point := by
  unfold ExecutableIntegerMonomial.scale ExecutableIntegerMonomial.evaluate
  push_cast
  ring

@[simp]
theorem ExecutableIntegerMonomial.multiply_evaluate
    {coordinateCount : ℕ}
    (first second : ExecutableIntegerMonomial coordinateCount)
    (point : Fin coordinateCount → ℝ) :
    (first.multiply second).evaluate point =
      first.evaluate point * second.evaluate point := by
  classical
  unfold ExecutableIntegerMonomial.multiply ExecutableIntegerMonomial.evaluate
  simp_rw [pow_add]
  rw [Finset.prod_mul_distrib]
  push_cast
  ring

@[simp]
theorem evaluateExecutablePolynomial_append
    {coordinateCount : ℕ}
    (first second : List (ExecutableIntegerMonomial coordinateCount))
    (point : Fin coordinateCount → ℝ) :
    evaluateExecutablePolynomial (first ++ second) point =
      evaluateExecutablePolynomial first point +
        evaluateExecutablePolynomial second point := by
  simp [evaluateExecutablePolynomial]

@[simp]
theorem evaluate_scaleExecutablePolynomial
    {coordinateCount : ℕ} (coefficient : ℤ)
    (terms : List (ExecutableIntegerMonomial coordinateCount))
    (point : Fin coordinateCount → ℝ) :
    evaluateExecutablePolynomial (scaleExecutablePolynomial coefficient terms)
        point =
      coefficient * evaluateExecutablePolynomial terms point := by
  induction terms with
  | nil => simp [evaluateExecutablePolynomial, scaleExecutablePolynomial]
  | cons term rest ih =>
      simp only [scaleExecutablePolynomial, List.map_cons,
        evaluateExecutablePolynomial, List.sum_cons,
        ExecutableIntegerMonomial.scale_evaluate]
      change coefficient * term.evaluate point +
          evaluateExecutablePolynomial
            (scaleExecutablePolynomial coefficient rest) point = _
      rw [ih]
      change coefficient * term.evaluate point +
          coefficient * evaluateExecutablePolynomial rest point =
        coefficient *
          (term.evaluate point + evaluateExecutablePolynomial rest point)
      ring

theorem evaluateExecutablePolynomial_flatMap
    {coordinateCount : ℕ} {Item : Type*}
    (items : List Item)
    (terms : Item → List (ExecutableIntegerMonomial coordinateCount))
    (point : Fin coordinateCount → ℝ) :
    evaluateExecutablePolynomial (items.flatMap terms) point =
      (items.map fun item =>
        evaluateExecutablePolynomial (terms item) point).sum := by
  induction items with
  | nil => simp [evaluateExecutablePolynomial]
  | cons item rest ih =>
      simp [evaluateExecutablePolynomial_append, ih]

theorem evaluateExecutablePolynomial_map_multiply_left
    {coordinateCount : ℕ}
    (term : ExecutableIntegerMonomial coordinateCount)
    (terms : List (ExecutableIntegerMonomial coordinateCount))
    (point : Fin coordinateCount → ℝ) :
    evaluateExecutablePolynomial (terms.map term.multiply) point =
      term.evaluate point * evaluateExecutablePolynomial terms point := by
  induction terms with
  | nil => simp [evaluateExecutablePolynomial]
  | cons next rest ih =>
      simp only [List.map_cons, evaluateExecutablePolynomial,
        List.sum_cons, ExecutableIntegerMonomial.multiply_evaluate]
      change term.evaluate point * next.evaluate point +
          evaluateExecutablePolynomial (rest.map term.multiply) point = _
      rw [ih]
      change term.evaluate point * next.evaluate point +
          term.evaluate point * evaluateExecutablePolynomial rest point =
        term.evaluate point *
          (next.evaluate point + evaluateExecutablePolynomial rest point)
      ring

theorem evaluate_multiplyExecutablePolynomial
    {coordinateCount : ℕ}
    (first second : List (ExecutableIntegerMonomial coordinateCount))
    (point : Fin coordinateCount → ℝ) :
    evaluateExecutablePolynomial
        (multiplyExecutablePolynomial first second) point =
      evaluateExecutablePolynomial first point *
        evaluateExecutablePolynomial second point := by
  induction first with
  | nil => simp [multiplyExecutablePolynomial, evaluateExecutablePolynomial]
  | cons term rest ih =>
      unfold multiplyExecutablePolynomial
      rw [List.flatMap_cons,
        evaluateExecutablePolynomial_append,
        evaluateExecutablePolynomial_map_multiply_left]
      change term.evaluate point * evaluateExecutablePolynomial second point +
          evaluateExecutablePolynomial
            (multiplyExecutablePolynomial rest second) point = _
      rw [ih]
      simp [evaluateExecutablePolynomial]
      ring

@[simp]
theorem evaluate_squareExecutablePolynomial
    {coordinateCount : ℕ}
    (terms : List (ExecutableIntegerMonomial coordinateCount))
    (point : Fin coordinateCount → ℝ) :
    evaluateExecutablePolynomial (squareExecutablePolynomial terms) point =
      evaluateExecutablePolynomial terms point ^ 2 := by
  rw [squareExecutablePolynomial, evaluate_multiplyExecutablePolynomial]
  ring

/-! ## Direct source-residual expansion -/

def executableSourceVariable
    (problem : BoundedETRINVInstance) (tailLength : ℕ)
    (coordinate : Fin problem.variableCount) :
    Fin (problem.variableCount + tailLength) :=
  Fin.castAdd tailLength coordinate

def executableSourceEquationResidual
    (problem : BoundedETRINVInstance) (tailLength : ℕ)
    (equation : BoundedETRINVEquation problem.variableCount) :
    List (ExecutableIntegerMonomial
      (problem.variableCount + tailLength)) :=
  match equation with
  | .unit x =>
      [executableConstantMonomial _ (-2),
        executableVariableMonomial
          (executableSourceVariable problem tailLength x) 1 6]
  | .add x y z =>
      [executableConstantMonomial _ 2,
        executableVariableMonomial
          (executableSourceVariable problem tailLength x) 1 6,
        executableVariableMonomial
          (executableSourceVariable problem tailLength y) 1 6,
        executableVariableMonomial
          (executableSourceVariable problem tailLength z) 1 (-6)]
  | .inverse x y =>
      [executableConstantMonomial _ (-3),
        executableVariableMonomial
          (executableSourceVariable problem tailLength x) 1 3,
        executableVariableMonomial
          (executableSourceVariable problem tailLength y) 1 3,
        (executableVariableMonomial
          (executableSourceVariable problem tailLength x) 1 3).multiply
          (executableVariableMonomial
            (executableSourceVariable problem tailLength y) 1 3)]

def executableSourceResidualPolynomial
    (problem : BoundedETRINVInstance) (tailLength : ℕ) :
    List (ExecutableIntegerMonomial
      (problem.variableCount + tailLength)) :=
  (List.ofFn problem.equation).flatMap fun equation =>
    squareExecutablePolynomial
      (executableSourceEquationResidual problem tailLength equation)

theorem executableSourceVariable_point
    (problem : BoundedETRINVInstance) (tailLength : ℕ)
    (point : Fin (problem.variableCount + tailLength) → ℝ)
    (coordinate : Fin problem.variableCount) :
    point (executableSourceVariable problem tailLength coordinate) =
      strictifierSourceActivity problem tailLength
        (strictifierSumPointOfFin problem tailLength point) coordinate := by
  simp [executableSourceVariable, strictifierSourceActivity,
    strictifierSumPointOfFin]

theorem evaluate_executableSourceEquationResidual
    (problem : BoundedETRINVInstance) (tailLength : ℕ)
    (equation : BoundedETRINVEquation problem.variableCount)
    (point : Fin (problem.variableCount + tailLength) → ℝ) :
    evaluateExecutablePolynomial
        (executableSourceEquationResidual problem tailLength equation) point =
      equation.scaledResidual
        (strictifierSourceActivity problem tailLength
          (strictifierSumPointOfFin problem tailLength point)) := by
  cases equation <;>
    simp [executableSourceEquationResidual,
      evaluateExecutablePolynomial,
      BoundedETRINVEquation.scaledResidual,
      executableSourceVariable_point] <;> ring

theorem evaluate_executableSourceResidualPolynomial
    (problem : BoundedETRINVInstance) (tailLength : ℕ)
    (point : Fin (problem.variableCount + tailLength) → ℝ) :
    evaluateExecutablePolynomial
        (executableSourceResidualPolynomial problem tailLength) point =
      problem.sourceResidualSum
        (strictifierSourceActivity problem tailLength
          (strictifierSumPointOfFin problem tailLength point)) := by
  unfold executableSourceResidualPolynomial
    BoundedETRINVInstance.sourceResidualSum
  rw [evaluateExecutablePolynomial_flatMap]
  simp_rw [evaluate_squareExecutablePolynomial,
    evaluate_executableSourceEquationResidual]
  rw [List.map_ofFn, List.sum_ofFn]
  simp only [Function.comp_apply]

/-! ## Direct contraction-chain expansion -/

def executableTailVariable
    (problem : BoundedETRINVInstance) (tailLength : ℕ)
    (coordinate : Fin tailLength) :
    Fin (problem.variableCount + tailLength) :=
  Fin.natAdd problem.variableCount coordinate

def executableChainCoordinate
    (problem : BoundedETRINVInstance) (tailLength : ℕ)
    (coordinate : Fin (tailLength + 1)) :
    List (ExecutableIntegerMonomial
      (problem.variableCount + tailLength)) :=
  Fin.cases
    [executableConstantMonomial _ 1]
    (fun tail =>
      [executableVariableMonomial
        (executableTailVariable problem tailLength tail) 1 1])
    coordinate

def executableContractionResidual
    (problem : BoundedETRINVInstance) (tailLength : ℕ)
    (step : Fin tailLength) :
    List (ExecutableIntegerMonomial
      (problem.variableCount + tailLength)) :=
  scaleExecutablePolynomial 2
      (executableChainCoordinate problem tailLength step.succ) ++
    scaleExecutablePolynomial (-1)
      (squareExecutablePolynomial
        (executableChainCoordinate problem tailLength step.castSucc))

def executableContractionPenalty
    (problem : BoundedETRINVInstance) (tailLength : ℕ) :
    List (ExecutableIntegerMonomial
      (problem.variableCount + tailLength)) :=
  (List.ofFn fun step : Fin tailLength =>
    squareExecutablePolynomial
      (executableContractionResidual problem tailLength step)).flatMap id

theorem executableTailVariable_point
    (problem : BoundedETRINVInstance) (tailLength : ℕ)
    (point : Fin (problem.variableCount + tailLength) → ℝ)
    (coordinate : Fin tailLength) :
    point (executableTailVariable problem tailLength coordinate) =
      strictifierTailActivity problem tailLength
        (strictifierSumPointOfFin problem tailLength point) coordinate := by
  simp [executableTailVariable, strictifierTailActivity,
    strictifierSumPointOfFin]

theorem evaluate_executableChainCoordinate
    (problem : BoundedETRINVInstance) (tailLength : ℕ)
    (point : Fin (problem.variableCount + tailLength) → ℝ)
    (coordinate : Fin (tailLength + 1)) :
    evaluateExecutablePolynomial
        (executableChainCoordinate problem tailLength coordinate) point =
      strictifierChainFromTail
        (strictifierTailActivity problem tailLength
          (strictifierSumPointOfFin problem tailLength point)) coordinate.val := by
  refine Fin.cases ?_ (fun tail => ?_) coordinate
  · simp [executableChainCoordinate, evaluateExecutablePolynomial]
  · simp only [executableChainCoordinate, Fin.cases_succ,
      evaluateExecutablePolynomial, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, executableVariableMonomial_evaluate,
      add_zero]
    rw [executableTailVariable_point problem tailLength point tail]
    simp [strictifierChainFromTail]

theorem evaluate_executableContractionResidual
    (problem : BoundedETRINVInstance) (tailLength : ℕ)
    (point : Fin (problem.variableCount + tailLength) → ℝ)
    (step : Fin tailLength) :
    evaluateExecutablePolynomial
        (executableContractionResidual problem tailLength step) point =
      contractionResidual
        (strictifierChainFromTail
          (strictifierTailActivity problem tailLength
            (strictifierSumPointOfFin problem tailLength point))) step.val := by
  simp [executableContractionResidual,
    evaluate_executableChainCoordinate, contractionResidual]
  ring

theorem evaluate_executableContractionPenalty
    (problem : BoundedETRINVInstance) (tailLength : ℕ)
    (point : Fin (problem.variableCount + tailLength) → ℝ) :
    evaluateExecutablePolynomial
        (executableContractionPenalty problem tailLength) point =
      ∑ step : Fin tailLength,
        contractionResidual
          (strictifierChainFromTail
            (strictifierTailActivity problem tailLength
              (strictifierSumPointOfFin problem tailLength point))) step.val ^ 2 := by
  unfold executableContractionPenalty evaluateExecutablePolynomial
  change evaluateExecutablePolynomial
      ((List.ofFn fun step : Fin tailLength =>
        squareExecutablePolynomial
          (executableContractionResidual problem tailLength step)).flatMap id)
      point = _
  rw [evaluateExecutablePolynomial_flatMap]
  change
    ((List.ofFn fun step : Fin tailLength =>
      squareExecutablePolynomial
        (executableContractionResidual problem tailLength step)).map
      (fun terms => evaluateExecutablePolynomial terms point)).sum = _
  rw [List.map_ofFn, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro step _
  simp only [Function.comp_apply]
  rw [evaluate_squareExecutablePolynomial,
    evaluate_executableContractionResidual]

/-! ## Complete strictifier list -/

def executableStrictifierPolynomial
    (problem : BoundedETRINVInstance) (tailLength : ℕ) :
    List (ExecutableIntegerMonomial
      (problem.variableCount + tailLength)) :=
  scaleExecutablePolynomial 2
      (executableSourceResidualPolynomial problem tailLength) ++
    scaleExecutablePolynomial tailLength
      (executableContractionPenalty problem tailLength) ++
    scaleExecutablePolynomial (-2)
      (squareExecutablePolynomial
        (executableChainCoordinate problem tailLength (Fin.last tailLength)))

theorem evaluate_executableStrictifierPolynomial
    (problem : BoundedETRINVInstance) (tailLength : ℕ)
    (point : Fin (problem.variableCount + tailLength) → ℝ) :
    evaluateExecutablePolynomial
        (executableStrictifierPolynomial problem tailLength) point =
      contractionStrictifier problem.sourceResidualSum tailLength
        (strictifierSourceActivity problem tailLength
          (strictifierSumPointOfFin problem tailLength point))
        (strictifierChainFromTail
          (strictifierTailActivity problem tailLength
            (strictifierSumPointOfFin problem tailLength point))) := by
  rw [executableStrictifierPolynomial,
    evaluateExecutablePolynomial_append,
    evaluateExecutablePolynomial_append,
    evaluate_scaleExecutablePolynomial,
    evaluate_scaleExecutablePolynomial,
    evaluate_scaleExecutablePolynomial,
    evaluate_executableSourceResidualPolynomial,
    evaluate_executableContractionPenalty,
    evaluate_squareExecutablePolynomial,
    evaluate_executableChainCoordinate]
  unfold contractionStrictifier
  let chain := strictifierChainFromTail
    (strictifierTailActivity problem tailLength
      (strictifierSumPointOfFin problem tailLength point))
  have hsum :
      (∑ step : Fin tailLength,
        contractionResidual chain step.val ^ 2) =
        ∑ step ∈ Finset.range tailLength,
          contractionResidual chain step ^ 2 := by
    simpa using Fin.sum_univ_eq_sum_range
      (fun step => contractionResidual chain step ^ 2) tailLength
  dsimp [chain] at hsum
  rw [hsum]
  simp only [Fin.val_last]
  push_cast
  ring

/-! ## Quartic and finite-size proofs -/

def ExecutableIntegerMonomial.totalDegree
    {coordinateCount : ℕ}
    (term : ExecutableIntegerMonomial coordinateCount) : ℕ :=
  ∑ coordinate, term.exponent coordinate

def ExecutablePolynomialDegreeAtMost
    {coordinateCount : ℕ}
    (degree : ℕ)
    (terms : List (ExecutableIntegerMonomial coordinateCount)) : Prop :=
  ∀ term ∈ terms, term.totalDegree ≤ degree

@[simp]
theorem executableConstantMonomial_totalDegree
    (coordinateCount : ℕ) (coefficient : ℤ) :
    (executableConstantMonomial coordinateCount coefficient).totalDegree = 0 := by
  simp [ExecutableIntegerMonomial.totalDegree,
    executableConstantMonomial, zeroExecutableExponent]

@[simp]
theorem executableVariableMonomial_totalDegree
    {coordinateCount : ℕ} (selected : Fin coordinateCount)
    (power : ℕ) (coefficient : ℤ) :
    (executableVariableMonomial selected power coefficient).totalDegree =
      power := by
  classical
  simp [ExecutableIntegerMonomial.totalDegree,
    executableVariableMonomial, singleExecutableExponent]

@[simp]
theorem ExecutableIntegerMonomial.scale_totalDegree
    {coordinateCount : ℕ} (coefficient : ℤ)
    (term : ExecutableIntegerMonomial coordinateCount) :
    (term.scale coefficient).totalDegree = term.totalDegree := rfl

theorem ExecutableIntegerMonomial.multiply_totalDegree
    {coordinateCount : ℕ}
    (first second : ExecutableIntegerMonomial coordinateCount) :
    (first.multiply second).totalDegree =
      first.totalDegree + second.totalDegree := by
  classical
  simp [ExecutableIntegerMonomial.totalDegree,
    ExecutableIntegerMonomial.multiply, Finset.sum_add_distrib]

theorem degreeAtMost_append {coordinateCount degree : ℕ}
    {first second : List (ExecutableIntegerMonomial coordinateCount)}
    (hFirst : ExecutablePolynomialDegreeAtMost degree first)
    (hSecond : ExecutablePolynomialDegreeAtMost degree second) :
    ExecutablePolynomialDegreeAtMost degree (first ++ second) := by
  intro term hTerm
  rw [List.mem_append] at hTerm
  exact hTerm.elim (hFirst term) (hSecond term)

theorem degreeAtMost_scale {coordinateCount degree : ℕ}
    (coefficient : ℤ)
    {terms : List (ExecutableIntegerMonomial coordinateCount)}
    (hTerms : ExecutablePolynomialDegreeAtMost degree terms) :
    ExecutablePolynomialDegreeAtMost degree
      (scaleExecutablePolynomial coefficient terms) := by
  intro term hTerm
  rw [scaleExecutablePolynomial, List.mem_map] at hTerm
  obtain ⟨source, hSource, rfl⟩ := hTerm
  simpa using hTerms source hSource

theorem degreeAtMost_multiply {coordinateCount firstDegree secondDegree : ℕ}
    {first second : List (ExecutableIntegerMonomial coordinateCount)}
    (hFirst : ExecutablePolynomialDegreeAtMost firstDegree first)
    (hSecond : ExecutablePolynomialDegreeAtMost secondDegree second) :
    ExecutablePolynomialDegreeAtMost (firstDegree + secondDegree)
      (multiplyExecutablePolynomial first second) := by
  intro term hTerm
  rw [multiplyExecutablePolynomial, List.mem_flatMap] at hTerm
  obtain ⟨left, hLeft, hTerm⟩ := hTerm
  rw [List.mem_map] at hTerm
  obtain ⟨right, hRight, rfl⟩ := hTerm
  rw [ExecutableIntegerMonomial.multiply_totalDegree]
  exact Nat.add_le_add (hFirst left hLeft) (hSecond right hRight)

theorem degreeAtMost_square {coordinateCount degree : ℕ}
    {terms : List (ExecutableIntegerMonomial coordinateCount)}
    (hTerms : ExecutablePolynomialDegreeAtMost degree terms) :
    ExecutablePolynomialDegreeAtMost (degree + degree)
      (squareExecutablePolynomial terms) := by
  exact degreeAtMost_multiply hTerms hTerms

theorem executableSourceEquationResidual_degreeAtMostTwo
    (problem : BoundedETRINVInstance) (tailLength : ℕ)
    (equation : BoundedETRINVEquation problem.variableCount) :
    ExecutablePolynomialDegreeAtMost 2
      (executableSourceEquationResidual problem tailLength equation) := by
  cases equation <;>
    simp [ExecutablePolynomialDegreeAtMost,
      executableSourceEquationResidual,
      ExecutableIntegerMonomial.multiply_totalDegree]

theorem executableSourceResidualPolynomial_degreeAtMostFour
    (problem : BoundedETRINVInstance) (tailLength : ℕ) :
    ExecutablePolynomialDegreeAtMost 4
      (executableSourceResidualPolynomial problem tailLength) := by
  intro term hTerm
  rw [executableSourceResidualPolynomial, List.mem_flatMap] at hTerm
  obtain ⟨equation, hEquation, hTerm⟩ := hTerm
  have hSquare := degreeAtMost_square
    (executableSourceEquationResidual_degreeAtMostTwo
      problem tailLength equation)
  exact hSquare term hTerm

theorem executableChainCoordinate_degreeAtMostOne
    (problem : BoundedETRINVInstance) (tailLength : ℕ)
    (coordinate : Fin (tailLength + 1)) :
    ExecutablePolynomialDegreeAtMost 1
      (executableChainCoordinate problem tailLength coordinate) := by
  refine Fin.cases ?_ (fun tail => ?_) coordinate <;>
    simp [ExecutablePolynomialDegreeAtMost, executableChainCoordinate]

theorem executableContractionResidual_degreeAtMostTwo
    (problem : BoundedETRINVInstance) (tailLength : ℕ)
    (step : Fin tailLength) :
    ExecutablePolynomialDegreeAtMost 2
      (executableContractionResidual problem tailLength step) := by
  unfold executableContractionResidual
  apply degreeAtMost_append
  · exact degreeAtMost_scale 2
      ((executableChainCoordinate_degreeAtMostOne
        problem tailLength step.succ) |> fun h =>
          fun term hTerm => (h term hTerm).trans (by omega))
  · exact degreeAtMost_scale (-1)
      (degreeAtMost_square
        (executableChainCoordinate_degreeAtMostOne
          problem tailLength step.castSucc))

theorem executableContractionPenalty_degreeAtMostFour
    (problem : BoundedETRINVInstance) (tailLength : ℕ) :
    ExecutablePolynomialDegreeAtMost 4
      (executableContractionPenalty problem tailLength) := by
  intro term hTerm
  rw [executableContractionPenalty, List.mem_flatMap] at hTerm
  obtain ⟨terms, hTerms, hTerm⟩ := hTerm
  rw [List.mem_ofFn] at hTerms
  obtain ⟨step, rfl⟩ := hTerms
  exact (degreeAtMost_square
    (executableContractionResidual_degreeAtMostTwo
      problem tailLength step)) term hTerm

theorem executableStrictifierPolynomial_degreeAtMostFour
    (problem : BoundedETRINVInstance) (tailLength : ℕ) :
    ExecutablePolynomialDegreeAtMost 4
      (executableStrictifierPolynomial problem tailLength) := by
  unfold executableStrictifierPolynomial
  apply degreeAtMost_append
  · apply degreeAtMost_append
    · exact degreeAtMost_scale 2
        (executableSourceResidualPolynomial_degreeAtMostFour
          problem tailLength)
    · exact degreeAtMost_scale tailLength
        (executableContractionPenalty_degreeAtMostFour
          problem tailLength)
  · apply degreeAtMost_scale (-2)
    intro term hTerm
    have hDegree := (degreeAtMost_square
      (executableChainCoordinate_degreeAtMostOne
        problem tailLength (Fin.last tailLength))) term hTerm
    omega

/-- Expanded unary coefficient mass of an executable term list. -/
def executableCoefficientL1 {coordinateCount : ℕ}
    (terms : List (ExecutableIntegerMonomial coordinateCount)) : ℕ :=
  (terms.map fun term => term.coefficient.natAbs).sum

@[simp]
theorem executableCoefficientL1_append {coordinateCount : ℕ}
    (first second : List (ExecutableIntegerMonomial coordinateCount)) :
    executableCoefficientL1 (first ++ second) =
      executableCoefficientL1 first + executableCoefficientL1 second := by
  simp [executableCoefficientL1]

theorem executableCoefficientL1_scale {coordinateCount : ℕ}
    (coefficient : ℤ)
    (terms : List (ExecutableIntegerMonomial coordinateCount)) :
    executableCoefficientL1 (scaleExecutablePolynomial coefficient terms) =
      coefficient.natAbs * executableCoefficientL1 terms := by
  induction terms with
  | nil => simp [executableCoefficientL1, scaleExecutablePolynomial]
  | cons term rest ih =>
      change (coefficient * term.coefficient).natAbs +
          executableCoefficientL1
            (scaleExecutablePolynomial coefficient rest) = _
      rw [Int.natAbs_mul, ih]
      simp only [executableCoefficientL1, List.map_cons, List.sum_cons]
      rw [Nat.mul_add]

theorem executableCoefficientL1_map_multiply_left {coordinateCount : ℕ}
    (term : ExecutableIntegerMonomial coordinateCount)
    (terms : List (ExecutableIntegerMonomial coordinateCount)) :
    executableCoefficientL1 (terms.map term.multiply) =
      term.coefficient.natAbs * executableCoefficientL1 terms := by
  induction terms with
  | nil => simp [executableCoefficientL1]
  | cons next rest ih =>
      change (term.coefficient * next.coefficient).natAbs +
          executableCoefficientL1 (rest.map term.multiply) = _
      rw [Int.natAbs_mul, ih]
      simp only [executableCoefficientL1, List.map_cons, List.sum_cons]
      rw [Nat.mul_add]

theorem executableCoefficientL1_multiply {coordinateCount : ℕ}
    (first second : List (ExecutableIntegerMonomial coordinateCount)) :
    executableCoefficientL1
        (multiplyExecutablePolynomial first second) =
      executableCoefficientL1 first * executableCoefficientL1 second := by
  induction first with
  | nil => simp [executableCoefficientL1, multiplyExecutablePolynomial]
  | cons term rest ih =>
      unfold multiplyExecutablePolynomial
      rw [List.flatMap_cons, executableCoefficientL1_append,
        executableCoefficientL1_map_multiply_left]
      change term.coefficient.natAbs * executableCoefficientL1 second +
          executableCoefficientL1
            (multiplyExecutablePolynomial rest second) = _
      rw [ih]
      simp [executableCoefficientL1]
      ring

@[simp]
theorem executableCoefficientL1_square {coordinateCount : ℕ}
    (terms : List (ExecutableIntegerMonomial coordinateCount)) :
    executableCoefficientL1 (squareExecutablePolynomial terms) =
      executableCoefficientL1 terms ^ 2 := by
  rw [squareExecutablePolynomial, executableCoefficientL1_multiply]
  ring

theorem executableSourceEquationResidual_coefficientL1_le_twenty
    (problem : BoundedETRINVInstance) (tailLength : ℕ)
    (equation : BoundedETRINVEquation problem.variableCount) :
    executableCoefficientL1
      (executableSourceEquationResidual problem tailLength equation) ≤ 20 := by
  cases equation <;>
    norm_num [executableSourceEquationResidual, executableCoefficientL1,
      ExecutableIntegerMonomial.multiply, executableConstantMonomial,
      executableVariableMonomial]

theorem executableCoefficientL1_flatMap
    {coordinateCount : ℕ} {Item : Type*}
    (items : List Item)
    (terms : Item → List (ExecutableIntegerMonomial coordinateCount)) :
    executableCoefficientL1 (items.flatMap terms) =
      (items.map fun item => executableCoefficientL1 (terms item)).sum := by
  induction items with
  | nil => simp [executableCoefficientL1]
  | cons item rest ih =>
      simp [executableCoefficientL1_append, ih]

theorem executableSourceResidualList_coefficientL1_le
    (problem : BoundedETRINVInstance) (tailLength : ℕ)
    (equations : List (BoundedETRINVEquation problem.variableCount)) :
    executableCoefficientL1
        (equations.flatMap fun equation =>
          squareExecutablePolynomial
            (executableSourceEquationResidual problem tailLength equation)) ≤
      400 * equations.length := by
  induction equations with
  | nil => simp [executableCoefficientL1]
  | cons equation rest ih =>
      rw [List.flatMap_cons, executableCoefficientL1_append,
        executableCoefficientL1_square]
      have hEquation :=
        executableSourceEquationResidual_coefficientL1_le_twenty
          problem tailLength equation
      have hSquare :
          executableCoefficientL1
              (executableSourceEquationResidual problem tailLength equation) ^ 2 ≤
            20 ^ 2 := Nat.pow_le_pow_left hEquation 2
      norm_num at hSquare
      simp only [List.length_cons]
      omega

theorem executableSourceResidualPolynomial_coefficientL1_le
    (problem : BoundedETRINVInstance) (tailLength : ℕ) :
    executableCoefficientL1
        (executableSourceResidualPolynomial problem tailLength) ≤
      400 * problem.equationCount := by
  unfold executableSourceResidualPolynomial
  simpa using executableSourceResidualList_coefficientL1_le
    problem tailLength (List.ofFn problem.equation)

theorem executableChainCoordinate_coefficientL1
    (problem : BoundedETRINVInstance) (tailLength : ℕ)
    (coordinate : Fin (tailLength + 1)) :
    executableCoefficientL1
      (executableChainCoordinate problem tailLength coordinate) = 1 := by
  refine Fin.cases ?_ (fun tail => ?_) coordinate <;>
    simp [executableChainCoordinate, executableCoefficientL1,
      executableConstantMonomial, executableVariableMonomial]

theorem executableContractionResidual_coefficientL1
    (problem : BoundedETRINVInstance) (tailLength : ℕ)
    (step : Fin tailLength) :
    executableCoefficientL1
      (executableContractionResidual problem tailLength step) = 3 := by
  rw [executableContractionResidual, executableCoefficientL1_append,
    executableCoefficientL1_scale, executableCoefficientL1_scale,
    executableCoefficientL1_square,
    executableChainCoordinate_coefficientL1,
    executableChainCoordinate_coefficientL1]
  norm_num

theorem executableContractionPenalty_coefficientL1
    (problem : BoundedETRINVInstance) (tailLength : ℕ) :
    executableCoefficientL1
      (executableContractionPenalty problem tailLength) = 9 * tailLength := by
  unfold executableContractionPenalty
  rw [executableCoefficientL1_flatMap]
  change
    ((List.ofFn fun step : Fin tailLength =>
      squareExecutablePolynomial
        (executableContractionResidual problem tailLength step)).map
      executableCoefficientL1).sum = _
  rw [List.map_ofFn, List.sum_ofFn]
  simp [executableContractionResidual_coefficientL1]
  omega

theorem executableStrictifierPolynomial_coefficientL1_le
    (problem : BoundedETRINVInstance) (tailLength : ℕ) :
    executableCoefficientL1
        (executableStrictifierPolynomial problem tailLength) ≤
      800 * problem.equationCount + 9 * tailLength ^ 2 + 2 := by
  unfold executableStrictifierPolynomial
  rw [executableCoefficientL1_append,
    executableCoefficientL1_append,
    executableCoefficientL1_scale,
    executableCoefficientL1_scale,
    executableCoefficientL1_scale,
    executableCoefficientL1_square,
    executableContractionPenalty_coefficientL1]
  have hSource := executableSourceResidualPolynomial_coefficientL1_le
    problem tailLength
  have hTerminal : executableCoefficientL1
      (executableChainCoordinate problem tailLength (Fin.last tailLength)) = 1 := by
    exact executableChainCoordinate_coefficientL1
      problem tailLength (Fin.last tailLength)
  rw [hTerminal]
  norm_num
  nlinarith

end PhonologicalCalculus.MaxEnt
