import PhonologicalCalculus.MaxEnt.ETRTagReductionComplete
import Mathlib.Data.List.Defs
import Mathlib.Data.Nat.Size
import Mathlib.Tactic

/-!
# Executable finite encodings and complexity interfaces

This module separates two notions that must not be conflated:

* a concrete finite encoding;
* a deterministic evaluator with a declared charge in a finite list model.

It also replaces the formerly arbitrary compact-gap exponent and contraction
length by the explicit formulas used by the bounded-ETR construction.  The
only remaining analytic premise is the stated compact integer-quartic minimum
bound.  No target-specific semantic fact is placed in that premise.
-/

namespace PhonologicalCalculus.MaxEnt

open Finset

/-! ## Self-delimiting finite encodings -/

/-- Unary, self-delimiting encoding of a natural number. -/
def encodeNatUnary (value : ℕ) : List Bool :=
  List.replicate value true ++ [false]

@[simp]
theorem encodeNatUnary_length (value : ℕ) :
    (encodeNatUnary value).length = value + 1 := by
  simp [encodeNatUnary]

theorem encodeNatUnary_injective : Function.Injective encodeNatUnary := by
  intro first second h
  have hLength := congrArg List.length h
  simp only [encodeNatUnary_length] at hLength
  omega

/-- Two-bit constructor tag followed by unary variable indices. -/
def encodeBoundedETRINVEquation {variableCount : ℕ}
    (equation : BoundedETRINVEquation variableCount) : List Bool :=
  match equation with
  | .unit x => false :: false :: encodeNatUnary x.val
  | .add x y z =>
      false :: true ::
        (encodeNatUnary x.val ++ encodeNatUnary y.val ++ encodeNatUnary z.val)
  | .inverse x y =>
      true :: false :: (encodeNatUnary x.val ++ encodeNatUnary y.val)

/-- Concrete source encoding: declared dimensions followed by every equation
in canonical finite-index order. -/
def encodeBoundedETRINVInstance
    (problem : BoundedETRINVInstance) : List Bool :=
  encodeNatUnary problem.variableCount ++
    encodeNatUnary problem.equationCount ++
    (List.ofFn problem.equation).flatMap encodeBoundedETRINVEquation

theorem encodeBoundedETRINVInstance_length_positive
    (problem : BoundedETRINVInstance) :
    0 < (encodeBoundedETRINVInstance problem).length := by
  simp [encodeBoundedETRINVInstance]

/-! ## Exact explicit compact-gap parameters -/

/-- Dimension used by the compact polynomial bound.  Low-dimensional source
instances are padded by unused coordinates so that the imported theorem's
dimension hypothesis is met without changing the residual objective. -/
def explicitPaddedDimension (problem : BoundedETRINVInstance) : ℕ :=
  max 2 problem.variableCount

/-- Integer height envelope for the residual polynomial. -/
def explicitResidualHeight (problem : BoundedETRINVInstance) : ℕ :=
  max (400 * problem.equationCount)
    (6 * explicitPaddedDimension problem)

/-- Exponent in the explicit dyadic compact minimum bound. -/
def explicitGapExponent (problem : BoundedETRINVInstance) : ℕ :=
  explicitPaddedDimension problem * 8 ^ explicitPaddedDimension problem *
    (4 + 2 * explicitPaddedDimension problem +
      Nat.size (explicitResidualHeight problem))

/-- Canonical strictifier-tail length computed from the explicit exponent. -/
def explicitChainLength (problem : BoundedETRINVInstance) : ℕ :=
  Nat.size (explicitGapExponent problem + 3)

theorem explicitResidualHeight_positive
    (problem : BoundedETRINVInstance) :
    0 < explicitResidualHeight problem := by
  unfold explicitResidualHeight
  have hDimension : 2 ≤ explicitPaddedDimension problem := by
    unfold explicitPaddedDimension
    omega
  omega

theorem explicitPaddedDimension_at_least_two
    (problem : BoundedETRINVInstance) :
    2 ≤ explicitPaddedDimension problem := by
  unfold explicitPaddedDimension
  omega

theorem explicitPaddedDimension_source_le
    (problem : BoundedETRINVInstance) :
    problem.variableCount ≤ explicitPaddedDimension problem := by
  unfold explicitPaddedDimension
  omega

theorem explicitPaddedDimension_upper_bound
    (problem : BoundedETRINVInstance) :
    explicitPaddedDimension problem ≤ problem.variableCount + 2 := by
  unfold explicitPaddedDimension
  omega

theorem explicitResidualHeight_paddedDimension_bound
    (problem : BoundedETRINVInstance) :
    6 * explicitPaddedDimension problem ≤ explicitResidualHeight problem := by
  unfold explicitResidualHeight
  omega

theorem explicitResidualHeight_variable_bound
    (problem : BoundedETRINVInstance) :
    6 * problem.variableCount ≤ explicitResidualHeight problem := by
  have hSource := explicitPaddedDimension_source_le problem
  have hPadded := explicitResidualHeight_paddedDimension_bound problem
  omega

theorem explicitResidualHeight_equation_bound
    (problem : BoundedETRINVInstance) :
    400 * problem.equationCount ≤ explicitResidualHeight problem := by
  unfold explicitResidualHeight
  omega

theorem nat_size_le_self (value : ℕ) : Nat.size value ≤ value := by
  cases value with
  | zero => simp
  | succ value =>
      apply Nat.size_le.mpr
      exact Nat.lt_two_pow_self

theorem nat_size_mul_le (first second : ℕ) :
    Nat.size (first * second) ≤ Nat.size first + Nat.size second := by
  apply Nat.size_le.mpr
  calc
    first * second < 2 ^ Nat.size first * 2 ^ Nat.size second := by
      nlinarith [Nat.lt_size_self first, Nat.lt_size_self second]
    _ = 2 ^ (Nat.size first + Nat.size second) := by
      rw [pow_add]

theorem nat_size_add_le (first second : ℕ) :
    Nat.size (first + second) ≤
      Nat.size first + Nat.size second + 1 := by
  apply Nat.size_le.mpr
  have hFirst := Nat.lt_size_self first
  have hSecond := Nat.lt_size_self second
  have hOneFirst : 1 ≤ 2 ^ Nat.size first := by
    exact Nat.one_le_pow _ _ (by norm_num)
  have hOneSecond : 1 ≤ 2 ^ Nat.size second := by
    exact Nat.one_le_pow _ _ (by norm_num)
  calc
    first + second < 2 ^ Nat.size first + 2 ^ Nat.size second :=
      Nat.add_lt_add hFirst hSecond
    _ ≤ 2 ^ Nat.size first * 2 ^ Nat.size second * 2 := by
      nlinarith
    _ = 2 ^ (Nat.size first + Nat.size second + 1) := by
      rw [pow_add, pow_succ]
      ring

theorem explicitResidualHeight_upper_bound
    (problem : BoundedETRINVInstance) :
    explicitResidualHeight problem ≤
      400 * problem.equationCount + 6 * problem.variableCount + 12 := by
  have hDimension := explicitPaddedDimension_upper_bound problem
  unfold explicitResidualHeight
  omega

theorem explicitGapExponent_size_linear
    (problem : BoundedETRINVInstance) :
    Nat.size (explicitGapExponent problem) ≤
      13 * problem.variableCount + 400 * problem.equationCount + 32 := by
  let n := problem.variableCount
  let q := problem.equationCount
  let padded := explicitPaddedDimension problem
  let height := explicitResidualHeight problem
  let factor := 4 + 2 * padded + Nat.size height
  have hPadded : padded ≤ n + 2 := by
    simpa [n, padded] using explicitPaddedDimension_upper_bound problem
  have hHeight : height ≤ 400 * q + 6 * n + 12 := by
    simpa [n, q, height] using explicitResidualHeight_upper_bound problem
  have hHeightSize : Nat.size height ≤ 400 * q + 6 * n + 12 :=
    (nat_size_le_self height).trans hHeight
  have hFactor : factor ≤ 8 * n + 400 * q + 20 := by
    dsimp [factor]
    omega
  have hPow : Nat.size (8 ^ padded) = 3 * padded + 1 := by
    rw [show 8 ^ padded = 2 ^ (3 * padded) by
      rw [show 8 = 2 ^ 3 by norm_num, ← pow_mul]]
    simp [Nat.size_pow]
  calc
    Nat.size (explicitGapExponent problem) =
        Nat.size (padded * 8 ^ padded * factor) := by
      rfl
    _ ≤ Nat.size (padded * 8 ^ padded) + Nat.size factor :=
      nat_size_mul_le _ _
    _ ≤ (Nat.size padded + Nat.size (8 ^ padded)) + Nat.size factor := by
      exact Nat.add_le_add_right
        (nat_size_mul_le padded (8 ^ padded)) _
    _ ≤ (padded + (3 * padded + 1)) + factor := by
      rw [hPow]
      have hn := nat_size_le_self padded
      have hf := nat_size_le_self factor
      omega
    _ ≤ 13 * n + 400 * q + 32 := by omega

theorem explicitChainLength_linear
    (problem : BoundedETRINVInstance) :
    explicitChainLength problem ≤
      13 * problem.variableCount + 400 * problem.equationCount + 35 := by
  unfold explicitChainLength
  calc
    Nat.size (explicitGapExponent problem + 3) ≤
        Nat.size (explicitGapExponent problem) + Nat.size 3 + 1 :=
      nat_size_add_le _ _
    _ ≤ 13 * problem.variableCount + 400 * problem.equationCount + 35 := by
      have h := explicitGapExponent_size_linear problem
      have hThree : Nat.size 3 = 2 := rfl
      rw [hThree]
      omega

theorem explicitChainLength_sourceSize_bound
    (problem : BoundedETRINVInstance) :
    explicitChainLength problem ≤
      412 * boundedETRINVCodeSize problem := by
  have h := explicitChainLength_linear problem
  unfold boundedETRINVCodeSize
  omega

/-! ## Exact low-dimensional padding bridge -/

def explicitPaddedProjection
    (problem : BoundedETRINVInstance)
    (point : Fin (explicitPaddedDimension problem) → ℝ) :
    Fin problem.variableCount → ℝ :=
  fun coordinate => point
    (Fin.castLE (explicitPaddedDimension_source_le problem) coordinate)

def explicitPadSourcePoint
    (problem : BoundedETRINVInstance)
    (source : Fin problem.variableCount → ℝ) :
    Fin (explicitPaddedDimension problem) → ℝ :=
  fun coordinate =>
    if hCoordinate : coordinate.val < problem.variableCount then
      source ⟨coordinate.val, hCoordinate⟩
    else 0

def ExplicitPaddedCubePoint
    (problem : BoundedETRINVInstance)
    (point : Fin (explicitPaddedDimension problem) → ℝ) : Prop :=
  ∀ coordinate, 0 ≤ point coordinate ∧ point coordinate ≤ 1

noncomputable def explicitPaddedResidualPolynomial
    (problem : BoundedETRINVInstance) :
    MvPolynomial (Fin (explicitPaddedDimension problem)) ℤ :=
  MvPolynomial.rename
    (Fin.castLE (explicitPaddedDimension_source_le problem))
    problem.sourceResidualPolynomial

def explicitPaddedResidual
    (problem : BoundedETRINVInstance)
    (point : Fin (explicitPaddedDimension problem) → ℝ) : ℝ :=
  problem.sourceResidualSum (explicitPaddedProjection problem point)

theorem explicitPaddedResidualPolynomial_eval
    (problem : BoundedETRINVInstance)
    (point : Fin (explicitPaddedDimension problem) → ℝ) :
    MvPolynomial.eval₂ (Int.castRingHom ℝ) point
        (explicitPaddedResidualPolynomial problem) =
      explicitPaddedResidual problem point := by
  rw [explicitPaddedResidualPolynomial, MvPolynomial.eval₂_rename,
    eval_sourceResidualPolynomial]
  rfl

theorem explicitPaddedResidualPolynomial_degree_le_four
    (problem : BoundedETRINVInstance) :
    (explicitPaddedResidualPolynomial problem).totalDegree ≤ 4 := by
  exact (MvPolynomial.totalDegree_rename_le
    (Fin.castLE (explicitPaddedDimension_source_le problem))
    problem.sourceResidualPolynomial).trans
      (sourceResidualPolynomial_totalDegree_le_four problem)

theorem explicitPaddedResidualPolynomial_coefficientL1
    (problem : BoundedETRINVInstance) :
    coefficientL1 (explicitPaddedResidualPolynomial problem) =
      coefficientL1 problem.sourceResidualPolynomial := by
  unfold explicitPaddedResidualPolynomial
  apply coefficientL1_rename_injective
  intro first second hEqual
  apply Fin.ext
  exact congrArg
    (fun coordinate : Fin (explicitPaddedDimension problem) => coordinate.val)
    hEqual

theorem explicitPaddedResidualPolynomial_coefficientL1_le_height
    (problem : BoundedETRINVInstance) :
    coefficientL1 (explicitPaddedResidualPolynomial problem) ≤
      explicitResidualHeight problem := by
  rw [explicitPaddedResidualPolynomial_coefficientL1]
  exact (sourceResidualPolynomial_coefficientL1_le problem).trans
    (explicitResidualHeight_equation_bound problem)

@[simp]
theorem explicitPaddedProjection_padSourcePoint
    (problem : BoundedETRINVInstance)
    (source : Fin problem.variableCount → ℝ) :
    explicitPaddedProjection problem
      (explicitPadSourcePoint problem source) = source := by
  funext coordinate
  simp [explicitPaddedProjection, explicitPadSourcePoint,
    Fin.castLE]

theorem explicitPaddedProjection_cube
    (problem : BoundedETRINVInstance)
    {point : Fin (explicitPaddedDimension problem) → ℝ}
    (hPoint : ExplicitPaddedCubePoint problem point) :
    problem.IsCubePoint (explicitPaddedProjection problem point) := by
  intro coordinate
  exact hPoint
    (Fin.castLE (explicitPaddedDimension_source_le problem) coordinate)

theorem explicitPadSourcePoint_cube
    (problem : BoundedETRINVInstance)
    {source : Fin problem.variableCount → ℝ}
    (hSource : problem.IsCubePoint source) :
    ExplicitPaddedCubePoint problem
      (explicitPadSourcePoint problem source) := by
  intro coordinate
  by_cases hCoordinate : coordinate.val < problem.variableCount
  · simpa [explicitPadSourcePoint, hCoordinate] using
      hSource ⟨coordinate.val, hCoordinate⟩
  · simp [explicitPadSourcePoint, hCoordinate]

@[simp]
theorem explicitPaddedResidual_padSourcePoint
    (problem : BoundedETRINVInstance)
    (source : Fin problem.variableCount → ℝ) :
    explicitPaddedResidual problem
        (explicitPadSourcePoint problem source) =
      problem.sourceResidualSum source := by
  simp [explicitPaddedResidual]

theorem explicitPaddedResidual_zero_iff
    (problem : BoundedETRINVInstance) :
    (∃ point, ExplicitPaddedCubePoint problem point ∧
        explicitPaddedResidual problem point = 0) ↔
      ∃ source, problem.IsCubePoint source ∧
        problem.sourceResidualSum source = 0 := by
  constructor
  · rintro ⟨point, hPoint, hZero⟩
    exact ⟨explicitPaddedProjection problem point,
      explicitPaddedProjection_cube problem hPoint, hZero⟩
  · rintro ⟨source, hSource, hZero⟩
    exact ⟨explicitPadSourcePoint problem source,
      explicitPadSourcePoint_cube problem hSource, by simpa using hZero⟩

/-- Analytic premise for the project residual after explicit padding.  Its
hypotheses expose the dimension and height requirements of the compact
integer-quartic minimum theorem used by the reduction. -/
structure ExplicitCompactMinimumFoundation : Prop where
  paddedLowerBound : ∀ problem : BoundedETRINVInstance,
    2 ≤ explicitPaddedDimension problem →
    (explicitPaddedResidualPolynomial problem).totalDegree ≤ 4 →
    coefficientL1 (explicitPaddedResidualPolynomial problem) ≤
      explicitResidualHeight problem →
    6 * explicitPaddedDimension problem ≤ explicitResidualHeight problem →
    (¬ ∃ point, ExplicitPaddedCubePoint problem point ∧
        explicitPaddedResidual problem point = 0) →
      ∀ point, ExplicitPaddedCubePoint problem point →
        dyadicCompactGap (explicitGapExponent problem) ≤
          explicitPaddedResidual problem point

theorem ExplicitCompactMinimumFoundation.lowerBound
    (foundation : ExplicitCompactMinimumFoundation)
    (problem : BoundedETRINVInstance)
    (hNoZero : ¬ ∃ source, problem.IsCubePoint source ∧
      problem.sourceResidualSum source = 0) :
    ∀ source, problem.IsCubePoint source →
      dyadicCompactGap (explicitGapExponent problem) ≤
        problem.sourceResidualSum source := by
  have hNoPaddedZero : ¬ ∃ point,
      ExplicitPaddedCubePoint problem point ∧
        explicitPaddedResidual problem point = 0 := by
    intro hPadded
    exact hNoZero (explicitPaddedResidual_zero_iff problem |>.mp hPadded)
  intro source hSource
  have hBound := foundation.paddedLowerBound problem
    (explicitPaddedDimension_at_least_two problem)
    (explicitPaddedResidualPolynomial_degree_le_four problem)
    (explicitPaddedResidualPolynomial_coefficientL1_le_height problem)
    (explicitResidualHeight_paddedDimension_bound problem)
    hNoPaddedZero
    (explicitPadSourcePoint problem source)
    (explicitPadSourcePoint_cube problem hSource)
  simpa using hBound

/-- The explicit formula instantiates the semantic compact-gap interface;
its bit-length bound is proved locally. -/
def explicitCompactGapFoundation
    (foundation : ExplicitCompactMinimumFoundation) : CompactGapFoundation where
  gapExponent := explicitGapExponent
  gapIfNoZero := foundation.lowerBound
  chainLengthCoefficient := 412
  chainLengthDegree := 1
  chainLengthCoefficient_positive := by norm_num
  chainLength_bound := by
    intro problem
    simpa [explicitChainLength, CompactGapFoundation.chainLength, pow_one]
      using explicitChainLength_sourceSize_bound problem

@[simp]
theorem explicitCompactGapFoundation_chainLength
    (foundation : ExplicitCompactMinimumFoundation)
    (problem : BoundedETRINVInstance) :
    (explicitCompactGapFoundation foundation).chainLength problem =
      explicitChainLength problem := rfl

theorem explicit_compiler_universalOrder_iff_unsatisfiable
    (foundation : ExplicitCompactMinimumFoundation)
    (problem : BoundedETRINVInstance) :
    (compileGapProvedBoundedETRINV
        (explicitCompactGapFoundation foundation) problem).universalOrder ↔
      ¬ problem.Satisfiable :=
  compileGapProvedBoundedETRINV_correct
    (explicitCompactGapFoundation foundation) problem

/-! ## Charge-bearing deterministic evaluators -/

/-- A returned value paired with a declared unit-cost arithmetic or list-scan
charge.  This field is not a standard-machine running time. -/
structure Costed (Result : Type*) where
  value : Result
  steps : ℕ
  deriving Repr

namespace Costed

def pure (value : Result) : Costed Result := ⟨value, 0⟩

def bind (run : Costed Result) (next : Result → Costed Output) : Costed Output :=
  let continuation := next run.value
  ⟨continuation.value, run.steps + continuation.steps⟩

@[simp]
theorem pure_value (value : Result) : (pure value).value = value := rfl

@[simp]
theorem bind_value (run : Costed Result) (next : Result → Costed Output) :
    (bind run next).value = (next run.value).value := rfl

@[simp]
theorem bind_steps (run : Costed Result) (next : Result → Costed Output) :
    (bind run next).steps = run.steps + (next run.value).steps := rfl

end Costed

/-- Executable computation of the strictifier parameters, with a declared
unit-cost arithmetic charge. -/
def computeExplicitStrictifierParameters
    (problem : BoundedETRINVInstance) : Costed (ℕ × ℕ × ℕ) :=
  ⟨(explicitResidualHeight problem, explicitGapExponent problem,
      explicitChainLength problem),
    20 + 8 * problem.variableCount + 8 * problem.equationCount⟩

@[simp]
theorem computeExplicitStrictifierParameters_value
    (problem : BoundedETRINVInstance) :
    (computeExplicitStrictifierParameters problem).value =
      (explicitResidualHeight problem, explicitGapExponent problem,
        explicitChainLength problem) := rfl

theorem computeExplicitStrictifierParameters_steps_bound
    (problem : BoundedETRINVInstance) :
    (computeExplicitStrictifierParameters problem).steps ≤
      20 * boundedETRINVCodeSize problem := by
  unfold computeExplicitStrictifierParameters boundedETRINVCodeSize
  dsimp
  omega

/-! ## Executable Boolean-row verifier -/

/-- A list representation of a finite duplicate-free `{1,2}` residual table.
Proof fields prove that conversion to finite sets loses no row identity. -/
structure ExecutableOneTwoOrderCode where
  coordinateCount : ℕ
  positiveRows : List (Fin coordinateCount → Bool)
  negativeRows : List (Fin coordinateCount → Bool)
  positive_nodup : positiveRows.Nodup
  negative_nodup : negativeRows.Nodup
  rows_disjoint : List.Disjoint positiveRows negativeRows

def executableRowActive {coordinateCount : ℕ}
    (row assignment : Fin coordinateCount → Bool) : Bool :=
  decide (∀ coordinate, row coordinate = true → assignment coordinate = true)

def executableActiveRowCount {coordinateCount : ℕ}
    (rows : List (Fin coordinateCount → Bool))
    (assignment : Fin coordinateCount → Bool) : ℕ :=
  (rows.filter (fun row => executableRowActive row assignment)).length

/-- Deterministic row-by-coordinate scan.  The charge is exact for the declared
list-scan model: one setup unit plus one coordinate test per row. -/
def executableOneTwoNegativeVerifier
    (input : ExecutableOneTwoOrderCode)
    (proofWitness : Fin input.coordinateCount → Bool) : Costed Bool :=
  ⟨decide
      (executableActiveRowCount input.positiveRows proofWitness <
        executableActiveRowCount input.negativeRows proofWitness),
    1 + (input.positiveRows.length + input.negativeRows.length) *
      (input.coordinateCount + 1)⟩

@[simp]
theorem executableRowActive_eq_true_iff {coordinateCount : ℕ}
    (row assignment : Fin coordinateCount → Bool) :
    executableRowActive row assignment = true ↔
      residualRowActive row assignment := by
  simp [executableRowActive, residualRowActive]

/-- Finite-set semantics of an executable row table. -/
noncomputable def ExecutableOneTwoOrderCode.toOrderInstance
    (input : ExecutableOneTwoOrderCode) :
    DuplicateFreeOneTwoOrderInstance (Fin input.coordinateCount) := by
  classical
  refine
    { positiveRows := input.positiveRows.toFinset
      negativeRows := input.negativeRows.toFinset
      rows_disjoint := ?_ }
  rw [Finset.disjoint_left]
  intro row hPositive hNegative
  simp only [List.mem_toFinset] at hPositive hNegative
  exact input.rows_disjoint hPositive hNegative

theorem executableActiveRowCount_eq_finset
    {coordinateCount : ℕ}
    (rows : List (Fin coordinateCount → Bool)) (hRows : rows.Nodup)
    (assignment : Fin coordinateCount → Bool) :
    executableActiveRowCount rows assignment =
      activeResidualRowCount rows.toFinset assignment := by
  classical
  unfold executableActiveRowCount activeResidualRowCount
  have hFiltered :
      (rows.filter (fun row => executableRowActive row assignment)).toFinset =
        rows.toFinset.filter (fun row => residualRowActive row assignment) := by
    ext row
    simp [executableRowActive_eq_true_iff]
  calc
    (rows.filter (fun row => executableRowActive row assignment)).length =
        (rows.filter (fun row => executableRowActive row assignment)).toFinset.card := by
      symm
      exact List.toFinset_card_of_nodup (hRows.filter _)
    _ = _ := congrArg Finset.card hFiltered

theorem executableOneTwoNegativeVerifier_value_iff
    (input : ExecutableOneTwoOrderCode)
    (proofWitness : Fin input.coordinateCount → Bool) :
    (executableOneTwoNegativeVerifier input proofWitness).value = true ↔
      input.toOrderInstance.negativeBooleanWitness proofWitness := by
  classical
  unfold executableOneTwoNegativeVerifier
  dsimp
  rw [decide_eq_true_eq,
    executableActiveRowCount_eq_finset input.positiveRows
      input.positive_nodup proofWitness,
    executableActiveRowCount_eq_finset input.negativeRows
      input.negative_nodup proofWitness]
  exact (negativeBooleanWitness_iff_activeRowCount_lt
    input.toOrderInstance proofWitness).symm

def executableOneTwoOrderCodeSize (input : ExecutableOneTwoOrderCode) : ℕ :=
  (input.coordinateCount + 1) *
    (input.positiveRows.length + input.negativeRows.length + 1)

theorem executableOneTwoNegativeVerifier_steps_le_tableSize
    (input : ExecutableOneTwoOrderCode)
    (proofWitness : Fin input.coordinateCount → Bool) :
    (executableOneTwoNegativeVerifier input proofWitness).steps ≤
      executableOneTwoOrderCodeSize input := by
  unfold executableOneTwoNegativeVerifier executableOneTwoOrderCodeSize
  dsimp
  ring_nf
  omega

end PhonologicalCalculus.MaxEnt
