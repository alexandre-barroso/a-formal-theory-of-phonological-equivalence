import PhonologicalCalculus.MaxEnt.SparseLaurentCarrier
import PhonologicalCalculus.MaxEnt.SparseCompiler
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-!
# Exact normalizer-by-relation classification

This module formalizes the finite algebraic cells of `MAX-G4` at their
declared scope: complete nonempty finite candidate ledgers, positive rational
base masses, nonnegative integer violation rows, and the full nonnegative
weight orthant. Candidate labels are never quotiented, so repeated rows retain
their full mass and multiplicity.

The imported complexity classifications are kept separate from the locally
proved compiler requirements. This mirrors the public theorem's explicit
trusted-foundation boundary instead of introducing a project-specific
unproved declaration.
-/

namespace PhonologicalCalculus.MaxEnt

open MvPolynomial Set

universe uConstraint uCandidate

/-! ## Complete finite ledgers and weight semantics -/

/-- A complete finite MaxEnt ledger at the scope used by `MAX-G4`.
Finiteness and nonemptiness are supplied by typeclass instances on the
candidate type; positivity is a proof-bearing field. -/
structure CompleteFiniteLedger
    (J : Type uConstraint) (C : Type uCandidate) where
  baseMass : C → ℚ
  row : C → J → ℕ
  baseMass_pos : ∀ candidate, 0 < baseMass candidate

/-- Weighted violation cost of a candidate. -/
noncomputable def weightCost
    {J : Type uConstraint} {C : Type uCandidate} [Fintype J]
    (ledger : CompleteFiniteLedger J C) (weight : J → ℝ)
    (candidate : C) : ℝ :=
  ∑ coordinate, weight coordinate * ledger.row candidate coordinate

/-- Positive unnormalized exponential mass of one candidate. -/
noncomputable def exponentialCandidateMass
    {J : Type uConstraint} {C : Type uCandidate} [Fintype J]
    (ledger : CompleteFiniteLedger J C) (weight : J → ℝ)
    (candidate : C) : ℝ :=
  (ledger.baseMass candidate : ℝ) *
    Real.exp (-weightCost ledger weight candidate)

/-- Complete finite partition function. -/
noncomputable def exponentialPartition
    {J : Type uConstraint} {C : Type uCandidate}
    [Fintype J] [Fintype C]
    (ledger : CompleteFiniteLedger J C) (weight : J → ℝ) : ℝ :=
  ∑ candidate, exponentialCandidateMass ledger weight candidate

/-- Normalized candidate probability. -/
noncomputable def exponentialCandidateProbability
    {J : Type uConstraint} {C : Type uCandidate}
    [Fintype J] [Fintype C]
    (ledger : CompleteFiniteLedger J C) (weight : J → ℝ)
    (candidate : C) : ℝ :=
  exponentialCandidateMass ledger weight candidate /
    exponentialPartition ledger weight

theorem exponentialCandidateMass_pos
    {J : Type uConstraint} {C : Type uCandidate} [Fintype J]
    (ledger : CompleteFiniteLedger J C) (weight : J → ℝ)
    (candidate : C) :
    0 < exponentialCandidateMass ledger weight candidate := by
  exact mul_pos (Rat.cast_pos.2 (ledger.baseMass_pos candidate))
    (Real.exp_pos _)

theorem exponentialPartition_pos
    {J : Type uConstraint} {C : Type uCandidate}
    [Fintype J] [Fintype C] [Nonempty C]
    (ledger : CompleteFiniteLedger J C) (weight : J → ℝ) :
    0 < exponentialPartition ledger weight := by
  classical
  apply Finset.sum_pos'
  · intro candidate _
    exact (exponentialCandidateMass_pos ledger weight candidate).le
  · let candidate : C := Classical.choice (inferInstance : Nonempty C)
    exact ⟨candidate, Finset.mem_univ candidate,
      exponentialCandidateMass_pos ledger weight candidate⟩

/-- Full nonnegative weight orthant. -/
def IsNonnegativeWeight {J : Type*} (weight : J → ℝ) : Prop :=
  ∀ coordinate, 0 ≤ weight coordinate

/-- Coordinatewise domination, oriented so that the dominating row has no
larger probability under every nonnegative weight vector. -/
def RowDominates {J : Type*} (first second : J → ℕ) : Prop :=
  ∀ coordinate, second coordinate ≤ first coordinate

/-- Activity coordinates corresponding to a real weight vector. -/
noncomputable def activityOfWeight {J : Type*} (weight : J → ℝ) : J → ℝ :=
  fun coordinate => Real.exp (-weight coordinate)

theorem activityOfWeight_pos {J : Type*} (weight : J → ℝ) :
    ∀ coordinate, 0 < activityOfWeight weight coordinate := by
  intro coordinate
  exact Real.exp_pos _

theorem activityOfWeight_le_one {J : Type*} (weight : J → ℝ)
    (hWeight : IsNonnegativeWeight weight) :
    ∀ coordinate, activityOfWeight weight coordinate ≤ 1 := by
  intro coordinate
  rw [activityOfWeight, ← Real.exp_zero]
  exact Real.exp_le_exp.mpr (neg_nonpos.mpr (hWeight coordinate))

theorem activityOfWeight_monomial_eq_exp_neg_cost
    {J : Type uConstraint} {C : Type uCandidate} [Fintype J]
    (ledger : CompleteFiniteLedger J C) (weight : J → ℝ)
    (candidate : C) :
    laurentMonomial
        (fun coordinate => (ledger.row candidate coordinate : ℤ))
        (activityOfWeight weight) =
      Real.exp (-weightCost ledger weight candidate) := by
  classical
  unfold laurentMonomial activityOfWeight weightCost
  calc
    (∏ coordinate,
        Real.exp (-weight coordinate) ^ ledger.row candidate coordinate) =
        ∏ coordinate, Real.exp
          (-(weight coordinate * ledger.row candidate coordinate)) := by
      apply Finset.prod_congr rfl
      intro coordinate _
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    _ = Real.exp
        (∑ coordinate,
          -(weight coordinate * ledger.row candidate coordinate)) := by
      rw [Real.exp_sum]
    _ = Real.exp
        (-∑ coordinate,
          weight coordinate * ledger.row candidate coordinate) := by
      rw [Finset.sum_neg_distrib]

theorem activityProbability_eq_exponentialProbability
    {J : Type uConstraint} {C : Type uCandidate}
    [Fintype J] [Fintype C]
    (ledger : CompleteFiniteLedger J C) (weight : J → ℝ)
    (candidate : C) :
    rationalNamedCandidateProbability ledger.baseMass
        (fun c coordinate => ledger.row c coordinate)
        candidate (activityOfWeight weight) =
      exponentialCandidateProbability ledger weight candidate := by
  classical
  unfold rationalNamedCandidateProbability exponentialCandidateProbability
  unfold candidateMass partitionMass exponentialCandidateMass
  rw [activityOfWeight_monomial_eq_exp_neg_cost ledger weight candidate]
  congr 1
  apply Finset.sum_congr rfl
  intro other _
  unfold candidateMass exponentialCandidateMass
  rw [activityOfWeight_monomial_eq_exp_neg_cost ledger weight other]

/-- Inverse coordinate change on the positive physical activity cube. -/
noncomputable def weightOfActivity {J : Type*}
    (activity : J → ℝ) : J → ℝ :=
  fun coordinate => -Real.log (activity coordinate)

theorem activityOfWeight_weightOfActivity {J : Type*}
    (activity : J → ℝ) (hActivity : ∀ coordinate, 0 < activity coordinate) :
    activityOfWeight (weightOfActivity activity) = activity := by
  funext coordinate
  simp [activityOfWeight, weightOfActivity,
    Real.exp_log (hActivity coordinate)]

theorem weightOfActivity_nonnegative {J : Type*}
    (activity : J → ℝ)
    (hActivity : ∀ coordinate,
      0 < activity coordinate ∧ activity coordinate ≤ 1) :
    IsNonnegativeWeight (weightOfActivity activity) := by
  intro coordinate
  exact neg_nonneg.mpr
    (Real.log_nonpos (hActivity coordinate).1.le (hActivity coordinate).2)

/-- A basis weight belongs to the full nonnegative orthant. -/
def coordinateWeight {J : Type*} [DecidableEq J]
    (selected : J) : J → ℝ :=
  fun coordinate => if coordinate = selected then 1 else 0

theorem coordinateWeight_nonnegative {J : Type*} [DecidableEq J]
    (selected : J) : IsNonnegativeWeight (coordinateWeight selected) := by
  intro coordinate
  simp only [coordinateWeight]
  split_ifs <;> norm_num

theorem weightCost_coordinateWeight
    {J : Type uConstraint} {C : Type uCandidate}
    [Fintype J] [DecidableEq J]
    (ledger : CompleteFiniteLedger J C) (candidate : C) (selected : J) :
    weightCost ledger (coordinateWeight selected) candidate =
      ledger.row candidate selected := by
  classical
  simp [weightCost, coordinateWeight]

theorem probability_eq_iff_mass_eq
    {J : Type uConstraint} {C : Type uCandidate}
    [Fintype J] [Fintype C] [Nonempty C]
    (ledger : CompleteFiniteLedger J C) (weight : J → ℝ)
    (first second : C) :
    exponentialCandidateProbability ledger weight first =
        exponentialCandidateProbability ledger weight second ↔
      exponentialCandidateMass ledger weight first =
        exponentialCandidateMass ledger weight second := by
  have hPartition := exponentialPartition_pos ledger weight
  exact div_left_inj' (ne_of_gt hPartition)

theorem probability_le_iff_mass_le
    {J : Type uConstraint} {C : Type uCandidate}
    [Fintype J] [Fintype C] [Nonempty C]
    (ledger : CompleteFiniteLedger J C) (weight : J → ℝ)
    (first second : C) :
    exponentialCandidateProbability ledger weight first ≤
        exponentialCandidateProbability ledger weight second ↔
      exponentialCandidateMass ledger weight first ≤
        exponentialCandidateMass ledger weight second := by
  unfold exponentialCandidateProbability
  exact div_le_div_iff_of_pos_right (exponentialPartition_pos ledger weight)

theorem equal_baseMass_mass_eq_iff_cost_eq
    {J : Type uConstraint} {C : Type uCandidate} [Fintype J]
    (ledger : CompleteFiniteLedger J C) (weight : J → ℝ)
    (first second : C)
    (hMass : ledger.baseMass first = ledger.baseMass second) :
    exponentialCandidateMass ledger weight first =
        exponentialCandidateMass ledger weight second ↔
      weightCost ledger weight first = weightCost ledger weight second := by
  have hPositive : 0 < (ledger.baseMass first : ℝ) :=
    Rat.cast_pos.2 (ledger.baseMass_pos first)
  constructor
  · intro h
    have hExp : Real.exp (-weightCost ledger weight first) =
        Real.exp (-weightCost ledger weight second) := by
      apply (mul_left_cancel₀ (ne_of_gt hPositive))
      simpa [exponentialCandidateMass, hMass]
        using h
    have hNeg := Real.exp_injective hExp
    linarith
  · intro h
    simp [exponentialCandidateMass, hMass, h]

theorem equal_baseMass_mass_le_iff_cost_ge
    {J : Type uConstraint} {C : Type uCandidate} [Fintype J]
    (ledger : CompleteFiniteLedger J C) (weight : J → ℝ)
    (first second : C)
    (hMass : ledger.baseMass first = ledger.baseMass second) :
    exponentialCandidateMass ledger weight first ≤
        exponentialCandidateMass ledger weight second ↔
      weightCost ledger weight second ≤ weightCost ledger weight first := by
  have hPositive : 0 < (ledger.baseMass first : ℝ) :=
    Rat.cast_pos.2 (ledger.baseMass_pos first)
  constructor
  · intro h
    have hProduct :
        (ledger.baseMass first : ℝ) *
            Real.exp (-weightCost ledger weight first) ≤
          (ledger.baseMass first : ℝ) *
            Real.exp (-weightCost ledger weight second) := by
      simpa [exponentialCandidateMass, hMass] using h
    have hExp : Real.exp (-weightCost ledger weight first) ≤
        Real.exp (-weightCost ledger weight second) := by
      nlinarith
    have := Real.exp_le_exp.mp hExp
    linarith
  · intro h
    have hExp : Real.exp (-weightCost ledger weight first) ≤
        Real.exp (-weightCost ledger weight second) :=
      Real.exp_le_exp.mpr (by linarith)
    simpa [exponentialCandidateMass, hMass] using
      mul_le_mul_of_nonneg_left hExp hPositive.le

/-- **MAX-G4.REVERSAL.01, same-input equality cell.** For two candidates in
one complete finite ledger with equal positive base mass, equality of their
probabilities at every point of the full nonnegative weight orthant is
equivalent to identity of their complete violation rows. -/
theorem allWeightSameInputProbabilityEqual_iff_row_eq
    {J : Type uConstraint} {C : Type uCandidate}
    [Fintype J] [DecidableEq J] [Fintype C] [Nonempty C]
    (ledger : CompleteFiniteLedger J C) (first second : C)
    (hMass : ledger.baseMass first = ledger.baseMass second) :
    (∀ weight, IsNonnegativeWeight weight →
      exponentialCandidateProbability ledger weight first =
        exponentialCandidateProbability ledger weight second) ↔
      ledger.row first = ledger.row second := by
  constructor
  · intro h
    funext coordinate
    have hProbability := h (coordinateWeight coordinate)
      (coordinateWeight_nonnegative coordinate)
    have hCost := (equal_baseMass_mass_eq_iff_cost_eq ledger
      (coordinateWeight coordinate) first second hMass).1
      ((probability_eq_iff_mass_eq ledger
        (coordinateWeight coordinate) first second).1 hProbability)
    simpa [weightCost_coordinateWeight] using hCost
  · intro hRow weight _
    have hCost : weightCost ledger weight first =
        weightCost ledger weight second := by
      simp [weightCost, hRow]
    apply (probability_eq_iff_mass_eq ledger weight first second).2
    exact (equal_baseMass_mass_eq_iff_cost_eq ledger weight
      first second hMass).2 hCost

/-- **MAX-G4.REVERSAL.01, same-input order cell.** Under the same equal-mass
contract, universal weak probability order on the full nonnegative orthant is
equivalent to coordinatewise domination of the named violation rows. -/
theorem allWeightSameInputProbabilityOrder_iff_row_domination
    {J : Type uConstraint} {C : Type uCandidate}
    [Fintype J] [DecidableEq J] [Fintype C] [Nonempty C]
    (ledger : CompleteFiniteLedger J C) (first second : C)
    (hMass : ledger.baseMass first = ledger.baseMass second) :
    (∀ weight, IsNonnegativeWeight weight →
      exponentialCandidateProbability ledger weight first ≤
        exponentialCandidateProbability ledger weight second) ↔
      RowDominates (ledger.row first) (ledger.row second) := by
  constructor
  · intro h coordinate
    have hProbability := h (coordinateWeight coordinate)
      (coordinateWeight_nonnegative coordinate)
    have hCost := (equal_baseMass_mass_le_iff_cost_ge ledger
      (coordinateWeight coordinate) first second hMass).1
      ((probability_le_iff_mass_le ledger
        (coordinateWeight coordinate) first second).1 hProbability)
    exact_mod_cast (by
      simpa [weightCost_coordinateWeight] using hCost)
  · intro hDom weight hWeight
    apply (probability_le_iff_mass_le ledger weight first second).2
    apply (equal_baseMass_mass_le_iff_cost_ge ledger weight
      first second hMass).2
    unfold weightCost
    apply Finset.sum_le_sum
    intro coordinate _
    exact mul_le_mul_of_nonneg_left
      (by exact_mod_cast hDom coordinate) (hWeight coordinate)

/-! ## Registered exact reversal and tie witnesses -/

/-- Registered left-input probability with two multiplicity-distinct
competitors at violation row three. -/
def registeredReversalLeftProbability (activity : ℚ) : ℚ :=
  1 / (1 + 2 * activity ^ 3)

/-- Registered right-input probability with one competitor at row two. -/
def registeredReversalRightProbability (activity : ℚ) : ℚ :=
  1 / (1 + activity ^ 2)

/-- **MAX-G4.REVERSAL.01, exact cross-input witness.** The same named pair
reverses order between activities `3/4` and `1/4` and ties at `1/2`; all
three registered rational probabilities are computed exactly. -/
theorem max_g4_reversal_01_registered :
    registeredReversalLeftProbability (3 / 4) = 32 / 59 ∧
    registeredReversalRightProbability (3 / 4) = 16 / 25 ∧
    registeredReversalLeftProbability (3 / 4) <
      registeredReversalRightProbability (3 / 4) ∧
    registeredReversalLeftProbability (1 / 2) = 4 / 5 ∧
    registeredReversalRightProbability (1 / 2) = 4 / 5 ∧
    registeredReversalLeftProbability (1 / 4) = 32 / 33 ∧
    registeredReversalRightProbability (1 / 4) = 16 / 17 ∧
    registeredReversalRightProbability (1 / 4) <
      registeredReversalLeftProbability (1 / 4) := by
  norm_num [registeredReversalLeftProbability,
    registeredReversalRightProbability]

/-! ## Multiplicity-sensitive relative-row measures -/

/-- Integer row relative to a named candidate. -/
def relativeViolationRow
    {J : Type uConstraint} {C : Type uCandidate}
    (ledger : CompleteFiniteLedger J C) (named candidate : C) : J → ℤ :=
  fun coordinate =>
    (ledger.row candidate coordinate : ℤ) -
      ledger.row named coordinate

/-- Nonnegative violation row embedded in the Laurent exponent lattice. -/
def integerViolationRow
    {J : Type uConstraint} {C : Type uCandidate}
    (ledger : CompleteFiniteLedger J C) (candidate : C) : J → ℤ :=
  fun coordinate => ledger.row candidate coordinate

/-- Mass-weighted, multiplicity-sensitive relative-row atomic measure.
Every candidate label contributes one atom; equal rows aggregate by addition. -/
noncomputable def relativeRowMassMeasure
    {J : Type uConstraint} {C : Type uCandidate}
    [DecidableEq J] [Fintype C]
    (ledger : CompleteFiniteLedger J C) (named : C) :
    LaurentExponent J →₀ ℚ :=
  weightedSparseLedgerMass
    (fun candidate => ledger.baseMass candidate / ledger.baseMass named)
    (relativeViolationRow ledger named)

theorem weightedSparseLedgerMass_apply
    {J : Type uConstraint} {C : Type uCandidate}
    [DecidableEq J] [Fintype J] [Fintype C]
    (coefficient : C → ℚ) (row : C → LaurentExponent J)
    (exponent : LaurentExponent J) :
    weightedSparseLedgerMass coefficient row exponent =
      ∑ candidate : C,
        if row candidate = exponent then coefficient candidate else 0 := by
  classical
  rw [weightedSparseLedgerMass]
  change (Finsupp.applyAddHom exponent)
      (∑ candidate : C,
        Finsupp.single (row candidate) (coefficient candidate)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro candidate _
  by_cases hRow : row candidate = exponent
  · subst exponent
    simp
  · have hReverse : exponent ≠ row candidate :=
      fun h => hRow h.symm
    simp [hRow, hReverse]

/-- Relative partition sum obtained by dividing the complete partition by
the named candidate's own positive mass. -/
noncomputable def relativePartitionEvaluation
    {J : Type uConstraint} {C : Type uCandidate}
    [DecidableEq J] [Fintype J] [Fintype C]
    (ledger : CompleteFiniteLedger J C) (named : C)
    (activity : J → ℝ) : ℝ :=
  evaluateRationalSparseLaurent
    (relativeRowMassMeasure ledger named) activity

theorem relativePartitionEvaluation_eq_sum
    {J : Type uConstraint} {C : Type uCandidate}
    [DecidableEq J] [Fintype J] [Fintype C]
    (ledger : CompleteFiniteLedger J C) (named : C)
    (activity : J → ℝ) :
    relativePartitionEvaluation ledger named activity =
      ∑ candidate : C,
        ((ledger.baseMass candidate / ledger.baseMass named : ℚ) : ℝ) *
          laurentMonomial (relativeViolationRow ledger named candidate)
            activity := by
  exact evaluateRationalSparseLaurent_weightedLedger
    (fun candidate => ledger.baseMass candidate / ledger.baseMass named)
    (relativeViolationRow ledger named) activity

theorem relativePartitionEvaluation_pos
    {J : Type uConstraint} {C : Type uCandidate}
    [DecidableEq J] [Fintype J] [Fintype C] [Nonempty C]
    (ledger : CompleteFiniteLedger J C) (named : C)
    (activity : J → ℝ) (hActivity : ∀ coordinate, 0 < activity coordinate) :
    0 < relativePartitionEvaluation ledger named activity := by
  classical
  rw [relativePartitionEvaluation_eq_sum]
  apply Finset.sum_pos'
  · intro candidate _
    apply mul_nonneg
    · exact Rat.cast_nonneg.2 (div_nonneg
        (ledger.baseMass_pos candidate).le
        (ledger.baseMass_pos named).le)
    · exact (laurentMonomial_pos
        (relativeViolationRow ledger named candidate)
        activity hActivity).le
  · refine ⟨named, Finset.mem_univ named, ?_⟩
    have hNamedRatio : ledger.baseMass named / ledger.baseMass named = 1 :=
      div_self (ne_of_gt (ledger.baseMass_pos named))
    simp [hNamedRatio, relativeViolationRow, laurentMonomial]

/-! ### A locally proved finite Laurent independence theorem -/

theorem rationalClearedExponent_injective_on_support
    {J : Type uConstraint} [Finite J]
    (carrier : LaurentExponent J →₀ ℚ)
    {first second : LaurentExponent J}
    (hFirst : first ∈ carrier.support)
    (hSecond : second ∈ carrier.support)
    (hEqual : rationalClearedExponent carrier first =
      rationalClearedExponent carrier second) :
    first = second := by
  funext coordinate
  have hApply := congrArg (fun exponent => exponent coordinate) hEqual
  rw [rationalClearedExponent_apply,
    rationalClearedExponent_apply] at hApply
  have hFirstNonnegative :=
    rationalExponent_add_minimalShift_nonnegative
      carrier first hFirst coordinate
  have hSecondNonnegative :=
    rationalExponent_add_minimalShift_nonnegative
      carrier second hSecond coordinate
  omega

theorem coeff_rationalClearedIntegerPolynomial_of_support
    {J : Type uConstraint} [DecidableEq J] [Fintype J]
    (carrier : LaurentExponent J →₀ ℚ)
    (exponent : LaurentExponent J) (hExponent : exponent ∈ carrier.support) :
    (rationalClearedIntegerPolynomial carrier).coeff
        (rationalClearedExponent carrier exponent) =
      lcmScaledIntegerCoefficient carrier exponent := by
  classical
  unfold rationalClearedIntegerPolynomial
  simp only [Finsupp.sum, MvPolynomial.coeff_sum]
  rw [Finset.sum_eq_single exponent]
  · simp
  · intro other hOther hOtherNe
    have hShiftNe : rationalClearedExponent carrier other ≠
        rationalClearedExponent carrier exponent := by
      intro hShift
      exact hOtherNe (rationalClearedExponent_injective_on_support
        carrier hOther hExponent hShift)
    simp [hShiftNe]
  · exact fun hNot => (hNot hExponent).elim

theorem rationalClearedIntegerPolynomial_eq_zero_iff
    {J : Type uConstraint} [DecidableEq J] [Fintype J]
    (carrier : LaurentExponent J →₀ ℚ) :
    rationalClearedIntegerPolynomial carrier = 0 ↔ carrier = 0 := by
  constructor
  · intro hPolynomial
    ext exponent
    by_cases hExponent : exponent ∈ carrier.support
    · have hCoefficient := coeff_rationalClearedIntegerPolynomial_of_support
        carrier exponent hExponent
      rw [hPolynomial] at hCoefficient
      simp only [MvPolynomial.coeff_zero] at hCoefficient
      have hCast := lcmScaledIntegerCoefficient_cast
        carrier exponent hExponent
      rw [← hCoefficient] at hCast
      simp only [Int.cast_zero] at hCast
      have hLCM : (rationalDenominatorLCM carrier : ℚ) ≠ 0 := by
        exact_mod_cast ne_of_gt (rationalDenominatorLCM_pos carrier)
      change carrier exponent = 0
      exact (mul_eq_zero.mp hCast.symm).resolve_left hLCM
    · exact Finsupp.notMem_support_iff.mp hExponent
  · rintro rfl
    simp [rationalClearedIntegerPolynomial]

theorem rationalSparseLaurent_eq_zero_of_open_cube
    {J : Type uConstraint} [DecidableEq J] [Fintype J]
    (carrier : LaurentExponent J →₀ ℚ)
    (hEvaluation : ∀ activity,
      (∀ coordinate, 0 < activity coordinate ∧ activity coordinate < 1) →
      evaluateRationalSparseLaurent carrier activity = 0) :
    carrier = 0 := by
  let polynomial : MvPolynomial J ℤ :=
    rationalClearedIntegerPolynomial carrier
  have hMapped : polynomial.map (Int.castRingHom ℝ) = 0 := by
    apply MvPolynomial.funext_set
      (fun _ : J => Set.Ioo (0 : ℝ) 1)
      (fun _ => Set.Ioo_infinite zero_lt_one)
    intro activity hActivity
    change MvPolynomial.eval activity
        (polynomial.map (Int.castRingHom ℝ)) = 0
    rw [← MvPolynomial.eval₂_eq_eval_map]
    rw [show polynomial = rationalClearedIntegerPolynomial carrier by rfl]
    rw [eval₂_rationalClearedIntegerPolynomial]
    rw [evaluateRationalClearedInteger_factorization carrier activity
      (fun coordinate => ne_of_gt
        (hActivity coordinate (Set.mem_univ coordinate)).1)]
    rw [hEvaluation activity (fun coordinate =>
      hActivity coordinate (Set.mem_univ coordinate))]
    ring
  have hPolynomial : polynomial = 0 := by
    apply (MvPolynomial.map_injective (Int.castRingHom ℝ)
      (Int.cast_injective : Function.Injective (Int.cast : ℤ → ℝ)))
    simpa using hMapped
  exact (rationalClearedIntegerPolynomial_eq_zero_iff carrier).1 hPolynomial

theorem rationalSparseLaurent_ext_on_open_cube
    {J : Type uConstraint} [DecidableEq J] [Fintype J]
    (first second : LaurentExponent J →₀ ℚ) :
    (∀ activity,
      (∀ coordinate, 0 < activity coordinate ∧ activity coordinate < 1) →
      evaluateRationalSparseLaurent first activity =
        evaluateRationalSparseLaurent second activity) ↔
      first = second := by
  constructor
  · intro h
    have hZero : first - second = 0 := by
      apply rationalSparseLaurent_eq_zero_of_open_cube (first - second)
      intro activity hActivity
      change evaluateRationalSparseLaurentLinear activity
        (first - second) = 0
      rw [map_sub]
      change evaluateRationalSparseLaurent first activity -
        evaluateRationalSparseLaurent second activity = 0
      rw [h activity hActivity, sub_self]
    exact sub_eq_zero.mp hZero
  · rintro rfl
    intro activity _
    rfl

/-! The exact probability-to-relative-partition factorization is stated in
activity coordinates because violation rows are integral and the physical
weight orthant maps to `0 < activity ≤ 1`. -/

theorem candidateProbability_eq_inv_relativePartition
    {J : Type uConstraint} {C : Type uCandidate}
    [DecidableEq J] [Fintype J] [Fintype C] [Nonempty C]
    (ledger : CompleteFiniteLedger J C) (named : C)
    (activity : J → ℝ) (hActivity : ∀ coordinate, 0 < activity coordinate) :
    rationalNamedCandidateProbability ledger.baseMass
        (fun candidate coordinate => ledger.row candidate coordinate)
        named activity =
      1 / relativePartitionEvaluation ledger named activity := by
  classical
  rw [relativePartitionEvaluation_eq_sum]
  unfold rationalNamedCandidateProbability candidateMass partitionMass
  have hNamedMass : (ledger.baseMass named : ℝ) ≠ 0 :=
    ne_of_gt (Rat.cast_pos.2 (ledger.baseMass_pos named))
  have hNamedMonomial :
      laurentMonomial (fun coordinate =>
        (ledger.row named coordinate : ℤ)) activity ≠ 0 :=
    ne_of_gt (laurentMonomial_pos _ activity hActivity)
  have hFactor : ∀ candidate : C,
      ((ledger.baseMass candidate / ledger.baseMass named : ℚ) : ℝ) *
          laurentMonomial (relativeViolationRow ledger named candidate)
            activity =
        ((ledger.baseMass candidate : ℝ) *
            laurentMonomial (fun coordinate =>
              (ledger.row candidate coordinate : ℤ)) activity) /
          ((ledger.baseMass named : ℝ) *
            laurentMonomial (fun coordinate =>
              (ledger.row named coordinate : ℤ)) activity) := by
    intro candidate
    rw [Rat.cast_div]
    rw [show relativeViolationRow ledger named candidate =
        fun coordinate =>
          (ledger.row candidate coordinate : ℤ) -
            ledger.row named coordinate by rfl]
    unfold laurentMonomial
    have hMonomial :
        (∏ coordinate,
            activity coordinate ^
              ((ledger.row candidate coordinate : ℤ) -
                ledger.row named coordinate)) =
          (∏ coordinate,
              activity coordinate ^
                (ledger.row candidate coordinate : ℤ)) /
            ∏ coordinate,
              activity coordinate ^
                (ledger.row named coordinate : ℤ) := by
      calc
        (∏ coordinate,
            activity coordinate ^
              ((ledger.row candidate coordinate : ℤ) -
                ledger.row named coordinate)) =
            ∏ coordinate,
              activity coordinate ^
                  (ledger.row candidate coordinate : ℤ) /
                activity coordinate ^
                  (ledger.row named coordinate : ℤ) := by
          apply Finset.prod_congr rfl
          intro coordinate _
          rw [zpow_sub₀ (ne_of_gt (hActivity coordinate))]
        _ = (∏ coordinate,
              activity coordinate ^
                (ledger.row candidate coordinate : ℤ)) /
            ∏ coordinate,
              activity coordinate ^
                (ledger.row named coordinate : ℤ) := by
          rw [Finset.prod_div_distrib]
    rw [hMonomial]
    ring
  simp_rw [hFactor]
  rw [← Finset.sum_div]
  simp only [candidateMass]
  field_simp [hNamedMass, hNamedMonomial]

/-- **MAX-G4.MULTISET.03, universal equality cell.** Across two complete
finite inputs with a shared finite constraint inventory, named-candidate
probabilities agree throughout the full positive activity cube exactly when
their mass-weighted relative-row atomic measures are identical. -/
theorem allActivityCrossInputProbabilityEqual_iff_relativeMeasure_eq
    {J : Type uConstraint} {C₁ C₂ : Type uCandidate}
    [DecidableEq J] [Fintype J]
    [Fintype C₁] [Fintype C₂] [Nonempty C₁] [Nonempty C₂]
    (first : CompleteFiniteLedger J C₁) (namedFirst : C₁)
    (second : CompleteFiniteLedger J C₂) (namedSecond : C₂) :
    (∀ activity,
      (∀ coordinate, 0 < activity coordinate ∧ activity coordinate ≤ 1) →
      rationalNamedCandidateProbability first.baseMass
          (fun candidate coordinate => first.row candidate coordinate)
          namedFirst activity =
        rationalNamedCandidateProbability second.baseMass
          (fun candidate coordinate => second.row candidate coordinate)
          namedSecond activity) ↔
      relativeRowMassMeasure first namedFirst =
        relativeRowMassMeasure second namedSecond := by
  constructor
  · intro hProbability
    apply (rationalSparseLaurent_ext_on_open_cube
      (relativeRowMassMeasure first namedFirst)
      (relativeRowMassMeasure second namedSecond)).1
    intro activity hActivity
    have hFirstPositive := relativePartitionEvaluation_pos
      first namedFirst activity (fun coordinate => (hActivity coordinate).1)
    have hSecondPositive := relativePartitionEvaluation_pos
      second namedSecond activity (fun coordinate => (hActivity coordinate).1)
    have hInv :
        1 / relativePartitionEvaluation first namedFirst activity =
          1 / relativePartitionEvaluation second namedSecond activity := by
      rw [← candidateProbability_eq_inv_relativePartition
          first namedFirst activity
          (fun coordinate => (hActivity coordinate).1),
        ← candidateProbability_eq_inv_relativePartition
          second namedSecond activity
          (fun coordinate => (hActivity coordinate).1)]
      exact hProbability activity fun coordinate =>
        ⟨(hActivity coordinate).1, (hActivity coordinate).2.le⟩
    exact eq_of_one_div_eq_one_div hInv
  · intro hMeasure activity hActivity
    rw [candidateProbability_eq_inv_relativePartition
        first namedFirst activity
        (fun coordinate => (hActivity coordinate).1),
      candidateProbability_eq_inv_relativePartition
        second namedSecond activity
        (fun coordinate => (hActivity coordinate).1)]
    rw [relativePartitionEvaluation, relativePartitionEvaluation, hMeasure]

/-- **MAX-G4.MULTISET.03, full-weight form.** The activity theorem is exactly
the registered all-weight theorem under the bijection
`activity = exp (-weight)` between the full nonnegative weight orthant and
the positive physical activity cube. -/
theorem allWeightCrossInputProbabilityEqual_iff_relativeMeasure_eq
    {J : Type uConstraint} {C₁ C₂ : Type uCandidate}
    [DecidableEq J] [Fintype J]
    [Fintype C₁] [Fintype C₂] [Nonempty C₁] [Nonempty C₂]
    (first : CompleteFiniteLedger J C₁) (namedFirst : C₁)
    (second : CompleteFiniteLedger J C₂) (namedSecond : C₂) :
    (∀ weight, IsNonnegativeWeight weight →
      exponentialCandidateProbability first weight namedFirst =
        exponentialCandidateProbability second weight namedSecond) ↔
      relativeRowMassMeasure first namedFirst =
        relativeRowMassMeasure second namedSecond := by
  constructor
  · intro hWeight
    apply (allActivityCrossInputProbabilityEqual_iff_relativeMeasure_eq
      first namedFirst second namedSecond).1
    intro activity hActivity
    let weight := weightOfActivity activity
    have hNonnegative : IsNonnegativeWeight weight :=
      weightOfActivity_nonnegative activity hActivity
    have hCoordinate : activityOfWeight weight = activity :=
      activityOfWeight_weightOfActivity activity
        (fun coordinate => (hActivity coordinate).1)
    rw [← hCoordinate]
    rw [activityProbability_eq_exponentialProbability,
      activityProbability_eq_exponentialProbability]
    exact hWeight weight hNonnegative
  · intro hMeasure weight hWeight
    have hActivity :=
      (allActivityCrossInputProbabilityEqual_iff_relativeMeasure_eq
        first namedFirst second namedSecond).2 hMeasure
        (activityOfWeight weight)
        (fun coordinate =>
          ⟨activityOfWeight_pos weight coordinate,
            activityOfWeight_le_one weight hWeight coordinate⟩)
    simpa only [activityProbability_eq_exponentialProbability]
      using hActivity

/-- **MAX-G4 cross-input order cell, Laurent form.** Universal probability
order on the full nonnegative weight orthant is exactly universal
nonnegativity of the canonical multiplicity-sensitive relative-partition
carrier on the positive physical activity cube. -/
theorem allWeightCrossInputProbabilityOrder_iff_carrier_nonnegative
    {J : Type uConstraint} {C₁ C₂ : Type uCandidate}
    [DecidableEq J] [Fintype J]
    [Fintype C₁] [Fintype C₂] [Nonempty C₁] [Nonempty C₂]
    (first : CompleteFiniteLedger J C₁) (namedFirst : C₁)
    (second : CompleteFiniteLedger J C₂) (namedSecond : C₂) :
    (∀ weight, IsNonnegativeWeight weight →
      exponentialCandidateProbability first weight namedFirst ≤
        exponentialCandidateProbability second weight namedSecond) ↔
      (∀ activity,
        (∀ coordinate, 0 < activity coordinate ∧
          activity coordinate ≤ 1) →
        0 ≤ evaluateRationalSparseLaurent
          (rationalNamedCrossCarrier first.baseMass
            (integerViolationRow first) namedFirst second.baseMass
            (integerViolationRow second) namedSecond) activity) := by
  constructor
  · intro hOrder activity hActivity
    let weight := weightOfActivity activity
    have hNonnegative : IsNonnegativeWeight weight :=
      weightOfActivity_nonnegative activity hActivity
    have hCoordinate : activityOfWeight weight = activity :=
      activityOfWeight_weightOfActivity activity
        (fun coordinate => (hActivity coordinate).1)
    rw [← hCoordinate]
    apply (max_g1_completeRationalLedgerCarrier
      first.baseMass (integerViolationRow first) namedFirst
      second.baseMass (integerViolationRow second) namedSecond
      (activityOfWeight weight) first.baseMass_pos second.baseMass_pos
      (activityOfWeight_pos weight)).1
    change rationalNamedCandidateProbability first.baseMass
        (fun candidate coordinate => first.row candidate coordinate)
        namedFirst (activityOfWeight weight) ≤
      rationalNamedCandidateProbability second.baseMass
        (fun candidate coordinate => second.row candidate coordinate)
        namedSecond (activityOfWeight weight)
    rw [activityProbability_eq_exponentialProbability,
      activityProbability_eq_exponentialProbability]
    exact hOrder weight hNonnegative
  · intro hCarrier weight hWeight
    have hActivity : ∀ coordinate,
        0 < activityOfWeight weight coordinate ∧
          activityOfWeight weight coordinate ≤ 1 :=
      fun coordinate =>
        ⟨activityOfWeight_pos weight coordinate,
          activityOfWeight_le_one weight hWeight coordinate⟩
    have hProbability := (max_g1_completeRationalLedgerCarrier
      first.baseMass (integerViolationRow first) namedFirst
      second.baseMass (integerViolationRow second) namedSecond
      (activityOfWeight weight) first.baseMass_pos second.baseMass_pos
      (activityOfWeight_pos weight)).2
      (hCarrier (activityOfWeight weight) hActivity)
    change rationalNamedCandidateProbability first.baseMass
        (fun candidate coordinate => first.row candidate coordinate)
        namedFirst (activityOfWeight weight) ≤
      rationalNamedCandidateProbability second.baseMass
        (fun candidate coordinate => second.row candidate coordinate)
        namedSecond (activityOfWeight weight) at hProbability
    rw [activityProbability_eq_exponentialProbability,
      activityProbability_eq_exponentialProbability] at hProbability
    exact hProbability

/-- Polynomial form of the same cross-input order cell. The common clearing
monomial and the least common coefficient denominator are strictly positive,
so the exact universal sign verdict is unchanged. -/
theorem allWeightCrossInputProbabilityOrder_iff_polynomial_nonnegative
    {J : Type uConstraint} {C₁ C₂ : Type uCandidate}
    [DecidableEq J] [Fintype J]
    [Fintype C₁] [Fintype C₂] [Nonempty C₁] [Nonempty C₂]
    (first : CompleteFiniteLedger J C₁) (namedFirst : C₁)
    (second : CompleteFiniteLedger J C₂) (namedSecond : C₂) :
    (∀ weight, IsNonnegativeWeight weight →
      exponentialCandidateProbability first weight namedFirst ≤
        exponentialCandidateProbability second weight namedSecond) ↔
      (∀ activity,
        (∀ coordinate, 0 < activity coordinate ∧
          activity coordinate ≤ 1) →
        0 ≤ (rationalClearedIntegerPolynomial
          (rationalNamedCrossCarrier first.baseMass
            (integerViolationRow first) namedFirst second.baseMass
            (integerViolationRow second) namedSecond)).eval₂
              (Int.castRingHom ℝ) activity) := by
  rw [allWeightCrossInputProbabilityOrder_iff_carrier_nonnegative]
  apply forall_congr'
  intro activity
  apply forall_congr'
  intro hActivity
  exact (rationalClearedIntegerPolynomial_sign_iff
    (rationalNamedCrossCarrier first.baseMass
      (integerViolationRow first) namedFirst second.baseMass
      (integerViolationRow second) namedSecond)
    activity (fun coordinate => (hActivity coordinate).1)).1.symm

/-! ## The duplicate-free `{1,2}` cube cell -/

/-- Closed unit-cube membership. -/
def IsClosedCubePoint {J : Type*} (point : J → ℝ) : Prop :=
  ∀ coordinate, 0 ≤ point coordinate ∧ point coordinate ≤ 1

/-- A real vector whose coordinates are Boolean vertices. -/
def IsBooleanVertex {J : Type*} (point : J → ℝ) : Prop :=
  ∀ coordinate, point coordinate = 0 ∨ point coordinate = 1

/-- Coordinate-replacement interpolation identity characterizing a
separately affine function. -/
def HasCoordinateInterpolation {J : Type*} [DecidableEq J]
    (function : (J → ℝ) → ℝ) : Prop :=
  ∀ point coordinate,
    function point =
      (1 - point coordinate) *
          function (Function.update point coordinate 0) +
        point coordinate *
          function (Function.update point coordinate 1)

theorem booleanVertex_isClosedCubePoint {J : Type*}
    {point : J → ℝ} (hBoolean : IsBooleanVertex point) :
    IsClosedCubePoint point := by
  intro coordinate
  rcases hBoolean coordinate with h | h <;> rw [h] <;> norm_num

/-- The multi-affine vertex lemma at the exact finite scope needed by
`MAX-G4.COMPLEXITY.04`: a separately affine function is nonnegative on the
closed cube iff it is nonnegative at every Boolean vertex. -/
theorem coordinateInterpolation_nonnegative_iff_booleanVertices
    {J : Type*} [Fintype J] [DecidableEq J]
    (function : (J → ℝ) → ℝ)
    (hInterpolation : HasCoordinateInterpolation function) :
    (∀ point, IsClosedCubePoint point → 0 ≤ function point) ↔
      (∀ point, IsBooleanVertex point → 0 ≤ function point) := by
  constructor
  · intro h point hBoolean
    exact h point (booleanVertex_isClosedCubePoint hBoolean)
  · intro hVertices
    have hFinite : ∀ coordinates : Finset J, ∀ point : J → ℝ,
        IsClosedCubePoint point →
        (∀ coordinate, coordinate ∉ coordinates →
          point coordinate = 0 ∨ point coordinate = 1) →
        0 ≤ function point := by
      intro coordinates
      induction coordinates using Finset.induction_on with
      | empty =>
          intro point _ hOutside
          apply hVertices point
          intro coordinate
          exact hOutside coordinate (by simp)
      | @insert selected coordinates hSelected inductionHypothesis =>
          intro point hCube hOutside
          let pointZero := Function.update point selected 0
          let pointOne := Function.update point selected 1
          have hCubeZero : IsClosedCubePoint pointZero := by
            intro coordinate
            by_cases hCoordinate : coordinate = selected
            · subst coordinate
              simp [pointZero]
            · simpa [pointZero, Function.update, hCoordinate]
                using hCube coordinate
          have hCubeOne : IsClosedCubePoint pointOne := by
            intro coordinate
            by_cases hCoordinate : coordinate = selected
            · subst coordinate
              simp [pointOne]
            · simpa [pointOne, Function.update, hCoordinate]
                using hCube coordinate
          have hOutsideZero : ∀ coordinate,
              coordinate ∉ coordinates →
              pointZero coordinate = 0 ∨ pointZero coordinate = 1 := by
            intro coordinate hCoordinateOutside
            by_cases hCoordinate : coordinate = selected
            · subst coordinate
              simp [pointZero]
            · have hNotInserted : coordinate ∉ insert selected coordinates := by
                simp [hCoordinate, hCoordinateOutside]
              simpa [pointZero, Function.update, hCoordinate] using
                hOutside coordinate hNotInserted
          have hOutsideOne : ∀ coordinate,
              coordinate ∉ coordinates →
              pointOne coordinate = 0 ∨ pointOne coordinate = 1 := by
            intro coordinate hCoordinateOutside
            by_cases hCoordinate : coordinate = selected
            · subst coordinate
              simp [pointOne]
            · have hNotInserted : coordinate ∉ insert selected coordinates := by
                simp [hCoordinate, hCoordinateOutside]
              simpa [pointOne, Function.update, hCoordinate] using
                hOutside coordinate hNotInserted
          have hZero := inductionHypothesis pointZero hCubeZero hOutsideZero
          have hOne := inductionHypothesis pointOne hCubeOne hOutsideOne
          rw [hInterpolation point selected]
          exact add_nonneg
            (mul_nonneg (sub_nonneg.mpr (hCube selected).2) hZero)
            (mul_nonneg (hCube selected).1 hOne)
    intro point hCube
    exact hFinite Finset.univ point hCube (by simp)

/-- Residual monomial after factoring the common all-one monomial from a
`{1,2}` violation row. The Boolean row records which coordinates retain one
additional activity factor. -/
def residualBooleanMonomial {J : Type*} [Fintype J]
    (row : J → Bool) (point : J → ℝ) : ℝ :=
  ∏ coordinate, if row coordinate then point coordinate else 1

theorem residualBooleanMonomial_coordinateInterpolation
    {J : Type*} [Fintype J] [DecidableEq J]
    (row : J → Bool) :
    HasCoordinateInterpolation (residualBooleanMonomial row) := by
  intro point selected
  let rest : ℝ :=
    ∏ coordinate ∈ (Finset.univ.erase selected),
      if row coordinate then point coordinate else 1
  have hDecompose : ∀ value : ℝ,
      residualBooleanMonomial row (Function.update point selected value) =
        (if row selected then value else 1) * rest := by
    intro value
    unfold residualBooleanMonomial
    rw [← Finset.mul_prod_erase Finset.univ
      (fun coordinate =>
        if row coordinate then
          Function.update point selected value coordinate else 1)
      (Finset.mem_univ selected)]
    congr 1
    · simp
    · unfold rest
      apply Finset.prod_congr rfl
      intro coordinate hCoordinate
      have hNe : coordinate ≠ selected :=
        (Finset.mem_erase.mp hCoordinate).1
      simp [Function.update, hNe]
  have hPoint : residualBooleanMonomial row point =
      (if row selected then point selected else 1) * rest := by
    calc
      residualBooleanMonomial row point =
          residualBooleanMonomial row
            (Function.update point selected (point selected)) := by
        rw [Function.update_eq_self]
      _ = _ := hDecompose (point selected)
  rw [hPoint, hDecompose 0, hDecompose 1]
  cases row selected
  · simp
    ring
  · simp

/-- Duplicate-free unit-mass `{1,2}` relative margin after removal of the
common all-one monomial. Finsets make row uniqueness explicit; disjointness
prevents cancellation between the two input ledgers. -/
def duplicateFreeResidualMargin {J : Type*} [Fintype J]
    (positiveRows negativeRows : Finset (J → Bool))
    (point : J → ℝ) : ℝ :=
  (∑ row ∈ positiveRows, residualBooleanMonomial row point) -
    ∑ row ∈ negativeRows, residualBooleanMonomial row point

theorem duplicateFreeResidualMargin_coordinateInterpolation
    {J : Type*} [Fintype J] [DecidableEq J]
    (positiveRows negativeRows : Finset (J → Bool)) :
    HasCoordinateInterpolation
      (duplicateFreeResidualMargin positiveRows negativeRows) := by
  intro point selected
  have hPositive :
      (∑ row ∈ positiveRows, residualBooleanMonomial row point) =
        (1 - point selected) *
            ∑ row ∈ positiveRows,
              residualBooleanMonomial row
                (Function.update point selected 0) +
          point selected *
            ∑ row ∈ positiveRows,
              residualBooleanMonomial row
                (Function.update point selected 1) := by
    calc
      _ = ∑ row ∈ positiveRows,
          ((1 - point selected) *
              residualBooleanMonomial row
                (Function.update point selected 0) +
            point selected *
              residualBooleanMonomial row
                (Function.update point selected 1)) := by
        apply Finset.sum_congr rfl
        intro row _
        exact residualBooleanMonomial_coordinateInterpolation row point selected
      _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hNegative :
      (∑ row ∈ negativeRows, residualBooleanMonomial row point) =
        (1 - point selected) *
            ∑ row ∈ negativeRows,
              residualBooleanMonomial row
                (Function.update point selected 0) +
          point selected *
            ∑ row ∈ negativeRows,
              residualBooleanMonomial row
                (Function.update point selected 1) := by
    calc
      _ = ∑ row ∈ negativeRows,
          ((1 - point selected) *
              residualBooleanMonomial row
                (Function.update point selected 0) +
            point selected *
              residualBooleanMonomial row
                (Function.update point selected 1)) := by
        apply Finset.sum_congr rfl
        intro row _
        exact residualBooleanMonomial_coordinateInterpolation row point selected
      _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  unfold duplicateFreeResidualMargin
  rw [hPositive, hNegative]
  ring

theorem duplicateFreeResidualMargin_nonnegative_iff_booleanVertices
    {J : Type*} [Fintype J] [DecidableEq J]
    (positiveRows negativeRows : Finset (J → Bool)) :
    (∀ point, IsClosedCubePoint point →
        0 ≤ duplicateFreeResidualMargin positiveRows negativeRows point) ↔
      (∀ point, IsBooleanVertex point →
        0 ≤ duplicateFreeResidualMargin positiveRows negativeRows point) :=
  coordinateInterpolation_nonnegative_iff_booleanVertices _
    (duplicateFreeResidualMargin_coordinateInterpolation
      positiveRows negativeRows)

/-- Real Boolean vertex associated with a Boolean assignment. -/
def realBooleanPoint {J : Type*} (assignment : J → Bool) : J → ℝ :=
  fun coordinate => if assignment coordinate then 1 else 0

theorem realBooleanPoint_isBooleanVertex {J : Type*}
    (assignment : J → Bool) :
    IsBooleanVertex (realBooleanPoint assignment) := by
  intro coordinate
  cases h : assignment coordinate <;>
    simp [realBooleanPoint, h]

theorem realBooleanPoint_isClosedCubePoint {J : Type*}
    (assignment : J → Bool) :
    IsClosedCubePoint (realBooleanPoint assignment) :=
  booleanVertex_isClosedCubePoint
    (realBooleanPoint_isBooleanVertex assignment)

theorem exists_assignment_eq_of_isBooleanVertex
    {J : Type*} [DecidableEq J]
    (point : J → ℝ) (hPoint : IsBooleanVertex point) :
    ∃ assignment : J → Bool, realBooleanPoint assignment = point := by
  let assignment : J → Bool := fun coordinate => point coordinate = 1
  refine ⟨assignment, ?_⟩
  funext coordinate
  rcases hPoint coordinate with hZero | hOne
  · simp [assignment, realBooleanPoint, hZero]
  · simp [assignment, realBooleanPoint, hOne]

/-- A duplicate-free unit-mass `{1,2}` cross-input order instance. The
residual rows are Finsets, and disjointness makes the two signed supports
globally duplicate-free. -/
structure DuplicateFreeOneTwoOrderInstance (J : Type*) [Fintype J] where
  positiveRows : Finset (J → Bool)
  negativeRows : Finset (J → Bool)
  rows_disjoint : Disjoint positiveRows negativeRows

/-- Universal order decision predicate for the restricted instance. -/
def DuplicateFreeOneTwoOrderInstance.universalOrder
    {J : Type*} [Fintype J]
    (problem : DuplicateFreeOneTwoOrderInstance J) : Prop :=
  ∀ point, IsClosedCubePoint point →
    0 ≤ duplicateFreeResidualMargin
      problem.positiveRows problem.negativeRows point

/-- Polynomially short Boolean counterwitness predicate for failure of the
universal order. -/
def DuplicateFreeOneTwoOrderInstance.negativeBooleanWitness
    {J : Type*} [Fintype J]
    (problem : DuplicateFreeOneTwoOrderInstance J)
    (assignment : J → Bool) : Prop :=
  duplicateFreeResidualMargin problem.positiveRows problem.negativeRows
      (realBooleanPoint assignment) < 0

/-- Exact complement-witness theorem underlying coNP membership of the
duplicate-free `{1,2}` cell. -/
theorem duplicateFreeOneTwo_not_universalOrder_iff_negativeBooleanWitness
    {J : Type*} [Fintype J] [DecidableEq J]
    (problem : DuplicateFreeOneTwoOrderInstance J) :
    ¬ problem.universalOrder ↔
      ∃ assignment : J → Bool,
        problem.negativeBooleanWitness assignment := by
  constructor
  · intro hNotUniversal
    by_contra hNoWitness
    have hVertices : ∀ point, IsBooleanVertex point →
        0 ≤ duplicateFreeResidualMargin
          problem.positiveRows problem.negativeRows point := by
      intro point hPoint
      obtain ⟨assignment, rfl⟩ :=
        exists_assignment_eq_of_isBooleanVertex point hPoint
      have hNotNegative : ¬ problem.negativeBooleanWitness assignment := by
        intro hWitness
        exact hNoWitness ⟨assignment, hWitness⟩
      exact le_of_not_gt hNotNegative
    have hCube :=
      (duplicateFreeResidualMargin_nonnegative_iff_booleanVertices
        problem.positiveRows problem.negativeRows).2 hVertices
    exact hNotUniversal hCube
  · rintro ⟨assignment, hNegative⟩ hUniversal
    have hNonnegative := hUniversal (realBooleanPoint assignment)
      (realBooleanPoint_isClosedCubePoint assignment)
    exact (not_lt_of_ge hNonnegative) hNegative

/-! ## Proper at-most-three-CNF selector compiler -/

/-- A proper clause is represented by disjoint positive- and negative-literal
variable sets.  Finset representation excludes repeated literals, while
disjointness excludes complementary literal pairs.  The width field records
the at-most-three restriction used by the source completeness theorem. -/
structure ProperAtMostThreeClause (V : Type*) [DecidableEq V] where
  positive : Finset V
  negative : Finset V
  signs_disjoint : Disjoint positive negative
  nonempty : (positive ∪ negative).Nonempty
  width_le_three : positive.card + negative.card ≤ 3

/-- A finite proper at-most-three-CNF formula with at least two clauses.
The lower bound makes the global selector monomial distinct from every
single-clause selector monomial. -/
structure ProperAtMostThreeCNF
    (V C : Type*) [DecidableEq V] [Fintype C] where
  clause : C → ProperAtMostThreeClause V
  atLeastTwoClauses : 2 ≤ Fintype.card C

/-- A clause is unsatisfied exactly when every positive literal is false and
every negative literal is true. -/
def ProperAtMostThreeClause.Unsatisfied
    {V : Type*} [DecidableEq V]
    (clause : ProperAtMostThreeClause V)
    (assignment : V → Bool) : Prop :=
  (∀ v ∈ clause.positive, assignment v = false) ∧
    ∀ v ∈ clause.negative, assignment v = true

/-- Boolean satisfiability of a proper finite CNF formula. -/
def ProperAtMostThreeCNF.Satisfiable
    {V C : Type*} [DecidableEq V] [Fintype C]
    (formula : ProperAtMostThreeCNF V C) : Prop :=
  ∃ assignment : V → Bool,
    ∀ clause, ¬ (formula.clause clause).Unsatisfied assignment

/-- One canonical expansion term of `y_c U_c(x)`: the subset records which
positive-literal factors contribute their `-x` summand. -/
structure SelectorExpansionTerm
    (V C : Type*) [DecidableEq V] [Fintype C]
    (formula : ProperAtMostThreeCNF V C) where
  clause : C
  selected : Finset V
  selected_subset : selected ⊆ (formula.clause clause).positive

def selectorExpansionTermEquiv
    {V C : Type*} [DecidableEq V] [Fintype C]
    (formula : ProperAtMostThreeCNF V C) :
    SelectorExpansionTerm V C formula ≃
      Σ clause : C,
        { selected : Finset V //
          selected ⊆ (formula.clause clause).positive } where
  toFun term := ⟨term.clause, term.selected, term.selected_subset⟩
  invFun term := ⟨term.1, term.2.1, term.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance selectorExpansionTermFintype
    {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C]
    (formula : ProperAtMostThreeCNF V C) :
    Fintype (SelectorExpansionTerm V C formula) := by
  exact Fintype.ofEquiv _ (selectorExpansionTermEquiv formula).symm

noncomputable instance selectorExpansionTermDecidableEq
    {V C : Type*} [DecidableEq V] [DecidableEq C] [Fintype C]
    (formula : ProperAtMostThreeCNF V C) :
    DecidableEq (SelectorExpansionTerm V C formula) :=
  Classical.decEq _

/-- Residual Boolean exponent row of one selector-expansion term. Variable
coordinates contain the negative-literal base plus the selected positive
literals; selector coordinates contain exactly the term's clause selector. -/
def selectorClauseRow
    {V C : Type*} [DecidableEq V] [DecidableEq C] [Fintype C]
    {formula : ProperAtMostThreeCNF V C}
    (term : SelectorExpansionTerm V C formula) : Sum V C → Bool
  | .inl v =>
      decide
        (v ∈ (formula.clause term.clause).negative ∨
          v ∈ term.selected)
  | .inr clause => decide (clause = term.clause)

/-- Residual row of the single negative global selector monomial. -/
def selectorGlobalRow {V C : Type*} : Sum V C → Bool
  | .inl _ => false
  | .inr _ => true

theorem selectorClauseRow_selector
    {V C : Type*} [DecidableEq V] [DecidableEq C] [Fintype C]
    {formula : ProperAtMostThreeCNF V C}
    (term : SelectorExpansionTerm V C formula) (clause : C) :
    selectorClauseRow term (.inr clause) = decide (clause = term.clause) :=
  rfl

theorem selectorClauseRow_injective
    {V C : Type*} [DecidableEq V] [DecidableEq C] [Fintype C]
    {formula : ProperAtMostThreeCNF V C} :
    Function.Injective
      (selectorClauseRow (formula := formula)) := by
  intro first second hRows
  have hClause : first.clause = second.clause := by
    have hAtFirst := congrFun hRows (.inr first.clause)
    simp [selectorClauseRow] at hAtFirst
    exact hAtFirst
  cases first with
  | mk firstClause firstSelected firstSubset =>
    cases second with
    | mk secondClause secondSelected secondSubset =>
      dsimp only at hClause
      subst secondClause
      congr 1
      ext v
      have hAtVariable := congrFun hRows (.inl v)
      have hPositiveOrNot :
          v ∈ (formula.clause firstClause).positive ∨
            v ∉ (formula.clause firstClause).positive :=
        Classical.em _
      rcases hPositiveOrNot with hPositive | hNotPositive
      · have hNotNegative :
            v ∉ (formula.clause firstClause).negative := by
          intro hNegative
          exact Finset.disjoint_left.mp
            (formula.clause firstClause).signs_disjoint
            hPositive hNegative
        simpa [selectorClauseRow, hNotNegative] using hAtVariable
      · have hFirstNot : v ∉ firstSelected := by
          intro hMember
          exact hNotPositive (firstSubset hMember)
        have hSecondNot : v ∉ secondSelected := by
          intro hMember
          exact hNotPositive (secondSubset hMember)
        simp [hFirstNot, hSecondNot]

theorem selectorGlobalRow_ne_clauseRow
    {V C : Type*} [DecidableEq V] [DecidableEq C] [Fintype C]
    {formula : ProperAtMostThreeCNF V C}
    (term : SelectorExpansionTerm V C formula) :
    selectorGlobalRow ≠ selectorClauseRow term := by
  intro hRows
  have hTwo := formula.atLeastTwoClauses
  have hExists : ∃ clause : C, clause ≠ term.clause := by
    by_contra hNo
    push Not at hNo
    have hCard : Fintype.card C ≤ 1 :=
      Fintype.card_le_one_iff.mpr
        (fun first second => (hNo first).trans (hNo second).symm)
    omega
  obtain ⟨other, hOther⟩ := hExists
  have hAtOther := congrFun hRows (.inr other)
  simp [selectorGlobalRow, selectorClauseRow, hOther] at hAtOther

/-- Even-parity clause rows carry coefficient `+1`. -/
def selectorPositiveRows
    {V C : Type*} [Fintype V] [DecidableEq V]
    [Fintype C] [DecidableEq C]
    (formula : ProperAtMostThreeCNF V C) : Finset (Sum V C → Bool) :=
  ((Finset.univ : Finset (SelectorExpansionTerm V C formula)).filter
      (fun term => Even term.selected.card)).image selectorClauseRow

/-- Odd-parity clause rows and the global selector row carry coefficient
`-1`. -/
def selectorNegativeRows
    {V C : Type*} [Fintype V] [DecidableEq V]
    [Fintype C] [DecidableEq C]
    (formula : ProperAtMostThreeCNF V C) : Finset (Sum V C → Bool) :=
  insert selectorGlobalRow
    (((Finset.univ : Finset (SelectorExpansionTerm V C formula)).filter
      (fun term => ¬ Even term.selected.card)).image selectorClauseRow)

theorem selectorRows_disjoint
    {V C : Type*} [Fintype V] [DecidableEq V]
    [Fintype C] [DecidableEq C]
    (formula : ProperAtMostThreeCNF V C) :
    Disjoint (selectorPositiveRows formula) (selectorNegativeRows formula) := by
  classical
  rw [Finset.disjoint_left]
  intro row hPositive hNegative
  rw [selectorPositiveRows, Finset.mem_image] at hPositive
  obtain ⟨positiveTerm, hPositiveTerm, rfl⟩ := hPositive
  rw [selectorNegativeRows, Finset.mem_insert] at hNegative
  rcases hNegative with hGlobal | hNegative
  · exact selectorGlobalRow_ne_clauseRow positiveTerm hGlobal.symm
  · rw [Finset.mem_image] at hNegative
    obtain ⟨negativeTerm, hNegativeTerm, hRows⟩ := hNegative
    have hTerms : positiveTerm = negativeTerm :=
      selectorClauseRow_injective hRows.symm
    subst negativeTerm
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hPositiveTerm hNegativeTerm
    exact hNegativeTerm hPositiveTerm

/-- The duplicate-free residual-row target compiled from a proper
at-most-three-CNF formula. -/
def properCNFSelectorInstance
    {V C : Type*} [Fintype V] [DecidableEq V]
    [Fintype C] [DecidableEq C]
    (formula : ProperAtMostThreeCNF V C) :
    DuplicateFreeOneTwoOrderInstance (Sum V C) where
  positiveRows := selectorPositiveRows formula
  negativeRows := selectorNegativeRows formula
  rows_disjoint := selectorRows_disjoint formula

theorem selectorClauseRow_monomial
    {V C : Type*} [Fintype V] [DecidableEq V]
    [Fintype C] [DecidableEq C]
    {formula : ProperAtMostThreeCNF V C}
    (term : SelectorExpansionTerm V C formula)
    (point : Sum V C → ℝ) :
    residualBooleanMonomial (selectorClauseRow term) point =
      point (.inr term.clause) *
        (∏ v ∈ (formula.clause term.clause).negative,
          point (.inl v)) *
        ∏ v ∈ term.selected, point (.inl v) := by
  classical
  unfold residualBooleanMonomial
  rw [Fintype.prod_sum_type]
  simp only [selectorClauseRow, decide_eq_true_eq]
  rw [show
    (∏ v,
      if v ∈ (formula.clause term.clause).negative ∨
          v ∈ term.selected then point (.inl v) else 1) =
      ∏ v ∈
        ((formula.clause term.clause).negative ∪ term.selected),
        point (.inl v) by
      simpa only [Finset.mem_union] using
        (Fintype.prod_ite_mem
          (s := (formula.clause term.clause).negative ∪ term.selected)
          (f := fun v => point (.inl v)))]
  rw [Finset.prod_union]
  · rw [Fintype.prod_ite_eq']
    ring
  · exact Finset.disjoint_left.mpr (by
      intro v hNegative hSelected
      exact Finset.disjoint_left.mp
        (formula.clause term.clause).signs_disjoint
        (term.selected_subset hSelected) hNegative)

theorem selectorGlobalRow_monomial
    {V C : Type*} [Fintype V] [Fintype C]
    (point : Sum V C → ℝ) :
    residualBooleanMonomial selectorGlobalRow point =
      ∏ clause : C, point (.inr clause) := by
  classical
  unfold residualBooleanMonomial
  rw [Fintype.prod_sum_type]
  simp [selectorGlobalRow]

/-- Real clause-unsatisfaction factor used by the selector polynomial. -/
def selectorClauseFactor
    {V C : Type*} [Fintype V] [DecidableEq V]
    [Fintype C]
    (formula : ProperAtMostThreeCNF V C)
    (clause : C) (point : Sum V C → ℝ) : ℝ :=
  (∏ v ∈ (formula.clause clause).negative,
      point (.inl v)) *
    ∏ v ∈ (formula.clause clause).positive,
      (1 - point (.inl v))

/-- Project selector polynomial
`-∏_c y_c + Σ_c y_c U_c(x)` evaluated on the common cube. -/
def properCNFSelectorPolynomial
    {V C : Type*} [Fintype V] [DecidableEq V]
    [Fintype C]
    (formula : ProperAtMostThreeCNF V C)
    (point : Sum V C → ℝ) : ℝ :=
  -(∏ clause : C, point (.inr clause)) +
    ∑ clause : C,
      point (.inr clause) * selectorClauseFactor formula clause point

def finsetSubsetPowersetEquiv
    {V : Type*} [DecidableEq V] (support : Finset V) :
    { selected : Finset V // selected ⊆ support } ≃
      { selected : Finset V // selected ∈ support.powerset } where
  toFun selected := ⟨selected.1, Finset.mem_powerset.mpr selected.2⟩
  invFun selected := ⟨selected.1, Finset.mem_powerset.mp selected.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Exact number of expansion terms produced by the selector compiler.  A
clause contributes one term for every subset of its positive literals. -/
theorem selectorExpansionTerm_card_eq
    {V C : Type*} [Fintype V] [DecidableEq V]
    [Fintype C] [DecidableEq C]
    (formula : ProperAtMostThreeCNF V C) :
    Fintype.card (SelectorExpansionTerm V C formula) =
      ∑ clause : C, 2 ^ (formula.clause clause).positive.card := by
  classical
  calc
    Fintype.card (SelectorExpansionTerm V C formula) =
        Fintype.card
          (Σ clause : C,
            { selected : Finset V //
              selected ⊆ (formula.clause clause).positive }) :=
      Fintype.card_congr (selectorExpansionTermEquiv formula)
    _ = ∑ clause : C,
          Fintype.card
            { selected : Finset V //
              selected ⊆ (formula.clause clause).positive } := by
      rw [Fintype.card_sigma]
    _ = ∑ clause : C,
          2 ^ (formula.clause clause).positive.card := by
      apply Finset.sum_congr rfl
      intro clause _
      calc
        Fintype.card
            { selected : Finset V //
              selected ⊆ (formula.clause clause).positive } =
            Fintype.card
              { selected : Finset V //
                selected ∈
                  (formula.clause clause).positive.powerset } :=
          Fintype.card_congr
            (finsetSubsetPowersetEquiv
              (formula.clause clause).positive)
        _ = (formula.clause clause).positive.powerset.card :=
          Fintype.card_coe _
        _ = 2 ^ (formula.clause clause).positive.card :=
          Finset.card_powerset _

/-- Every proper at-most-three clause contributes at most eight canonical
selector terms.  Thus the compiler has an explicit linear output-support
bound in the number of clauses. -/
theorem selectorExpansionTerm_card_le_eight_mul_clause_card
    {V C : Type*} [Fintype V] [DecidableEq V]
    [Fintype C] [DecidableEq C]
    (formula : ProperAtMostThreeCNF V C) :
    Fintype.card (SelectorExpansionTerm V C formula) ≤
      8 * Fintype.card C := by
  rw [selectorExpansionTerm_card_eq]
  calc
    (∑ clause : C, 2 ^ (formula.clause clause).positive.card) ≤
        ∑ _clause : C, 8 := by
      apply Finset.sum_le_sum
      intro clause _
      have hCard : (formula.clause clause).positive.card ≤ 3 := by
        have := (formula.clause clause).width_le_three
        omega
      simpa using Nat.pow_le_pow_right (by omega : 0 < 2) hCard
    _ = 8 * Fintype.card C := by simp [Nat.mul_comm]

theorem selectorPositiveRows_card
    {V C : Type*} [Fintype V] [DecidableEq V]
    [Fintype C] [DecidableEq C]
    (formula : ProperAtMostThreeCNF V C) :
    (selectorPositiveRows formula).card =
      ((Finset.univ : Finset (SelectorExpansionTerm V C formula)).filter
        (fun term => Even term.selected.card)).card := by
  classical
  unfold selectorPositiveRows
  exact Finset.card_image_of_injective _ selectorClauseRow_injective

theorem selectorNegativeRows_card
    {V C : Type*} [Fintype V] [DecidableEq V]
    [Fintype C] [DecidableEq C]
    (formula : ProperAtMostThreeCNF V C) :
    (selectorNegativeRows formula).card =
      1 +
        ((Finset.univ : Finset (SelectorExpansionTerm V C formula)).filter
          (fun term => ¬ Even term.selected.card)).card := by
  classical
  have hGlobalNotMem : selectorGlobalRow ∉
      (((Finset.univ : Finset (SelectorExpansionTerm V C formula)).filter
        (fun term => ¬ Even term.selected.card)).image selectorClauseRow) := by
    intro hMember
    rw [Finset.mem_image] at hMember
    obtain ⟨term, _, hTerm⟩ := hMember
    exact selectorGlobalRow_ne_clauseRow term hTerm.symm
  unfold selectorNegativeRows
  rw [Finset.card_insert_of_notMem hGlobalNotMem,
    Finset.card_image_of_injective _ selectorClauseRow_injective]
  omega

/-- Exact row count of the compiled duplicate-free target.  The single
global monomial is disjoint from the parity-partitioned clause expansions. -/
theorem properCNFSelector_total_row_card
    {V C : Type*} [Fintype V] [DecidableEq V]
    [Fintype C] [DecidableEq C]
    (formula : ProperAtMostThreeCNF V C) :
    (properCNFSelectorInstance formula).positiveRows.card +
        (properCNFSelectorInstance formula).negativeRows.card =
      1 + Fintype.card (SelectorExpansionTerm V C formula) := by
  rw [properCNFSelectorInstance, selectorPositiveRows_card,
    selectorNegativeRows_card]
  have hPartition := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (SelectorExpansionTerm V C formula)))
    (fun term => Even term.selected.card)
  rw [Finset.card_univ] at hPartition
  omega

/-- Canonical compiler support bound: at most `1 + 8m` globally distinct
rows for `m` clauses. -/
theorem properCNFSelector_total_row_card_le
    {V C : Type*} [Fintype V] [DecidableEq V]
    [Fintype C] [DecidableEq C]
    (formula : ProperAtMostThreeCNF V C) :
    (properCNFSelectorInstance formula).positiveRows.card +
        (properCNFSelectorInstance formula).negativeRows.card ≤
      1 + 8 * Fintype.card C := by
  rw [properCNFSelector_total_row_card]
  exact Nat.add_le_add_left
    (selectorExpansionTerm_card_le_eight_mul_clause_card formula) 1

theorem parityFilteredSum_sub_eq_signedSum
    {A : Type*} [DecidableEq A]
    (support : Finset A) (degree : A → ℕ) (value : A → ℝ) :
    (∑ item ∈ support.filter (fun item => Even (degree item)), value item) -
        ∑ item ∈ support.filter (fun item => ¬ Even (degree item)), value item =
      ∑ item ∈ support, (-1 : ℝ) ^ degree item * value item := by
  classical
  let parity : A → Prop := fun item => Even (degree item)
  calc
    (∑ item ∈ support.filter parity, value item) -
          ∑ item ∈ support.filter (fun item => ¬ parity item), value item =
        (∑ item ∈ support.filter parity, value item) +
          ∑ item ∈ support.filter (fun item => ¬ parity item),
            -value item := by
      rw [sub_eq_add_neg, Finset.sum_neg_distrib]
    _ = (∑ item ∈ support.filter parity,
            if parity item then value item else -value item) +
          ∑ item ∈ support.filter (fun item => ¬ parity item),
            if parity item then value item else -value item := by
      congr 1
      · apply Finset.sum_congr rfl
        intro item hItem
        simp [(Finset.mem_filter.mp hItem).2]
      · apply Finset.sum_congr rfl
        intro item hItem
        simp [(Finset.mem_filter.mp hItem).2]
    _ = ∑ item ∈ support,
          if parity item then value item else -value item :=
      Finset.sum_filter_add_sum_filter_not support parity
        (fun item => if parity item then value item else -value item)
    _ = ∑ item ∈ support,
          (-1 : ℝ) ^ degree item * value item := by
      apply Finset.sum_congr rfl
      intro item _
      by_cases hEven : Even (degree item)
      · simp [parity, hEven, hEven.neg_one_pow]
      · have hOdd : Odd (degree item) := Nat.not_even_iff_odd.mp hEven
        simp [parity, hEven, hOdd.neg_one_pow]

theorem signedSubsetMonomialSum_eq_prod_one_sub
    {V : Type*} [Fintype V] [DecidableEq V]
    (support : Finset V) (value : V → ℝ) :
    (∑ selected : { selected : Finset V // selected ⊆ support },
        (-1 : ℝ) ^ selected.1.card *
          ∏ v ∈ selected.1, value v) =
      ∏ v ∈ support, (1 - value v) := by
  classical
  calc
    _ = ∑ selected :
          { selected : Finset V // selected ∈ support.powerset },
        (-1 : ℝ) ^ selected.1.card *
          ∏ v ∈ selected.1, value v := by
      apply Fintype.sum_equiv (finsetSubsetPowersetEquiv support)
      intro selected
      rfl
    _ = ∑ selected ∈ support.powerset,
        (-1 : ℝ) ^ selected.card *
          ∏ v ∈ selected, value v := by
      exact Finset.sum_coe_sort support.powerset
        (fun selected =>
          (-1 : ℝ) ^ selected.card *
            ∏ v ∈ selected, value v)
    _ = _ := by
      rw [Finset.prod_sub (fun _ => 1) value support]
      simp

theorem selectorClause_signed_expansion
    {V C : Type*} [Fintype V] [DecidableEq V]
    [Fintype C] [DecidableEq C]
    (formula : ProperAtMostThreeCNF V C) (clause : C)
    (point : Sum V C → ℝ) :
    (∑ selected :
        { selected : Finset V //
          selected ⊆ (formula.clause clause).positive },
      (-1 : ℝ) ^ selected.1.card *
        residualBooleanMonomial
          (selectorClauseRow
            (⟨clause, selected.1, selected.2⟩ :
              SelectorExpansionTerm V C formula)) point) =
      point (.inr clause) * selectorClauseFactor formula clause point := by
  classical
  simp_rw [selectorClauseRow_monomial]
  calc
    _ = ∑ selected :
        { selected : Finset V //
          selected ⊆ (formula.clause clause).positive },
      (point (.inr clause) *
          ∏ v ∈ (formula.clause clause).negative, point (.inl v)) *
        ((-1 : ℝ) ^ selected.1.card *
          ∏ v ∈ selected.1, point (.inl v)) := by
      apply Finset.sum_congr rfl
      intro selected _
      ring
    _ = (point (.inr clause) *
          ∏ v ∈ (formula.clause clause).negative, point (.inl v)) *
        ∑ selected :
          { selected : Finset V //
            selected ⊆ (formula.clause clause).positive },
          ((-1 : ℝ) ^ selected.1.card *
            ∏ v ∈ selected.1, point (.inl v)) := by
      rw [Finset.mul_sum]
    _ = _ := by
      rw [signedSubsetMonomialSum_eq_prod_one_sub]
      unfold selectorClauseFactor
      ring

theorem selectorPositiveRows_sum
    {V C : Type*} [Fintype V] [DecidableEq V]
    [Fintype C] [DecidableEq C]
    (formula : ProperAtMostThreeCNF V C)
    (point : Sum V C → ℝ) :
    (∑ row ∈ selectorPositiveRows formula,
        residualBooleanMonomial row point) =
      ∑ term ∈
        (Finset.univ : Finset (SelectorExpansionTerm V C formula)).filter
          (fun term => Even term.selected.card),
        residualBooleanMonomial (selectorClauseRow term) point := by
  classical
  unfold selectorPositiveRows
  exact Finset.sum_image selectorClauseRow_injective.injOn

theorem selectorNegativeRows_sum
    {V C : Type*} [Fintype V] [DecidableEq V]
    [Fintype C] [DecidableEq C]
    (formula : ProperAtMostThreeCNF V C)
    (point : Sum V C → ℝ) :
    (∑ row ∈ selectorNegativeRows formula,
        residualBooleanMonomial row point) =
      residualBooleanMonomial selectorGlobalRow point +
        ∑ term ∈
          (Finset.univ : Finset (SelectorExpansionTerm V C formula)).filter
            (fun term => ¬ Even term.selected.card),
          residualBooleanMonomial (selectorClauseRow term) point := by
  classical
  have hGlobalNotMem : selectorGlobalRow ∉
      (((Finset.univ : Finset (SelectorExpansionTerm V C formula)).filter
        (fun term => ¬ Even term.selected.card)).image selectorClauseRow) := by
    intro hMember
    rw [Finset.mem_image] at hMember
    obtain ⟨term, _, hTerm⟩ := hMember
    exact selectorGlobalRow_ne_clauseRow term hTerm.symm
  unfold selectorNegativeRows
  rw [Finset.sum_insert hGlobalNotMem]
  congr 1
  exact Finset.sum_image selectorClauseRow_injective.injOn

theorem selectorSignedTermSum_eq_clauseSum
    {V C : Type*} [Fintype V] [DecidableEq V]
    [Fintype C] [DecidableEq C]
    (formula : ProperAtMostThreeCNF V C)
    (point : Sum V C → ℝ) :
    (∑ term : SelectorExpansionTerm V C formula,
        (-1 : ℝ) ^ term.selected.card *
          residualBooleanMonomial (selectorClauseRow term) point) =
      ∑ clause : C,
        point (.inr clause) * selectorClauseFactor formula clause point := by
  classical
  calc
    _ = ∑ term :
        (Σ clause : C,
          { selected : Finset V //
            selected ⊆ (formula.clause clause).positive }),
        (-1 : ℝ) ^ term.2.1.card *
          residualBooleanMonomial
            (selectorClauseRow
              (⟨term.1, term.2.1, term.2.2⟩ :
                SelectorExpansionTerm V C formula)) point := by
      apply Fintype.sum_equiv (selectorExpansionTermEquiv formula)
      intro term
      rfl
    _ = ∑ clause : C,
        ∑ selected :
          { selected : Finset V //
            selected ⊆ (formula.clause clause).positive },
          (-1 : ℝ) ^ selected.1.card *
            residualBooleanMonomial
              (selectorClauseRow
                (⟨clause, selected.1, selected.2⟩ :
                  SelectorExpansionTerm V C formula)) point := by
      rw [Fintype.sum_sigma]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro clause _
      exact selectorClause_signed_expansion formula clause point

/-- Exact algebraic compiler identity: the duplicate-free residual margin is
the proper-CNF selector polynomial, with no candidate aliases or coefficient
multiplicities hidden by the representation. -/
theorem properCNFSelectorMargin_eq_polynomial
    {V C : Type*} [Fintype V] [DecidableEq V]
    [Fintype C] [DecidableEq C]
    (formula : ProperAtMostThreeCNF V C)
    (point : Sum V C → ℝ) :
    duplicateFreeResidualMargin
        (selectorPositiveRows formula) (selectorNegativeRows formula) point =
      properCNFSelectorPolynomial formula point := by
  classical
  rw [duplicateFreeResidualMargin, selectorPositiveRows_sum,
    selectorNegativeRows_sum]
  have hParity := parityFilteredSum_sub_eq_signedSum
    (Finset.univ : Finset (SelectorExpansionTerm V C formula))
    (fun term => term.selected.card)
    (fun term => residualBooleanMonomial (selectorClauseRow term) point)
  calc
    _ = -residualBooleanMonomial selectorGlobalRow point +
        ((∑ term ∈
            (Finset.univ : Finset (SelectorExpansionTerm V C formula)).filter
              (fun term => Even term.selected.card),
            residualBooleanMonomial (selectorClauseRow term) point) -
          ∑ term ∈
            (Finset.univ : Finset (SelectorExpansionTerm V C formula)).filter
              (fun term => ¬ Even term.selected.card),
            residualBooleanMonomial (selectorClauseRow term) point) := by
      ring
    _ = -residualBooleanMonomial selectorGlobalRow point +
        ∑ term : SelectorExpansionTerm V C formula,
          (-1 : ℝ) ^ term.selected.card *
            residualBooleanMonomial (selectorClauseRow term) point := by
      rw [hParity]
    _ = _ := by
      rw [selectorSignedTermSum_eq_clauseSum,
        selectorGlobalRow_monomial]
      unfold properCNFSelectorPolynomial
      ring

/-- Extend a source assignment by setting every selector to one. -/
def allSelectorsAssignment {V C : Type*}
    (assignment : V → Bool) : Sum V C → Bool
  | .inl v => assignment v
  | .inr _ => true

noncomputable def selectorClauseUnsatisfiedIndicator
    {V C : Type*} [DecidableEq V] [Fintype C]
    (formula : ProperAtMostThreeCNF V C) (clause : C)
    (assignment : Sum V C → Bool) : ℝ :=
  @ite ℝ
    ((formula.clause clause).Unsatisfied
      (fun v => assignment (.inl v)))
    (Classical.propDecidable _) 1 0

noncomputable def allSelectorsIndicator
    {V C : Type*} [DecidableEq V] [Fintype C]
    (_formula : ProperAtMostThreeCNF V C)
    (assignment : Sum V C → Bool) : ℝ :=
  @ite ℝ (∀ clause : C, assignment (.inr clause) = true)
    (Classical.propDecidable _) 1 0

noncomputable def selectorActiveUnsatisfiedClauses
    {V C : Type*} [DecidableEq V] [Fintype C]
    (formula : ProperAtMostThreeCNF V C)
    (assignment : Sum V C → Bool) : Finset C := by
  classical
  exact Finset.univ.filter (fun clause =>
    assignment (.inr clause) = true ∧
      (formula.clause clause).Unsatisfied
        (fun v => assignment (.inl v)))

theorem selectorClauseFactor_realBooleanPoint
    {V C : Type*} [Fintype V] [DecidableEq V]
    [Fintype C]
    (formula : ProperAtMostThreeCNF V C) (clause : C)
    (assignment : Sum V C → Bool) :
    selectorClauseFactor formula clause (realBooleanPoint assignment) =
      selectorClauseUnsatisfiedIndicator formula clause assignment := by
  classical
  unfold selectorClauseUnsatisfiedIndicator
  by_cases hUnsatisfied : (formula.clause clause).Unsatisfied
      (fun v => assignment (.inl v))
  · rw [if_pos hUnsatisfied]
    rcases hUnsatisfied with ⟨hPositive, hNegative⟩
    have hNegativeProduct :
        (∏ v ∈ (formula.clause clause).negative,
          realBooleanPoint assignment (.inl v)) = 1 := by
      apply Finset.prod_eq_one
      intro v hMember
      simp [realBooleanPoint, hNegative v hMember]
    have hPositiveProduct :
        (∏ v ∈ (formula.clause clause).positive,
          (1 - realBooleanPoint assignment (.inl v))) = 1 := by
      apply Finset.prod_eq_one
      intro v hMember
      simp [realBooleanPoint, hPositive v hMember]
    unfold selectorClauseFactor
    rw [hNegativeProduct, hPositiveProduct]
    norm_num
  · rw [if_neg hUnsatisfied]
    simp only [ProperAtMostThreeClause.Unsatisfied] at hUnsatisfied
    by_cases hPositiveAll :
        ∀ v ∈ (formula.clause clause).positive,
          assignment (.inl v) = false
    · have hNegativeNot :
          ¬ ∀ v ∈ (formula.clause clause).negative,
            assignment (.inl v) = true := by
        intro hNegativeAll
        exact hUnsatisfied ⟨hPositiveAll, hNegativeAll⟩
      push Not at hNegativeNot
      obtain ⟨v, hMember, hValue⟩ := hNegativeNot
      have hFalse : assignment (.inl v) = false := by
        cases h : assignment (.inl v) <;> simp_all
      have hNegativeProduct :
          (∏ v ∈ (formula.clause clause).negative,
            realBooleanPoint assignment (.inl v)) = 0 := by
        apply Finset.prod_eq_zero hMember
        simp [realBooleanPoint, hFalse]
      unfold selectorClauseFactor
      rw [hNegativeProduct]
      ring
    · push Not at hPositiveAll
      obtain ⟨v, hMember, hValue⟩ := hPositiveAll
      have hTrue : assignment (.inl v) = true := by
        cases h : assignment (.inl v) <;> simp_all
      have hPositiveProduct :
          (∏ v ∈ (formula.clause clause).positive,
            (1 - realBooleanPoint assignment (.inl v))) = 0 := by
        apply Finset.prod_eq_zero hMember
        simp [realBooleanPoint, hTrue]
      unfold selectorClauseFactor
      rw [hPositiveProduct]
      ring

theorem selectorPolynomial_realBooleanPoint
    {V C : Type*} [Fintype V] [DecidableEq V]
    [Fintype C]
    (formula : ProperAtMostThreeCNF V C)
    (assignment : Sum V C → Bool) :
    properCNFSelectorPolynomial formula (realBooleanPoint assignment) =
      -allSelectorsIndicator formula assignment +
        (selectorActiveUnsatisfiedClauses formula assignment).card := by
  classical
  unfold properCNFSelectorPolynomial
  simp_rw [selectorClauseFactor_realBooleanPoint]
  rw [show
      (∏ clause : C, realBooleanPoint assignment (.inr clause)) =
        allSelectorsIndicator formula assignment by
    unfold allSelectorsIndicator
    simp [realBooleanPoint, Fintype.prod_boole]]
  rw [show
      (∑ clause : C,
        realBooleanPoint assignment (.inr clause) *
          selectorClauseUnsatisfiedIndicator formula clause assignment) =
        (selectorActiveUnsatisfiedClauses formula assignment).card by
    unfold selectorActiveUnsatisfiedClauses
    simp only [realBooleanPoint]
    rw [← Finset.sum_boole
      (R := ℝ)
      (fun clause : C =>
        assignment (.inr clause) = true ∧
          (formula.clause clause).Unsatisfied
            (fun v => assignment (.inl v))) Finset.univ]
    apply Finset.sum_congr rfl
    intro clause _
    unfold selectorClauseUnsatisfiedIndicator
    by_cases hSelector : assignment (.inr clause) = true <;>
      by_cases hClause : (formula.clause clause).Unsatisfied
        (fun v => assignment (.inl v)) <;>
      simp [hSelector, hClause]]

/-- **MAX-G4.COMPLEXITY.04, selector correctness.** A proper at-most-three-CNF
formula is satisfiable exactly when its compiled duplicate-free `{1,2}` order
instance has a negative Boolean counterwitness, equivalently when universal
order fails.  All target-specific algebra and witness construction are proved
locally. -/
theorem properCNFSelector_satisfiable_iff_not_universalOrder
    {V C : Type*} [Fintype V] [DecidableEq V]
    [Fintype C] [DecidableEq C]
    (formula : ProperAtMostThreeCNF V C) :
    formula.Satisfiable ↔
      ¬ (properCNFSelectorInstance formula).universalOrder := by
  constructor
  · rintro ⟨assignment, hSatisfies⟩
    apply (duplicateFreeOneTwo_not_universalOrder_iff_negativeBooleanWitness
      (properCNFSelectorInstance formula)).2
    refine ⟨allSelectorsAssignment assignment, ?_⟩
    change duplicateFreeResidualMargin
      (selectorPositiveRows formula) (selectorNegativeRows formula)
      (realBooleanPoint (allSelectorsAssignment assignment)) < 0
    rw [properCNFSelectorMargin_eq_polynomial,
      selectorPolynomial_realBooleanPoint]
    have hAllSelectors :
        allSelectorsIndicator formula
          (allSelectorsAssignment assignment) = 1 := by
      unfold allSelectorsIndicator
      simp [allSelectorsAssignment]
    have hNoActive :
        selectorActiveUnsatisfiedClauses formula
          (allSelectorsAssignment assignment) = ∅ := by
      unfold selectorActiveUnsatisfiedClauses
      ext clause
      simp [allSelectorsAssignment, hSatisfies clause]
    rw [hAllSelectors, hNoActive]
    norm_num
  · intro hNotUniversal
    obtain ⟨combinedAssignment, hNegative⟩ :=
      (duplicateFreeOneTwo_not_universalOrder_iff_negativeBooleanWitness
        (properCNFSelectorInstance formula)).1 hNotUniversal
    have hPolynomial :
        -allSelectorsIndicator formula combinedAssignment +
            (selectorActiveUnsatisfiedClauses formula
              combinedAssignment).card < 0 := by
      rw [← selectorPolynomial_realBooleanPoint]
      rw [← properCNFSelectorMargin_eq_polynomial]
      exact hNegative
    have hAllSelectors :
        ∀ clause : C, combinedAssignment (.inr clause) = true := by
      by_contra hNotAll
      have hIndicatorZero :
          allSelectorsIndicator formula combinedAssignment = 0 := by
        unfold allSelectorsIndicator
        rw [if_neg hNotAll]
      rw [hIndicatorZero] at hPolynomial
      have hCardNonnegative :
          (0 : ℝ) ≤
            (selectorActiveUnsatisfiedClauses formula
              combinedAssignment).card := by positivity
      linarith
    refine ⟨fun v => combinedAssignment (.inl v), ?_⟩
    intro clause hUnsatisfied
    have hMember : clause ∈
        selectorActiveUnsatisfiedClauses formula combinedAssignment := by
      unfold selectorActiveUnsatisfiedClauses
      simp [hAllSelectors clause, hUnsatisfied]
    have hOneLeCard :
        1 ≤ (selectorActiveUnsatisfiedClauses formula
          combinedAssignment).card :=
      Finset.one_le_card.mpr ⟨clause, hMember⟩
    have hIndicatorOne :
        allSelectorsIndicator formula combinedAssignment = 1 := by
      unfold allSelectorsIndicator
      rw [if_pos hAllSelectors]
    rw [hIndicatorOne] at hPolynomial
    have hOneLeCardReal :
        (1 : ℝ) ≤
          (selectorActiveUnsatisfiedClauses formula
            combinedAssignment).card := by
      exact_mod_cast hOneLeCard
    linarith

theorem properCNFSelector_unsatisfiable_iff_universalOrder
    {V C : Type*} [Fintype V] [DecidableEq V]
    [Fintype C] [DecidableEq C]
    (formula : ProperAtMostThreeCNF V C) :
    ¬ formula.Satisfiable ↔
      (properCNFSelectorInstance formula).universalOrder := by
  rw [← not_iff_not]
  simpa using properCNFSelector_satisfiable_iff_not_universalOrder formula

/-! ## Explicit decision languages and polynomial reduction -/

/-!
The objects in this section deliberately record semantic correctness and
polynomial *output-size* bounds only.  They do not define a machine encoding,
an executable compiler/verifier, or a running-time cost semantics.
Consequently, `HardFor` and `CompleteFor` below are local semantic-size notions
and must not be read as standard polynomial-time complexity classifications
without an additional effective machine-model bridge.
-/

/-- A decision language with an explicit positive encoding-size function.
The size is the only machine-model datum used by the local reduction layer;
the conventional complexity interpretation is isolated below. -/
structure EncodedDecisionProblem where
  Instance : Type
  accepts : Instance → Prop
  size : Instance → ℕ
  size_positive : ∀ input, 0 < size input

/-- A proof-bearing many-one reduction with an explicit monomial size bound.
This is the local reduction object consumed by the conventional complexity
foundation. -/
structure PolynomialSizeManyOneReduction
    (source target : EncodedDecisionProblem) where
  map : source.Instance → target.Instance
  correct : ∀ input, target.accepts (map input) ↔ source.accepts input
  coefficient : ℕ
  degree : ℕ
  coefficient_positive : 0 < coefficient
  size_bound : ∀ input,
    target.size (map input) ≤ coefficient * source.size input ^ degree

namespace PolynomialSizeManyOneReduction

def identity (problem : EncodedDecisionProblem) :
    PolynomialSizeManyOneReduction problem problem where
  map := id
  correct := by intro; rfl
  coefficient := 1
  degree := 1
  coefficient_positive := by norm_num
  size_bound := by intro; simp

/-- Polynomial-size reductions compose, with the displayed coefficient and
degree obtained by substituting the first monomial bound into the second. -/
def trans {first middle last : EncodedDecisionProblem}
    (left : PolynomialSizeManyOneReduction first middle)
    (right : PolynomialSizeManyOneReduction middle last) :
    PolynomialSizeManyOneReduction first last where
  map := fun input => right.map (left.map input)
  correct := fun input => (right.correct (left.map input)).trans
    (left.correct input)
  coefficient := right.coefficient * left.coefficient ^ right.degree
  degree := left.degree * right.degree
  coefficient_positive := mul_pos right.coefficient_positive
    (pow_pos left.coefficient_positive _)
  size_bound := by
    intro input
    calc
      last.size (right.map (left.map input)) ≤
          right.coefficient * middle.size (left.map input) ^ right.degree :=
        right.size_bound (left.map input)
      _ ≤ right.coefficient *
          (left.coefficient * first.size input ^ left.degree) ^
            right.degree := by
        exact Nat.mul_le_mul_left _
          (Nat.pow_le_pow_left (left.size_bound input) _)
      _ = (right.coefficient * left.coefficient ^ right.degree) *
          first.size input ^ (left.degree * right.degree) := by
        rw [mul_pow, pow_mul]
        ring

end PolynomialSizeManyOneReduction

/-- A class of encoded decision languages. -/
abbrev EncodedDecisionClass := EncodedDecisionProblem → Prop

def HardFor (languageClass : EncodedDecisionClass)
    (problem : EncodedDecisionProblem) : Prop :=
  ∀ source, languageClass source →
    Nonempty (PolynomialSizeManyOneReduction source problem)

def CompleteFor (languageClass : EncodedDecisionClass)
    (problem : EncodedDecisionProblem) : Prop :=
  languageClass problem ∧ HardFor languageClass problem

theorem complete_of_complete_source
    {languageClass : EncodedDecisionClass}
    {source target : EncodedDecisionProblem}
    (sourceComplete : CompleteFor languageClass source)
    (targetMember : languageClass target)
    (reduction : PolynomialSizeManyOneReduction source target) :
    CompleteFor languageClass target := by
  refine ⟨targetMember, ?_⟩
  intro problem hProblem
  obtain ⟨toSource⟩ := sourceComplete.2 problem hProblem
  exact ⟨toSource.trans reduction⟩

/-- Uniform finite encoding of a proper at-most-three-CNF instance. -/
structure ProperAtMostThreeCNFCode where
  variableCount : ℕ
  clauseCount : ℕ
  formula : ProperAtMostThreeCNF
    (Fin variableCount) (Fin clauseCount)

def properAtMostThreeCNFCodeSize
    (input : ProperAtMostThreeCNFCode) : ℕ :=
  input.variableCount + input.clauseCount + 1

/-- The source language used for the local hardness reduction has YES
instances exactly at unsatisfiable proper at-most-three-CNF codes. -/
def properAtMostThreeCNFUnsatisfiability : EncodedDecisionProblem where
  Instance := ProperAtMostThreeCNFCode
  accepts := fun input => ¬ input.formula.Satisfiable
  size := properAtMostThreeCNFCodeSize
  size_positive := by
    intro input
    unfold properAtMostThreeCNFCodeSize
    omega

/-- Explicit finite-table encoding of a duplicate-free `{1,2}` universal
order instance.  A split coordinate type avoids any hidden reindexing in the
selector compiler while still representing arbitrary finite dimensions. -/
structure DuplicateFreeOneTwoOrderCode where
  leftCoordinateCount : ℕ
  rightCoordinateCount : ℕ
  positiveRows : Finset
    (Sum (Fin leftCoordinateCount) (Fin rightCoordinateCount) → Bool)
  negativeRows : Finset
    (Sum (Fin leftCoordinateCount) (Fin rightCoordinateCount) → Bool)
  rows_disjoint : Disjoint positiveRows negativeRows

def DuplicateFreeOneTwoOrderCode.toOrderInstance
    (input : DuplicateFreeOneTwoOrderCode) :
    DuplicateFreeOneTwoOrderInstance
      (Sum (Fin input.leftCoordinateCount)
        (Fin input.rightCoordinateCount)) where
  positiveRows := input.positiveRows
  negativeRows := input.negativeRows
  rows_disjoint := input.rows_disjoint

def duplicateFreeOneTwoOrderCodeSize
    (input : DuplicateFreeOneTwoOrderCode) : ℕ :=
  (input.leftCoordinateCount + input.rightCoordinateCount + 1) *
    (input.positiveRows.card + input.negativeRows.card + 1)

def duplicateFreeOneTwoUniversalOrder : EncodedDecisionProblem where
  Instance := DuplicateFreeOneTwoOrderCode
  accepts := fun input => input.toOrderInstance.universalOrder
  size := duplicateFreeOneTwoOrderCodeSize
  size_positive := by
    intro input
    unfold duplicateFreeOneTwoOrderCodeSize
    positivity

/-- The uniform selector compiler between the two explicit decision
languages. -/
def compileProperCNFSelector
    (input : ProperAtMostThreeCNFCode) :
    DuplicateFreeOneTwoOrderCode where
  leftCoordinateCount := input.variableCount
  rightCoordinateCount := input.clauseCount
  positiveRows := selectorPositiveRows input.formula
  negativeRows := selectorNegativeRows input.formula
  rows_disjoint := selectorRows_disjoint input.formula

theorem compileProperCNFSelector_correct
    (input : ProperAtMostThreeCNFCode) :
    duplicateFreeOneTwoUniversalOrder.accepts
        (compileProperCNFSelector input) ↔
      properAtMostThreeCNFUnsatisfiability.accepts input := by
  change (properCNFSelectorInstance input.formula).universalOrder ↔
    ¬ input.formula.Satisfiable
  exact (properCNFSelector_unsatisfiable_iff_universalOrder
    input.formula).symm

/-- The explicit selector table has quadratic size in the declared source
encoding.  The constant ten is a simple uniform envelope over the sharp
`1 + 8m` row bound. -/
theorem compileProperCNFSelector_size_bound
    (input : ProperAtMostThreeCNFCode) :
    duplicateFreeOneTwoUniversalOrder.size
        (compileProperCNFSelector input) ≤
      10 * properAtMostThreeCNFUnsatisfiability.size input ^ 2 := by
  have hRows := properCNFSelector_total_row_card_le input.formula
  have hRows' :
      (selectorPositiveRows input.formula).card +
          (selectorNegativeRows input.formula).card ≤
        1 + 8 * input.clauseCount := by
    simpa [properCNFSelectorInstance] using hRows
  let sourceSize : ℕ :=
    input.variableCount + input.clauseCount + 1
  have hClauseCount : input.clauseCount ≤ sourceSize := by
    dsimp [sourceSize]
    omega
  have hRowFactor :
      (selectorPositiveRows input.formula).card +
          (selectorNegativeRows input.formula).card + 1 ≤
        10 * sourceSize := by
    calc
      (selectorPositiveRows input.formula).card +
            (selectorNegativeRows input.formula).card + 1 ≤
          (1 + 8 * input.clauseCount) + 1 :=
        Nat.add_le_add_right hRows' 1
      _ ≤ 10 * sourceSize := by omega
  change sourceSize *
      ((selectorPositiveRows input.formula).card +
        (selectorNegativeRows input.formula).card + 1) ≤
    10 * sourceSize ^ 2
  calc
    sourceSize *
        ((selectorPositiveRows input.formula).card +
          (selectorNegativeRows input.formula).card + 1) ≤
        sourceSize * (10 * sourceSize) :=
      Nat.mul_le_mul_left sourceSize hRowFactor
    _ = 10 * sourceSize ^ 2 := by ring

def properCNFSelectorReduction :
    PolynomialSizeManyOneReduction
      properAtMostThreeCNFUnsatisfiability
      duplicateFreeOneTwoUniversalOrder where
  map := compileProperCNFSelector
  correct := compileProperCNFSelector_correct
  coefficient := 10
  degree := 2
  coefficient_positive := by norm_num
  size_bound := compileProperCNFSelector_size_bound

/-! ## Exact Boolean complement verifier -/

/-- A residual row is active at a Boolean assignment when every coordinate
whose exponent is one is assigned one. -/
def residualRowActive {J : Type*}
    (row assignment : J → Bool) : Prop :=
  ∀ coordinate, row coordinate = true → assignment coordinate = true

/-- Number of active rows in a duplicate-free residual support. -/
noncomputable def activeResidualRowCount
    {J : Type*} [Fintype J]
    (rows : Finset (J → Bool)) (assignment : J → Bool) : ℕ := by
  classical
  exact (rows.filter (fun row => residualRowActive row assignment)).card

theorem residualBooleanMonomial_realBooleanPoint
    {J : Type*} [Fintype J]
    (row assignment : J → Bool) :
    residualBooleanMonomial row (realBooleanPoint assignment) =
      @ite ℝ (residualRowActive row assignment)
        (Classical.propDecidable _) 1 0 := by
  classical
  by_cases hActive : residualRowActive row assignment
  · rw [if_pos hActive]
    unfold residualBooleanMonomial
    apply Finset.prod_eq_one
    intro coordinate _
    cases hRow : row coordinate
    · simp
    · have hAssignment := hActive coordinate (by simp [hRow])
      simp [realBooleanPoint, hAssignment]
  · rw [if_neg hActive]
    unfold residualRowActive at hActive
    push Not at hActive
    obtain ⟨coordinate, hRow, hAssignment⟩ := hActive
    have hFalse : assignment coordinate = false := by
      cases hValue : assignment coordinate <;> simp_all
    unfold residualBooleanMonomial
    apply Finset.prod_eq_zero (Finset.mem_univ coordinate)
    simp [hRow, realBooleanPoint, hFalse]

theorem residualBooleanMonomial_sum_realBooleanPoint
    {J : Type*} [Fintype J]
    (rows : Finset (J → Bool)) (assignment : J → Bool) :
    (∑ row ∈ rows,
        residualBooleanMonomial row (realBooleanPoint assignment)) =
      (activeResidualRowCount rows assignment : ℝ) := by
  classical
  calc
    _ = ∑ row ∈ rows,
        if residualRowActive row assignment then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro row _
      exact residualBooleanMonomial_realBooleanPoint row assignment
    _ = _ := by
      rw [Finset.sum_boole]
      rfl

theorem negativeBooleanWitness_iff_activeRowCount_lt
    {J : Type*} [Fintype J]
    (problem : DuplicateFreeOneTwoOrderInstance J)
    (assignment : J → Bool) :
    problem.negativeBooleanWitness assignment ↔
      activeResidualRowCount problem.positiveRows assignment <
        activeResidualRowCount problem.negativeRows assignment := by
  unfold DuplicateFreeOneTwoOrderInstance.negativeBooleanWitness
  rw [duplicateFreeResidualMargin,
    residualBooleanMonomial_sum_realBooleanPoint,
    residualBooleanMonomial_sum_realBooleanPoint]
  constructor
  · intro hNegative
    have hCast :
        (activeResidualRowCount problem.positiveRows assignment : ℝ) <
          activeResidualRowCount problem.negativeRows assignment := by
      linarith
    exact_mod_cast hCast
  · intro hCount
    have hCast :
        (activeResidualRowCount problem.positiveRows assignment : ℝ) <
          activeResidualRowCount problem.negativeRows assignment := by
      exact_mod_cast hCount
    linarith

/-- Decode a fixed-length Boolean proof witness as an assignment on the split
coordinate type of an explicit order instance. -/
def DuplicateFreeOneTwoOrderCode.proofWitnessAssignment
    (input : DuplicateFreeOneTwoOrderCode)
    (proofWitness : Fin
      (input.leftCoordinateCount + input.rightCoordinateCount) → Bool) :
    Sum (Fin input.leftCoordinateCount)
      (Fin input.rightCoordinateCount) → Bool :=
  fun coordinate => proofWitness (finSumFinEquiv coordinate)

/-- Encode a split-coordinate assignment as a fixed-length Boolean proof
witness. -/
def DuplicateFreeOneTwoOrderCode.assignmentProofWitness
    (input : DuplicateFreeOneTwoOrderCode)
    (assignment : Sum (Fin input.leftCoordinateCount)
      (Fin input.rightCoordinateCount) → Bool) :
    Fin (input.leftCoordinateCount + input.rightCoordinateCount) → Bool :=
  fun coordinate => assignment (finSumFinEquiv.symm coordinate)

theorem DuplicateFreeOneTwoOrderCode.proofWitnessAssignment_assignmentProofWitness
    (input : DuplicateFreeOneTwoOrderCode)
    (assignment : Sum (Fin input.leftCoordinateCount)
      (Fin input.rightCoordinateCount) → Bool) :
    input.proofWitnessAssignment (input.assignmentProofWitness assignment) =
      assignment := by
  funext coordinate
  simp [proofWitnessAssignment, assignmentProofWitness]

/-- Executable Boolean comparison used by the complement proof witness. -/
noncomputable def duplicateFreeOneTwoNegativeVerifier
    (input : DuplicateFreeOneTwoOrderCode)
    (proofWitness : Fin
      (input.leftCoordinateCount + input.rightCoordinateCount) → Bool) :
    Bool := by
  classical
  exact decide
    (activeResidualRowCount input.positiveRows
        (input.proofWitnessAssignment proofWitness) <
      activeResidualRowCount input.negativeRows
        (input.proofWitnessAssignment proofWitness))

theorem duplicateFreeOneTwoNegativeVerifier_eq_true_iff
    (input : DuplicateFreeOneTwoOrderCode)
    (proofWitness : Fin
      (input.leftCoordinateCount + input.rightCoordinateCount) → Bool) :
    duplicateFreeOneTwoNegativeVerifier input proofWitness = true ↔
      input.toOrderInstance.negativeBooleanWitness
        (input.proofWitnessAssignment proofWitness) := by
  classical
  unfold duplicateFreeOneTwoNegativeVerifier
  rw [decide_eq_true_eq]
  exact (negativeBooleanWitness_iff_activeRowCount_lt
    input.toOrderInstance (input.proofWitnessAssignment proofWitness)).symm

theorem duplicateFreeOneTwo_not_accepts_iff_proofWitness
    (input : DuplicateFreeOneTwoOrderCode) :
    ¬ duplicateFreeOneTwoUniversalOrder.accepts input ↔
      ∃ proofWitness : Fin
        (input.leftCoordinateCount + input.rightCoordinateCount) → Bool,
        duplicateFreeOneTwoNegativeVerifier input proofWitness = true := by
  change ¬ input.toOrderInstance.universalOrder ↔ _
  rw [duplicateFreeOneTwo_not_universalOrder_iff_negativeBooleanWitness]
  constructor
  · rintro ⟨assignment, hAssignment⟩
    refine ⟨input.assignmentProofWitness assignment, ?_⟩
    rw [duplicateFreeOneTwoNegativeVerifier_eq_true_iff,
      input.proofWitnessAssignment_assignmentProofWitness]
    exact hAssignment
  · rintro ⟨proofWitness, hProofWitness⟩
    refine ⟨input.proofWitnessAssignment proofWitness, ?_⟩
    exact (duplicateFreeOneTwoNegativeVerifier_eq_true_iff
      input proofWitness).1 hProofWitness

/-- A typed polynomial complement proof-witness contract.  The external
complexity foundation below supplies the conventional machine-model theorem
that such contracts place a language in coNP; witness correctness and
all concrete size/cost bounds remain local. -/
structure PolynomialComplementProofWitness
    (problem : EncodedDecisionProblem) where
  proofWitnessLength : problem.Instance → ℕ
  verify : ∀ input, (Fin (proofWitnessLength input) → Bool) → Bool
  correctness : ∀ input,
    ¬ problem.accepts input ↔
      ∃ proofWitness, verify input proofWitness = true
  lengthCoefficient : ℕ
  lengthDegree : ℕ
  lengthCoefficient_positive : 0 < lengthCoefficient
  length_bound : ∀ input,
    proofWitnessLength input ≤
      lengthCoefficient * problem.size input ^ lengthDegree
  verificationCost : ∀ input,
    (Fin (proofWitnessLength input) → Bool) → ℕ
  costCoefficient : ℕ
  costDegree : ℕ
  costCoefficient_positive : 0 < costCoefficient
  cost_bound : ∀ input proofWitness,
    verificationCost input proofWitness ≤
      costCoefficient * problem.size input ^ costDegree

/-- In the explicit-table model, verification scans at most every row and
every coordinate once; its declared cost is the table size itself. -/
def duplicateFreeOneTwoVerificationCost
    (input : DuplicateFreeOneTwoOrderCode)
    (_proofWitness : Fin
      (input.leftCoordinateCount + input.rightCoordinateCount) → Bool) :
    ℕ := duplicateFreeOneTwoOrderCodeSize input

noncomputable def duplicateFreeOneTwoComplementProofWitness :
    PolynomialComplementProofWitness duplicateFreeOneTwoUniversalOrder where
  proofWitnessLength := fun input =>
    input.leftCoordinateCount + input.rightCoordinateCount
  verify := duplicateFreeOneTwoNegativeVerifier
  correctness := duplicateFreeOneTwo_not_accepts_iff_proofWitness
  lengthCoefficient := 1
  lengthDegree := 1
  lengthCoefficient_positive := by norm_num
  length_bound := by
    intro input
    simp only [one_mul, pow_one]
    change input.leftCoordinateCount + input.rightCoordinateCount ≤
      duplicateFreeOneTwoOrderCodeSize input
    unfold duplicateFreeOneTwoOrderCodeSize
    have hFactor :
        1 ≤ input.positiveRows.card + input.negativeRows.card + 1 := by
      omega
    calc
      input.leftCoordinateCount + input.rightCoordinateCount ≤
          input.leftCoordinateCount + input.rightCoordinateCount + 1 := by
        omega
      _ ≤
          (input.leftCoordinateCount + input.rightCoordinateCount + 1) *
            (input.positiveRows.card + input.negativeRows.card + 1) := by
        exact Nat.le_mul_of_pos_right
          (input.leftCoordinateCount + input.rightCoordinateCount + 1)
          hFactor
  verificationCost := duplicateFreeOneTwoVerificationCost
  costCoefficient := 1
  costDegree := 1
  costCoefficient_positive := by norm_num
  cost_bound := by
    intro input proofWitness
    simp [duplicateFreeOneTwoVerificationCost,
      duplicateFreeOneTwoUniversalOrder]

/-- Precisely typed abstract-class foundation for the two inherited facts
used by the local semantic-size component of `MAX-G4.COMPLEXITY.04`:
proper at-most-three-CNF unsatisfiability is complete for the selected class
under `CompleteFor`, and the declared complement proof-witness contract gives
class membership.  Neither field mentions the target language.  Calling the
selected class standard coNP additionally requires the effective
machine-model bridge not represented by this structure. -/
structure ConventionalCoNPFoundation
    (coNP : EncodedDecisionClass) where
  properAtMostThreeCNFUnsat_complete :
    CompleteFor coNP properAtMostThreeCNFUnsatisfiability
  complementProofWitness_mem : ∀ problem,
    PolynomialComplementProofWitness problem → coNP problem

/-- **MAX-G4.COMPLEXITY.04, local semantic-size component.**  Relative only
to the two abstract class facts in `ConventionalCoNPFoundation`, the explicit
duplicate-free unit-mass `{1,2}` universal-order language is complete under
the local semantic-size relation.  The reduction semantics, duplicate-
freedom, quadratic output bound, and Boolean witness equivalence are proved in
this module.  An executable polynomial-time compiler/verifier and operational
cost proof are not represented here, so this theorem alone is not a standard
machine-model coNP-completeness proof. -/
theorem duplicateFreeOneTwo_semanticSize_complete
    {coNP : EncodedDecisionClass}
    (foundation : ConventionalCoNPFoundation coNP) :
    CompleteFor coNP duplicateFreeOneTwoUniversalOrder := by
  exact complete_of_complete_source
    foundation.properAtMostThreeCNFUnsat_complete
    (foundation.complementProofWitness_mem _
      duplicateFreeOneTwoComplementProofWitness)
    properCNFSelectorReduction

/-! ## Globally duplicate-free `{1,…,5}` universal-real bridge -/

/-- Positive activity cube corresponding to finite nonnegative MaxEnt
weights.  The upper endpoint is one and zero is excluded. -/
def IsPositiveUnitCubePoint {J : Type*} (point : J → ℝ) : Prop :=
  ∀ coordinate, 0 < point coordinate ∧ point coordinate ≤ 1

/-- Residual monomial with coordinate exponents in `{0,…,4}`. -/
def boundedQuarticResidualMonomial
    {J : Type*} [Fintype J]
    (row : J → Fin 5) (point : J → ℝ) : ℝ :=
  ∏ coordinate, point coordinate ^ (row coordinate).val

/-- Actual phonological monomial with coordinate violations in `{1,…,5}`.
The stored `Fin 5` value is the residual exponent; adding one gives the
violation count. -/
def oneToFiveViolationMonomial
    {J : Type*} [Fintype J]
    (row : J → Fin 5) (point : J → ℝ) : ℝ :=
  ∏ coordinate, point coordinate ^ ((row coordinate).val + 1)

def commonAllOneMonomial
    {J : Type*} [Fintype J] (point : J → ℝ) : ℝ :=
  ∏ coordinate, point coordinate

theorem oneToFiveViolationMonomial_factorization
    {J : Type*} [Fintype J]
    (row : J → Fin 5) (point : J → ℝ) :
    oneToFiveViolationMonomial row point =
      commonAllOneMonomial point *
        boundedQuarticResidualMonomial row point := by
  classical
  unfold oneToFiveViolationMonomial commonAllOneMonomial
    boundedQuarticResidualMonomial
  calc
    (∏ coordinate, point coordinate ^ ((row coordinate).val + 1)) =
        ∏ coordinate,
          point coordinate * point coordinate ^ (row coordinate).val := by
      apply Finset.prod_congr rfl
      intro coordinate _
      rw [pow_succ]
      ring
    _ = _ := Finset.prod_mul_distrib

theorem commonAllOneMonomial_pos
    {J : Type*} [Fintype J]
    {point : J → ℝ} (hPoint : IsPositiveUnitCubePoint point) :
    0 < commonAllOneMonomial point := by
  classical
  unfold commonAllOneMonomial
  exact Finset.prod_pos fun coordinate _ => (hPoint coordinate).1

/-- Signed sparse quartic polynomial represented by two globally disjoint
unit-coefficient supports. -/
def signedDistinctQuarticMargin
    {J : Type*} [Fintype J]
    (positiveRows negativeRows : Finset (J → Fin 5))
    (point : J → ℝ) : ℝ :=
  (∑ row ∈ positiveRows,
      boundedQuarticResidualMonomial row point) -
    ∑ row ∈ negativeRows,
      boundedQuarticResidualMonomial row point

/-- Cross-input relative-partition margin whose actual violation counts are
the stored residual counts plus one. -/
def duplicateFreeOneToFiveOrderMargin
    {J : Type*} [Fintype J]
    (positiveRows negativeRows : Finset (J → Fin 5))
    (point : J → ℝ) : ℝ :=
  (∑ row ∈ positiveRows,
      oneToFiveViolationMonomial row point) -
    ∑ row ∈ negativeRows,
      oneToFiveViolationMonomial row point

theorem duplicateFreeOneToFiveOrderMargin_factorization
    {J : Type*} [Fintype J]
    (positiveRows negativeRows : Finset (J → Fin 5))
    (point : J → ℝ) :
    duplicateFreeOneToFiveOrderMargin positiveRows negativeRows point =
      commonAllOneMonomial point *
        signedDistinctQuarticMargin positiveRows negativeRows point := by
  classical
  unfold duplicateFreeOneToFiveOrderMargin signedDistinctQuarticMargin
  simp_rw [oneToFiveViolationMonomial_factorization]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  ring

/-- Mathematical sparse-polynomial source language for the conventional
universal-real normal-form theorem. -/
structure SignedDistinctQuarticCode where
  coordinateCount : ℕ
  positiveRows : Finset (Fin coordinateCount → Fin 5)
  negativeRows : Finset (Fin coordinateCount → Fin 5)
  rows_disjoint : Disjoint positiveRows negativeRows

def SignedDistinctQuarticCode.universallyNonnegative
    (input : SignedDistinctQuarticCode) : Prop :=
  ∀ point : Fin input.coordinateCount → ℝ,
    IsPositiveUnitCubePoint point →
      0 ≤ signedDistinctQuarticMargin
        input.positiveRows input.negativeRows point

def signedDistinctQuarticCodeSize
    (input : SignedDistinctQuarticCode) : ℕ :=
  (input.coordinateCount + 1) *
    (input.positiveRows.card + input.negativeRows.card + 1)

def signedDistinctQuarticUniversalNonnegativity :
    EncodedDecisionProblem where
  Instance := SignedDistinctQuarticCode
  accepts := SignedDistinctQuarticCode.universallyNonnegative
  size := signedDistinctQuarticCodeSize
  size_positive := by
    intro input
    unfold signedDistinctQuarticCodeSize
    positivity

/-- Phonological target language with globally duplicate-free unit-mass
relative rows whose coordinate violations lie in `{1,…,5}`. -/
structure DuplicateFreeOneToFiveOrderCode where
  coordinateCount : ℕ
  positiveRows : Finset (Fin coordinateCount → Fin 5)
  negativeRows : Finset (Fin coordinateCount → Fin 5)
  rows_disjoint : Disjoint positiveRows negativeRows

def DuplicateFreeOneToFiveOrderCode.universalOrder
    (input : DuplicateFreeOneToFiveOrderCode) : Prop :=
  ∀ point : Fin input.coordinateCount → ℝ,
    IsPositiveUnitCubePoint point →
      0 ≤ duplicateFreeOneToFiveOrderMargin
        input.positiveRows input.negativeRows point

def duplicateFreeOneToFiveOrderCodeSize
    (input : DuplicateFreeOneToFiveOrderCode) : ℕ :=
  (input.coordinateCount + 1) *
    (input.positiveRows.card + input.negativeRows.card + 1)

def duplicateFreeOneToFiveUniversalOrder : EncodedDecisionProblem where
  Instance := DuplicateFreeOneToFiveOrderCode
  accepts := DuplicateFreeOneToFiveOrderCode.universalOrder
  size := duplicateFreeOneToFiveOrderCodeSize
  size_positive := by
    intro input
    unfold duplicateFreeOneToFiveOrderCodeSize
    positivity

/-- Local bridge from the standard sparse-polynomial normal form to the
phonological row language.  Only the interpretation of exponents changes. -/
def compileSignedQuarticAsOneToFiveOrder
    (input : SignedDistinctQuarticCode) :
    DuplicateFreeOneToFiveOrderCode where
  coordinateCount := input.coordinateCount
  positiveRows := input.positiveRows
  negativeRows := input.negativeRows
  rows_disjoint := input.rows_disjoint

theorem compileSignedQuarticAsOneToFiveOrder_correct
    (input : SignedDistinctQuarticCode) :
    duplicateFreeOneToFiveUniversalOrder.accepts
        (compileSignedQuarticAsOneToFiveOrder input) ↔
      signedDistinctQuarticUniversalNonnegativity.accepts input := by
  change
    (∀ point : Fin input.coordinateCount → ℝ,
      IsPositiveUnitCubePoint point →
        0 ≤ duplicateFreeOneToFiveOrderMargin
          input.positiveRows input.negativeRows point) ↔
    (∀ point : Fin input.coordinateCount → ℝ,
      IsPositiveUnitCubePoint point →
        0 ≤ signedDistinctQuarticMargin
          input.positiveRows input.negativeRows point)
  constructor
  · intro hOrder point hPoint
    have hMargin := hOrder point hPoint
    rw [duplicateFreeOneToFiveOrderMargin_factorization] at hMargin
    exact nonneg_of_mul_nonneg_right hMargin
      (commonAllOneMonomial_pos hPoint)
  · intro hPolynomial point hPoint
    rw [duplicateFreeOneToFiveOrderMargin_factorization]
    exact mul_nonneg (commonAllOneMonomial_pos hPoint).le
      (hPolynomial point hPoint)

theorem compileSignedQuarticAsOneToFiveOrder_size
    (input : SignedDistinctQuarticCode) :
    duplicateFreeOneToFiveUniversalOrder.size
        (compileSignedQuarticAsOneToFiveOrder input) =
      signedDistinctQuarticUniversalNonnegativity.size input := rfl

def signedQuarticToOneToFiveReduction :
    PolynomialSizeManyOneReduction
      signedDistinctQuarticUniversalNonnegativity
      duplicateFreeOneToFiveUniversalOrder where
  map := compileSignedQuarticAsOneToFiveOrder
  correct := compileSignedQuarticAsOneToFiveOrder_correct
  coefficient := 1
  degree := 1
  coefficient_positive := by norm_num
  size_bound := by
    intro input
    rw [compileSignedQuarticAsOneToFiveOrder_size]
    simp

/-- Reverse bridge used only to transport membership in the conventional
universal-real class across the exact representation change. -/
def compileOneToFiveOrderAsSignedQuartic
    (input : DuplicateFreeOneToFiveOrderCode) :
    SignedDistinctQuarticCode where
  coordinateCount := input.coordinateCount
  positiveRows := input.positiveRows
  negativeRows := input.negativeRows
  rows_disjoint := input.rows_disjoint

theorem compileOneToFiveOrderAsSignedQuartic_correct
    (input : DuplicateFreeOneToFiveOrderCode) :
    signedDistinctQuarticUniversalNonnegativity.accepts
        (compileOneToFiveOrderAsSignedQuartic input) ↔
      duplicateFreeOneToFiveUniversalOrder.accepts input := by
  change
    (∀ point : Fin input.coordinateCount → ℝ,
      IsPositiveUnitCubePoint point →
        0 ≤ signedDistinctQuarticMargin
          input.positiveRows input.negativeRows point) ↔
    (∀ point : Fin input.coordinateCount → ℝ,
      IsPositiveUnitCubePoint point →
        0 ≤ duplicateFreeOneToFiveOrderMargin
          input.positiveRows input.negativeRows point)
  constructor
  · intro hPolynomial point hPoint
    rw [duplicateFreeOneToFiveOrderMargin_factorization]
    exact mul_nonneg (commonAllOneMonomial_pos hPoint).le
      (hPolynomial point hPoint)
  · intro hOrder point hPoint
    have hMargin := hOrder point hPoint
    rw [duplicateFreeOneToFiveOrderMargin_factorization] at hMargin
    exact nonneg_of_mul_nonneg_right hMargin
      (commonAllOneMonomial_pos hPoint)

def oneToFiveToSignedQuarticReduction :
    PolynomialSizeManyOneReduction
      duplicateFreeOneToFiveUniversalOrder
      signedDistinctQuarticUniversalNonnegativity where
  map := compileOneToFiveOrderAsSignedQuartic
  correct := compileOneToFiveOrderAsSignedQuartic_correct
  coefficient := 1
  degree := 1
  coefficient_positive := by norm_num
  size_bound := by
    intro input
    change duplicateFreeOneToFiveOrderCodeSize input ≤
      1 * duplicateFreeOneToFiveOrderCodeSize input ^ 1
    simp

/-- Explicit stronger hypothesis under which the local sparse-polynomial to
phonological bridge yields the universal-real classification.  This is not
the registered bounded ETR-INV foundation: proving the ETR-INV-to-signed-
quartic compiler remains a separate proof requirement. -/
structure SignedQuarticCompletenessAssumption
    (universalReal : EncodedDecisionClass) where
  signedDistinctQuartic_complete :
    CompleteFor universalReal
      signedDistinctQuarticUniversalNonnegativity
  closed_under_reduction : ∀ {source target},
    PolynomialSizeManyOneReduction source target →
      universalReal target → universalReal source

theorem duplicateFreeOneToFive_universalReal_complete_of_signedQuartic
    {universalReal : EncodedDecisionClass}
    (foundation : SignedQuarticCompletenessAssumption universalReal) :
    CompleteFor universalReal duplicateFreeOneToFiveUniversalOrder := by
  exact complete_of_complete_source
    foundation.signedDistinctQuartic_complete
    (foundation.closed_under_reduction
      oneToFiveToSignedQuarticReduction
      foundation.signedDistinctQuartic_complete.1)
    signedQuarticToOneToFiveReduction

/-- The registered multiplicity-sensitive ledgers. The left input contains
two distinct labels at row one; the right input contains one. -/
inductive MultiplicityLeftCandidate
  | named | copyOne | copyTwo
  deriving DecidableEq, Fintype

inductive MultiplicityRightCandidate
  | named | copy
  deriving DecidableEq, Fintype

def multiplicityLeftLedger :
    CompleteFiniteLedger (Fin 1) MultiplicityLeftCandidate where
  baseMass := fun _ => 1
  row
    | .named => fun _ => 0
    | .copyOne => fun _ => 1
    | .copyTwo => fun _ => 1
  baseMass_pos := by intro; norm_num

def multiplicityRightLedger :
    CompleteFiniteLedger (Fin 1) MultiplicityRightCandidate where
  baseMass := fun _ => 1
  row
    | .named => fun _ => 0
    | .copy => fun _ => 1
  baseMass_pos := by intro; norm_num

/-- **MAX-G4.MULTISET.03, exact counterexample.** Literal row-set equality
does not preserve the probability law when distinct candidate labels repeat a
row. At activity `1/2`, the named probabilities are exactly `1/2` and `2/3`,
and the relative atomic masses at row one are exactly two and one. -/
theorem max_g4_multiset_03_registered :
    rationalNamedCandidateProbability multiplicityLeftLedger.baseMass
        (fun candidate coordinate =>
          multiplicityLeftLedger.row candidate coordinate)
        MultiplicityLeftCandidate.named (fun _ => (1 / 2 : ℝ)) = 1 / 2 ∧
    rationalNamedCandidateProbability multiplicityRightLedger.baseMass
        (fun candidate coordinate =>
          multiplicityRightLedger.row candidate coordinate)
        MultiplicityRightCandidate.named (fun _ => (1 / 2 : ℝ)) = 2 / 3 ∧
    relativeRowMassMeasure multiplicityLeftLedger
        MultiplicityLeftCandidate.named (fun _ => (1 : ℤ)) = 2 ∧
    relativeRowMassMeasure multiplicityRightLedger
        MultiplicityRightCandidate.named (fun _ => (1 : ℤ)) = 1 := by
  classical
  have hLeftUniv : (Finset.univ : Finset MultiplicityLeftCandidate) =
      {MultiplicityLeftCandidate.named,
        MultiplicityLeftCandidate.copyOne,
        MultiplicityLeftCandidate.copyTwo} := by
    ext candidate
    fin_cases candidate <;> simp
  have hRightUniv : (Finset.univ : Finset MultiplicityRightCandidate) =
      {MultiplicityRightCandidate.named,
        MultiplicityRightCandidate.copy} := by
    ext candidate
    fin_cases candidate <;> simp
  have hLeftNamed : relativeViolationRow multiplicityLeftLedger
      MultiplicityLeftCandidate.named MultiplicityLeftCandidate.named ≠
        (fun _ => (1 : ℤ)) := by
    intro h
    have hAtZero := congrFun h (0 : Fin 1)
    norm_num [relativeViolationRow, multiplicityLeftLedger] at hAtZero
  have hLeftCopyOne : relativeViolationRow multiplicityLeftLedger
      MultiplicityLeftCandidate.named MultiplicityLeftCandidate.copyOne =
        (fun _ => (1 : ℤ)) := by
    funext coordinate
    fin_cases coordinate
    norm_num [relativeViolationRow, multiplicityLeftLedger]
  have hLeftCopyTwo : relativeViolationRow multiplicityLeftLedger
      MultiplicityLeftCandidate.named MultiplicityLeftCandidate.copyTwo =
        (fun _ => (1 : ℤ)) := by
    funext coordinate
    fin_cases coordinate
    norm_num [relativeViolationRow, multiplicityLeftLedger]
  have hRightNamed : relativeViolationRow multiplicityRightLedger
      MultiplicityRightCandidate.named MultiplicityRightCandidate.named ≠
        (fun _ => (1 : ℤ)) := by
    intro h
    have hAtZero := congrFun h (0 : Fin 1)
    norm_num [relativeViolationRow, multiplicityRightLedger] at hAtZero
  have hRightCopy : relativeViolationRow multiplicityRightLedger
      MultiplicityRightCandidate.named MultiplicityRightCandidate.copy =
        (fun _ => (1 : ℤ)) := by
    funext coordinate
    fin_cases coordinate
    norm_num [relativeViolationRow, multiplicityRightLedger]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [rationalNamedCandidateProbability, candidateMass, partitionMass,
      laurentMonomial, multiplicityLeftLedger, hLeftUniv,
      Finset.sum_insert]
    norm_num
  · simp [rationalNamedCandidateProbability, candidateMass, partitionMass,
      laurentMonomial, multiplicityRightLedger, hRightUniv,
      Finset.sum_insert]
    norm_num
  · rw [relativeRowMassMeasure, weightedSparseLedgerMass_apply]
    simp only [multiplicityLeftLedger, div_one]
    change (∑ candidate : MultiplicityLeftCandidate,
      if relativeViolationRow multiplicityLeftLedger
          MultiplicityLeftCandidate.named candidate = (fun _ => (1 : ℤ))
        then (1 : ℚ) else 0) = 2
    rw [hLeftUniv]
    have hFilter :
        {candidate ∈
            ({MultiplicityLeftCandidate.named,
              MultiplicityLeftCandidate.copyOne,
              MultiplicityLeftCandidate.copyTwo} :
                Finset MultiplicityLeftCandidate) |
          relativeViolationRow multiplicityLeftLedger
            MultiplicityLeftCandidate.named candidate = (fun _ => (1 : ℤ))} =
          {MultiplicityLeftCandidate.copyOne,
            MultiplicityLeftCandidate.copyTwo} := by
      ext candidate
      fin_cases candidate <;>
        simp [hLeftNamed, hLeftCopyOne, hLeftCopyTwo]
    rw [Finset.sum_boole, hFilter]
    simp
  · rw [relativeRowMassMeasure, weightedSparseLedgerMass_apply]
    simp only [multiplicityRightLedger, div_one]
    change (∑ candidate : MultiplicityRightCandidate,
      if relativeViolationRow multiplicityRightLedger
          MultiplicityRightCandidate.named candidate = (fun _ => (1 : ℤ))
        then (1 : ℚ) else 0) = 1
    rw [hRightUniv]
    have hFilter :
        {candidate ∈
            ({MultiplicityRightCandidate.named,
              MultiplicityRightCandidate.copy} :
                Finset MultiplicityRightCandidate) |
          relativeViolationRow multiplicityRightLedger
            MultiplicityRightCandidate.named candidate = (fun _ => (1 : ℤ))} =
          {MultiplicityRightCandidate.copy} := by
      ext candidate
      fin_cases candidate <;> simp [hRightNamed, hRightCopy]
    rw [Finset.sum_boole, hFilter]
    simp

end PhonologicalCalculus.MaxEnt
