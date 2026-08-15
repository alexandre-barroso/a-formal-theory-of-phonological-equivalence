import PhonologicalCalculus.MaxEnt.FiniteLaw
import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Canonical sparse Laurent carriers and minimal clearing

This module exposes every algebraic object in the MAX-G1 reduction. Candidate
labels are collected into a multiplicity-sensitive sparse Laurent carrier.
Its support determines a componentwise least nonnegative clearing vector and
therefore an integer multivariate polynomial. The construction is extensional:
no ordering or deduplication of candidate labels is hidden in the carrier.
-/

namespace PhonologicalCalculus.MaxEnt

open MvPolynomial

universe uConstraint uCandidate

/-- A Laurent exponent vector over the finite constraint inventory. -/
abbrev LaurentExponent (J : Type uConstraint) := J → ℤ

/-- The sparse integer mass function of one explicitly labelled finite
ledger. Repeated rows contribute repeatedly. -/
noncomputable def sparseLedgerMass
    {J : Type uConstraint} {C : Type uCandidate}
    [DecidableEq J] [Fintype C]
    (row : C → LaurentExponent J) : LaurentExponent J →₀ ℤ :=
  ∑ candidate : C, Finsupp.single (row candidate) 1

/-- The canonical signed carrier comparing two complete finite ledgers. -/
noncomputable def sparseRelativeCarrier
    {J : Type uConstraint} {C₁ C₂ : Type uCandidate}
    [DecidableEq J] [Fintype C₁] [Fintype C₂]
    (row₁ : C₁ → LaurentExponent J)
    (row₂ : C₂ → LaurentExponent J) : LaurentExponent J →₀ ℤ :=
  sparseLedgerMass row₁ - sparseLedgerMass row₂

/-- Multiplicity of one exponent vector in an explicitly labelled ledger. -/
noncomputable def exponentMultiplicity
    {J : Type uConstraint} {C : Type uCandidate}
    [Fintype C]
    (row : C → LaurentExponent J) (exponent : LaurentExponent J) : ℤ := by
  classical
  exact ∑ candidate : C, if row candidate = exponent then 1 else 0

/-- One sparse-ledger coefficient is exactly the number of labels carrying
that row. -/
theorem sparseLedgerMass_apply_eq_multiplicity
    {J : Type uConstraint} {C : Type uCandidate}
    [DecidableEq J] [Fintype C]
    (row : C → LaurentExponent J) (exponent : LaurentExponent J) :
    sparseLedgerMass row exponent = exponentMultiplicity row exponent := by
  classical
  rw [sparseLedgerMass]
  change (Finsupp.applyAddHom exponent)
      (∑ candidate : C, Finsupp.single (row candidate) 1) = _
  rw [map_sum]
  unfold exponentMultiplicity
  apply Finset.sum_congr rfl
  intro candidate _
  by_cases hRow : row candidate = exponent
  · subst exponent
    simp
  · have hReverse : exponent ≠ row candidate := by
      exact fun h => hRow h.symm
    simp [hRow, hReverse]

/-- Every signed carrier coefficient is the exact difference of the two row
multiplicities. -/
theorem sparseRelativeCarrier_apply
    {J : Type uConstraint} {C₁ C₂ : Type uCandidate}
    [DecidableEq J] [Fintype C₁] [Fintype C₂]
    (row₁ : C₁ → LaurentExponent J)
    (row₂ : C₂ → LaurentExponent J) (exponent : LaurentExponent J) :
    sparseRelativeCarrier row₁ row₂ exponent =
      exponentMultiplicity row₁ exponent -
        exponentMultiplicity row₂ exponent := by
  classical
  simp [sparseRelativeCarrier, sparseLedgerMass_apply_eq_multiplicity]

/-- Evaluation of a sparse Laurent carrier. -/
noncomputable def evaluateSparseLaurentLinear
    {J : Type uConstraint} [Fintype J]
    (activity : J → ℝ) : (LaurentExponent J →₀ ℤ) →ₗ[ℤ] ℝ :=
  Finsupp.linearCombination ℤ fun exponent =>
    ∏ coordinate, activity coordinate ^ exponent coordinate

/-- Evaluation of a sparse Laurent carrier. -/
noncomputable def evaluateSparseLaurent
    {J : Type uConstraint} [Fintype J]
    (carrier : LaurentExponent J →₀ ℤ) (activity : J → ℝ) : ℝ :=
  evaluateSparseLaurentLinear activity carrier

theorem evaluateSparseLaurent_eq_sum
    {J : Type uConstraint} [Fintype J]
    (carrier : LaurentExponent J →₀ ℤ) (activity : J → ℝ) :
    evaluateSparseLaurent carrier activity =
      carrier.sum fun exponent coefficient =>
        (coefficient : ℝ) *
          ∏ coordinate, activity coordinate ^ exponent coordinate := by
  classical
  simp [evaluateSparseLaurent, evaluateSparseLaurentLinear,
    Finsupp.linearCombination_apply]

/-- Sparse-ledger evaluation is the explicitly multiplicity-preserving sum
over all candidate labels. -/
theorem evaluateSparseLaurent_sparseLedgerMass
    {J : Type uConstraint} {C : Type uCandidate}
    [DecidableEq J] [Fintype J] [Fintype C]
    (row : C → LaurentExponent J) (activity : J → ℝ) :
    evaluateSparseLaurent (sparseLedgerMass row) activity =
      ∑ candidate : C,
        ∏ coordinate, activity coordinate ^ row candidate coordinate := by
  classical
  simp [evaluateSparseLaurent, evaluateSparseLaurentLinear, sparseLedgerMass]

/-- The signed sparse carrier evaluates to the exact difference of the two
complete labelled-ledger Laurent sums. -/
theorem evaluateSparseLaurent_sparseRelativeCarrier
    {J : Type uConstraint} {C₁ C₂ : Type uCandidate}
    [DecidableEq J] [Fintype J] [Fintype C₁] [Fintype C₂]
    (row₁ : C₁ → LaurentExponent J)
    (row₂ : C₂ → LaurentExponent J) (activity : J → ℝ) :
    evaluateSparseLaurent (sparseRelativeCarrier row₁ row₂) activity =
      (∑ candidate : C₁,
          ∏ coordinate, activity coordinate ^ row₁ candidate coordinate) -
        ∑ candidate : C₂,
          ∏ coordinate, activity coordinate ^ row₂ candidate coordinate := by
  classical
  change evaluateSparseLaurentLinear activity
      (sparseRelativeCarrier row₁ row₂) = _
  rw [sparseRelativeCarrier, map_sub]
  have hFirst := evaluateSparseLaurent_sparseLedgerMass row₁ activity
  have hSecond := evaluateSparseLaurent_sparseLedgerMass row₂ activity
  simpa [evaluateSparseLaurent] using congrArg₂ (· - ·) hFirst hSecond

/-- The componentwise clearing requirement contributed by one exponent. -/
def exponentClearingRequirement
    {J : Type uConstraint} (exponent : LaurentExponent J) (coordinate : J) : ℕ :=
  (-exponent coordinate).toNat

/-- The support-determined clearing vector. -/
noncomputable def minimalClearingShift
    {J : Type uConstraint} (carrier : LaurentExponent J →₀ ℤ) (coordinate : J) : ℕ :=
  carrier.support.sup fun exponent =>
    exponentClearingRequirement exponent coordinate

/-- The clearing vector makes every supported exponent nonnegative. -/
theorem exponent_add_minimalClearingShift_nonnegative
    {J : Type uConstraint} (carrier : LaurentExponent J →₀ ℤ)
    (exponent : LaurentExponent J) (hExponent : exponent ∈ carrier.support)
    (coordinate : J) :
    0 ≤ exponent coordinate + (minimalClearingShift carrier coordinate : ℤ) := by
  have hRequirement : exponentClearingRequirement exponent coordinate ≤
      minimalClearingShift carrier coordinate := by
    exact Finset.le_sup (s := carrier.support)
      (f := fun candidate => exponentClearingRequirement candidate coordinate)
      hExponent
  have hBase : 0 ≤ exponent coordinate +
      (exponentClearingRequirement exponent coordinate : ℤ) := by
    simp only [exponentClearingRequirement]
    omega
  have hRequirementInteger :
      (exponentClearingRequirement exponent coordinate : ℤ) ≤
        (minimalClearingShift carrier coordinate : ℤ) :=
    Int.ofNat_le.2 hRequirement
  linarith

/-- Componentwise minimality: every natural shift that clears the full sparse
support lies above the support supremum. -/
theorem minimalClearingShift_le
    {J : Type uConstraint} (carrier : LaurentExponent J →₀ ℤ)
    (shift : J → ℕ)
    (hClears : ∀ exponent ∈ carrier.support, ∀ coordinate,
      0 ≤ exponent coordinate + (shift coordinate : ℤ)) :
    ∀ coordinate, minimalClearingShift carrier coordinate ≤ shift coordinate := by
  intro coordinate
  apply Finset.sup_le
  intro exponent hExponent
  have hNonnegative := hClears exponent hExponent coordinate
  simp only [exponentClearingRequirement]
  omega

/-! ### Rational base-mass denominator clearing -/

/-- Least common multiple of all reduced denominators on the finite nonzero
support of a rational sparse carrier. -/
noncomputable def rationalDenominatorLCM
    {Exponent : Type*} (carrier : Exponent →₀ ℚ) : ℕ :=
  carrier.support.lcm fun exponent => (carrier exponent).den

/-- Every supported coefficient denominator divides the common LCM. -/
theorem coefficient_denominator_dvd_lcm
    {Exponent : Type*} (carrier : Exponent →₀ ℚ)
    (exponent : Exponent) (hExponent : exponent ∈ carrier.support) :
    (carrier exponent).den ∣ rationalDenominatorLCM carrier := by
  exact Finset.dvd_lcm hExponent

/-- The denominator LCM is the least common positive clearing denominator in
the divisibility order. -/
theorem rationalDenominatorLCM_dvd_of_common
    {Exponent : Type*} (carrier : Exponent →₀ ℚ) (common : ℕ)
    (hCommon : ∀ exponent ∈ carrier.support,
      (carrier exponent).den ∣ common) :
    rationalDenominatorLCM carrier ∣ common := by
  exact Finset.lcm_dvd hCommon

theorem rationalDenominatorLCM_pos
    {Exponent : Type*} (carrier : Exponent →₀ ℚ) :
  0 < rationalDenominatorLCM carrier := by
  apply Nat.pos_of_ne_zero
  unfold rationalDenominatorLCM
  rw [Finset.lcm_ne_zero_iff]
  intro exponent _
  exact (carrier exponent).den_nz

/-- Multiplication by the common denominator turns each supported rational
coefficient into an integer exactly. -/
theorem rationalDenominatorLCM_clears_coefficient
    {Exponent : Type*} (carrier : Exponent →₀ ℚ)
    (exponent : Exponent) (hExponent : exponent ∈ carrier.support) :
    ∃ integerCoefficient : ℤ,
      (integerCoefficient : ℚ) =
        (rationalDenominatorLCM carrier : ℚ) * carrier exponent := by
  let coefficient : ℚ := carrier exponent
  have hDivides : coefficient.den ∣ rationalDenominatorLCM carrier := by
    simpa [coefficient] using
      coefficient_denominator_dvd_lcm carrier exponent hExponent
  obtain ⟨factor, hFactor⟩ := hDivides
  refine ⟨(factor : ℤ) * coefficient.num, ?_⟩
  calc
    (((factor : ℤ) * coefficient.num : ℤ) : ℚ) =
        (factor : ℚ) * (coefficient.num : ℚ) := by push_cast; rfl
    _ = ((coefficient.den * factor : ℕ) : ℚ) *
          ((coefficient.num : ℚ) / (coefficient.den : ℚ)) := by
            rw [Nat.cast_mul]
            field_simp [coefficient.den_nz]
    _ = (rationalDenominatorLCM carrier : ℚ) * coefficient := by
          rw [← hFactor, coefficient.num_div_den]
    _ = (rationalDenominatorLCM carrier : ℚ) * carrier exponent := by
          rfl

/-! ### Complete positive-rational MaxEnt ledger bridge -/

/-- Sparse rational mass of a labelled ledger with explicit coefficient on
each candidate. -/
noncomputable def weightedSparseLedgerMass
    {J : Type uConstraint} {C : Type uCandidate}
    [DecidableEq J] [Fintype C]
    (coefficient : C → ℚ) (row : C → LaurentExponent J) :
    LaurentExponent J →₀ ℚ :=
  ∑ candidate : C, Finsupp.single (row candidate) (coefficient candidate)

/-- Rational cross-product carrier for two named finite-MaxEnt candidates.
Its first half is the second named mass times the first partition; its second
half has the opposite orientation. -/
noncomputable def rationalNamedCrossCarrier
    {J : Type uConstraint} {C₁ C₂ : Type uCandidate}
    [DecidableEq J] [Fintype C₁] [Fintype C₂]
    (baseMass₁ : C₁ → ℚ) (row₁ : C₁ → LaurentExponent J) (named₁ : C₁)
    (baseMass₂ : C₂ → ℚ) (row₂ : C₂ → LaurentExponent J) (named₂ : C₂) :
    LaurentExponent J →₀ ℚ :=
  weightedSparseLedgerMass
      (fun candidate => baseMass₂ named₂ * baseMass₁ candidate)
      (fun candidate coordinate =>
        row₂ named₂ coordinate + row₁ candidate coordinate) -
    weightedSparseLedgerMass
      (fun candidate => baseMass₁ named₁ * baseMass₂ candidate)
      (fun candidate coordinate =>
        row₁ named₁ coordinate + row₂ candidate coordinate)

/-- Rational-coefficient Laurent evaluation in the real ordered field. -/
noncomputable def evaluateRationalSparseLaurentLinear
    {J : Type uConstraint} [Fintype J]
    (activity : J → ℝ) : (LaurentExponent J →₀ ℚ) →ₗ[ℚ] ℝ :=
  Finsupp.linearCombination ℚ fun exponent =>
    ∏ coordinate, activity coordinate ^ exponent coordinate

noncomputable def evaluateRationalSparseLaurent
    {J : Type uConstraint} [Fintype J]
    (carrier : LaurentExponent J →₀ ℚ) (activity : J → ℝ) : ℝ :=
  evaluateRationalSparseLaurentLinear activity carrier

theorem evaluateRationalSparseLaurent_weightedLedger
    {J : Type uConstraint} {C : Type uCandidate}
    [DecidableEq J] [Fintype J] [Fintype C]
    (coefficient : C → ℚ) (row : C → LaurentExponent J)
    (activity : J → ℝ) :
    evaluateRationalSparseLaurent
        (weightedSparseLedgerMass coefficient row) activity =
      ∑ candidate : C, (coefficient candidate : ℝ) *
        ∏ coordinate, activity coordinate ^ row candidate coordinate := by
  classical
  simp [evaluateRationalSparseLaurent,
    evaluateRationalSparseLaurentLinear, weightedSparseLedgerMass,
    Finsupp.linearCombination_apply, Rat.smul_def]

/-- Laurent monomials turn exponent addition into multiplication on a
nonzero activity vector. -/
theorem laurentMonomial_add_of_nonzero
    {J : Type uConstraint} [Fintype J]
    (first second : LaurentExponent J) (activity : J → ℝ)
    (hActivity : ∀ coordinate, activity coordinate ≠ 0) :
    laurentMonomial (fun coordinate =>
        first coordinate + second coordinate) activity =
      laurentMonomial first activity * laurentMonomial second activity := by
  classical
  unfold laurentMonomial
  calc
    (∏ coordinate,
        activity coordinate ^ (first coordinate + second coordinate)) =
        ∏ coordinate,
          (activity coordinate ^ first coordinate) *
            (activity coordinate ^ second coordinate) := by
          apply Finset.prod_congr rfl
          intro coordinate _
          rw [zpow_add₀ (hActivity coordinate)]
    _ = (∏ coordinate, activity coordinate ^ first coordinate) *
          ∏ coordinate, activity coordinate ^ second coordinate := by
          rw [Finset.prod_mul_distrib]

/-- Named candidate probability for a complete finite ledger with rational
base masses and integer violation rows. -/
noncomputable def rationalNamedCandidateProbability
    {J : Type uConstraint} {C : Type uCandidate}
    [Fintype J] [Fintype C]
    (baseMass : C → ℚ) (row : C → LaurentExponent J)
    (named : C) (activity : J → ℝ) : ℝ :=
  candidateMass (fun candidate => (baseMass candidate : ℝ)) row activity named /
    partitionMass (fun candidate => (baseMass candidate : ℝ)) row activity

/-- Evaluation of the rational sparse cross carrier is exactly the normalized
probability cross-product margin. -/
theorem evaluateRationalNamedCrossCarrier_eq_margin
    {J : Type uConstraint} {C₁ C₂ : Type uCandidate}
    [DecidableEq J] [Fintype J] [Fintype C₁] [Fintype C₂]
    (baseMass₁ : C₁ → ℚ) (row₁ : C₁ → LaurentExponent J) (named₁ : C₁)
    (baseMass₂ : C₂ → ℚ) (row₂ : C₂ → LaurentExponent J) (named₂ : C₂)
    (activity : J → ℝ) (hActivity : ∀ coordinate, activity coordinate ≠ 0) :
    evaluateRationalSparseLaurent
        (rationalNamedCrossCarrier baseMass₁ row₁ named₁
          baseMass₂ row₂ named₂) activity =
      candidateMass (fun candidate => (baseMass₂ candidate : ℝ)) row₂
          activity named₂ *
        partitionMass (fun candidate => (baseMass₁ candidate : ℝ)) row₁
          activity -
      candidateMass (fun candidate => (baseMass₁ candidate : ℝ)) row₁
          activity named₁ *
        partitionMass (fun candidate => (baseMass₂ candidate : ℝ)) row₂
          activity := by
  classical
  change evaluateRationalSparseLaurentLinear activity
      (rationalNamedCrossCarrier baseMass₁ row₁ named₁
        baseMass₂ row₂ named₂) = _
  rw [rationalNamedCrossCarrier, map_sub]
  change evaluateRationalSparseLaurent
      (weightedSparseLedgerMass
        (fun candidate => baseMass₂ named₂ * baseMass₁ candidate)
        (fun candidate coordinate =>
          row₂ named₂ coordinate + row₁ candidate coordinate)) activity -
      evaluateRationalSparseLaurent
      (weightedSparseLedgerMass
        (fun candidate => baseMass₁ named₁ * baseMass₂ candidate)
        (fun candidate coordinate =>
          row₁ named₁ coordinate + row₂ candidate coordinate)) activity = _
  rw [evaluateRationalSparseLaurent_weightedLedger,
    evaluateRationalSparseLaurent_weightedLedger]
  unfold partitionMass candidateMass
  rw [Finset.mul_sum, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro candidate _
    change (baseMass₂ named₂ * baseMass₁ candidate : ℚ) *
        laurentMonomial (fun coordinate =>
          row₂ named₂ coordinate + row₁ candidate coordinate) activity = _
    rw [laurentMonomial_add_of_nonzero
      (row₂ named₂) (row₁ candidate) activity hActivity]
    push_cast
    ring
  · apply Finset.sum_congr rfl
    intro candidate _
    change (baseMass₁ named₁ * baseMass₂ candidate : ℚ) *
        laurentMonomial (fun coordinate =>
          row₁ named₁ coordinate + row₂ candidate coordinate) activity = _
    rw [laurentMonomial_add_of_nonzero
      (row₁ named₁) (row₂ candidate) activity hActivity]
    push_cast
    ring

/-- Complete positive-rational finite-MaxEnt named-candidate order reduces
exactly to the sign of the canonical sparse rational carrier. -/
theorem max_g1_completeRationalLedgerCarrier
    {J : Type uConstraint} {C₁ C₂ : Type uCandidate}
    [DecidableEq J] [Fintype J] [Fintype C₁] [Fintype C₂]
    [Nonempty C₁] [Nonempty C₂]
    (baseMass₁ : C₁ → ℚ) (row₁ : C₁ → LaurentExponent J) (named₁ : C₁)
    (baseMass₂ : C₂ → ℚ) (row₂ : C₂ → LaurentExponent J) (named₂ : C₂)
    (activity : J → ℝ)
    (hBase₁ : ∀ candidate, 0 < baseMass₁ candidate)
    (hBase₂ : ∀ candidate, 0 < baseMass₂ candidate)
    (hActivity : ∀ coordinate, 0 < activity coordinate) :
    rationalNamedCandidateProbability baseMass₁ row₁ named₁ activity ≤
        rationalNamedCandidateProbability baseMass₂ row₂ named₂ activity ↔
      0 ≤ evaluateRationalSparseLaurent
        (rationalNamedCrossCarrier baseMass₁ row₁ named₁
          baseMass₂ row₂ named₂) activity := by
  have hRealBase₁ : ∀ candidate, 0 < (baseMass₁ candidate : ℝ) := by
    exact fun candidate => Rat.cast_pos.2 (hBase₁ candidate)
  have hRealBase₂ : ∀ candidate, 0 < (baseMass₂ candidate : ℝ) := by
    exact fun candidate => Rat.cast_pos.2 (hBase₂ candidate)
  have hPartition₁ := partitionMass_pos
    (fun candidate => (baseMass₁ candidate : ℝ)) row₁ activity
    hRealBase₁ hActivity
  have hPartition₂ := partitionMass_pos
    (fun candidate => (baseMass₂ candidate : ℝ)) row₂ activity
    hRealBase₂ hActivity
  rw [rationalNamedCandidateProbability,
    rationalNamedCandidateProbability,
    normalized_order_iff_cross_product hPartition₁ hPartition₂]
  rw [evaluateRationalNamedCrossCarrier_eq_margin
    baseMass₁ row₁ named₁ baseMass₂ row₂ named₂ activity
    (fun coordinate => ne_of_gt (hActivity coordinate))]
  constructor <;> intro hOrder <;> linarith

/-- The natural exponent obtained after applying the least clearing vector. -/
noncomputable def clearedExponent
    {J : Type uConstraint} [Finite J]
    (carrier : LaurentExponent J →₀ ℤ) (exponent : LaurentExponent J) : J →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun coordinate =>
    (exponent coordinate + (minimalClearingShift carrier coordinate : ℤ)).toNat

theorem clearedExponent_apply_of_mem
    {J : Type uConstraint} [Finite J]
    (carrier : LaurentExponent J →₀ ℤ)
    (exponent : LaurentExponent J) (_hExponent : exponent ∈ carrier.support)
    (coordinate : J) :
    (clearedExponent carrier exponent) coordinate =
      (exponent coordinate +
        (minimalClearingShift carrier coordinate : ℤ)).toNat := by
  rfl

/-- Integer polynomial obtained from the multiplicity-sensitive sparse
carrier after the componentwise least Laurent clearing. -/
noncomputable def sparseClearedPolynomial
    {J : Type uConstraint} [DecidableEq J] [Fintype J]
    (carrier : LaurentExponent J →₀ ℤ) : MvPolynomial J ℤ :=
  carrier.sum fun exponent coefficient =>
    monomial (clearedExponent carrier exponent) coefficient

/-- Coefficient collection in `sparseClearedPolynomial` remains explicit:
all source support terms are mapped with their signed integer coefficient. -/
theorem sparseClearedPolynomial_eq_support_sum
    {J : Type uConstraint} [DecidableEq J] [Fintype J]
    (carrier : LaurentExponent J →₀ ℤ) :
    sparseClearedPolynomial carrier =
      ∑ exponent ∈ carrier.support,
        monomial (clearedExponent carrier exponent) (carrier exponent) := by
  classical
  simp [sparseClearedPolynomial, Finsupp.sum]

/-- Evaluation of the cleared sparse carrier before it is bundled as an
`MvPolynomial`. -/
noncomputable def evaluateSparseCleared
    {J : Type uConstraint} [Fintype J]
    (carrier : LaurentExponent J →₀ ℤ) (activity : J → ℝ) : ℝ :=
  carrier.sum fun exponent coefficient =>
    (coefficient : ℝ) *
      ∏ coordinate, activity coordinate ^
        (clearedExponent carrier exponent) coordinate

/-- On nonzero activities, one cleared monomial is exactly the original
Laurent monomial multiplied by the common clearing monomial. -/
theorem clearedMonomial_eq_clearing_mul_laurent
    {J : Type uConstraint} [Fintype J]
    (carrier : LaurentExponent J →₀ ℤ)
    (exponent : LaurentExponent J) (hExponent : exponent ∈ carrier.support)
    (activity : J → ℝ) (hActivity : ∀ coordinate, activity coordinate ≠ 0) :
    (∏ coordinate, activity coordinate ^
        (clearedExponent carrier exponent) coordinate) =
      positiveClearingMonomial (minimalClearingShift carrier) activity *
        ∏ coordinate, activity coordinate ^ exponent coordinate := by
  classical
  calc
    (∏ coordinate, activity coordinate ^
        (clearedExponent carrier exponent) coordinate) =
        ∏ coordinate,
          activity coordinate ^
            (exponent coordinate +
              (minimalClearingShift carrier coordinate : ℤ)) := by
          apply Finset.prod_congr rfl
          intro coordinate _
          rw [clearedExponent_apply_of_mem carrier exponent hExponent]
          rw [← zpow_natCast]
          rw [Int.toNat_of_nonneg
            (exponent_add_minimalClearingShift_nonnegative
              carrier exponent hExponent coordinate)]
    _ = ∏ coordinate,
          (activity coordinate ^ minimalClearingShift carrier coordinate) *
            (activity coordinate ^ exponent coordinate) := by
          apply Finset.prod_congr rfl
          intro coordinate _
          rw [zpow_add₀ (hActivity coordinate), zpow_natCast]
          ring
    _ = positiveClearingMonomial (minimalClearingShift carrier) activity *
          ∏ coordinate, activity coordinate ^ exponent coordinate := by
          rw [Finset.prod_mul_distrib]
          rfl

/-- The complete sparse carrier obeys the same common-factor identity. -/
theorem evaluateSparseCleared_eq_clearing_mul_laurent
    {J : Type uConstraint} [Fintype J]
    (carrier : LaurentExponent J →₀ ℤ)
    (activity : J → ℝ) (hActivity : ∀ coordinate, activity coordinate ≠ 0) :
    evaluateSparseCleared carrier activity =
      positiveClearingMonomial (minimalClearingShift carrier) activity *
        evaluateSparseLaurent carrier activity := by
  classical
  rw [evaluateSparseLaurent_eq_sum]
  unfold evaluateSparseCleared
  simp only [Finsupp.sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro exponent hExponent
  rw [clearedMonomial_eq_clearing_mul_laurent
    carrier exponent hExponent activity hActivity]
  ring

/-- Evaluation of the bundled integer polynomial is the direct cleared
sparse evaluation. -/
theorem eval₂_sparseClearedPolynomial
    {J : Type uConstraint} [DecidableEq J] [Fintype J]
    (carrier : LaurentExponent J →₀ ℤ) (activity : J → ℝ) :
    (sparseClearedPolynomial carrier).eval₂ (Int.castRingHom ℝ) activity =
      evaluateSparseCleared carrier activity := by
  classical
  rw [sparseClearedPolynomial_eq_support_sum,
    MvPolynomial.eval₂_sum]
  unfold evaluateSparseCleared
  apply Finset.sum_congr rfl
  intro exponent _
  simp [MvPolynomial.eval₂_monomial]

/-- The integer polynomial is an exact positive-factor sign carrier on the
physical activity cube. -/
theorem sparseClearedPolynomial_sign_iff
    {J : Type uConstraint} [DecidableEq J] [Fintype J]
    (carrier : LaurentExponent J →₀ ℤ)
    (activity : J → ℝ) (hActivity : ∀ coordinate, 0 < activity coordinate) :
    (0 ≤ (sparseClearedPolynomial carrier).eval₂
        (Int.castRingHom ℝ) activity ↔
      0 ≤ evaluateSparseLaurent carrier activity) ∧
    ((sparseClearedPolynomial carrier).eval₂
        (Int.castRingHom ℝ) activity = 0 ↔
      evaluateSparseLaurent carrier activity = 0) ∧
    (0 < (sparseClearedPolynomial carrier).eval₂
        (Int.castRingHom ℝ) activity ↔
      0 < evaluateSparseLaurent carrier activity) := by
  have hNonzero : ∀ coordinate, activity coordinate ≠ 0 :=
    fun coordinate => ne_of_gt (hActivity coordinate)
  rw [eval₂_sparseClearedPolynomial,
    evaluateSparseCleared_eq_clearing_mul_laurent
      carrier activity hNonzero]
  obtain ⟨hZero, hNonnegative, hPositive⟩ :=
    max_g1_clear_02 (minimalClearingShift carrier) activity
      (evaluateSparseLaurent carrier activity) hActivity
  exact ⟨hNonnegative, hZero, hPositive⟩

/-! ### Rational carrier to integer polynomial -/

/-- Componentwise least exponent shift for a rational sparse Laurent
carrier. -/
noncomputable def rationalMinimalClearingShift
    {J : Type uConstraint} (carrier : LaurentExponent J →₀ ℚ)
    (coordinate : J) : ℕ :=
  carrier.support.sup fun exponent =>
    exponentClearingRequirement exponent coordinate

theorem rationalExponent_add_minimalShift_nonnegative
    {J : Type uConstraint} (carrier : LaurentExponent J →₀ ℚ)
    (exponent : LaurentExponent J) (hExponent : exponent ∈ carrier.support)
    (coordinate : J) :
    0 ≤ exponent coordinate +
      (rationalMinimalClearingShift carrier coordinate : ℤ) := by
  have hRequirement : exponentClearingRequirement exponent coordinate ≤
      rationalMinimalClearingShift carrier coordinate :=
    Finset.le_sup (s := carrier.support)
      (f := fun candidate => exponentClearingRequirement candidate coordinate)
      hExponent
  have hBase : 0 ≤ exponent coordinate +
      (exponentClearingRequirement exponent coordinate : ℤ) := by
    simp only [exponentClearingRequirement]
    omega
  have hRequirementInteger :
      (exponentClearingRequirement exponent coordinate : ℤ) ≤
        (rationalMinimalClearingShift carrier coordinate : ℤ) :=
    Int.ofNat_le.2 hRequirement
  linarith

theorem rationalMinimalClearingShift_le
    {J : Type uConstraint} (carrier : LaurentExponent J →₀ ℚ)
    (shift : J → ℕ)
    (hClears : ∀ exponent ∈ carrier.support, ∀ coordinate,
      0 ≤ exponent coordinate + (shift coordinate : ℤ)) :
    ∀ coordinate,
      rationalMinimalClearingShift carrier coordinate ≤ shift coordinate := by
  intro coordinate
  apply Finset.sup_le
  intro exponent hExponent
  have hNonnegative := hClears exponent hExponent coordinate
  simp only [exponentClearingRequirement]
  omega

/-- Explicit integer coefficient obtained by the least common denominator. -/
noncomputable def lcmScaledIntegerCoefficient
    {Exponent : Type*} (carrier : Exponent →₀ ℚ)
    (exponent : Exponent) : ℤ :=
  (carrier exponent).num *
    (rationalDenominatorLCM carrier / (carrier exponent).den : ℕ)

theorem lcmScaledIntegerCoefficient_cast
    {Exponent : Type*} (carrier : Exponent →₀ ℚ)
    (exponent : Exponent) (hExponent : exponent ∈ carrier.support) :
    (lcmScaledIntegerCoefficient carrier exponent : ℚ) =
      (rationalDenominatorLCM carrier : ℚ) * carrier exponent := by
  have hDivides := coefficient_denominator_dvd_lcm
    carrier exponent hExponent
  obtain ⟨factor, hFactor⟩ := hDivides
  have hDenominatorPositive : 0 < (carrier exponent).den :=
    Nat.pos_of_ne_zero (carrier exponent).den_nz
  have hQuotient :
      rationalDenominatorLCM carrier / (carrier exponent).den = factor := by
    rw [hFactor]
    exact Nat.mul_div_cancel_left factor hDenominatorPositive
  rw [lcmScaledIntegerCoefficient, hQuotient]
  calc
    ((((carrier exponent).num * (factor : ℕ) : ℤ)) : ℚ) =
        ((carrier exponent).num : ℚ) * (factor : ℚ) := by push_cast; rfl
    _ = (((carrier exponent).den * factor : ℕ) : ℚ) *
          (((carrier exponent).num : ℚ) /
            ((carrier exponent).den : ℚ)) := by
          rw [Nat.cast_mul]
          field_simp [(carrier exponent).den_nz]
    _ = (rationalDenominatorLCM carrier : ℚ) * carrier exponent := by
          rw [← hFactor, (carrier exponent).num_div_den]

/-- Cleared natural exponent for a rational sparse carrier. -/
noncomputable def rationalClearedExponent
    {J : Type uConstraint} [Finite J]
    (carrier : LaurentExponent J →₀ ℚ)
    (exponent : LaurentExponent J) : J →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun coordinate =>
    (exponent coordinate +
      (rationalMinimalClearingShift carrier coordinate : ℤ)).toNat

@[simp]
theorem rationalClearedExponent_apply
    {J : Type uConstraint} [Finite J]
    (carrier : LaurentExponent J →₀ ℚ)
    (exponent : LaurentExponent J) (coordinate : J) :
    rationalClearedExponent carrier exponent coordinate =
      (exponent coordinate +
        (rationalMinimalClearingShift carrier coordinate : ℤ)).toNat := by
  rfl

/-- Integer polynomial obtained by simultaneous denominator and exponent
clearing of a rational sparse Laurent carrier. -/
noncomputable def rationalClearedIntegerPolynomial
    {J : Type uConstraint} [DecidableEq J] [Fintype J]
    (carrier : LaurentExponent J →₀ ℚ) : MvPolynomial J ℤ :=
  carrier.sum fun exponent _ =>
    monomial (rationalClearedExponent carrier exponent)
      (lcmScaledIntegerCoefficient carrier exponent)

noncomputable def evaluateRationalClearedInteger
    {J : Type uConstraint} [Fintype J]
    (carrier : LaurentExponent J →₀ ℚ) (activity : J → ℝ) : ℝ :=
  carrier.sum fun exponent _ =>
    (lcmScaledIntegerCoefficient carrier exponent : ℝ) *
      ∏ coordinate, activity coordinate ^
        (rationalClearedExponent carrier exponent) coordinate

theorem evaluateRationalSparseLaurent_eq_sum
    {J : Type uConstraint} [Fintype J]
    (carrier : LaurentExponent J →₀ ℚ) (activity : J → ℝ) :
    evaluateRationalSparseLaurent carrier activity =
      carrier.sum fun exponent coefficient =>
        (coefficient : ℝ) *
          ∏ coordinate, activity coordinate ^ exponent coordinate := by
  classical
  simp [evaluateRationalSparseLaurent,
    evaluateRationalSparseLaurentLinear, Finsupp.linearCombination_apply,
    Rat.smul_def]

theorem rationalClearedMonomial_eq
    {J : Type uConstraint} [Fintype J]
    (carrier : LaurentExponent J →₀ ℚ)
    (exponent : LaurentExponent J) (hExponent : exponent ∈ carrier.support)
    (activity : J → ℝ) (hActivity : ∀ coordinate, activity coordinate ≠ 0) :
    (∏ coordinate, activity coordinate ^
        (rationalClearedExponent carrier exponent) coordinate) =
      positiveClearingMonomial
          (rationalMinimalClearingShift carrier) activity *
        ∏ coordinate, activity coordinate ^ exponent coordinate := by
  classical
  calc
    (∏ coordinate, activity coordinate ^
        (rationalClearedExponent carrier exponent) coordinate) =
        ∏ coordinate,
          activity coordinate ^
            (exponent coordinate +
              (rationalMinimalClearingShift carrier coordinate : ℤ)) := by
          apply Finset.prod_congr rfl
          intro coordinate _
          rw [rationalClearedExponent_apply]
          rw [← zpow_natCast]
          rw [Int.toNat_of_nonneg
            (rationalExponent_add_minimalShift_nonnegative
              carrier exponent hExponent coordinate)]
    _ = ∏ coordinate,
          (activity coordinate ^
              rationalMinimalClearingShift carrier coordinate) *
            (activity coordinate ^ exponent coordinate) := by
          apply Finset.prod_congr rfl
          intro coordinate _
          rw [zpow_add₀ (hActivity coordinate), zpow_natCast]
          ring
    _ = positiveClearingMonomial
          (rationalMinimalClearingShift carrier) activity *
          ∏ coordinate, activity coordinate ^ exponent coordinate := by
          rw [Finset.prod_mul_distrib]
          rfl

theorem evaluateRationalClearedInteger_factorization
    {J : Type uConstraint} [Fintype J]
    (carrier : LaurentExponent J →₀ ℚ)
    (activity : J → ℝ) (hActivity : ∀ coordinate, activity coordinate ≠ 0) :
    evaluateRationalClearedInteger carrier activity =
      (rationalDenominatorLCM carrier : ℝ) *
        positiveClearingMonomial
          (rationalMinimalClearingShift carrier) activity *
        evaluateRationalSparseLaurent carrier activity := by
  classical
  rw [evaluateRationalSparseLaurent_eq_sum]
  unfold evaluateRationalClearedInteger
  simp only [Finsupp.sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro exponent hExponent
  rw [rationalClearedMonomial_eq
    carrier exponent hExponent activity hActivity]
  have hCoefficient := lcmScaledIntegerCoefficient_cast
    carrier exponent hExponent
  have hCoefficientReal :
      (lcmScaledIntegerCoefficient carrier exponent : ℝ) =
        (rationalDenominatorLCM carrier : ℝ) *
          (carrier exponent : ℝ) := by
    exact_mod_cast hCoefficient
  rw [hCoefficientReal]
  ring

theorem eval₂_rationalClearedIntegerPolynomial
    {J : Type uConstraint} [DecidableEq J] [Fintype J]
    (carrier : LaurentExponent J →₀ ℚ) (activity : J → ℝ) :
    (rationalClearedIntegerPolynomial carrier).eval₂
        (Int.castRingHom ℝ) activity =
      evaluateRationalClearedInteger carrier activity := by
  classical
  unfold rationalClearedIntegerPolynomial evaluateRationalClearedInteger
  simp only [Finsupp.sum, MvPolynomial.eval₂_sum]
  apply Finset.sum_congr rfl
  intro exponent _
  simp [MvPolynomial.eval₂_monomial]

/-- Exact sign identity for the rational-to-integer MAX-G1 reduction. -/
theorem rationalClearedIntegerPolynomial_sign_iff
    {J : Type uConstraint} [DecidableEq J] [Fintype J]
    (carrier : LaurentExponent J →₀ ℚ)
    (activity : J → ℝ) (hActivity : ∀ coordinate, 0 < activity coordinate) :
    (0 ≤ (rationalClearedIntegerPolynomial carrier).eval₂
        (Int.castRingHom ℝ) activity ↔
      0 ≤ evaluateRationalSparseLaurent carrier activity) ∧
    ((rationalClearedIntegerPolynomial carrier).eval₂
        (Int.castRingHom ℝ) activity = 0 ↔
      evaluateRationalSparseLaurent carrier activity = 0) ∧
    (0 < (rationalClearedIntegerPolynomial carrier).eval₂
        (Int.castRingHom ℝ) activity ↔
      0 < evaluateRationalSparseLaurent carrier activity) := by
  have hActivityNonzero : ∀ coordinate, activity coordinate ≠ 0 :=
    fun coordinate => ne_of_gt (hActivity coordinate)
  rw [eval₂_rationalClearedIntegerPolynomial,
    evaluateRationalClearedInteger_factorization
      carrier activity hActivityNonzero]
  have hDenominator : 0 < (rationalDenominatorLCM carrier : ℝ) := by
    exact_mod_cast rationalDenominatorLCM_pos carrier
  have hMonomial := positiveClearingMonomial_pos
    (rationalMinimalClearingShift carrier) activity hActivity
  have hFactor : 0 < (rationalDenominatorLCM carrier : ℝ) *
      positiveClearingMonomial
        (rationalMinimalClearingShift carrier) activity :=
    mul_pos hDenominator hMonomial
  constructor
  · exact positive_clearing_preserves_nonneg hFactor
  constructor
  · simp [ne_of_gt hFactor]
  · exact mul_pos_iff_of_pos_left hFactor

/-- Complete positive-rational named-candidate MAX-G1 reduction to one
explicit integer multivariate polynomial. -/
theorem max_g1_completeRationalSparsePolynomialCarrier
    {J : Type uConstraint} {C₁ C₂ : Type uCandidate}
    [DecidableEq J] [Fintype J] [Fintype C₁] [Fintype C₂]
    [Nonempty C₁] [Nonempty C₂]
    (baseMass₁ : C₁ → ℚ) (row₁ : C₁ → LaurentExponent J) (named₁ : C₁)
    (baseMass₂ : C₂ → ℚ) (row₂ : C₂ → LaurentExponent J) (named₂ : C₂)
    (activity : J → ℝ)
    (hBase₁ : ∀ candidate, 0 < baseMass₁ candidate)
    (hBase₂ : ∀ candidate, 0 < baseMass₂ candidate)
    (hActivity : ∀ coordinate, 0 < activity coordinate) :
    rationalNamedCandidateProbability baseMass₁ row₁ named₁ activity ≤
        rationalNamedCandidateProbability baseMass₂ row₂ named₂ activity ↔
      0 ≤ (rationalClearedIntegerPolynomial
        (rationalNamedCrossCarrier baseMass₁ row₁ named₁
          baseMass₂ row₂ named₂)).eval₂
        (Int.castRingHom ℝ) activity := by
  rw [max_g1_completeRationalLedgerCarrier
    baseMass₁ row₁ named₁ baseMass₂ row₂ named₂ activity
    hBase₁ hBase₂ hActivity]
  exact (rationalClearedIntegerPolynomial_sign_iff
    (rationalNamedCrossCarrier baseMass₁ row₁ named₁
      baseMass₂ row₂ named₂) activity hActivity).1.symm

/-- MAX-G1 canonical carrier and minimal-clearing package. -/
theorem max_g1_sparseCarrier_minimalClearing
    {J : Type uConstraint} {C₁ C₂ : Type uCandidate}
    [DecidableEq J] [Fintype J] [Fintype C₁] [Fintype C₂]
    (row₁ : C₁ → LaurentExponent J)
    (row₂ : C₂ → LaurentExponent J) :
    (∀ exponent,
      sparseRelativeCarrier row₁ row₂ exponent =
        exponentMultiplicity row₁ exponent -
          exponentMultiplicity row₂ exponent) ∧
      (∀ exponent ∈ (sparseRelativeCarrier row₁ row₂).support,
        ∀ coordinate,
          0 ≤ exponent coordinate +
            (minimalClearingShift
              (sparseRelativeCarrier row₁ row₂) coordinate : ℤ)) ∧
      (∀ shift : J → ℕ,
        (∀ exponent ∈ (sparseRelativeCarrier row₁ row₂).support,
          ∀ coordinate,
            0 ≤ exponent coordinate + (shift coordinate : ℤ)) →
        ∀ coordinate,
          minimalClearingShift (sparseRelativeCarrier row₁ row₂) coordinate ≤
            shift coordinate) ∧
      sparseClearedPolynomial (sparseRelativeCarrier row₁ row₂) =
        ∑ exponent ∈ (sparseRelativeCarrier row₁ row₂).support,
          monomial
            (clearedExponent (sparseRelativeCarrier row₁ row₂) exponent)
            (sparseRelativeCarrier row₁ row₂ exponent) := by
  exact ⟨sparseRelativeCarrier_apply row₁ row₂,
    fun exponent hExponent coordinate =>
      exponent_add_minimalClearingShift_nonnegative
        (sparseRelativeCarrier row₁ row₂) exponent hExponent coordinate,
    fun shift hClears =>
      minimalClearingShift_le (sparseRelativeCarrier row₁ row₂) shift hClears,
    sparseClearedPolynomial_eq_support_sum
      (sparseRelativeCarrier row₁ row₂)⟩

/-- Complete MAX-G1 sparse-carrier package, including exact evaluation and
sign transport to the componentwise minimally cleared integer polynomial. -/
theorem max_g1_sparsePolynomialCarrier
    {J : Type uConstraint} {C₁ C₂ : Type uCandidate}
    [DecidableEq J] [Fintype J] [Fintype C₁] [Fintype C₂]
    (row₁ : C₁ → LaurentExponent J)
    (row₂ : C₂ → LaurentExponent J)
    (activity : J → ℝ) (hActivity : ∀ coordinate, 0 < activity coordinate) :
    evaluateSparseLaurent (sparseRelativeCarrier row₁ row₂) activity =
        (∑ candidate : C₁,
            ∏ coordinate, activity coordinate ^ row₁ candidate coordinate) -
          ∑ candidate : C₂,
            ∏ coordinate, activity coordinate ^ row₂ candidate coordinate ∧
      (0 ≤ (sparseClearedPolynomial
          (sparseRelativeCarrier row₁ row₂)).eval₂
          (Int.castRingHom ℝ) activity ↔
        0 ≤ evaluateSparseLaurent
          (sparseRelativeCarrier row₁ row₂) activity) ∧
      ((sparseClearedPolynomial
          (sparseRelativeCarrier row₁ row₂)).eval₂
          (Int.castRingHom ℝ) activity = 0 ↔
        evaluateSparseLaurent
          (sparseRelativeCarrier row₁ row₂) activity = 0) ∧
      (0 < (sparseClearedPolynomial
          (sparseRelativeCarrier row₁ row₂)).eval₂
          (Int.castRingHom ℝ) activity ↔
        0 < evaluateSparseLaurent
          (sparseRelativeCarrier row₁ row₂) activity) := by
  exact ⟨evaluateSparseLaurent_sparseRelativeCarrier row₁ row₂ activity,
    (sparseClearedPolynomial_sign_iff
      (sparseRelativeCarrier row₁ row₂) activity hActivity).1,
    (sparseClearedPolynomial_sign_iff
      (sparseRelativeCarrier row₁ row₂) activity hActivity).2.1,
    (sparseClearedPolynomial_sign_iff
      (sparseRelativeCarrier row₁ row₂) activity hActivity).2.2⟩

end PhonologicalCalculus.MaxEnt
