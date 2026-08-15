import PhonologicalCalculus.MaxEnt.FiniteLaw
import Mathlib.Algebra.MvPolynomial.Eval

/-!
Exact multiplicity-preserving compilation of an integer multivariate
polynomial into two finite MaxEnt alternative ledgers.

Each unit of a positive or negative coefficient becomes a separately labelled
alternative.  Repeated violation rows are therefore retained with their full
multiplicity.  The difference between the two alternative partition sums is
the source polynomial itself, both as a formal polynomial and after every
evaluation in a commutative ring.
-/

namespace PhonologicalCalculus.MaxEnt

open MvPolynomial

section CoefficientSplitting

/-- Positive multiplicity of an integer coefficient. -/
def positiveMultiplicity (coefficient : ℤ) : ℕ :=
  coefficient.toNat

/-- Negative multiplicity of an integer coefficient. -/
def negativeMultiplicity (coefficient : ℤ) : ℕ :=
  (-coefficient).toNat

/-- Signed reconstruction from positive and negative coefficient copies. -/
theorem positiveMultiplicity_sub_negativeMultiplicity (coefficient : ℤ) :
    (positiveMultiplicity coefficient : ℤ) -
        (negativeMultiplicity coefficient : ℤ) = coefficient := by
  cases coefficient <;> simp [positiveMultiplicity, negativeMultiplicity] <;>
    omega

/-- Total number of coefficient copies is the absolute coefficient. -/
theorem positiveMultiplicity_add_negativeMultiplicity (coefficient : ℤ) :
    positiveMultiplicity coefficient + negativeMultiplicity coefficient =
      coefficient.natAbs := by
  cases coefficient <;> simp [positiveMultiplicity, negativeMultiplicity]

end CoefficientSplitting

section Compiler

variable {J : Type*} [DecidableEq J]

/-- Positive-side alternative rows.  The multiset representation records one
labelled candidate for every coefficient unit. -/
def positiveAlternativeRows (polynomial : MvPolynomial J ℤ) :
    Multiset (J →₀ ℕ) :=
  polynomial.support.1.bind fun exponent ↦
    Multiset.replicate
      (positiveMultiplicity (polynomial.coeff exponent)) exponent

/-- Negative-side alternative rows, again retaining one label per coefficient
unit. -/
def negativeAlternativeRows (polynomial : MvPolynomial J ℤ) :
    Multiset (J →₀ ℕ) :=
  polynomial.support.1.bind fun exponent ↦
    Multiset.replicate
      (negativeMultiplicity (polynomial.coeff exponent)) exponent

/-- Formal polynomial represented by a multiset of unit-mass alternative
rows. -/
noncomputable def alternativeRowsPolynomial (rows : Multiset (J →₀ ℕ)) :
    MvPolynomial J ℤ :=
  (rows.map fun exponent ↦ monomial exponent 1).sum

/-- Relative-partition difference of the compiled two-input ledger. -/
noncomputable def compiledRelativePartitionPolynomial
    (polynomial : MvPolynomial J ℤ) :
    MvPolynomial J ℤ :=
  alternativeRowsPolynomial (positiveAlternativeRows polynomial) -
    alternativeRowsPolynomial (negativeAlternativeRows polynomial)

/-- The positive ledger polynomial is the positive coefficient part of the
source support expansion. -/
theorem alternativeRowsPolynomial_positiveAlternativeRows
    (polynomial : MvPolynomial J ℤ) :
    alternativeRowsPolynomial (positiveAlternativeRows polynomial) =
      ∑ exponent ∈ polynomial.support,
        positiveMultiplicity (polynomial.coeff exponent) •
          monomial exponent (1 : ℤ) := by
  classical
  simp [alternativeRowsPolynomial, positiveAlternativeRows,
    Multiset.map_bind, Multiset.sum_bind, Multiset.map_replicate,
    Multiset.sum_replicate, nsmul_eq_mul]

/-- The negative ledger polynomial is the negative coefficient part of the
source support expansion. -/
theorem alternativeRowsPolynomial_negativeAlternativeRows
    (polynomial : MvPolynomial J ℤ) :
    alternativeRowsPolynomial (negativeAlternativeRows polynomial) =
      ∑ exponent ∈ polynomial.support,
        negativeMultiplicity (polynomial.coeff exponent) •
          monomial exponent (1 : ℤ) := by
  classical
  simp [alternativeRowsPolynomial, negativeAlternativeRows,
    Multiset.map_bind, Multiset.sum_bind, Multiset.map_replicate,
    Multiset.sum_replicate, nsmul_eq_mul]

/-- **MAX-G2 compiler core.**  Every integer multivariate polynomial is
exactly the relative-partition difference of its two finite unit-mass
alternative ledgers. -/
theorem compiledRelativePartitionPolynomial_eq
    (polynomial : MvPolynomial J ℤ) :
    compiledRelativePartitionPolynomial polynomial = polynomial := by
  classical
  rw [compiledRelativePartitionPolynomial,
    alternativeRowsPolynomial_positiveAlternativeRows,
    alternativeRowsPolynomial_negativeAlternativeRows]
  rw [← Finset.sum_sub_distrib]
  calc
    ∑ exponent ∈ polynomial.support,
        (positiveMultiplicity (polynomial.coeff exponent) •
            monomial exponent (1 : ℤ) -
          negativeMultiplicity (polynomial.coeff exponent) •
            monomial exponent (1 : ℤ)) =
        ∑ exponent ∈ polynomial.support,
          monomial exponent (polynomial.coeff exponent) := by
            apply Finset.sum_congr rfl
            intro exponent _
            simp only [smul_monomial, nsmul_eq_mul, mul_one]
            calc
              monomial exponent
                    (positiveMultiplicity (polynomial.coeff exponent) : ℤ) -
                  monomial exponent
                    (negativeMultiplicity (polynomial.coeff exponent) : ℤ) =
                monomial exponent
                  ((positiveMultiplicity (polynomial.coeff exponent) : ℤ) -
                    (negativeMultiplicity
                      (polynomial.coeff exponent) : ℤ)) := by
                        rw [map_sub]
              _ = monomial exponent (polynomial.coeff exponent) := by
                rw [positiveMultiplicity_sub_negativeMultiplicity]
    _ = polynomial := support_sum_monomial_coeff polynomial

/-- Multiplicity of one violation row across both compiled alternative
ledgers. -/
def compiledRowMultiplicity (polynomial : MvPolynomial J ℤ)
    (exponent : J →₀ ℕ) : ℕ :=
  (positiveAlternativeRows polynomial).count exponent +
    (negativeAlternativeRows polynomial).count exponent

/-- Positive-ledger multiplicity of one exponent. -/
theorem count_positiveAlternativeRows
    (polynomial : MvPolynomial J ℤ) (exponent : J →₀ ℕ) :
    (positiveAlternativeRows polynomial).count exponent =
      positiveMultiplicity (polynomial.coeff exponent) := by
  classical
  rw [positiveAlternativeRows, Multiset.count_bind]
  change (∑ candidate ∈ polynomial.support,
      Multiset.count exponent
        (Multiset.replicate
          (positiveMultiplicity (polynomial.coeff candidate)) candidate)) =
    positiveMultiplicity (polynomial.coeff exponent)
  by_cases hexponent : exponent ∈ polynomial.support
  · rw [Finset.sum_eq_single exponent]
    · exact Multiset.count_replicate_self exponent _
    · intro candidate _ hcandidate
      rw [Multiset.count_replicate]
      simp [hcandidate]
    · exact fun hnot ↦ (hnot hexponent).elim
  · have hcoefficient : polynomial.coeff exponent = 0 :=
      MvPolynomial.notMem_support_iff.mp hexponent
    rw [hcoefficient]
    simp only [positiveMultiplicity, Int.toNat_zero]
    apply Finset.sum_eq_zero
    intro candidate hcandidate
    rw [Multiset.count_replicate]
    simp only [ite_eq_right_iff]
    intro hcandidateExponent
    subst candidate
    exact (hexponent hcandidate).elim

/-- Negative-ledger multiplicity of one exponent. -/
theorem count_negativeAlternativeRows
    (polynomial : MvPolynomial J ℤ) (exponent : J →₀ ℕ) :
    (negativeAlternativeRows polynomial).count exponent =
      negativeMultiplicity (polynomial.coeff exponent) := by
  classical
  rw [negativeAlternativeRows, Multiset.count_bind]
  change (∑ candidate ∈ polynomial.support,
      Multiset.count exponent
        (Multiset.replicate
          (negativeMultiplicity (polynomial.coeff candidate)) candidate)) =
    negativeMultiplicity (polynomial.coeff exponent)
  by_cases hexponent : exponent ∈ polynomial.support
  · rw [Finset.sum_eq_single exponent]
    · exact Multiset.count_replicate_self exponent _
    · intro candidate _ hcandidate
      rw [Multiset.count_replicate]
      simp [hcandidate]
    · exact fun hnot ↦ (hnot hexponent).elim
  · have hcoefficient : polynomial.coeff exponent = 0 :=
      MvPolynomial.notMem_support_iff.mp hexponent
    rw [hcoefficient]
    simp only [negativeMultiplicity, neg_zero, Int.toNat_zero]
    apply Finset.sum_eq_zero
    intro candidate hcandidate
    rw [Multiset.count_replicate]
    simp only [ite_eq_right_iff]
    intro hcandidateExponent
    subst candidate
    exact (hexponent hcandidate).elim

/-- **MAX-G2 per-row multiplicity clause.**  Every exponent occurs across
the two ledgers exactly as many times as the absolute value of its source
coefficient, including the zero multiplicity outside the source support. -/
theorem compiledRowMultiplicity_eq_natAbs_coefficient
    (polynomial : MvPolynomial J ℤ) (exponent : J →₀ ℕ) :
    compiledRowMultiplicity polynomial exponent =
      (polynomial.coeff exponent).natAbs := by
  rw [compiledRowMultiplicity, count_positiveAlternativeRows,
    count_negativeAlternativeRows,
    positiveMultiplicity_add_negativeMultiplicity]

/-- Candidate-count identity for the multiplicity-preserving compiler. -/
theorem compiledAlternativeRows_card
    (polynomial : MvPolynomial J ℤ) :
    (positiveAlternativeRows polynomial).card +
        (negativeAlternativeRows polynomial).card =
      ∑ exponent ∈ polynomial.support,
        (polynomial.coeff exponent).natAbs := by
  classical
  simp only [positiveAlternativeRows, negativeAlternativeRows,
    Multiset.card_bind]
  simp only [Function.comp_apply, Multiset.card_replicate,
    Finset.sum_val]
  rw [← Multiset.sum_map_add]
  congr 1
  exact Multiset.map_congr rfl fun exponent _ ↦
    positiveMultiplicity_add_negativeMultiplicity
      (polynomial.coeff exponent)

/-- The two named zero-row candidates add exactly two candidates to the
alternative count. -/
theorem compiledCandidateCount_eq
    (polynomial : MvPolynomial J ℤ) :
    2 + (positiveAlternativeRows polynomial).card +
          (negativeAlternativeRows polynomial).card =
      2 + ∑ exponent ∈ polynomial.support,
        (polynomial.coeff exponent).natAbs := by
  rw [add_assoc, compiledAlternativeRows_card]

/-- Left input candidate labels: index zero is named and every remaining index
labels one positive alternative copy. -/
abbrev CompiledLeftCandidate (polynomial : MvPolynomial J ℤ) :=
  Fin (1 + (positiveAlternativeRows polynomial).card)

/-- Right input candidate labels: index zero is named and every remaining
index labels one negative alternative copy. -/
abbrev CompiledRightCandidate (polynomial : MvPolynomial J ℤ) :=
  Fin (1 + (negativeAlternativeRows polynomial).card)

/-- The named left candidate has the zero violation row. -/
def compiledLeftNamedRow (_polynomial : MvPolynomial J ℤ) : J →₀ ℕ :=
  0

/-- The named right candidate has the zero violation row. -/
def compiledRightNamedRow (_polynomial : MvPolynomial J ℤ) : J →₀ ℕ :=
  0

/-- Unit base mass on every candidate label. -/
def compiledUnitBaseMass {Candidate : Type*} (_ : Candidate) : ℚ :=
  1

/-- **MAX-G2 well-formed ledger package.**  Both candidate types are finite
and nonempty, their named candidates have the zero row, and every labelled
candidate has positive unit base mass. -/
theorem compiledLedgerPair_wellFormed
    (polynomial : MvPolynomial J ℤ) :
    Finite (CompiledLeftCandidate polynomial) ∧
    Finite (CompiledRightCandidate polynomial) ∧
    Nonempty (CompiledLeftCandidate polynomial) ∧
    Nonempty (CompiledRightCandidate polynomial) ∧
    compiledLeftNamedRow polynomial = 0 ∧
    compiledRightNamedRow polynomial = 0 ∧
    (∀ candidate : CompiledLeftCandidate polynomial,
      compiledUnitBaseMass candidate = 1 ∧
        0 < compiledUnitBaseMass candidate) ∧
    (∀ candidate : CompiledRightCandidate polynomial,
      compiledUnitBaseMass candidate = 1 ∧
        0 < compiledUnitBaseMass candidate) := by
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, rfl, rfl,
    ?_, ?_⟩ <;> intro candidate <;> norm_num [compiledUnitBaseMass]

/-- Exact semantic evaluation of the compiled relative-partition difference
in an arbitrary commutative ring. -/
theorem eval2_compiledRelativePartitionPolynomial
    {R : Type*} [CommRing R] (coefficientMap : ℤ →+* R)
    (activity : J → R) (polynomial : MvPolynomial J ℤ) :
    (compiledRelativePartitionPolynomial polynomial).eval₂
        coefficientMap activity =
      polynomial.eval₂ coefficientMap activity := by
  rw [compiledRelativePartitionPolynomial_eq]

/-- Compiler sign preservation after evaluation in an ordered commutative
ring.  This is the exact Boolean probability-order carrier once the positive
partition denominators have been cleared. -/
theorem compiledRelativePartition_nonnegative_iff
    {R : Type*} [CommRing R] [PartialOrder R]
    (coefficientMap : ℤ →+* R) (activity : J → R)
    (polynomial : MvPolynomial J ℤ) :
    0 ≤ (compiledRelativePartitionPolynomial polynomial).eval₂
        coefficientMap activity ↔
      0 ≤ polynomial.eval₂ coefficientMap activity := by
  rw [eval2_compiledRelativePartitionPolynomial]

/-- The universal order verdict is preserved pointwise on every declared
activity domain, without any assumption about how that domain is presented. -/
theorem compiledRelativePartition_universal_nonnegative_iff
    {R : Type*} [CommRing R] [PartialOrder R]
    (coefficientMap : ℤ →+* R) (domain : Set (J → R))
    (polynomial : MvPolynomial J ℤ) :
    (∀ activity ∈ domain,
        0 ≤ (compiledRelativePartitionPolynomial polynomial).eval₂
          coefficientMap activity) ↔
      (∀ activity ∈ domain,
        0 ≤ polynomial.eval₂ coefficientMap activity) := by
  simp only [eval2_compiledRelativePartitionPolynomial]

section ProbabilitySemantics

/-- Evaluation of a unit-mass multiset of alternative rows. -/
def evaluateAlternativeRows (rows : Multiset (J →₀ ℕ))
    (activity : J → ℝ) : ℝ :=
  (rows.map fun exponent ↦
    exponent.prod fun coordinate power ↦ activity coordinate ^ power).sum

/-- Named probability at the input carrying the positive coefficient copies. -/
noncomputable def compiledLeftNamedProbability
    (polynomial : MvPolynomial J ℤ)
    (activity : J → ℝ) : ℝ :=
  1 / (1 + evaluateAlternativeRows
    (positiveAlternativeRows polynomial) activity)

/-- Named probability at the input carrying the negative coefficient copies. -/
noncomputable def compiledRightNamedProbability
    (polynomial : MvPolynomial J ℤ)
    (activity : J → ℝ) : ℝ :=
  1 / (1 + evaluateAlternativeRows
    (negativeAlternativeRows polynomial) activity)

/-- Formal row-polynomial evaluation equals the explicit labelled-candidate
sum. -/
theorem eval2_alternativeRowsPolynomial
    (rows : Multiset (J →₀ ℕ)) (activity : J → ℝ) :
    (alternativeRowsPolynomial rows).eval₂ (Int.castRingHom ℝ) activity =
      evaluateAlternativeRows rows activity := by
  induction rows using Multiset.induction_on with
  | empty => simp [alternativeRowsPolynomial, evaluateAlternativeRows]
  | @cons exponent rows inductionHypothesis =>
      rw [show alternativeRowsPolynomial (exponent ::ₘ rows) =
          monomial exponent (1 : ℤ) +
            alternativeRowsPolynomial rows by
        simp [alternativeRowsPolynomial]]
      rw [show evaluateAlternativeRows (exponent ::ₘ rows) activity =
          exponent.prod
              (fun coordinate power ↦ activity coordinate ^ power) +
            evaluateAlternativeRows rows activity by
        simp [evaluateAlternativeRows]]
      rw [MvPolynomial.eval₂_add, MvPolynomial.eval₂_monomial,
        inductionHypothesis]
      norm_num

/-- Every unit-mass alternative sum is nonnegative on the closed nonnegative
activity orthant. -/
theorem evaluateAlternativeRows_nonnegative
    (rows : Multiset (J →₀ ℕ)) (activity : J → ℝ)
    (hactivity : ∀ coordinate, 0 ≤ activity coordinate) :
    0 ≤ evaluateAlternativeRows rows activity := by
  apply Multiset.sum_nonneg
  intro value hvalue
  rw [Multiset.mem_map] at hvalue
  obtain ⟨exponent, _, rfl⟩ := hvalue
  exact Finset.prod_nonneg fun coordinate _ ↦
    pow_nonneg (hactivity coordinate) _

/-- The explicit difference between the two alternative partition sums is
the source polynomial evaluation. -/
theorem evaluateAlternativeRows_compiler_difference
    (polynomial : MvPolynomial J ℤ) (activity : J → ℝ) :
    evaluateAlternativeRows (positiveAlternativeRows polynomial) activity -
        evaluateAlternativeRows (negativeAlternativeRows polynomial) activity =
      polynomial.eval₂ (Int.castRingHom ℝ) activity := by
  rw [← eval2_alternativeRowsPolynomial,
    ← eval2_alternativeRowsPolynomial,
    ← MvPolynomial.eval₂_sub]
  exact eval2_compiledRelativePartitionPolynomial
    (Int.castRingHom ℝ) activity polynomial

/-- **MAX-G2 probability-order orientation.**  The compiled named-probability
order is equivalent to nonnegativity of the source polynomial at every
nonnegative activity vector. -/
theorem compiledNamedProbability_order_iff
    (polynomial : MvPolynomial J ℤ) (activity : J → ℝ)
    (hactivity : ∀ coordinate, 0 ≤ activity coordinate) :
    compiledLeftNamedProbability polynomial activity ≤
        compiledRightNamedProbability polynomial activity ↔
      0 ≤ polynomial.eval₂ (Int.castRingHom ℝ) activity := by
  have hpositiveNonnegative := evaluateAlternativeRows_nonnegative
    (positiveAlternativeRows polynomial) activity hactivity
  have hnegativeNonnegative := evaluateAlternativeRows_nonnegative
    (negativeAlternativeRows polynomial) activity hactivity
  have hleftDenominator :
      0 < 1 + evaluateAlternativeRows
        (positiveAlternativeRows polynomial) activity := by linarith
  have hrightDenominator :
      0 < 1 + evaluateAlternativeRows
        (negativeAlternativeRows polynomial) activity := by linarith
  rw [compiledLeftNamedProbability, compiledRightNamedProbability,
    div_le_div_iff₀ hleftDenominator hrightDenominator]
  simp only [one_mul]
  have hdifference := evaluateAlternativeRows_compiler_difference
    polynomial activity
  constructor <;> intro horder <;> linarith

/-- Universal named-probability order over an arbitrary declared
nonnegative activity domain is equivalent to universal polynomial
nonnegativity on that same domain. -/
theorem compiledNamedProbability_universal_order_iff
    (polynomial : MvPolynomial J ℤ) (domain : Set (J → ℝ))
    (hdomain : ∀ activity ∈ domain,
      ∀ coordinate, 0 ≤ activity coordinate) :
    (∀ activity ∈ domain,
        compiledLeftNamedProbability polynomial activity ≤
          compiledRightNamedProbability polynomial activity) ↔
      (∀ activity ∈ domain,
        0 ≤ polynomial.eval₂ (Int.castRingHom ℝ) activity) := by
  constructor
  · intro horder activity hactivity
    exact (compiledNamedProbability_order_iff polynomial activity
      (hdomain activity hactivity)).1 (horder activity hactivity)
  · intro hpolynomial activity hactivity
    exact (compiledNamedProbability_order_iff polynomial activity
      (hdomain activity hactivity)).2 (hpolynomial activity hactivity)

end ProbabilitySemantics

end Compiler

end PhonologicalCalculus.MaxEnt
