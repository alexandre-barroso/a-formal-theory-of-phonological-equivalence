import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
Exact algebraic core for the MAX theorem family.

This module deliberately separates three kinds of declaration:

* declarations bearing a proof-goal identifier are exact Lean counterparts
  of the registered nullary witness proof goals;
* reusable lemmas expose algebra used by stronger MAX proof goals without
  claiming that those proof goals have thereby been formalized; and
* named examples replay exact arithmetic appearing in the semantic proof
  objects, again without promoting an example to a universal theorem.

Every declaration in this module has a kernel-checkable proof term; no
unproved project declaration or native-code evaluator is used.
-/

namespace PhonologicalCalculus.MaxEnt

/-- The two answer sorts that MAX-G5.TYPES.01 requires the analysis contract
to keep distinct. -/
inductive MaxEntAnswerSort
  | booleanEventInclusion
  | orderedRealProbability
  deriving DecidableEq

/-- A registered assertion carries its answer sort explicitly.  No coercion
between categorical and numerical assertions is declared. -/
structure MaxEntTypedAssertion where
  answerSort : MaxEntAnswerSort
  holds : Prop

/-- Categorical implication is inclusion of finite events. -/
def categoricalEventImplication {A : Type*} [DecidableEq A]
    (E F : Finset A) : Prop :=
  E ⊆ F

/-- Numerical probability order is weak order in the registered ordered-real
codomain; it is not obtained by coercing categorical truth. -/
def numericalProbabilityOrder {A K : Type*} [DecidableEq A] [LE K]
    (probability : Finset A → K) (E F : Finset A) : Prop :=
  probability E ≤ probability F

/-- Equality in the numerical probability sort. -/
def numericalProbabilityEqual {A K : Type*} [DecidableEq A]
    (probability : Finset A → K) (E F : Finset A) : Prop :=
  probability E = probability F

/-- Typed categorical assertion associated with a pair of finite events. -/
def categoricalEventImplicationAssertion {A : Type*} [DecidableEq A]
    (E F : Finset A) : MaxEntTypedAssertion :=
  ⟨MaxEntAnswerSort.booleanEventInclusion,
    categoricalEventImplication E F⟩

/-- Typed numerical assertion associated with the same event pair. -/
def numericalProbabilityOrderAssertion {A K : Type*} [DecidableEq A] [LE K]
    (probability : Finset A → K) (E F : Finset A) : MaxEntTypedAssertion :=
  ⟨MaxEntAnswerSort.orderedRealProbability,
    numericalProbabilityOrder probability E F⟩

/-- **MAX-G5.TYPES.01**.  Empty-event implication is categorical vacuity,
the categorical and numerical answer sorts are distinct, and mutual weak
probability order is exactly numerical equality.  The last equivalence is
proved under the registered empty-event antecedent (and in fact follows from
ordered-field antisymmetry independently of emptiness). -/
theorem max_g5_types_01 {A K : Type*} [DecidableEq A]
    [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (probability : Finset A → K) (E F : Finset A) :
    (E = ∅ → categoricalEventImplication E F) ∧
    (categoricalEventImplicationAssertion E F).answerSort ≠
      (numericalProbabilityOrderAssertion probability E F).answerSort ∧
    (E = ∅ ∧ F = ∅ →
      ((numericalProbabilityOrder probability E F ∧
          numericalProbabilityOrder probability F E) ↔
        numericalProbabilityEqual probability E F)) := by
  constructor
  · intro hE
    subst E
    simp [categoricalEventImplication]
  · constructor
    · simp [categoricalEventImplicationAssertion,
        numericalProbabilityOrderAssertion]
    · intro _
      constructor
      · rintro ⟨hEF, hFE⟩
        exact le_antisymm hEF hFE
      · intro hEq
        exact ⟨hEq.le, hEq.ge⟩

section OrderedField

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The binary normalized law used in the exact MAX-G9 witnesses. -/
def normalizedBinaryLaw (a b : K) : K × K :=
  (a / (a + b), b / (a + b))

/-- Positive denominators turn probability comparison into a cross-product
comparison.  This is the algebraic carrier used by MAX-G1 and MAX-G2. -/
theorem normalized_order_iff_cross_product {a b sa sb : K}
    (hsa : 0 < sa) (hsb : 0 < sb) :
    a / sa ≤ b / sb ↔ a * sb ≤ b * sa :=
  div_le_div_iff₀ hsa hsb

/-- Equality of normalized values is likewise exactly a cross-product
identity when both denominators are nonzero. -/
theorem normalized_eq_iff_cross_product {L : Type*} [Field L]
    {a b sa sb : L}
    (hsa : sa ≠ 0) (hsb : sb ≠ 0) :
    a / sa = b / sb ↔ a * sb = b * sa :=
  div_eq_div_iff hsa hsb

/-- A common positive fibre factor is invisible to a normalized binary law.
This is the forward algebraic half of the projective factorization result in
MAX-G7, not a declaration of the full registered MAX-G7 proof goal. -/
theorem normalizedBinaryLaw_common_factor (a b c : K)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    normalizedBinaryLaw (c * a) (c * b) = normalizedBinaryLaw a b := by
  have hab : a + b ≠ 0 := ne_of_gt (add_pos ha hb)
  have hc0 : c ≠ 0 := ne_of_gt hc
  apply Prod.ext
  · simp only [normalizedBinaryLaw]
    field_simp [hab, hc0]
  · simp only [normalizedBinaryLaw]
    field_simp [hab, hc0]

/-- In the positive binary case, equality of normalized laws is equivalent to
projective equality.  It is a reusable finite-fibre core for MAX-G7; the full
registered proof goal also contains a mixed-jet completion theorem and is not
claimed here. -/
theorem normalizedBinaryLaw_eq_iff_cross_minor_zero
    {a b c d : K} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hd : 0 < d) :
    normalizedBinaryLaw a b = normalizedBinaryLaw c d ↔ a * d = c * b := by
  have hab : a + b ≠ 0 := ne_of_gt (add_pos ha hb)
  have hcd : c + d ≠ 0 := ne_of_gt (add_pos hc hd)
  constructor
  · intro h
    have hfirst := congrArg Prod.fst h
    have hcross : a * (c + d) = c * (a + b) :=
      (normalized_eq_iff_cross_product hab hcd).1
        (by simpa [normalizedBinaryLaw] using hfirst)
    nlinarith
  · intro hminor
    apply Prod.ext
    · simp only [normalizedBinaryLaw]
      apply (normalized_eq_iff_cross_product hab hcd).2
      linarith
    · simp only [normalizedBinaryLaw]
      apply (normalized_eq_iff_cross_product hab hcd).2
      linarith

/-- Clearing by a positive monomial cannot change a sign.  This is the sign
invariance used by MAX-G1.CLEAR.02, without claiming the stronger Laurent
normal-form and minimal-shift clauses of that proof goal. -/
theorem positive_clearing_preserves_nonneg {c p : K} (hc : 0 < c) :
    0 ≤ c * p ↔ 0 ≤ p := by
  constructor
  · exact fun h => nonneg_of_mul_nonneg_right h hc
  · exact fun h => mul_nonneg hc.le h

/-- A finite sum of squared residuals vanishes exactly when every residual
vanishes.  This is the algebraic core used by MAX-G3.RESIDUAL.01; degree,
coefficient-size, and reduction-complexity clauses remain outside this lemma. -/
theorem sum_sq_eq_zero_iff {I : Type*} (s : Finset I) (r : I → K) :
    ∑ i ∈ s, (r i) ^ 2 = 0 ↔ ∀ i ∈ s, r i = 0 := by
  rw [Finset.sum_eq_zero_iff_of_nonneg]
  · simp
  · intro i _
    exact sq_nonneg (r i)

/-- The exact cross-input margin registered by MAX-G4.TIE.02. -/
def registeredTieMargin (z : K) : K :=
  z ^ 2 * (2 * z - 1)

/-- **MAX-G4.TIE.02**.  On the physical activity interval, the registered
cross-input margin has the unique interior root `1/2`, is strictly negative
below it, and is strictly positive above it. -/
theorem max_g4_tie_02 :
    (∀ z : K, 0 < z → z ≤ 1 →
      (registeredTieMargin z = 0 ↔ z = (1 / 2 : K))) ∧
    (∀ z : K, 0 < z → z < (1 / 2 : K) →
      registeredTieMargin z < 0) ∧
    (∀ z : K, (1 / 2 : K) < z → z ≤ 1 →
      0 < registeredTieMargin z) := by
  constructor
  · intro z hz _
    constructor
    · intro hzero
      have hzsq : 0 < z ^ 2 := sq_pos_of_pos hz
      have hfactor : 2 * z - 1 = 0 := by
        by_contra hne
        exact (mul_ne_zero (ne_of_gt hzsq) hne) hzero
      linarith
    · rintro rfl
      norm_num [registeredTieMargin]
  · constructor
    · intro z hz hhalf
      have hzsq : 0 < z ^ 2 := sq_pos_of_pos hz
      have hfactor : 2 * z - 1 < 0 := by linarith
      exact mul_neg_of_pos_of_neg hzsq hfactor
    · intro z hhalf _
      have hz : 0 < z := by linarith
      have hzsq : 0 < z ^ 2 := sq_pos_of_pos hz
      have hfactor : 0 < 2 * z - 1 := by linarith
      exact mul_pos hzsq hfactor

/-- One-dimensional closed response envelope from the four extrema used in
the MAX-G9 exact witnesses. -/
def responseEnvelope1D
    (minA maxA minB maxB : ℤ) : ℤ × ℤ :=
  (minB - maxA, maxB - minA)

/-- Minimum of a nonempty finite one-dimensional row ledger. -/
def rowMinimum : List ℤ → Option ℤ
  | [] => none
  | first :: rest => some (rest.foldl min first)

/-- Maximum of a nonempty finite one-dimensional row ledger. -/
def rowMaximum : List ℤ → Option ℤ
  | [] => none
  | first :: rest => some (rest.foldl max first)

/-- Closed one-dimensional response envelope computed from the rows of two
nonempty fibres. -/
def responseEnvelopeOfRows (rowsA rowsB : List ℤ) : Option (ℤ × ℤ) :=
  match rowMinimum rowsA, rowMaximum rowsA,
      rowMinimum rowsB, rowMaximum rowsB with
  | some minA, some maxA, some minB, some maxB =>
      some (responseEnvelope1D minA maxA minB maxB)
  | _, _, _, _ => none

/-- **MAX-G9.LAWTOENV.01**.  The two registered ledgers have the same
fixed-mass normalized law throughout the physical activity interval because
the second pair has common factor `1 + z²`; their closed response envelopes
are nevertheless the distinct intervals `[1,1]` and `[-1,3]`. -/
theorem max_g9_lawtoenv_01 :
    (∀ z : K, 0 < z → z ≤ 1 →
      normalizedBinaryLaw 1 z =
        normalizedBinaryLaw (1 + z ^ 2) (z + z ^ 3)) ∧
    responseEnvelopeOfRows [0] [1] = some (1, 1) ∧
    responseEnvelopeOfRows [0, 2] [1, 3] = some (-1, 3) ∧
    responseEnvelopeOfRows [0] [1] ≠
      responseEnvelopeOfRows [0, 2] [1, 3] := by
  constructor
  · intro z hz _
    have hc : 0 < 1 + z ^ 2 := by nlinarith [sq_nonneg z]
    have hfactorA : (1 + z ^ 2) * 1 = 1 + z ^ 2 := by ring
    have hfactorB : (1 + z ^ 2) * z = z + z ^ 3 := by ring
    rw [← hfactorA, ← hfactorB]
    exact (normalizedBinaryLaw_common_factor 1 z (1 + z ^ 2)
      (by norm_num) hz hc).symm
  · norm_num [responseEnvelopeOfRows, rowMinimum, rowMaximum,
      responseEnvelope1D]

/-- The exact positive numerator behind the converse MAX-G9 witness. -/
theorem registeredEnvelopeLawDifferenceNumerator {R : Type*} [CommRing R]
    (z : R) :
    (1 + z + z ^ 2) * (1 + z ^ 2 + z ^ 3) -
        (1 + z ^ 2) * (1 + z + z ^ 2 + z ^ 3) = z ^ 4 := by
  ring

/-- The denominator factorization recorded for MAX-G9.ENVTOLAW.02. -/
theorem registeredEnvelopeLawDenominatorFactorization {R : Type*} [CommRing R]
    (z : R) :
    (1 + z + z ^ 2 + z ^ 3) * (1 + z ^ 2 + z ^ 3) =
      (1 + z) * (1 + z ^ 2) * (1 + z ^ 2 + z ^ 3) := by
  ring

/-- **MAX-G9.ENVTOLAW.02**.  The registered ledgers have the same closed
response envelope `[1,3]`, but their fixed-mass normalized laws differ at
every physical activity.  Their first-coordinate difference has the exact
positive numerator `z⁴` and the registered positive denominator factors. -/
theorem max_g9_envtolaw_02 :
    responseEnvelopeOfRows [0, 1, 2] [3] = some (1, 3) ∧
    responseEnvelopeOfRows [0, 2] [3] = some (1, 3) ∧
    responseEnvelopeOfRows [0, 1, 2] [3] =
      responseEnvelopeOfRows [0, 2] [3] ∧
    (∀ z : K, 0 < z → z ≤ 1 →
      normalizedBinaryLaw (1 + z + z ^ 2) (z ^ 3) ≠
        normalizedBinaryLaw (1 + z ^ 2) (z ^ 3) ∧
      (1 + z + z ^ 2) * (1 + z ^ 2 + z ^ 3) -
          (1 + z ^ 2) * (1 + z + z ^ 2 + z ^ 3) = z ^ 4 ∧
      0 < (1 + z) * (1 + z ^ 2) * (1 + z ^ 2 + z ^ 3)) := by
  constructor
  · norm_num [responseEnvelopeOfRows, rowMinimum, rowMaximum,
      responseEnvelope1D]
  · constructor
    · norm_num [responseEnvelopeOfRows, rowMinimum, rowMaximum,
        responseEnvelope1D]
    · constructor
      · norm_num [responseEnvelopeOfRows, rowMinimum, rowMaximum,
          responseEnvelope1D]
      · intro z hz _
        have hz2 : 0 ≤ z ^ 2 := sq_nonneg z
        have hz3 : 0 < z ^ 3 := pow_pos hz 3
        have hS1 : 0 < 1 + z + z ^ 2 + z ^ 3 := by nlinarith
        have hS2 : 0 < 1 + z ^ 2 + z ^ 3 := by nlinarith
        have hnumer :
            (1 + z + z ^ 2) * (1 + z ^ 2 + z ^ 3) -
                (1 + z ^ 2) * (1 + z + z ^ 2 + z ^ 3) = z ^ 4 :=
          registeredEnvelopeLawDifferenceNumerator z
        have hnumerPos : 0 < z ^ 4 := pow_pos hz 4
        have hfirstNe :
            (1 + z + z ^ 2) / (1 + z + z ^ 2 + z ^ 3) ≠
              (1 + z ^ 2) / (1 + z ^ 2 + z ^ 3) := by
          intro heq
          have hcross := (normalized_eq_iff_cross_product
            (ne_of_gt hS1) (ne_of_gt hS2)).1 heq
          linarith
        constructor
        · intro hlaw
          exact hfirstNe (congrArg Prod.fst hlaw)
        · constructor
          · exact hnumer
          · exact mul_pos (mul_pos (by linarith) (by nlinarith)) hS2

/-- The exact univariate factorization used in the MAX-G8 sharpness example.
This proves the displayed polynomial identity, not the universal arbitrary-
contact sharpness theorem registered as MAX-G8.SHARP.01. -/
theorem max_g8_registered_sharp_factorization (z : K) :
    4608 * z * (z - 3 / 4) ^ 2 * (z - 1 / 2) ^ 3 *
        (z - 1 / 4) * (z - 2 / 3) * (z - 1 / 3) =
      18 * z - 309 * z ^ 2 + 2267 * z ^ 3 - 9302 * z ^ 4 +
        23388 * z ^ 5 - 36952 * z ^ 6 + 35872 * z ^ 7 -
        19584 * z ^ 8 + 4608 * z ^ 9 := by
  ring

end OrderedField

end PhonologicalCalculus.MaxEnt
