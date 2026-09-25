import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace PhonologicalCalculus.MaxEnt

                  
inductive MaxEntAnswerSort
  | booleanEventInclusion
  | orderedRealProbability
  deriving DecidableEq

structure MaxEntTypedAssertion where
  answerSort : MaxEntAnswerSort
  holds : Prop

def categoricalEventImplication {A : Type*} [DecidableEq A]
    (E F : Finset A) : Prop :=
  E ⊆ F

def numericalProbabilityOrder {A K : Type*} [DecidableEq A] [LE K]
    (probability : Finset A → K) (E F : Finset A) : Prop :=
  probability E ≤ probability F

def numericalProbabilityEqual {A K : Type*} [DecidableEq A]
    (probability : Finset A → K) (E F : Finset A) : Prop :=
  probability E = probability F

def categoricalEventImplicationAssertion {A : Type*} [DecidableEq A]
    (E F : Finset A) : MaxEntTypedAssertion :=
  ⟨MaxEntAnswerSort.booleanEventInclusion,
    categoricalEventImplication E F⟩

def numericalProbabilityOrderAssertion {A K : Type*} [DecidableEq A] [LE K]
    (probability : Finset A → K) (E F : Finset A) : MaxEntTypedAssertion :=
  ⟨MaxEntAnswerSort.orderedRealProbability,
    numericalProbabilityOrder probability E F⟩

                  
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

         
def normalizedBinaryLaw (a b : K) : K × K :=
  (a / (a + b), b / (a + b))

                
theorem normalized_order_iff_cross_product {a b sa sb : K}
    (hsa : 0 < sa) (hsb : 0 < sb) :
    a / sa ≤ b / sb ↔ a * sb ≤ b * sa :=
  div_le_div_iff₀ hsa hsb

theorem normalized_eq_iff_cross_product {L : Type*} [Field L]
    {a b sa sb : L}
    (hsa : sa ≠ 0) (hsb : sb ≠ 0) :
    a / sa = b / sb ↔ a * sb = b * sa :=
  div_eq_div_iff hsa hsb

         
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

                  
theorem positive_clearing_preserves_nonneg {c p : K} (hc : 0 < c) :
    0 ≤ c * p ↔ 0 ≤ p := by
  constructor
  · exact fun h => nonneg_of_mul_nonneg_right h hc
  · exact fun h => mul_nonneg hc.le h

                     
theorem sum_sq_eq_zero_iff {I : Type*} (s : Finset I) (r : I → K) :
    ∑ i ∈ s, (r i) ^ 2 = 0 ↔ ∀ i ∈ s, r i = 0 := by
  rw [Finset.sum_eq_zero_iff_of_nonneg]
  · simp
  · intro i _
    exact sq_nonneg (r i)

                
def registeredTieMargin (z : K) : K :=
  z ^ 2 * (2 * z - 1)

                
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

         
def responseEnvelope1D
    (minA maxA minB maxB : ℤ) : ℤ × ℤ :=
  (minB - maxA, maxB - minA)

def rowMinimum : List ℤ → Option ℤ
  | [] => none
  | first :: rest => some (rest.foldl min first)

def rowMaximum : List ℤ → Option ℤ
  | [] => none
  | first :: rest => some (rest.foldl max first)

def responseEnvelopeOfRows (rowsA rowsB : List ℤ) : Option (ℤ × ℤ) :=
  match rowMinimum rowsA, rowMaximum rowsA,
      rowMinimum rowsB, rowMaximum rowsB with
  | some minA, some maxA, some minB, some maxB =>
      some (responseEnvelope1D minA maxA minB maxB)
  | _, _, _, _ => none

                     
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

         
theorem registeredEnvelopeLawDifferenceNumerator {R : Type*} [CommRing R]
    (z : R) :
    (1 + z + z ^ 2) * (1 + z ^ 2 + z ^ 3) -
        (1 + z ^ 2) * (1 + z + z ^ 2 + z ^ 3) = z ^ 4 := by
  ring

                     
theorem registeredEnvelopeLawDenominatorFactorization {R : Type*} [CommRing R]
    (z : R) :
    (1 + z + z ^ 2 + z ^ 3) * (1 + z ^ 2 + z ^ 3) =
      (1 + z) * (1 + z ^ 2) * (1 + z ^ 2 + z ^ 3) := by
  ring

                     
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

                         
theorem max_g8_registered_sharp_factorization (z : K) :
    4608 * z * (z - 3 / 4) ^ 2 * (z - 1 / 2) ^ 3 *
        (z - 1 / 4) * (z - 2 / 3) * (z - 1 / 3) =
      18 * z - 309 * z ^ 2 + 2267 * z ^ 3 - 9302 * z ^ 4 +
        23388 * z ^ 5 - 36952 * z ^ 6 + 35872 * z ^ 7 -
        19584 * z ^ 8 + 4608 * z ^ 9 := by
  ring

end OrderedField

end PhonologicalCalculus.MaxEnt
