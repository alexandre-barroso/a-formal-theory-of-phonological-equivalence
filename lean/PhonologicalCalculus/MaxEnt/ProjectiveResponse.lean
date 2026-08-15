import PhonologicalCalculus.MaxEnt.FiniteLaw
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
import Mathlib.LinearAlgebra.Vandermonde

/-!
Projective normalized laws and support-dependent finite interpolation.

The normalized law forgets exactly one common positive scale.  On any fixed
finite support, a separating one-dimensional projection converts coefficient
identification into an invertible Vandermonde system.  The required audit
order therefore depends on the cardinality and geometry of the retained
support.
-/

namespace PhonologicalCalculus.MaxEnt

section ProjectiveLaw

variable {K Y : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [Fintype Y] [Nonempty Y]

/-- Total mass of a complete finite consequence ledger. -/
def totalConsequenceMass (mass : Y → K) : K :=
  ∑ answer, mass answer

/-- Normalized finite consequence law. -/
def normalizedConsequenceLaw (mass : Y → K) : Y → K :=
  fun answer ↦ mass answer / totalConsequenceMass mass

/-- Equality modulo one common positive scalar. -/
def PositiveProjectivelyEquivalent (left right : Y → K) : Prop :=
  ∃ scale : K, 0 < scale ∧ ∀ answer, left answer = scale * right answer

/-- Positive component masses have positive total mass. -/
theorem totalConsequenceMass_pos (mass : Y → K) (hmass : ∀ y, 0 < mass y) :
    0 < totalConsequenceMass mass := by
  classical
  apply Finset.sum_pos'
  · exact fun y _ ↦ (hmass y).le
  · let y : Y := Classical.choice (inferInstance : Nonempty Y)
    exact ⟨y, Finset.mem_univ y, hmass y⟩

/-- A common positive scale is invisible to normalization. -/
theorem normalizedConsequenceLaw_of_common_scale
    (left right : Y → K) (scale : K) (hscale : 0 < scale)
    (hleft : ∀ y, left y = scale * right y)
    (hright : ∀ y, 0 < right y) :
    normalizedConsequenceLaw left = normalizedConsequenceLaw right := by
  classical
  have hrightTotal : totalConsequenceMass right ≠ 0 :=
    ne_of_gt (totalConsequenceMass_pos right hright)
  have hscale0 : scale ≠ 0 := ne_of_gt hscale
  have htotal : totalConsequenceMass left =
      scale * totalConsequenceMass right := by
    simp only [totalConsequenceMass]
    simp_rw [hleft]
    exact (Finset.mul_sum Finset.univ right scale).symm
  funext y
  simp only [normalizedConsequenceLaw, hleft y, htotal]
  field_simp [hscale0, hrightTotal]

/-- Equality of positive normalized laws determines the unique common
projective scale. -/
theorem common_scale_of_normalizedConsequenceLaw_eq
    (left right : Y → K) (hleft : ∀ y, 0 < left y)
    (hright : ∀ y, 0 < right y)
    (hlaw : normalizedConsequenceLaw left = normalizedConsequenceLaw right) :
    ∃ scale : K, 0 < scale ∧ ∀ y, left y = scale * right y := by
  let leftTotal := totalConsequenceMass left
  let rightTotal := totalConsequenceMass right
  have hleftTotal : 0 < leftTotal := totalConsequenceMass_pos left hleft
  have hrightTotal : 0 < rightTotal := totalConsequenceMass_pos right hright
  refine ⟨leftTotal / rightTotal, div_pos hleftTotal hrightTotal, ?_⟩
  intro y
  have hy := congrFun hlaw y
  simp only [normalizedConsequenceLaw] at hy
  change left y / leftTotal = right y / rightTotal at hy
  have hcross : left y * rightTotal = right y * leftTotal :=
    (normalized_eq_iff_cross_product
      (ne_of_gt hleftTotal) (ne_of_gt hrightTotal)).1 hy
  field_simp [ne_of_gt hrightTotal]
  simpa [mul_comm] using hcross

/-- **MAX-G7.FACTORIZATION.04**, projective carrier clause.  For complete
positive finite consequence masses, equality of normalized laws is equivalent
to equality modulo one common positive factor. -/
theorem max_g7_projective_factorization_iff
    (left right : Y → K) (hleft : ∀ y, 0 < left y)
    (hright : ∀ y, 0 < right y) :
    normalizedConsequenceLaw left = normalizedConsequenceLaw right ↔
      PositiveProjectivelyEquivalent left right := by
  constructor
  · exact common_scale_of_normalizedConsequenceLaw_eq left right hleft hright
  · rintro ⟨scale, hscale, hcommon⟩
    exact normalizedConsequenceLaw_of_common_scale left right scale hscale
      hcommon hright

omit [IsStrictOrderedRing K] [Fintype Y] in
/-- The projective scale is unique for a positive nonempty right-hand mass
vector. -/
theorem positive_projective_scale_unique
    (left right : Y → K) (hright : ∀ y, 0 < right y)
    {scale₁ scale₂ : K} (h₁ : ∀ y, left y = scale₁ * right y)
    (h₂ : ∀ y, left y = scale₂ * right y) :
    scale₁ = scale₂ := by
  let y : Y := Classical.choice (inferInstance : Nonempty Y)
  have hright0 : right y ≠ 0 := ne_of_gt (hright y)
  apply mul_right_cancel₀ hright0
  rw [← h₁ y, h₂ y]

end ProjectiveLaw

section PolynomialJets

open Polynomial

variable {K : Type*} [Field K]

/-- Vanishing of every Taylor coefficient through a finite registered order. -/
def jetZeroThrough (polynomial : K[X]) (order : ℕ) : Prop :=
  ∀ degree, degree ≤ order → polynomial.coeff degree = 0

/-- For a nonzero polynomial, a zero jet through `order` is equivalent to
placing the first nonzero coefficient strictly above `order`. -/
theorem jetZeroThrough_iff_lt_natTrailingDegree
    {polynomial : K[X]} (hpolynomial : polynomial ≠ 0) (order : ℕ) :
    jetZeroThrough polynomial order ↔
      order < polynomial.natTrailingDegree := by
  constructor
  · intro hjet
    by_contra hnot
    have hle : polynomial.natTrailingDegree ≤ order := Nat.le_of_not_gt hnot
    exact polynomial.coeff_natTrailingDegree_ne_zero.mpr hpolynomial
      (hjet polynomial.natTrailingDegree hle)
  · intro hdegree degree hle
    exact polynomial.coeff_eq_zero_of_lt_natTrailingDegree
      (hle.trans_lt hdegree)

/-- Multiplication by a polynomial with nonzero constant coefficient neither
creates nor removes a finite zero jet. -/
theorem jetZeroThrough_mul_iff_right
    {denominator response : K[X]} (hconstant : denominator.coeff 0 ≠ 0)
    (order : ℕ) :
    jetZeroThrough (denominator * response) order ↔
      jetZeroThrough response order := by
  have hdenominator : denominator ≠ 0 := by
    intro hzero
    exact hconstant (by simp [hzero])
  have hdenominatorDegree : denominator.natTrailingDegree = 0 :=
    Polynomial.natTrailingDegree_eq_zero.mpr (Or.inr hconstant)
  by_cases hresponse : response = 0
  · subst response
    simp [jetZeroThrough]
  · have hproduct : denominator * response ≠ 0 :=
      mul_ne_zero hdenominator hresponse
    rw [jetZeroThrough_iff_lt_natTrailingDegree hproduct,
      jetZeroThrough_iff_lt_natTrailingDegree hresponse,
      Polynomial.natTrailingDegree_mul hdenominator hresponse,
      hdenominatorDegree, zero_add]

/-- **MAX-G7.CONTACT.02**.  If a finite Taylor numerator factors as a
denominator with nonzero base coefficient times the response polynomial, then
the response jet vanishes through a registered order exactly when the
numerator jet does. -/
theorem max_g7_contact_02
    {denominator numerator response : K[X]} (order : ℕ)
    (hconstant : denominator.coeff 0 ≠ 0)
    (hfactor : numerator = denominator * response) :
    jetZeroThrough numerator order ↔ jetZeroThrough response order := by
  rw [hfactor]
  exact jetZeroThrough_mul_iff_right hconstant order

end PolynomialJets

section SupportInterpolation

variable {K : Type*} [Field K]

/-- Moment of a coefficient vector on a finite projected support. -/
def projectedMoment {n : ℕ} (node coefficient : Fin n → K) (order : ℕ) : K :=
  ∑ i, coefficient i * node i ^ order

/-- Coefficients are identified by all projected moments through a declared
degree. -/
def IdentifiesThrough {n : ℕ} (node : Fin n → K) (degree : ℕ) : Prop :=
  ∀ coefficient : Fin n → K,
    (∀ order, order ≤ degree → projectedMoment node coefficient order = 0) →
      coefficient = 0

/-- Distinct projected support values make the first `n` moments a complete
coefficient audit. -/
theorem vandermonde_moments_identify {n : ℕ} (node coefficient : Fin n → K)
    (hnode : Function.Injective node)
    (hmoment : ∀ order : Fin n,
      projectedMoment node coefficient order = 0) :
    coefficient = 0 := by
  apply Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hnode
  intro order
  simpa [projectedMoment] using hmoment order

/-- For nonempty support of cardinality `n`, degree `n-1` always suffices
after a separating projection. -/
theorem identifiesThrough_card_sub_one {n : ℕ} (_hn : 0 < n)
    (node : Fin n → K) (hnode : Function.Injective node) :
    IdentifiesThrough node (n - 1) := by
  intro coefficient hmoment
  apply vandermonde_moments_identify node coefficient hnode
  intro order
  apply hmoment order
  exact Nat.le_pred_of_lt order.isLt

/-- Least support-dependent interpolation degree.  Existence is supplied by
the Vandermonde cardinality bound rather than postulated. -/
noncomputable def leastInterpolationDegree {n : ℕ} (hn : 0 < n)
    (node : Fin n → K) (hnode : Function.Injective node) : ℕ :=
  by
    classical
    exact Nat.find ⟨n - 1, identifiesThrough_card_sub_one hn node hnode⟩

/-- The least interpolation degree has its defining identification property. -/
theorem leastInterpolationDegree_spec {n : ℕ} (hn : 0 < n)
    (node : Fin n → K) (hnode : Function.Injective node) :
    IdentifiesThrough node (leastInterpolationDegree hn node hnode) := by
  classical
  exact Nat.find_spec ⟨n - 1, identifiesThrough_card_sub_one hn node hnode⟩

/-- The least interpolation degree is no larger than support cardinality
minus one. -/
theorem leastInterpolationDegree_le_card_sub_one {n : ℕ} (hn : 0 < n)
    (node : Fin n → K) (hnode : Function.Injective node) :
    leastInterpolationDegree hn node hnode ≤ n - 1 := by
  classical
  exact Nat.find_min' ⟨n - 1, identifiesThrough_card_sub_one hn node hnode⟩
    (identifiesThrough_card_sub_one hn node hnode)

/-- Mixed-radix scalar code for one bounded nonnegative violation vector. -/
def mixedRadixCode (base : ℕ) (digits : List ℕ) : ℕ :=
  Nat.ofDigits base digits

/-- A mixed-radix code is injective on fixed-length digit vectors whose
coordinates are all strictly below the base. -/
theorem mixedRadixCode_injective_on_bounded_vectors
    {base length : ℕ} (hbase : 1 < base) :
    Set.InjOn (mixedRadixCode base)
      {digits : List ℕ | digits.length = length ∧ ∀ digit ∈ digits, digit < base} :=
  Nat.injOn_ofDigits hbase length

/-- An injectively enumerated support remains separated by its mixed-radix
projection. -/
theorem mixedRadixCode_separates_finite_support
    {n base length : ℕ} (hbase : 1 < base)
    (row : Fin n → List ℕ) (hrow : Function.Injective row)
    (hbounded : ∀ i, (row i).length = length ∧ ∀ digit ∈ row i, digit < base) :
    Function.Injective fun i ↦ mixedRadixCode base (row i) := by
  intro i j hij
  apply hrow
  exact mixedRadixCode_injective_on_bounded_vectors hbase
    (hbounded i) (hbounded j) hij

/-- **MAX-G7.RANK.01**, generic finite-support core.  A mixed-radix
projection separates every explicitly bounded, duplicate-free support; its
Vandermonde moment audit has a least sufficient degree bounded by `n-1`. -/
theorem max_g7_rank_01
    {n base length : ℕ} (hn : 0 < n) (hbase : 1 < base)
    (row : Fin n → List ℕ) (hrow : Function.Injective row)
    (hbounded : ∀ i, (row i).length = length ∧ ∀ digit ∈ row i, digit < base) :
    let node : Fin n → ℚ := fun i ↦ mixedRadixCode base (row i)
    ∃ hnode : Function.Injective node,
      IdentifiesThrough node (leastInterpolationDegree hn node hnode) ∧
      leastInterpolationDegree hn node hnode ≤ n - 1 := by
  dsimp only
  have hnodeNat := mixedRadixCode_separates_finite_support hbase row hrow hbounded
  have hnodeRat : Function.Injective
      (fun i : Fin n ↦ (mixedRadixCode base (row i) : ℚ)) := by
    intro i j hij
    apply hnodeNat
    exact (Nat.cast_inj (R := ℚ)).mp hij
  exact ⟨hnodeRat, leastInterpolationDegree_spec hn _ hnodeRat,
    leastInterpolationDegree_le_card_sub_one hn _ hnodeRat⟩

/-- A nonseparating projection can hide a nonzero signed coefficient vector
at every derivative order. -/
theorem nonseparating_projection_hides_all_moments :
    let node : Fin 2 → ℚ := fun _ ↦ 1
    let coefficient : Fin 2 → ℚ := ![1, -1]
    coefficient ≠ 0 ∧ ∀ order, projectedMoment node coefficient order = 0 := by
  dsimp only
  constructor
  · intro hzero
    have := congrFun hzero 0
    norm_num at this
  · intro order
    simp [projectedMoment, Fin.sum_univ_two]

/-- **MAX-G7.RAY.03**.  Separating directions inherit the cardinality audit
bound, while the explicit constant projection hides a nonzero difference to
every order. -/
theorem max_g7_ray_03 :
    (∀ {n : ℕ} (_hn : 0 < n) (node : Fin n → ℚ),
      Function.Injective node → IdentifiesThrough node (n - 1)) ∧
    (let node : Fin 2 → ℚ := fun _ ↦ 1
     let coefficient : Fin 2 → ℚ := ![1, -1]
     coefficient ≠ 0 ∧ ∀ order, projectedMoment node coefficient order = 0) := by
  constructor
  · intro n hn node hnode
    exact identifiesThrough_card_sub_one hn node hnode
  · exact nonseparating_projection_hides_all_moments

end SupportInterpolation

end PhonologicalCalculus.MaxEnt
