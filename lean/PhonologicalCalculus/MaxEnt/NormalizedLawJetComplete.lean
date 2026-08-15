import PhonologicalCalculus.MaxEnt.CollectedSupport
import PhonologicalCalculus.MaxEnt.ResponseQuotientGerm
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Tactic

/-!
# Mixed normalized-law jets and complete fixed-support response identification

This module closes the final response-identification bridge in `MAX-G7`.
It starts with two complete finite fixed-mass exponential ledgers, constructs
their canonical collected cross-numerator supports, transports a mixed jet of
the normalized-law difference through the positive common denominator, and
uses the least support-dependent mixed interpolation degree to obtain equality
of the normalized laws at every weight.

Candidate labels, base masses, consequence fibres, exact alias collection,
zero-coefficient cancellation, the interior base point, and the separating
directions remain explicit.  Empty collected support is handled directly.
-/

namespace PhonologicalCalculus.MaxEnt

open Filter Set
open scoped Topology

section MixedJetTransport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Vanishing of the complete Fréchet jet through a finite order. -/
def mixedResponseJetZeroThrough
    (response : E → ℝ) (base : E) (order : ℕ) : Prop :=
  ∀ degree, degree ≤ order → iteratedFDeriv ℝ degree response base = 0

/-- Multiplication by a smooth factor preserves vanishing of a complete
mixed jet in the direction needed by normalized-law cross multiplication. -/
theorem mixedResponseJetZeroThrough_mul_right
    (denominator response : E → ℝ) (base : E) (order : ℕ)
    (hdenominator : ContDiff ℝ ⊤ denominator)
    (hresponse : ContDiff ℝ ⊤ response)
    (hzero : mixedResponseJetZeroThrough response base order) :
    mixedResponseJetZeroThrough
      (fun weight ↦ denominator weight * response weight) base order := by
  intro degree hdegree
  have hbound := norm_iteratedFDeriv_mul_le
    hdenominator hresponse base (n := degree) (by simp)
  have hsumZero :
      ∑ i ∈ Finset.range (degree + 1),
          (degree.choose i : ℝ) *
            ‖iteratedFDeriv ℝ i denominator base‖ *
            ‖iteratedFDeriv ℝ (degree - i) response base‖ = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hsubDegree : degree - i ≤ order :=
      (Nat.sub_le degree i).trans hdegree
    rw [hzero (degree - i) hsubDegree]
    simp
  rw [hsumZero] at hbound
  exact norm_eq_zero.mp (le_antisymm hbound (norm_nonneg _))

/-- On a globally nonvanishing smooth denominator, multiplication preserves
and reflects every finite mixed jet.  Complete finite MaxEnt denominators
satisfy this global premise because all candidate masses are positive. -/
theorem mixedResponseJetZeroThrough_mul_iff_right
    (denominator response : E → ℝ) (base : E) (order : ℕ)
    (hdenominator : ContDiff ℝ ⊤ denominator)
    (hresponse : ContDiff ℝ ⊤ response)
    (hdenominatorNe : ∀ weight, denominator weight ≠ 0) :
    mixedResponseJetZeroThrough
        (fun weight ↦ denominator weight * response weight) base order ↔
      mixedResponseJetZeroThrough response base order := by
  constructor
  · intro hproduct
    let inverseDenominator : E → ℝ := fun weight ↦ (denominator weight)⁻¹
    have hinverse : ContDiff ℝ ⊤ inverseDenominator := by
      exact hdenominator.inv hdenominatorNe
    have htransport := mixedResponseJetZeroThrough_mul_right
      inverseDenominator
      (fun weight ↦ denominator weight * response weight)
      base order hinverse (hdenominator.mul hresponse) hproduct
    have hfunction :
        (fun weight ↦
          inverseDenominator weight *
            (denominator weight * response weight)) = response := by
      funext weight
      dsimp only [inverseDenominator]
      field_simp [hdenominatorNe weight]
    rw [hfunction] at htransport
    exact htransport
  · exact mixedResponseJetZeroThrough_mul_right
      denominator response base order hdenominator hresponse

/-- Exact multivariate quotient-contact transport for the complete-ledger
domain.  The factorization is stated without introducing a division symbol,
so the denominator's role is visible in the proof term. -/
theorem max_g7_contact_02_mixedGerm
    (denominator numerator response : E → ℝ)
    (base : E) (order : ℕ)
    (hdenominator : ContDiff ℝ ⊤ denominator)
    (hresponse : ContDiff ℝ ⊤ response)
    (hdenominatorNe : ∀ weight, denominator weight ≠ 0)
    (hfactor : numerator = fun weight ↦ denominator weight * response weight) :
    mixedResponseJetZeroThrough numerator base order ↔
      mixedResponseJetZeroThrough response base order := by
  rw [hfactor]
  exact mixedResponseJetZeroThrough_mul_iff_right
    denominator response base order hdenominator hresponse hdenominatorNe

end MixedJetTransport

section LeastMixedDegree

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A total-degree mixed jet identifies every coefficient on the declared
finite linear-exponential support at the chosen base point. -/
def MixedIdentifiesThrough {n : ℕ}
    (node : Fin n → E →L[ℝ] ℝ) (base : E) (degree : ℕ) : Prop :=
  ∀ coefficient : Fin n → ℝ,
    mixedResponseJetZeroThrough
      (translatedLinearExponentialResponse node coefficient base) 0 degree →
        coefficient = 0

/-- A separating projection proves existence of a complete mixed audit at
degree `n - 1`. -/
theorem mixedIdentifiesThrough_card_sub_one {n : ℕ}
    (node : Fin n → E →L[ℝ] ℝ) (base direction : E)
    (hseparating : Function.Injective fun i ↦ node i direction) :
    MixedIdentifiesThrough node base (n - 1) := by
  intro coefficient hjet
  let projected : Fin n → ℝ := fun i ↦ node i direction
  let weighted : Fin n → ℝ :=
    fun i ↦ coefficient i * Real.exp (node i base)
  have hgerm : ∀ order : Fin n,
      iteratedFDeriv ℝ order
          (translatedLinearExponentialResponse node coefficient base) 0 =
        iteratedFDeriv ℝ order
          (translatedLinearExponentialResponse node 0 base) 0 := by
    intro order
    have hleft := hjet order (Nat.le_pred_of_lt order.isLt)
    have hzeroFunction :
        translatedLinearExponentialResponse node 0 base = 0 := by
      funext displacement
      simp [translatedLinearExponentialResponse,
        finiteLinearExponentialResponse]
    rw [hzeroFunction]
    simpa using hleft
  have hray := fullMixedGerm_eq_implies_rayJet_eq
    node coefficient 0 base direction hgerm
  have hrayZero : ∀ order : Fin n,
      iteratedDeriv order
        (finiteExponentialResponse projected weighted) 0 = 0 := by
    intro order
    have h := hray order
    have hzeroFunction :
        finiteExponentialResponse (fun i ↦ node i direction)
          (fun i ↦ (0 : Fin n → ℝ) i * Real.exp (node i base)) = 0 := by
      funext time
      simp [finiteExponentialResponse]
    rw [hzeroFunction] at h
    simpa [projected, weighted] using h
  have hweighted : weighted = 0 :=
    finiteExponentialResponse_coefficients_eq_zero_of_jet
      projected weighted hseparating 0 hrayZero
  funext i
  have hi := congrFun hweighted i
  dsimp only [weighted] at hi
  exact (mul_eq_zero.mp hi).resolve_right (Real.exp_ne_zero _)

/-- Least complete mixed interpolation degree for one finite support at one
base point.  Its existence is proved by a separating-ray Vandermonde bound. -/
noncomputable def leastMixedInterpolationDegree {n : ℕ}
    (node : Fin n → E →L[ℝ] ℝ) (base direction : E)
    (hseparating : Function.Injective fun i ↦ node i direction) : ℕ := by
  classical
  exact Nat.find ⟨n - 1,
    mixedIdentifiesThrough_card_sub_one node base direction hseparating⟩

theorem leastMixedInterpolationDegree_spec {n : ℕ}
    (node : Fin n → E →L[ℝ] ℝ) (base direction : E)
    (hseparating : Function.Injective fun i ↦ node i direction) :
    MixedIdentifiesThrough node base
      (leastMixedInterpolationDegree node base direction hseparating) := by
  classical
  exact Nat.find_spec ⟨n - 1,
    mixedIdentifiesThrough_card_sub_one node base direction hseparating⟩

theorem leastMixedInterpolationDegree_le_card_sub_one {n : ℕ}
    (node : Fin n → E →L[ℝ] ℝ) (base direction : E)
    (hseparating : Function.Injective fun i ↦ node i direction) :
    leastMixedInterpolationDegree node base direction hseparating ≤ n - 1 := by
  classical
  exact Nat.find_min' ⟨n - 1,
    mixedIdentifiesThrough_card_sub_one node base direction hseparating⟩
    (mixedIdentifiesThrough_card_sub_one node base direction hseparating)

end LeastMixedDegree

section FiniteExponentialLedgers

variable {E C₁ C₂ Y : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Fintype C₁] [Fintype C₂] [Nonempty C₁] [Nonempty C₂]
  [Fintype Y] [Nonempty Y] [DecidableEq Y]

/-- Unnormalized consequence-fibre mass of a finite fixed-mass exponential
ledger. -/
noncomputable def exponentialFibreMass {C : Type*} [Fintype C]
    (baseMass : C → ℝ) (node : C → E →L[ℝ] ℝ)
    (consequence : C → Y) (answer : Y) (weight : E) : ℝ :=
  ∑ candidate,
    if consequence candidate = answer then
      baseMass candidate * Real.exp (node candidate weight)
    else 0

/-- Complete unnormalized mass of a finite fixed-mass exponential ledger. -/
noncomputable def exponentialTotalMass {C : Type*} [Fintype C]
    (baseMass : C → ℝ) (node : C → E →L[ℝ] ℝ)
    (weight : E) : ℝ :=
  ∑ candidate, baseMass candidate * Real.exp (node candidate weight)

/-- Normalized consequence law of a finite fixed-mass exponential ledger. -/
noncomputable def exponentialConsequenceLaw {C : Type*} [Fintype C]
    (baseMass : C → ℝ) (node : C → E →L[ℝ] ℝ)
    (consequence : C → Y) (weight : E) (answer : Y) : ℝ :=
  exponentialFibreMass baseMass node consequence answer weight /
    exponentialTotalMass baseMass node weight

theorem exponentialTotalMass_pos {C : Type*} [Fintype C] [Nonempty C]
    (baseMass : C → ℝ) (node : C → E →L[ℝ] ℝ)
    (hbase : ∀ candidate, 0 < baseMass candidate) (weight : E) :
    0 < exponentialTotalMass baseMass node weight := by
  classical
  unfold exponentialTotalMass
  apply Finset.sum_pos'
  · intro candidate _
    exact (mul_pos (hbase candidate) (Real.exp_pos _)).le
  · let candidate : C := Classical.choice (inferInstance : Nonempty C)
    exact ⟨candidate, Finset.mem_univ candidate,
      mul_pos (hbase candidate) (Real.exp_pos _)⟩

omit [Fintype Y] [Nonempty Y] in
theorem exponentialFibreMass_pos_of_complete
    {C : Type*} [Fintype C]
    (baseMass : C → ℝ) (node : C → E →L[ℝ] ℝ)
    (consequence : C → Y) (hcomplete : CompleteConsequenceFibres consequence)
    (hbase : ∀ candidate, 0 < baseMass candidate)
    (answer : Y) (weight : E) :
    0 < exponentialFibreMass baseMass node consequence answer weight := by
  classical
  obtain ⟨candidate, hcandidate⟩ := hcomplete answer
  unfold exponentialFibreMass
  apply Finset.sum_pos'
  · intro c _
    split_ifs
    · exact (mul_pos (hbase c) (Real.exp_pos _)).le
    · exact le_rfl
  · refine ⟨candidate, Finset.mem_univ candidate, ?_⟩
    simp [hcandidate, mul_pos (hbase candidate) (Real.exp_pos _)]

omit [Fintype Y] [Nonempty Y] in
theorem exponentialFibreMass_contDiff {C : Type*} [Fintype C]
    (baseMass : C → ℝ) (node : C → E →L[ℝ] ℝ)
    (consequence : C → Y) (answer : Y) :
    ContDiff ℝ ⊤
      (exponentialFibreMass baseMass node consequence answer) := by
  classical
  unfold exponentialFibreMass
  apply ContDiff.sum
  intro candidate _
  by_cases hanswer : consequence candidate = answer
  · simp only [hanswer, if_true]
    fun_prop
  · simp only [hanswer, if_false]
    fun_prop

theorem exponentialTotalMass_contDiff {C : Type*} [Fintype C]
    (baseMass : C → ℝ) (node : C → E →L[ℝ] ℝ) :
    ContDiff ℝ ⊤ (exponentialTotalMass baseMass node) := by
  unfold exponentialTotalMass
  fun_prop

omit [Fintype Y] [Nonempty Y] in
theorem exponentialConsequenceLaw_contDiff {C : Type*}
    [Fintype C] [Nonempty C]
    (baseMass : C → ℝ) (node : C → E →L[ℝ] ℝ)
    (consequence : C → Y) (answer : Y)
    (hbase : ∀ candidate, 0 < baseMass candidate) :
    ContDiff ℝ ⊤
      (fun weight ↦
        exponentialConsequenceLaw baseMass node consequence weight answer) := by
  unfold exponentialConsequenceLaw
  exact (exponentialFibreMass_contDiff baseMass node consequence answer).div
    (exponentialTotalMass_contDiff baseMass node)
    (fun weight ↦ (exponentialTotalMass_pos baseMass node hbase weight).ne')

/-- Collected numerator comparing one consequence probability between two
complete ledgers. -/
noncomputable def exponentialLawCrossNumerator
    (baseMass₁ : C₁ → ℝ) (node₁ : C₁ → E →L[ℝ] ℝ)
    (consequence₁ : C₁ → Y)
    (baseMass₂ : C₂ → ℝ) (node₂ : C₂ → E →L[ℝ] ℝ)
    (consequence₂ : C₂ → Y)
    (answer : Y) (weight : E) : ℝ :=
  exponentialFibreMass baseMass₁ node₁ consequence₁ answer weight *
      exponentialTotalMass baseMass₂ node₂ weight -
    exponentialFibreMass baseMass₂ node₂ consequence₂ answer weight *
      exponentialTotalMass baseMass₁ node₁ weight

/-- Common denominator of the two normalized consequence laws. -/
noncomputable def exponentialLawCommonDenominator
    (baseMass₁ : C₁ → ℝ) (node₁ : C₁ → E →L[ℝ] ℝ)
    (baseMass₂ : C₂ → ℝ) (node₂ : C₂ → E →L[ℝ] ℝ)
    (weight : E) : ℝ :=
  exponentialTotalMass baseMass₁ node₁ weight *
    exponentialTotalMass baseMass₂ node₂ weight

omit [Nonempty C₁] [Nonempty C₂] [Fintype Y] [Nonempty Y] in
theorem exponentialLawCrossNumerator_factor
    (baseMass₁ : C₁ → ℝ) (node₁ : C₁ → E →L[ℝ] ℝ)
    (consequence₁ : C₁ → Y)
    (baseMass₂ : C₂ → ℝ) (node₂ : C₂ → E →L[ℝ] ℝ)
    (consequence₂ : C₂ → Y)
    (answer : Y) (weight : E)
    (htotal₁ : exponentialTotalMass baseMass₁ node₁ weight ≠ 0)
    (htotal₂ : exponentialTotalMass baseMass₂ node₂ weight ≠ 0) :
    exponentialLawCrossNumerator
        baseMass₁ node₁ consequence₁ baseMass₂ node₂ consequence₂
        answer weight =
      exponentialLawCommonDenominator baseMass₁ node₁ baseMass₂ node₂ weight *
        (exponentialConsequenceLaw baseMass₁ node₁ consequence₁ weight answer -
          exponentialConsequenceLaw baseMass₂ node₂ consequence₂ weight answer) := by
  unfold exponentialLawCrossNumerator exponentialLawCommonDenominator
    exponentialConsequenceLaw
  field_simp [htotal₁, htotal₂]

/-- Raw pairwise exponent row before exact alias collection. -/
def rawCrossNode
    (node₁ : C₁ → E →L[ℝ] ℝ) (node₂ : C₂ → E →L[ℝ] ℝ) :
    C₁ × C₂ → E →L[ℝ] ℝ :=
  fun pair ↦ node₁ pair.1 + node₂ pair.2

/-- Raw signed cross coefficient before equal exponent rows are aggregated. -/
def rawCrossCoefficient
    (baseMass₁ : C₁ → ℝ) (consequence₁ : C₁ → Y)
    (baseMass₂ : C₂ → ℝ) (consequence₂ : C₂ → Y)
    (answer : Y) : C₁ × C₂ → ℝ :=
  fun pair ↦
    (if consequence₁ pair.1 = answer then baseMass₁ pair.1 else 0) *
        baseMass₂ pair.2 -
      (if consequence₂ pair.2 = answer then baseMass₂ pair.2 else 0) *
        baseMass₁ pair.1

omit [Nonempty C₁] [Nonempty C₂] [Fintype Y] [Nonempty Y] in
/-- Expansion of the normalized-law cross numerator as one finite labelled
linear-exponential response. -/
theorem exponentialLawCrossNumerator_eq_raw_sum
    (baseMass₁ : C₁ → ℝ) (node₁ : C₁ → E →L[ℝ] ℝ)
    (consequence₁ : C₁ → Y)
    (baseMass₂ : C₂ → ℝ) (node₂ : C₂ → E →L[ℝ] ℝ)
    (consequence₂ : C₂ → Y)
    (answer : Y) (weight : E) :
    exponentialLawCrossNumerator
        baseMass₁ node₁ consequence₁ baseMass₂ node₂ consequence₂
        answer weight =
      ∑ pair : C₁ × C₂,
        rawCrossCoefficient baseMass₁ consequence₁ baseMass₂ consequence₂
            answer pair *
          Real.exp (rawCrossNode node₁ node₂ pair weight) := by
  classical
  unfold exponentialLawCrossNumerator exponentialFibreMass
    exponentialTotalMass rawCrossCoefficient rawCrossNode
  rw [Fintype.sum_mul_sum, Fintype.sum_mul_sum,
    Fintype.sum_prod_type]
  conv_lhs =>
    rhs
    rw [Finset.sum_comm]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro candidate₁ _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro candidate₂ _
  simp only [add_apply, Real.exp_add]
  split_ifs <;> ring

/-- Exact finite collected presentation of a scalar response. -/
structure CollectedExponentialPresentation (response : E → ℝ) where
  cardinality : ℕ
  node : Fin cardinality → E →L[ℝ] ℝ
  coefficient : Fin cardinality → ℝ
  injective_node : Function.Injective node
  coefficient_ne_zero : ∀ i, coefficient i ≠ 0
  response_eq : ∀ weight,
    response weight = finiteLinearExponentialResponse node coefficient weight

omit [Nonempty C₁] [Nonempty C₂] [Fintype Y] [Nonempty Y] in
/-- The exact collector produces a duplicate-free, nonzero presentation of
every finite-ledger law cross numerator. -/
theorem nonempty_collectedCrossPresentation
    (baseMass₁ : C₁ → ℝ) (node₁ : C₁ → E →L[ℝ] ℝ)
    (consequence₁ : C₁ → Y)
    (baseMass₂ : C₂ → ℝ) (node₂ : C₂ → E →L[ℝ] ℝ)
    (consequence₂ : C₂ → Y) (answer : Y) :
    Nonempty (CollectedExponentialPresentation
      (exponentialLawCrossNumerator
        baseMass₁ node₁ consequence₁ baseMass₂ node₂ consequence₂
        answer)) := by
  classical
  obtain ⟨n, node, coefficient, hnode, hcoefficient, hresponse⟩ :=
    exists_canonicalCollectedResponseEnumeration
      (rawCrossNode node₁ node₂)
      (rawCrossCoefficient baseMass₁ consequence₁ baseMass₂ consequence₂
        answer)
      (fun exponent weight ↦ Real.exp (exponent weight))
  refine ⟨⟨n, node, coefficient, hnode, hcoefficient, ?_⟩⟩
  intro weight
  rw [exponentialLawCrossNumerator_eq_raw_sum]
  simpa [finiteLinearExponentialResponse] using hresponse weight

/-- Canonical collected presentation, unique up to permutation of its
duplicate-free support enumeration. -/
noncomputable def canonicalCollectedCrossPresentation
    (baseMass₁ : C₁ → ℝ) (node₁ : C₁ → E →L[ℝ] ℝ)
    (consequence₁ : C₁ → Y)
    (baseMass₂ : C₂ → ℝ) (node₂ : C₂ → E →L[ℝ] ℝ)
    (consequence₂ : C₂ → Y) (answer : Y) :
    CollectedExponentialPresentation
      (exponentialLawCrossNumerator
        baseMass₁ node₁ consequence₁ baseMass₂ node₂ consequence₂
        answer) :=
  Classical.choice (nonempty_collectedCrossPresentation
    baseMass₁ node₁ consequence₁ baseMass₂ node₂ consequence₂ answer)

/-! ## Final normalized-law jet bridge -/

/-- A support-indexed family of exact collected presentations. -/
abbrev CollectedCrossPresentationFamily
    (baseMass₁ : C₁ → ℝ) (node₁ : C₁ → E →L[ℝ] ℝ)
    (consequence₁ : C₁ → Y)
    (baseMass₂ : C₂ → ℝ) (node₂ : C₂ → E →L[ℝ] ℝ)
    (consequence₂ : C₂ → Y) :=
  ∀ answer : Y, CollectedExponentialPresentation
    (exponentialLawCrossNumerator
      baseMass₁ node₁ consequence₁ baseMass₂ node₂ consequence₂ answer)

omit [Fintype Y] [Nonempty Y] in
/-- A complete mixed normalized-law jet, through the least interpolation
degree of each exact collected cross support, forces equality of the two
normalized laws at every weight.  This theorem accepts any exact collected
presentation; the canonical collector is substituted in the registered
wrapper below. -/
theorem mixedLawJet_implies_allWeightsLaw_eq_of_collected
    (baseMass₁ : C₁ → ℝ) (node₁ : C₁ → E →L[ℝ] ℝ)
    (consequence₁ : C₁ → Y)
    (baseMass₂ : C₂ → ℝ) (node₂ : C₂ → E →L[ℝ] ℝ)
    (consequence₂ : C₂ → Y)
    (hbase₁ : ∀ candidate, 0 < baseMass₁ candidate)
    (hbase₂ : ∀ candidate, 0 < baseMass₂ candidate)
    (base : E)
    (presentation : CollectedCrossPresentationFamily
      baseMass₁ node₁ consequence₁ baseMass₂ node₂ consequence₂)
    (direction : Y → E)
    (hseparating : ∀ answer,
      Function.Injective fun i ↦
        (presentation answer).node i (direction answer))
    (hjet : ∀ answer,
      mixedResponseJetZeroThrough
        (fun displacement ↦
          exponentialConsequenceLaw baseMass₁ node₁ consequence₁
              (base + displacement) answer -
            exponentialConsequenceLaw baseMass₂ node₂ consequence₂
              (base + displacement) answer)
        0
        (leastMixedInterpolationDegree
          (presentation answer).node base (direction answer)
          (hseparating answer))) :
    ∀ weight : E,
      (fun answer ↦
        exponentialConsequenceLaw baseMass₁ node₁ consequence₁ weight answer) =
      (fun answer ↦
        exponentialConsequenceLaw baseMass₂ node₂ consequence₂ weight answer) := by
  intro weight
  funext answer
  let response : E → ℝ := fun currentWeight ↦
    exponentialConsequenceLaw baseMass₁ node₁ consequence₁
        currentWeight answer -
      exponentialConsequenceLaw baseMass₂ node₂ consequence₂
        currentWeight answer
  let denominator : E → ℝ :=
    exponentialLawCommonDenominator baseMass₁ node₁ baseMass₂ node₂
  let numerator : E → ℝ :=
    exponentialLawCrossNumerator
      baseMass₁ node₁ consequence₁ baseMass₂ node₂ consequence₂ answer
  let currentPresentation := presentation answer
  let auditDegree := leastMixedInterpolationDegree
    currentPresentation.node base (direction answer) (hseparating answer)
  have htotal₁ : ∀ currentWeight,
      exponentialTotalMass baseMass₁ node₁ currentWeight ≠ 0 :=
    fun currentWeight ↦
      (exponentialTotalMass_pos baseMass₁ node₁ hbase₁ currentWeight).ne'
  have htotal₂ : ∀ currentWeight,
      exponentialTotalMass baseMass₂ node₂ currentWeight ≠ 0 :=
    fun currentWeight ↦
      (exponentialTotalMass_pos baseMass₂ node₂ hbase₂ currentWeight).ne'
  have hdenominatorSmooth : ContDiff ℝ ⊤ denominator := by
    exact (exponentialTotalMass_contDiff baseMass₁ node₁).mul
      (exponentialTotalMass_contDiff baseMass₂ node₂)
  have hresponseSmooth : ContDiff ℝ ⊤ response := by
    exact (exponentialConsequenceLaw_contDiff
      baseMass₁ node₁ consequence₁ answer hbase₁).sub
      (exponentialConsequenceLaw_contDiff
        baseMass₂ node₂ consequence₂ answer hbase₂)
  have hdenominatorTranslated : ContDiff ℝ ⊤
      (fun displacement ↦ denominator (base + displacement)) := by
    fun_prop
  have hresponseTranslated : ContDiff ℝ ⊤
      (fun displacement ↦ response (base + displacement)) := by
    fun_prop
  have hresponseJet : mixedResponseJetZeroThrough
      (fun displacement ↦ response (base + displacement)) 0 auditDegree := by
    simpa only [response, auditDegree, currentPresentation] using hjet answer
  have hproductJet : mixedResponseJetZeroThrough
      (fun displacement ↦
        denominator (base + displacement) * response (base + displacement))
      0 auditDegree :=
    mixedResponseJetZeroThrough_mul_right
      (fun displacement ↦ denominator (base + displacement))
      (fun displacement ↦ response (base + displacement))
      0 auditDegree hdenominatorTranslated hresponseTranslated hresponseJet
  have hfactorTranslated :
      (fun displacement ↦ numerator (base + displacement)) =
        (fun displacement ↦
          denominator (base + displacement) * response (base + displacement)) := by
    funext displacement
    exact exponentialLawCrossNumerator_factor
      baseMass₁ node₁ consequence₁ baseMass₂ node₂ consequence₂
      answer (base + displacement) (htotal₁ _) (htotal₂ _)
  have hnumeratorJet : mixedResponseJetZeroThrough
      (fun displacement ↦ numerator (base + displacement)) 0 auditDegree := by
    rw [hfactorTranslated]
    exact hproductJet
  have hpresentationTranslated :
      (fun displacement ↦ numerator (base + displacement)) =
        translatedLinearExponentialResponse
          currentPresentation.node currentPresentation.coefficient base := by
    funext displacement
    exact currentPresentation.response_eq (base + displacement)
  have hcollectedJet : mixedResponseJetZeroThrough
      (translatedLinearExponentialResponse
        currentPresentation.node currentPresentation.coefficient base)
      0 auditDegree := by
    rw [← hpresentationTranslated]
    exact hnumeratorJet
  have hcoefficient : currentPresentation.coefficient = 0 := by
    exact (leastMixedInterpolationDegree_spec
      currentPresentation.node base (direction answer) (hseparating answer))
      currentPresentation.coefficient hcollectedJet
  have hnumeratorZero : numerator weight = 0 := by
    change exponentialLawCrossNumerator
      baseMass₁ node₁ consequence₁ baseMass₂ node₂ consequence₂
      answer weight = 0
    rw [currentPresentation.response_eq weight, hcoefficient]
    simp [finiteLinearExponentialResponse]
  have hfactorWeight := exponentialLawCrossNumerator_factor
    baseMass₁ node₁ consequence₁ baseMass₂ node₂ consequence₂
    answer weight (htotal₁ weight) (htotal₂ weight)
  change numerator weight = denominator weight * response weight at hfactorWeight
  have hdenominatorNe : denominator weight ≠ 0 := by
    exact mul_ne_zero (htotal₁ weight) (htotal₂ weight)
  have hresponseZero : response weight = 0 := by
    apply (mul_eq_zero.mp (hfactorWeight.symm.trans hnumeratorZero)).resolve_left
    exact hdenominatorNe
  exact sub_eq_zero.mp hresponseZero

/-- Least canonical mixed-jet degree for one collected law cross numerator. -/
noncomputable def canonicalCrossJetDegree
    (baseMass₁ : C₁ → ℝ) (node₁ : C₁ → E →L[ℝ] ℝ)
    (consequence₁ : C₁ → Y)
    (baseMass₂ : C₂ → ℝ) (node₂ : C₂ → E →L[ℝ] ℝ)
    (consequence₂ : C₂ → Y)
    (base : E) (direction : Y → E)
    (hseparating : ∀ answer,
      Function.Injective fun i ↦
        (canonicalCollectedCrossPresentation
          baseMass₁ node₁ consequence₁ baseMass₂ node₂ consequence₂ answer).node i
          (direction answer))
    (answer : Y) : ℕ :=
  leastMixedInterpolationDegree
    (canonicalCollectedCrossPresentation
      baseMass₁ node₁ consequence₁ baseMass₂ node₂ consequence₂ answer).node
    base (direction answer) (hseparating answer)

/-- **MAX-G7.FACTORIZATION.04, final canonical bridge.**  A complete mixed
normalized-law jet through the least degree of every canonical collected
cross support forces all-weight law equality.  The same conclusion is
equivalent pointwise to equality of the positive fibre-mass vectors modulo
one common positive factor. -/
theorem max_g7_factorization_04_mixedLawJet
    (baseMass₁ : C₁ → ℝ) (node₁ : C₁ → E →L[ℝ] ℝ)
    (consequence₁ : C₁ → Y)
    (baseMass₂ : C₂ → ℝ) (node₂ : C₂ → E →L[ℝ] ℝ)
    (consequence₂ : C₂ → Y)
    (hbase₁ : ∀ candidate, 0 < baseMass₁ candidate)
    (hbase₂ : ∀ candidate, 0 < baseMass₂ candidate)
    (hcomplete₁ : CompleteConsequenceFibres consequence₁)
    (hcomplete₂ : CompleteConsequenceFibres consequence₂)
    (base : E) (direction : Y → E)
    (hseparating : ∀ answer,
      Function.Injective fun i ↦
        (canonicalCollectedCrossPresentation
          baseMass₁ node₁ consequence₁ baseMass₂ node₂ consequence₂ answer).node i
          (direction answer))
    (hjet : ∀ answer,
      mixedResponseJetZeroThrough
        (fun displacement ↦
          exponentialConsequenceLaw baseMass₁ node₁ consequence₁
              (base + displacement) answer -
            exponentialConsequenceLaw baseMass₂ node₂ consequence₂
              (base + displacement) answer)
        0
        (canonicalCrossJetDegree
          baseMass₁ node₁ consequence₁ baseMass₂ node₂ consequence₂
          base direction hseparating answer)) :
    (∀ weight : E,
      (fun answer ↦
        exponentialConsequenceLaw baseMass₁ node₁ consequence₁ weight answer) =
      (fun answer ↦
        exponentialConsequenceLaw baseMass₂ node₂ consequence₂ weight answer)) ∧
    (∀ weight : E,
      PositiveProjectivelyEquivalent
        (fun answer ↦
          exponentialFibreMass baseMass₁ node₁ consequence₁ answer weight)
        (fun answer ↦
          exponentialFibreMass baseMass₂ node₂ consequence₂ answer weight)) := by
  let presentation : CollectedCrossPresentationFamily
      baseMass₁ node₁ consequence₁ baseMass₂ node₂ consequence₂ :=
    fun answer ↦ canonicalCollectedCrossPresentation
      baseMass₁ node₁ consequence₁ baseMass₂ node₂ consequence₂ answer
  have hlaw : ∀ weight : E,
      (fun answer ↦
        exponentialConsequenceLaw baseMass₁ node₁ consequence₁ weight answer) =
      (fun answer ↦
        exponentialConsequenceLaw baseMass₂ node₂ consequence₂ weight answer) := by
    apply mixedLawJet_implies_allWeightsLaw_eq_of_collected
      baseMass₁ node₁ consequence₁ baseMass₂ node₂ consequence₂
      hbase₁ hbase₂ base presentation direction hseparating
    intro answer
    simpa only [presentation, canonicalCrossJetDegree] using hjet answer
  refine ⟨hlaw, ?_⟩
  intro weight
  have hleftPos : ∀ answer,
      0 < exponentialFibreMass baseMass₁ node₁ consequence₁ answer weight :=
    fun answer ↦ exponentialFibreMass_pos_of_complete
      baseMass₁ node₁ consequence₁ hcomplete₁ hbase₁ answer weight
  have hrightPos : ∀ answer,
      0 < exponentialFibreMass baseMass₂ node₂ consequence₂ answer weight :=
    fun answer ↦ exponentialFibreMass_pos_of_complete
      baseMass₂ node₂ consequence₂ hcomplete₂ hbase₂ answer weight
  apply (max_g7_projective_factorization_iff
    (fun answer ↦
      exponentialFibreMass baseMass₁ node₁ consequence₁ answer weight)
    (fun answer ↦
      exponentialFibreMass baseMass₂ node₂ consequence₂ answer weight)
    hleftPos hrightPos).1
  have hnormalizedLeft :
      normalizedConsequenceLaw
          (fun answer ↦
            exponentialFibreMass baseMass₁ node₁ consequence₁ answer weight) =
        (fun answer ↦
          exponentialConsequenceLaw baseMass₁ node₁ consequence₁ weight answer) := by
    funext answer
    unfold normalizedConsequenceLaw totalConsequenceMass
      exponentialConsequenceLaw
    congr 1
    unfold exponentialFibreMass exponentialTotalMass
    rw [Finset.sum_comm]
    simp [eq_comm]
  have hnormalizedRight :
      normalizedConsequenceLaw
          (fun answer ↦
            exponentialFibreMass baseMass₂ node₂ consequence₂ answer weight) =
        (fun answer ↦
          exponentialConsequenceLaw baseMass₂ node₂ consequence₂ weight answer) := by
    funext answer
    unfold normalizedConsequenceLaw totalConsequenceMass
      exponentialConsequenceLaw
    congr 1
    unfold exponentialFibreMass exponentialTotalMass
    rw [Finset.sum_comm]
    simp [eq_comm]
  rw [hnormalizedLeft, hnormalizedRight]
  exact hlaw weight

end FiniteExponentialLedgers

end PhonologicalCalculus.MaxEnt
