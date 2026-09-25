import PhonologicalCalculus.MaxEnt.FiniteLaw
import PhonologicalCalculus.MaxEnt.ProjectiveResponse
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

namespace PhonologicalCalculus.MaxEnt

section FiniteLedgerProjectivization

variable {K J C₁ C₂ Y : Type*}
  [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [Fintype J] [Fintype C₁] [Fintype C₂] [Nonempty C₁] [Nonempty C₂]
  [Fintype Y] [Nonempty Y] [DecidableEq Y]

def CompleteConsequenceFibres {C Y : Type*} (consequence : C → Y) : Prop :=
  Function.Surjective consequence

omit [Nonempty C₁] [Fintype Y] [Nonempty Y] in
theorem fibreMass_pos_of_completeFibres
    (baseMass : C₁ → K) (row : C₁ → J → ℤ)
    (consequence : C₁ → Y) (hcomplete : CompleteConsequenceFibres consequence)
    (activity : J → K) (hbase : ∀ c, 0 < baseMass c)
    (hactivity : ∀ j, 0 < activity j) (answer : Y) :
    0 < fibreMass baseMass row consequence answer activity := by
  obtain ⟨candidate, hcandidate⟩ := hcomplete answer
  exact fibreMass_pos_of_mem baseMass row consequence answer activity
    hbase hactivity candidate hcandidate

omit [LinearOrder K] [IsStrictOrderedRing K] [Nonempty C₁] [Nonempty Y] in
theorem normalized_fibreMass_eq_consequenceProbability
    (baseMass : C₁ → K) (row : C₁ → J → ℤ)
    (consequence : C₁ → Y) (activity : J → K) :
    normalizedConsequenceLaw
        (fun answer ↦ fibreMass baseMass row consequence answer activity) =
      fun answer ↦ consequenceProbability baseMass row consequence answer activity := by
  funext answer
  simp only [normalizedConsequenceLaw, totalConsequenceMass,
    consequenceProbability]
  rw [sum_fibreMass_eq_partitionMass]

omit [Nonempty C₁] [Nonempty C₂] in
                          
theorem max_g7_completeLedger_factorization_iff
    (baseMass₁ : C₁ → K) (row₁ : C₁ → J → ℤ)
    (consequence₁ : C₁ → Y)
    (baseMass₂ : C₂ → K) (row₂ : C₂ → J → ℤ)
    (consequence₂ : C₂ → Y)
    (hbase₁ : ∀ c, 0 < baseMass₁ c)
    (hbase₂ : ∀ c, 0 < baseMass₂ c)
    (hcomplete₁ : CompleteConsequenceFibres consequence₁)
    (hcomplete₂ : CompleteConsequenceFibres consequence₂)
    (activity : J → K) (hactivity : ∀ j, 0 < activity j) :
    (fun answer ↦ consequenceProbability baseMass₁ row₁ consequence₁ answer activity) =
        (fun answer ↦ consequenceProbability baseMass₂ row₂ consequence₂ answer activity) ↔
      PositiveProjectivelyEquivalent
        (fun answer ↦ fibreMass baseMass₁ row₁ consequence₁ answer activity)
        (fun answer ↦ fibreMass baseMass₂ row₂ consequence₂ answer activity) := by
  rw [← normalized_fibreMass_eq_consequenceProbability
      baseMass₁ row₁ consequence₁ activity,
    ← normalized_fibreMass_eq_consequenceProbability
      baseMass₂ row₂ consequence₂ activity]
  exact max_g7_projective_factorization_iff _ _
    (fibreMass_pos_of_completeFibres baseMass₁ row₁ consequence₁
      hcomplete₁ activity hbase₁ hactivity)
    (fibreMass_pos_of_completeFibres baseMass₂ row₂ consequence₂
      hcomplete₂ activity hbase₂ hactivity)

omit [Nonempty C₁] [Nonempty C₂] in
theorem max_g7_allWeights_completeLedger_factorization_iff
    (baseMass₁ : C₁ → K) (row₁ : C₁ → J → ℤ)
    (consequence₁ : C₁ → Y)
    (baseMass₂ : C₂ → K) (row₂ : C₂ → J → ℤ)
    (consequence₂ : C₂ → Y)
    (hbase₁ : ∀ c, 0 < baseMass₁ c)
    (hbase₂ : ∀ c, 0 < baseMass₂ c)
    (hcomplete₁ : CompleteConsequenceFibres consequence₁)
    (hcomplete₂ : CompleteConsequenceFibres consequence₂) :
    (∀ activity : J → K, (∀ j, 0 < activity j) →
      (fun answer ↦ consequenceProbability baseMass₁ row₁ consequence₁ answer activity) =
        (fun answer ↦ consequenceProbability baseMass₂ row₂ consequence₂ answer activity)) ↔
    (∀ activity : J → K, (∀ j, 0 < activity j) →
      PositiveProjectivelyEquivalent
        (fun answer ↦ fibreMass baseMass₁ row₁ consequence₁ answer activity)
        (fun answer ↦ fibreMass baseMass₂ row₂ consequence₂ answer activity)) := by
  constructor <;> intro h activity hactivity
  · exact (max_g7_completeLedger_factorization_iff
      baseMass₁ row₁ consequence₁ baseMass₂ row₂ consequence₂
      hbase₁ hbase₂ hcomplete₁ hcomplete₂ activity hactivity).1
      (h activity hactivity)
  · exact (max_g7_completeLedger_factorization_iff
      baseMass₁ row₁ consequence₁ baseMass₂ row₂ consequence₂
      hbase₁ hbase₂ hcomplete₁ hcomplete₂ activity hactivity).2
      (h activity hactivity)

end FiniteLedgerProjectivization

section ExponentialResponseJets

noncomputable def finiteExponentialResponse {n : ℕ}
    (node coefficient : Fin n → ℝ) (time : ℝ) : ℝ :=
  ∑ i, coefficient i * Real.exp (node i * time)

theorem iteratedDeriv_finiteExponentialResponse {n : ℕ}
    (node coefficient : Fin n → ℝ) (order : ℕ) (time : ℝ) :
    iteratedDeriv order (finiteExponentialResponse node coefficient) time =
      ∑ i, coefficient i * node i ^ order * Real.exp (node i * time) := by
  rw [show finiteExponentialResponse node coefficient =
      fun t ↦ ∑ i, coefficient i * Real.exp (node i * t) by rfl]
  rw [iteratedDeriv_fun_sum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [iteratedDeriv_const_mul_field,
      iteratedDeriv_exp_const_mul]
    ring
  · intro i _
    fun_prop

theorem finiteExponentialResponse_coefficients_eq_zero_of_jet
    {n : ℕ} (node coefficient : Fin n → ℝ)
    (hnode : Function.Injective node) (base : ℝ)
    (hjet : ∀ order : Fin n,
      iteratedDeriv order
        (finiteExponentialResponse node coefficient) base = 0) :
    coefficient = 0 := by
  let weighted : Fin n → ℝ :=
    fun i ↦ coefficient i * Real.exp (node i * base)
  have hmoments : ∀ order : Fin n,
      projectedMoment node weighted order = 0 := by
    intro order
    have h := hjet order
    rw [iteratedDeriv_finiteExponentialResponse] at h
    simpa only [projectedMoment, weighted, mul_assoc,
      mul_left_comm, mul_comm] using h
  have hweighted : weighted = 0 :=
    vandermonde_moments_identify node weighted hnode hmoments
  funext i
  have hi := congrFun hweighted i
  dsimp only [weighted] at hi
  exact (mul_eq_zero.mp hi).resolve_right (Real.exp_ne_zero _)

theorem finiteExponentialResponse_coefficients_eq_of_completeJet_eq
    {n : ℕ} (node left right : Fin n → ℝ)
    (hnode : Function.Injective node) (base : ℝ)
    (hjet : ∀ order : Fin n,
      iteratedDeriv order (finiteExponentialResponse node left) base =
        iteratedDeriv order (finiteExponentialResponse node right) base) :
    left = right := by
  let difference : Fin n → ℝ := fun i ↦ left i - right i
  have hzeroJet : ∀ order : Fin n,
      iteratedDeriv order
        (finiteExponentialResponse node difference) base = 0 := by
    intro order
    rw [iteratedDeriv_finiteExponentialResponse]
    have h := hjet order
    rw [iteratedDeriv_finiteExponentialResponse,
      iteratedDeriv_finiteExponentialResponse] at h
    dsimp only [difference]
    calc
      ∑ i, (left i - right i) * node i ^ (order : ℕ) *
            Real.exp (node i * base) =
          (∑ i, left i * node i ^ (order : ℕ) *
            Real.exp (node i * base)) -
          (∑ i, right i * node i ^ (order : ℕ) *
            Real.exp (node i * base)) := by
              rw [← Finset.sum_sub_distrib]
              apply Finset.sum_congr rfl
              intro i _
              ring
      _ = 0 := sub_eq_zero.mpr h
  have hdifference : difference = 0 :=
    finiteExponentialResponse_coefficients_eq_zero_of_jet
      node difference hnode base hzeroJet
  funext i
  have hi := congrFun hdifference i
  dsimp only [difference] at hi
  exact sub_eq_zero.mp hi

theorem finiteExponentialResponse_eq_iff_completeJet_eq
    {n : ℕ} (node left right : Fin n → ℝ)
    (hnode : Function.Injective node) (base : ℝ) :
    finiteExponentialResponse node left =
        finiteExponentialResponse node right ↔
      ∀ order : Fin n,
        iteratedDeriv order (finiteExponentialResponse node left) base =
          iteratedDeriv order (finiteExponentialResponse node right) base := by
  constructor
  · intro hresponse order
    rw [hresponse]
  · intro hjet
    rw [finiteExponentialResponse_coefficients_eq_of_completeJet_eq
      node left right hnode base hjet]

                
theorem max_g7_separatingRay_completeResponse :
    (∀ {n : ℕ} (node left right : Fin n → ℝ),
      Function.Injective node → ∀ base : ℝ,
      finiteExponentialResponse node left =
          finiteExponentialResponse node right ↔
        ∀ order : Fin n,
          iteratedDeriv order (finiteExponentialResponse node left) base =
            iteratedDeriv order (finiteExponentialResponse node right) base) ∧
    (let node : Fin 2 → ℚ := fun _ ↦ 1
     let coefficient : Fin 2 → ℚ := ![1, -1]
     coefficient ≠ 0 ∧
       ∀ order, projectedMoment node coefficient order = 0) := by
  constructor
  · intro n node left right hnode base
    exact finiteExponentialResponse_eq_iff_completeJet_eq
      node left right hnode base
  · exact nonseparating_projection_hides_all_moments

end ExponentialResponseJets

section MixedResponseGerm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def finiteLinearExponentialResponse {n : ℕ}
    (node : Fin n → E →L[ℝ] ℝ) (coefficient : Fin n → ℝ)
    (weight : E) : ℝ :=
  ∑ i, coefficient i * Real.exp (node i weight)

noncomputable def translatedLinearExponentialResponse {n : ℕ}
    (node : Fin n → E →L[ℝ] ℝ) (coefficient : Fin n → ℝ)
    (base displacement : E) : ℝ :=
  finiteLinearExponentialResponse node coefficient (base + displacement)

def responseRay (direction : E) : ℝ →L[ℝ] E :=
  (ContinuousLinearMap.id ℝ ℝ).smulRight direction

@[simp]
theorem responseRay_apply (direction : E) (time : ℝ) :
    responseRay direction time = time • direction := rfl

theorem translatedLinearExponentialResponse_contDiff {n : ℕ}
    (node : Fin n → E →L[ℝ] ℝ) (coefficient : Fin n → ℝ)
    (base : E) :
    ContDiff ℝ ⊤
      (translatedLinearExponentialResponse node coefficient base) := by
  unfold translatedLinearExponentialResponse finiteLinearExponentialResponse
  fun_prop

theorem translatedLinearExponentialResponse_comp_ray {n : ℕ}
    (node : Fin n → E →L[ℝ] ℝ) (coefficient : Fin n → ℝ)
    (base direction : E) :
    translatedLinearExponentialResponse node coefficient base ∘
        responseRay direction =
      finiteExponentialResponse
        (fun i ↦ node i direction)
        (fun i ↦ coefficient i * Real.exp (node i base)) := by
  funext time
  unfold translatedLinearExponentialResponse finiteLinearExponentialResponse
    finiteExponentialResponse responseRay
  apply Finset.sum_congr rfl
  intro i _
  rw [map_add]
  change coefficient i *
      Real.exp (node i base + node i (time • direction)) =
    (coefficient i * Real.exp (node i base)) *
      Real.exp (node i direction * time)
  rw [map_smul, Real.exp_add]
  ring_nf

theorem fullMixedGerm_eq_implies_rayJet_eq {n : ℕ}
    (node : Fin n → E →L[ℝ] ℝ) (left right : Fin n → ℝ)
    (base direction : E)
    (hgerm : ∀ order : Fin n,
      iteratedFDeriv ℝ order
          (translatedLinearExponentialResponse node left base) 0 =
        iteratedFDeriv ℝ order
          (translatedLinearExponentialResponse node right base) 0) :
    ∀ order : Fin n,
      iteratedDeriv order
          (finiteExponentialResponse
            (fun i ↦ node i direction)
            (fun i ↦ left i * Real.exp (node i base))) 0 =
        iteratedDeriv order
          (finiteExponentialResponse
            (fun i ↦ node i direction)
            (fun i ↦ right i * Real.exp (node i base))) 0 := by
  intro order
  rw [← translatedLinearExponentialResponse_comp_ray
      node left base direction,
    ← translatedLinearExponentialResponse_comp_ray
      node right base direction]
  change
    (iteratedFDeriv ℝ order
        (translatedLinearExponentialResponse node left base ∘
          responseRay direction) 0 : (Fin (order : ℕ) → ℝ) → ℝ)
        (fun _ ↦ 1) =
      (iteratedFDeriv ℝ order
        (translatedLinearExponentialResponse node right base ∘
          responseRay direction) 0 : (Fin (order : ℕ) → ℝ) → ℝ)
        (fun _ ↦ 1)
  have hleft := (responseRay direction).iteratedFDeriv_comp_right
    (translatedLinearExponentialResponse_contDiff node left base)
    (0 : ℝ) (i := (order : ℕ)) (by simp)
  have hright := (responseRay direction).iteratedFDeriv_comp_right
    (translatedLinearExponentialResponse_contDiff node right base)
    (0 : ℝ) (i := (order : ℕ)) (by simp)
  rw [hleft, hright]
  simp only [map_zero]
  rw [hgerm order]

theorem fullMixedGerm_completeResponse {n : ℕ}
    (node : Fin n → E →L[ℝ] ℝ) (left right : Fin n → ℝ)
    (base direction : E)
    (hseparating : Function.Injective fun i ↦ node i direction)
    (hgerm : ∀ order : Fin n,
      iteratedFDeriv ℝ order
          (translatedLinearExponentialResponse node left base) 0 =
        iteratedFDeriv ℝ order
          (translatedLinearExponentialResponse node right base) 0) :
    finiteLinearExponentialResponse node left =
      finiteLinearExponentialResponse node right := by
  let projected : Fin n → ℝ := fun i ↦ node i direction
  let weightedLeft : Fin n → ℝ :=
    fun i ↦ left i * Real.exp (node i base)
  let weightedRight : Fin n → ℝ :=
    fun i ↦ right i * Real.exp (node i base)
  have hjet : ∀ order : Fin n,
      iteratedDeriv order
          (finiteExponentialResponse projected weightedLeft) 0 =
        iteratedDeriv order
          (finiteExponentialResponse projected weightedRight) 0 := by
    simpa only [projected, weightedLeft, weightedRight] using
      fullMixedGerm_eq_implies_rayJet_eq
        node left right base direction hgerm
  have hweighted : weightedLeft = weightedRight :=
    finiteExponentialResponse_coefficients_eq_of_completeJet_eq
      projected weightedLeft weightedRight hseparating 0 hjet
  have hcoefficient : left = right := by
    funext i
    have hi := congrFun hweighted i
    dsimp only [weightedLeft, weightedRight] at hi
    exact mul_right_cancel₀ (Real.exp_ne_zero (node i base)) hi
  rw [hcoefficient]

theorem finiteLinearExponentialResponse_eq_iff_fullMixedGerm_eq {n : ℕ}
    (node : Fin n → E →L[ℝ] ℝ) (left right : Fin n → ℝ)
    (base direction : E)
    (hseparating : Function.Injective fun i ↦ node i direction) :
    finiteLinearExponentialResponse node left =
        finiteLinearExponentialResponse node right ↔
      ∀ order : Fin n,
        iteratedFDeriv ℝ order
            (translatedLinearExponentialResponse node left base) 0 =
          iteratedFDeriv ℝ order
            (translatedLinearExponentialResponse node right base) 0 := by
  constructor
  · intro hresponse order
    have htranslated :
        translatedLinearExponentialResponse node left base =
          translatedLinearExponentialResponse node right base := by
      funext displacement
      exact congrFun hresponse (base + displacement)
    rw [htranslated]
  · exact fullMixedGerm_completeResponse
      node left right base direction hseparating

end MixedResponseGerm

end PhonologicalCalculus.MaxEnt
