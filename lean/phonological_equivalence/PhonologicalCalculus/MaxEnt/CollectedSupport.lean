         
import PhonologicalCalculus.MaxEnt.FixedMassResponseComplete
import Mathlib.Tactic

namespace PhonologicalCalculus.MaxEnt

section Collection

variable {C R X : Type*} [Fintype C] [DecidableEq R]

def rawResponseSupport (row : C → R) : Finset R :=
  Finset.univ.image row

def aggregateResponseCoefficient
    (row : C → R) (coefficient : C → ℝ) (exponent : R) : ℝ :=
  ∑ candidate : C with row candidate = exponent, coefficient candidate

noncomputable def collectedResponseSupport
    (row : C → R) (coefficient : C → ℝ) : Finset R :=
  (rawResponseSupport row).filter
    (fun exponent ↦ aggregateResponseCoefficient row coefficient exponent ≠ 0)

theorem sum_eq_sum_aggregateResponseCoefficient
    (row : C → R) (coefficient : C → ℝ)
    (kernel : R → X → ℝ) (argument : X) :
    ∑ candidate, coefficient candidate * kernel (row candidate) argument =
      ∑ exponent ∈ rawResponseSupport row,
        aggregateResponseCoefficient row coefficient exponent *
          kernel exponent argument := by
  classical
  have hfiber := Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset C))
    (t := rawResponseSupport row) (g := row)
    (fun candidate _ ↦ by
      exact Finset.mem_image.mpr
        ⟨candidate, Finset.mem_univ candidate, rfl⟩)
    (fun candidate ↦ coefficient candidate * kernel (row candidate) argument)
  rw [← hfiber]
  apply Finset.sum_congr rfl
  intro exponent hexponent
  rw [aggregateResponseCoefficient, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro candidate hcandidate
  have hrow : row candidate = exponent :=
    (Finset.mem_filter.mp hcandidate).2
  rw [hrow]

theorem sum_collectedResponseSupport_eq_sum_rawResponseSupport
    (row : C → R) (coefficient : C → ℝ)
    (kernel : R → X → ℝ) (argument : X) :
    ∑ exponent ∈ collectedResponseSupport row coefficient,
        aggregateResponseCoefficient row coefficient exponent *
          kernel exponent argument =
      ∑ exponent ∈ rawResponseSupport row,
        aggregateResponseCoefficient row coefficient exponent *
          kernel exponent argument := by
  classical
  rw [collectedResponseSupport, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro exponent _
  by_cases hcoefficient :
      aggregateResponseCoefficient row coefficient exponent ≠ 0
  · simp [hcoefficient]
  · have hzero : aggregateResponseCoefficient row coefficient exponent = 0 :=
      not_ne_iff.mp hcoefficient
    simp [hzero]

theorem sum_eq_sum_collectedResponseSupport
    (row : C → R) (coefficient : C → ℝ)
    (kernel : R → X → ℝ) (argument : X) :
    ∑ candidate, coefficient candidate * kernel (row candidate) argument =
      ∑ exponent ∈ collectedResponseSupport row coefficient,
        aggregateResponseCoefficient row coefficient exponent *
          kernel exponent argument := by
  rw [sum_eq_sum_aggregateResponseCoefficient]
  exact (sum_collectedResponseSupport_eq_sum_rawResponseSupport
    row coefficient kernel argument).symm

theorem exists_canonicalCollectedResponseEnumeration
    (row : C → R) (coefficient : C → ℝ) (kernel : R → X → ℝ) :
    ∃ (n : ℕ) (node : Fin n → R) (collectedCoefficient : Fin n → ℝ),
      Function.Injective node ∧
      (∀ i, collectedCoefficient i ≠ 0) ∧
      (∀ argument : X,
        ∑ candidate, coefficient candidate * kernel (row candidate) argument =
          ∑ i, collectedCoefficient i * kernel (node i) argument) := by
  classical
  let support := collectedResponseSupport row coefficient
  let SupportIndex := {exponent : R // exponent ∈ support}
  let equivalence : SupportIndex ≃ Fin (Fintype.card SupportIndex) :=
    Fintype.equivFin SupportIndex
  let node : Fin (Fintype.card SupportIndex) → R :=
    fun i ↦ (equivalence.symm i).1
  let collectedCoefficient : Fin (Fintype.card SupportIndex) → ℝ :=
    fun i ↦ aggregateResponseCoefficient row coefficient (node i)
  refine ⟨Fintype.card SupportIndex, node, collectedCoefficient, ?_, ?_, ?_⟩
  · intro i j hij
    apply equivalence.symm.injective
    exact Subtype.ext hij
  · intro i
    have hmembership : node i ∈ support := (equivalence.symm i).2
    exact (Finset.mem_filter.mp hmembership).2
  · intro argument
    rw [sum_eq_sum_collectedResponseSupport]
    have hsubtype :
        ∑ exponent ∈ support,
            aggregateResponseCoefficient row coefficient exponent *
              kernel exponent argument =
          ∑ exponent : SupportIndex,
            aggregateResponseCoefficient row coefficient exponent.1 *
              kernel exponent.1 argument := by
      exact Finset.sum_subtype support (fun _ ↦ Iff.rfl) _
    rw [hsubtype]
    exact Fintype.sum_equiv equivalence
      (fun exponent : SupportIndex ↦
        aggregateResponseCoefficient row coefficient exponent.1 *
          kernel exponent.1 argument)
      (fun i ↦ collectedCoefficient i * kernel (node i) argument)
      (fun exponent ↦ by
        simp only [node, collectedCoefficient, Equiv.symm_apply_apply])

end Collection

end PhonologicalCalculus.MaxEnt
