import PhonologicalCalculus.MaxEnt.FixedMassResponseComplete
import Mathlib.Tactic

/-!
# Canonical collection of a finite response support

Raw finite MaxEnt cross-numerators may contain several labelled terms with
the same exponent row and may contain exact cancellation after those terms are
collected.  This module constructs the duplicate-free nonzero support and
proves that its canonical finite enumeration represents exactly the original
labelled sum.
-/

namespace PhonologicalCalculus.MaxEnt

section Collection

variable {C R X : Type*} [Fintype C] [DecidableEq R]

/-- Exponent rows occurring in a raw finite labelled term ledger. -/
def rawResponseSupport (row : C → R) : Finset R :=
  Finset.univ.image row

/-- Total signed coefficient of one exponent row after all labelled aliases
have been collected. -/
def aggregateResponseCoefficient
    (row : C → R) (coefficient : C → ℝ) (exponent : R) : ℝ :=
  ∑ candidate : C with row candidate = exponent, coefficient candidate

/-- Canonical duplicate-free support after exact coefficient cancellation. -/
noncomputable def collectedResponseSupport
    (row : C → R) (coefficient : C → ℝ) : Finset R :=
  (rawResponseSupport row).filter
    (fun exponent ↦ aggregateResponseCoefficient row coefficient exponent ≠ 0)

/-- Grouping a raw labelled response by equal exponent rows preserves its
value for every kernel and every argument. -/
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

/-- Removing a collected row whose aggregate coefficient is exactly zero
does not change the response. -/
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

/-- The canonical collected support is extensionally identical to the raw
labelled response. -/
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

/-- Canonical finite enumeration of a collected support.  The enumeration
has no duplicate rows, every retained coefficient is nonzero, and its response
is exactly the raw labelled sum for every argument. -/
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
