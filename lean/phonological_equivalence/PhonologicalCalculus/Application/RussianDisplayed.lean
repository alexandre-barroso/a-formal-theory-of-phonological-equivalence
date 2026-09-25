                                 
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

open scoped BigOperators

namespace RussianDisplayed

variable {J I : Type*} [Fintype J]

def retained (A B : J → I → ℝ) (lam : ℝ) (w : J → ℝ) (i : I) : ℝ :=
  ∑ j, w j * (A j i + lam * B j i)

def expanded (A B : J → I → ℝ) (u v : J → ℝ) (i : I) : ℝ :=
  ∑ j, (u j * A j i + v j * B j i)

def Pure (A B : J → I → ℝ) : Prop :=
  ∀ j, (∀ i, A j i = 0) ∨ (∀ i, B j i = 0)

theorem positive_reparameterization
    (A B : J → I → ℝ) (hp : Pure A B) (lam mu : ℝ)
    (hl : 0 < lam) (hm : 0 < mu) (w : J → ℝ) (hw : ∀ j, 0 ≤ w j) :
    ∃ v : J → ℝ, (∀ j, 0 ≤ v j) ∧
      ∀ i, retained A B lam w i = retained A B mu v i := by
  classical
  let v : J → ℝ := fun j => if ∀ i, A j i = 0 then lam / mu * w j else w j
  refine ⟨v, ?_, ?_⟩
  · intro j
    dsimp [v]
    split_ifs
    · exact mul_nonneg (div_nonneg hl.le hm.le) (hw j)
    · exact hw j
  · intro i
    unfold retained
    apply Finset.sum_congr rfl
    intro j _
    dsimp [v]
    split_ifs with h
    · rw [h i]
      field_simp
      ring
    · have hb := (hp j).resolve_left h
      rw [hb i]
      ring

theorem positive_family_equal
    (A B : J → I → ℝ) (hp : Pure A B) (lam mu : ℝ)
    (hl : 0 < lam) (hm : 0 < mu) (t : I → ℝ) :
    (∃ w, (∀ j, 0 ≤ w j) ∧ ∀ i, retained A B lam w i = t i) ↔
    (∃ w, (∀ j, 0 ≤ w j) ∧ ∀ i, retained A B mu w i = t i) := by
  constructor
  · rintro ⟨w, hw, ht⟩
    obtain ⟨v, hv, he⟩ := positive_reparameterization A B hp lam mu hl hm w hw
    exact ⟨v, hv, fun i => (he i).symm.trans (ht i)⟩
  · rintro ⟨w, hw, ht⟩
    obtain ⟨v, hv, he⟩ := positive_reparameterization A B hp mu lam hm hl w hw
    exact ⟨v, hv, fun i => (he i).symm.trans (ht i)⟩

theorem expanded_to_retained
    (A B : J → I → ℝ) (hp : Pure A B) (lam : ℝ) (hl : 0 < lam)
    (u v : J → ℝ) (hu : ∀ j, 0 ≤ u j) (hv : ∀ j, 0 ≤ v j) :
    ∃ w : J → ℝ, (∀ j, 0 ≤ w j) ∧
      ∀ i, expanded A B u v i = retained A B lam w i := by
  classical
  let w : J → ℝ := fun j => if ∀ i, A j i = 0 then v j / lam else u j
  refine ⟨w, ?_, ?_⟩
  · intro j
    dsimp [w]
    split_ifs
    · exact div_nonneg (hv j) hl.le
    · exact hu j
  · intro i
    unfold expanded retained
    apply Finset.sum_congr rfl
    intro j _
    dsimp [w]
    split_ifs with h
    · rw [h i]
      field_simp
      ring
    · have hb := (hp j).resolve_left h
      rw [hb i]
      ring

theorem retained_to_expanded
    (A B : J → I → ℝ) (lam : ℝ) (hl : 0 ≤ lam)
    (w : J → ℝ) (hw : ∀ j, 0 ≤ w j) :
    ∃ u v : J → ℝ, (∀ j, 0 ≤ u j) ∧ (∀ j, 0 ≤ v j) ∧
      ∀ i, retained A B lam w i = expanded A B u v i := by
  refine ⟨w, fun j => lam * w j, hw, fun j => mul_nonneg hl (hw j), ?_⟩
  intro i
  unfold retained expanded
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem expanded_family_equal
    (A B : J → I → ℝ) (hp : Pure A B) (lam : ℝ) (hl : 0 < lam)
    (t : I → ℝ) :
    (∃ u v, (∀ j, 0 ≤ u j) ∧ (∀ j, 0 ≤ v j) ∧
      ∀ i, expanded A B u v i = t i) ↔
    (∃ w, (∀ j, 0 ≤ w j) ∧ ∀ i, retained A B lam w i = t i) := by
  constructor
  · rintro ⟨u, v, hu, hv, ht⟩
    obtain ⟨w, hw, he⟩ := expanded_to_retained A B hp lam hl u v hu hv
    exact ⟨w, hw, fun i => (he i).symm.trans (ht i)⟩
  · rintro ⟨w, hw, ht⟩
    obtain ⟨u, v, hu, hv, he⟩ := retained_to_expanded A B lam hl.le w hw
    exact ⟨u, v, hu, hv, fun i => (he i).symm.trans (ht i)⟩

end RussianDisplayed

