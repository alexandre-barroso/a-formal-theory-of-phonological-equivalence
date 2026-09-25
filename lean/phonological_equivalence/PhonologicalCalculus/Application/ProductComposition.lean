                                                   
import Mathlib.Logic.Relation
import Mathlib.Data.Real.Basic

namespace ProductComposition

variable {A B : Type}

def localStep (ra : A → A → Prop) (rb : B → B → Prop) (p q : A × B) : Prop :=
  (ra p.1 q.1 ∧ p.2 = q.2) ∨ (p.1 = q.1 ∧ rb p.2 q.2)

theorem reachable_components (ra : A → A → Prop) (rb : B → B → Prop)
    {p q : A × B} (h : Relation.ReflTransGen (localStep ra rb) p q) :
    Relation.ReflTransGen ra p.1 q.1 ∧ Relation.ReflTransGen rb p.2 q.2 := by
  induction h with
  | refl => exact ⟨.refl,.refl⟩
  | @tail t u _ htu ih =>
    rcases htu with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · exact ⟨ih.1.tail ha, hb ▸ ih.2⟩
    · exact ⟨ha ▸ ih.1, ih.2.tail hb⟩

theorem lift_left (ra : A → A → Prop) (rb : B → B → Prop)
    {a a' : A} (b : B) (h : Relation.ReflTransGen ra a a') :
    Relation.ReflTransGen (localStep ra rb) (a,b) (a',b) := by
  induction h with
  | refl => exact .refl
  | tail _ ht ih => exact ih.tail (Or.inl ⟨ht,rfl⟩)

theorem lift_right (ra : A → A → Prop) (rb : B → B → Prop)
    (a : A) {b b' : B} (h : Relation.ReflTransGen rb b b') :
    Relation.ReflTransGen (localStep ra rb) (a,b) (a,b') := by
  induction h with
  | refl => exact .refl
  | tail _ ht ih => exact ih.tail (Or.inr ⟨rfl,ht⟩)

theorem reachable_product (ra : A → A → Prop) (rb : B → B → Prop)
    (a a' : A) (b b' : B) :
    Relation.ReflTransGen (localStep ra rb) (a,b) (a',b') ↔
      Relation.ReflTransGen ra a a' ∧ Relation.ReflTransGen rb b b' := by
  constructor
  · exact reachable_components ra rb
  · rintro ⟨ha,hb⟩
    exact (lift_left ra rb b ha).trans (lift_right ra rb a' hb)

def isMin {S : Type} (cost : S → ℝ) (domain : S → Prop) (s : S) : Prop :=
  domain s ∧ ∀ t, domain t → cost s ≤ cost t

theorem argmin_product (f : A → ℝ) (g : B → ℝ) (da : A → Prop) (db : B → Prop)
    (a : A) (b : B) :
    isMin (fun p : A × B => f p.1 + g p.2) (fun p => da p.1 ∧ db p.2) (a,b) ↔
      isMin f da a ∧ isMin g db b := by
  constructor
  · rintro ⟨⟨ha,hb⟩,hmin⟩
    refine ⟨⟨ha,?_⟩,⟨hb,?_⟩⟩
    · intro x hx
      exact (add_le_add_iff_right (g b)).mp (hmin (x,b) ⟨hx,hb⟩)
    · intro y hy
      exact (add_le_add_iff_left (f a)).mp (hmin (a,y) ⟨ha,hy⟩)
  · rintro ⟨⟨ha,hfa⟩,⟨hb,hgb⟩⟩
    refine ⟨⟨ha,hb⟩,?_⟩
    rintro ⟨x,y⟩ ⟨hx,hy⟩
    exact add_le_add (hfa x hx) (hgb y hy)

theorem noninterference (ra : A → A → Prop) (rb : B → B → Prop)
    (a₀ a : A) (b₀ b : B) (f : A → ℝ) (g : B → ℝ) :
    isMin (fun p : A × B => f p.1 + g p.2)
      (Relation.ReflTransGen (localStep ra rb) (a₀,b₀)) (a,b) ↔
    isMin f (Relation.ReflTransGen ra a₀) a ∧ isMin g (Relation.ReflTransGen rb b₀) b := by
  have hd : Relation.ReflTransGen (localStep ra rb) (a₀,b₀) =
      (fun p : A × B => Relation.ReflTransGen ra a₀ p.1 ∧ Relation.ReflTransGen rb b₀ p.2) := by
    funext p
    exact propext (reachable_product ra rb a₀ p.1 b₀ p.2)
  rw [hd]
  exact argmin_product f g _ _ a b

end ProductComposition
