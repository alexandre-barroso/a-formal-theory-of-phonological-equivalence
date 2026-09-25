        

namespace PhonologicalRequirements

def Refines {α β γ : Type} (d1 : α → β) (d2 : α → γ) : Prop :=
  ∀ x y, d1 x = d1 y → d2 x = d2 y

def ClosesCell {α β : Type} (d : α → β) (after : List α) (n : α) : Prop :=
  ∀ m ∈ after, d m ≠ d n

        
theorem closesCell_of_refines {α β γ : Type} {d1 : α → β} {d2 : α → γ}
    (h : Refines d1 d2) (after : List α) (n : α) :
    ClosesCell d2 after n → ClosesCell d1 after n := by
  intro hl m hm he
  exact hl m hm (h m n he)

theorem refines_trans {α β γ δ : Type} {d1 : α → β} {d2 : α → γ} {d3 : α → δ}
    (h12 : Refines d1 d2) (h23 : Refines d2 d3) : Refines d1 d3 :=
  fun x y hx => h23 x y (h12 x y hx)

theorem closesCell_not_symm :
    ∃ (d1 d2 : Bool → Nat) (after : List Bool) (n : Bool),
      Refines d1 d2 ∧ ClosesCell d1 after n ∧ ¬ ClosesCell d2 after n := by
  refine ⟨fun b => if b then 0 else 1, fun _ => 0, [false], true, ?_, ?_, ?_⟩
  · intro x y _
    rfl
  · intro m hm
    simp at hm
    subst hm
    decide
  · intro hc
    exact absurd (hc false (by simp)) (by decide)

end PhonologicalRequirements
