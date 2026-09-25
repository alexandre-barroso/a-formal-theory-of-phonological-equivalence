                                                
namespace PhonologicalRequirements
namespace Barrier

variable {S : Type}

def Chosen (P : S → Int) (E : S → S → Prop) (c : Int) (s t : S) : Prop :=
  E s t ∧ c + P t < P s ∧ ∀ r, E s r → c + P t ≤ c + P r

inductive Reach (P : S → Int) (E : S → S → Prop) (c : Int) : S → S → Prop
  | refl (s : S) : Reach P E c s s
  | step {s t u : S} : Reach P E c s t → Chosen P E c t u → Reach P E c s u

theorem chosen_decreases {P : S → Int} {E : S → S → Prop} {c : Int} (hc : 0 ≤ c) {s t : S}
    (h : Chosen P E c s t) : P t < P s := by
  have := h.2.1
  omega

theorem first_step_bound {P : S → Int} {E : S → S → Prop} {c : Int} {U Z t : S}
    (hZ : E U Z) (h : Chosen P E c U t) : P t ≤ P Z := by
  have := h.2.2 Z hZ
  omega

theorem reach_cases {P : S → Int} {E : S → S → Prop} {c : Int} {s x : S} (h : Reach P E c s x) :
    x = s ∨ ∃ t, Chosen P E c s t ∧ Reach P E c t x := by
  induction h with
  | refl => exact Or.inl rfl
  | step _ htu ih =>
    rcases ih with rfl | ⟨t', h1, h2⟩
    · exact Or.inr ⟨_, htu, Reach.refl _⟩
    · exact Or.inr ⟨t', h1, Reach.step h2 htu⟩

theorem reach_strict {P : S → Int} {E : S → S → Prop} {c : Int} (hc : 0 ≤ c) {s x : S}
    (h : Reach P E c s x) : x = s ∨ P x < P s := by
  induction h with
  | refl => exact Or.inl rfl
  | step _ htu ih =>
    have hd := chosen_decreases hc htu
    rcases ih with rfl | hlt
    · exact Or.inr hd
    · exact Or.inr (by omega)

theorem no_path_to_target {P : S → Int} {E : S → S → Prop} {c : Int} (hc : 0 ≤ c) {U T Z : S}
    (hUT : U ≠ T) (hZ : E U Z) (hT : ¬ E U T) (hPZ : P Z ≤ P T) :
    ¬ Reach P E c U T := by
  intro h
  rcases reach_cases h with rfl | ⟨t, hUt, htT⟩
  · exact hUT rfl
  · have hb := first_step_bound hZ hUt
    rcases reach_strict hc htT with rfl | hlt
    · exact hT hUt.1
    · omega

end Barrier
end PhonologicalRequirements
