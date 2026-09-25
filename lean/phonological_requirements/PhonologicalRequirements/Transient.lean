                                             
import PhonologicalRequirements.Contribution

namespace PhonologicalRequirements

                
theorem contrib_inert (num den w p : Nat) : contrib num den w 0 p 0 = 0 := by
  unfold contrib
  simp

                
theorem contrib_retained_destroyed (num den w p : Nat)
    (hw : 0 < w) (hd : 0 < den) (hp : 0 < p) :
    0 < contrib num den w 1 p 0 := by
  rw [contrib_a_one]
  exact Nat.mul_pos hw (Nat.mul_pos hd hp)

def dot : List (Nat × Nat) → Nat
  | [] => 0
  | (w, c) :: t => w * c + dot t

def dominates (l : List (Nat × Nat × Nat)) : Prop :=
  ∀ x ∈ l, x.2.1 ≤ x.2.2

def strictAt (l : List (Nat × Nat × Nat)) : Prop :=
  ∃ x ∈ l, 0 < x.1 ∧ x.2.1 < x.2.2

def lo (l : List (Nat × Nat × Nat)) : List (Nat × Nat) :=
  l.map (fun x => (x.1, x.2.1))

def hi (l : List (Nat × Nat × Nat)) : List (Nat × Nat) :=
  l.map (fun x => (x.1, x.2.2))

theorem dot_le_of_dominates : ∀ l : List (Nat × Nat × Nat),
    dominates l → dot (lo l) ≤ dot (hi l)
  | [], _ => Nat.le_refl 0
  | (w, a, b) :: t, h => by
      have hx : a ≤ b := h (w, a, b) (List.mem_cons_self)
      have ht : dominates t := fun x hm => h x (List.mem_cons_of_mem _ hm)
      have := dot_le_of_dominates t ht
      simp only [lo, hi, List.map_cons, dot]
      exact Nat.add_le_add (Nat.mul_le_mul_left w hx) this

                    
theorem dot_lt_of_dominates : ∀ l : List (Nat × Nat × Nat),
    dominates l → strictAt l → dot (lo l) < dot (hi l)
  | [], _, ⟨_, hm, _⟩ => (List.not_mem_nil hm).elim
  | (w, a, b) :: t, h, ⟨x, hm, hw, hab⟩ => by
      have ht : dominates t := fun y hy => h y (List.mem_cons_of_mem _ hy)
      have hx : a ≤ b := h (w, a, b) (List.mem_cons_self)
      simp only [lo, hi, List.map_cons, dot]
      rcases List.mem_cons.mp hm with he | hmt
      · subst he
        have h1 : w * a < w * b := (Nat.mul_lt_mul_left hw).mpr hab
        exact Nat.add_lt_add_of_lt_of_le h1 (dot_le_of_dominates t ht)
      · have h2 : dot (lo t) < dot (hi t) :=
          dot_lt_of_dominates t ht ⟨x, hmt, hw, hab⟩
        exact Nat.add_lt_add_of_le_of_lt (Nat.mul_le_mul_left w hx) h2

                   
theorem arapaho_transient_excluded (wNoCoda wSeg wDor wAnt : Nat) (h : 0 < wSeg) :
    dot (lo [(wNoCoda, 1, 1), (wSeg, 0, 1), (wDor, 0, 1), (wAnt, 0, 1)])
      < dot (hi [(wNoCoda, 1, 1), (wSeg, 0, 1), (wDor, 0, 1), (wAnt, 0, 1)]) := by
  refine dot_lt_of_dominates _ ?_ ⟨(wSeg, 0, 1), ?_, h, Nat.zero_lt_one⟩
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with h1 | h1 | h1 | h1 <;> subst h1 <;> simp
  · simp

                   
theorem arapaho_needs_positive_attenuation (num wMutAnt : Nat) (h : 0 < num * wMutAnt) : 0 < num := by
  rcases Nat.eq_zero_or_pos num with h0 | h0
  · subst h0; simp at h
  · exact h0

                   
theorem arapaho_control_needs_attenuation_below_one (num den wMut wSeg wDor wAnt : Nat)
    (hmut : wSeg + wDor + wAnt < wMut) (hctrl : wMut * num < (wDor + wSeg) * den) : num < den := by
  rcases Nat.lt_or_ge num den with h | h
  · exact h
  · exfalso
    have h1 : wMut * den ≤ wMut * num := Nat.mul_le_mul_left wMut h
    have h2 : (wDor + wSeg) * den ≤ (wSeg + wDor + wAnt) * den := Nat.mul_le_mul_right den (by omega)
    have h3 : (wSeg + wDor + wAnt) * den < wMut * den := by
      have hd : 0 < den := by
        rcases Nat.eq_zero_or_pos den with h0 | h0
        · subst h0; simp at hctrl
        · exact h0
      exact Nat.mul_lt_mul_of_pos_right hmut hd
    omega

end PhonologicalRequirements
