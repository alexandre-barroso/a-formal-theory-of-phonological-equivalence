                          
namespace PhonologicalRequirements
namespace Compose

inductive Reach {S : Type} (ops : List (S → Option S)) : S → S → Prop
  | refl (s : S) : Reach ops s s
  | step {s t u : S} (h : Reach ops s t) (op : S → Option S) (hop : op ∈ ops) (hu : op t = some u) : Reach ops s u

def liftA {A B : Type} (op : A → Option A) : A × B → Option (A × B) :=
  fun p => (op p.1).map (fun a => (a, p.2))
def liftB {A B : Type} (op : B → Option B) : A × B → Option (A × B) :=
  fun p => (op p.2).map (fun b => (p.1, b))

def localOps {A B : Type} (opsA : List (A → Option A)) (opsB : List (B → Option B)) : List (A × B → Option (A × B)) :=
  opsA.map liftA ++ opsB.map liftB

theorem reach_fst {A B : Type} {opsA : List (A → Option A)} {opsB : List (B → Option B)} {p q : A × B}
    (h : Reach (localOps opsA opsB) p q) : Reach opsA p.1 q.1 ∧ Reach opsB p.2 q.2 := by
  induction h with
  | refl => exact ⟨Reach.refl _, Reach.refl _⟩
  | step h op hop hu ih =>
    rcases List.mem_append.mp hop with hA | hB
    · rcases List.mem_map.mp hA with ⟨oa, hoa, rfl⟩
      simp only [liftA, Option.map] at hu
      cases hoa' : oa _ with
      | none => rw [hoa'] at hu; cases hu
      | some a => rw [hoa'] at hu; simp only at hu; cases hu; exact ⟨Reach.step ih.1 oa hoa hoa', ih.2⟩
    · rcases List.mem_map.mp hB with ⟨ob, hob, rfl⟩
      simp only [liftB, Option.map] at hu
      cases hob' : ob _ with
      | none => rw [hob'] at hu; cases hu
      | some b => rw [hob'] at hu; simp only at hu; cases hu; exact ⟨ih.1, Reach.step ih.2 ob hob hob'⟩

theorem reach_liftA {A B : Type} {opsA : List (A → Option A)} {opsB : List (B → Option B)} {a a' : A} (b : B)
    (h : Reach opsA a a') : Reach (localOps opsA opsB) (a, b) (a', b) := by
  induction h with
  | refl => exact Reach.refl _
  | step h op hop hu ih =>
    refine Reach.step ih (liftA op) (List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨op, hop, rfl⟩))) ?_
    simp [liftA, hu]

theorem reach_liftB {A B : Type} {opsA : List (A → Option A)} {opsB : List (B → Option B)} (a : A) {b b' : B}
    (h : Reach opsB b b') : Reach (localOps opsA opsB) (a, b) (a, b') := by
  induction h with
  | refl => exact Reach.refl _
  | step h op hop hu ih =>
    refine Reach.step ih (liftB op) (List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨op, hop, rfl⟩))) ?_
    simp [liftB, hu]

theorem reach_trans {S : Type} {ops : List (S → Option S)} {s t u : S} (h1 : Reach ops s t) (h2 : Reach ops t u) : Reach ops s u := by
  induction h2 with
  | refl => exact h1
  | step _ op hop hu ih => exact Reach.step ih op hop hu

theorem reach_prod {A B : Type} (opsA : List (A → Option A)) (opsB : List (B → Option B)) (a0 : A) (b0 : B) (a : A) (b : B) :
    Reach (localOps opsA opsB) (a0, b0) (a, b) ↔ Reach opsA a0 a ∧ Reach opsB b0 b := by
  constructor
  · intro h; exact reach_fst h
  · rintro ⟨ha, hb⟩
    exact reach_trans (reach_liftA b0 ha) (reach_liftB a hb)

def IsMinOn {S : Type} (P : S → Nat) (D : S → Prop) (s : S) : Prop := D s ∧ ∀ t, D t → P s ≤ P t

theorem argmin_prod {A B : Type} (f : A → Nat) (g : B → Nat) (DA : A → Prop) (DB : B → Prop) (a : A) (b : B) :
    IsMinOn (fun p : A × B => f p.1 + g p.2) (fun p => DA p.1 ∧ DB p.2) (a, b) ↔ IsMinOn f DA a ∧ IsMinOn g DB b := by
  constructor
  · rintro ⟨⟨ha, hb⟩, hmin⟩
    refine ⟨⟨ha, ?_⟩, ⟨hb, ?_⟩⟩
    · intro a' ha'
      have := hmin (a', b) ⟨ha', hb⟩
      simp only at this
      exact Nat.le_of_add_le_add_right this
    · intro b' hb'
      have := hmin (a, b') ⟨ha, hb'⟩
      simp only at this
      exact Nat.le_of_add_le_add_left this
  · rintro ⟨⟨ha, hfa⟩, ⟨hb, hgb⟩⟩
    refine ⟨⟨ha, hb⟩, ?_⟩
    rintro ⟨a', b'⟩ ⟨ha', hb'⟩
    exact Nat.add_le_add (hfa a' ha') (hgb b' hb')

theorem noninterference {A B : Type} (opsA : List (A → Option A)) (opsB : List (B → Option B)) (a0 : A) (b0 : B)
    (f : A → Nat) (g : B → Nat) (a : A) (b : B) :
    IsMinOn (fun p : A × B => f p.1 + g p.2) (fun p => Reach (localOps opsA opsB) (a0, b0) p) (a, b)
      ↔ IsMinOn f (Reach opsA a0) a ∧ IsMinOn g (Reach opsB b0) b := by
  have hd : ∀ p : A × B, Reach (localOps opsA opsB) (a0, b0) p ↔ (Reach opsA a0 p.1 ∧ Reach opsB b0 p.2) :=
    fun p => by rcases p with ⟨x, y⟩; exact reach_prod opsA opsB a0 b0 x y
  rw [← argmin_prod f g (Reach opsA a0) (Reach opsB b0) a b]
  constructor
  · rintro ⟨hp, hmin⟩
    refine ⟨(hd (a, b)).mp hp, ?_⟩
    intro t ht; exact hmin t ((hd t).mpr ht)
  · rintro ⟨hp, hmin⟩
    refine ⟨(hd (a, b)).mpr hp, ?_⟩
    intro t ht; exact hmin t ((hd t).mp ht)

end Compose
end PhonologicalRequirements
