                 
namespace PhonologicalRequirements
namespace Interaction

def sepCost (r w : Nat → Nat) : List Bool → Nat → Nat
  | [], _ => 0
  | b :: bs, i => (if b then r i else w i) + sepCost r w bs (i + 1)

def Pointwise (r w : Nat → Nat) : List Bool → Nat → Prop
  | [], _ => True
  | b :: bs, i => (if b then r i ≤ w i else w i ≤ r i) ∧ Pointwise r w bs (i + 1)

def minCost (r w : Nat → Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, i => min (r i) (w i) + minCost r w n (i + 1)

theorem choice_ge_min (r w : Nat → Nat) (b : Bool) (i : Nat) : min (r i) (w i) ≤ (if b then r i else w i) := by
  cases b
  · simp only [Bool.false_eq_true, ite_false]; exact Nat.min_le_right _ _
  · simp only [ite_true]; exact Nat.min_le_left _ _

theorem choice_eq_min_iff (r w : Nat → Nat) (b : Bool) (i : Nat) :
    (if b then r i else w i) = min (r i) (w i) ↔ (if b then r i ≤ w i else w i ≤ r i) := by
  cases b
  · simp only [Bool.false_eq_true, ite_false]
    constructor
    · intro h; have := Nat.min_le_left (r i) (w i); omega
    · intro h; exact (Nat.min_eq_right h).symm
  · simp only [ite_true]
    constructor
    · intro h; have := Nat.min_le_right (r i) (w i); omega
    · intro h; exact (Nat.min_eq_left h).symm

theorem sepCost_ge (r w : Nat → Nat) : ∀ (S : List Bool) (i : Nat), minCost r w S.length i ≤ sepCost r w S i
  | [], _ => Nat.le_refl _
  | b :: bs, i => Nat.add_le_add (choice_ge_min r w b i) (sepCost_ge r w bs (i + 1))

theorem sepCost_eq_min_iff (r w : Nat → Nat) : ∀ (S : List Bool) (i : Nat),
    sepCost r w S i = minCost r w S.length i ↔ Pointwise r w S i
  | [], _ => by simp [sepCost, minCost, Pointwise]
  | b :: bs, i => by
    have h1 := choice_ge_min r w b i
    have h2 := sepCost_ge r w bs (i + 1)
    have ih := sepCost_eq_min_iff r w bs (i + 1)
    show (if b then r i else w i) + sepCost r w bs (i + 1) = min (r i) (w i) + minCost r w bs.length (i + 1)
      ↔ (if b then r i ≤ w i else w i ≤ r i) ∧ Pointwise r w bs (i + 1)
    rw [← choice_eq_min_iff r w b i, ← ih]
    omega

def opt (r w : Nat → Nat) : Nat → Nat → List Bool
  | 0, _ => []
  | n + 1, i => decide (r i ≤ w i) :: opt r w n (i + 1)

theorem opt_length (r w : Nat → Nat) : ∀ n i, (opt r w n i).length = n
  | 0, _ => rfl
  | n + 1, i => by simp [opt, opt_length r w n (i + 1)]

theorem opt_pointwise (r w : Nat → Nat) : ∀ n i, Pointwise r w (opt r w n i) i
  | 0, _ => trivial
  | n + 1, i => by
    refine ⟨?_, opt_pointwise r w n (i + 1)⟩
    by_cases h : r i ≤ w i
    · simp [h]
    · simp [h]; omega

theorem separable_argmin (r w : Nat → Nat) (S : List Bool) (i : Nat) :
    (∀ T : List Bool, T.length = S.length → sepCost r w S i ≤ sepCost r w T i) ↔ Pointwise r w S i := by
  constructor
  · intro h
    have hopt := h (opt r w S.length i) (opt_length r w S.length i)
    have heq := (sepCost_eq_min_iff r w (opt r w S.length i) i).mpr (opt_pointwise r w S.length i)
    rw [opt_length] at heq
    rw [heq] at hopt
    exact (sepCost_eq_min_iff r w S i).mp (Nat.le_antisymm hopt (sepCost_ge r w S i))
  · intro hp T hT
    rw [(sepCost_eq_min_iff r w S i).mpr hp, ← hT]
    exact sepCost_ge r w T i

def cycleCost {k : Nat} (r w : Fin k → Nat) (pred : Fin k → Fin k) (S : Fin k → Bool) : Nat :=
  (List.finRange k).foldr (fun j acc => (if S j then r j else if S (pred j) then 0 else w j) + acc) 0

theorem foldr_add_le {k : Nat} (f g : Fin k → Nat) (l : List (Fin k)) (h : ∀ j, f j ≤ g j) :
    l.foldr (fun j acc => f j + acc) 0 ≤ l.foldr (fun j acc => g j + acc) 0 := by
  induction l with
  | nil => exact Nat.le_refl _
  | cons a l ih => exact Nat.add_le_add (h a) ih

theorem foldr_add_lt {k : Nat} (f g : Fin k → Nat) (l : List (Fin k)) (h : ∀ j, f j ≤ g j) (j0 : Fin k)
    (hj : j0 ∈ l) (hlt : f j0 < g j0) :
    l.foldr (fun j acc => f j + acc) 0 < l.foldr (fun j acc => g j + acc) 0 := by
  induction l with
  | nil => cases hj
  | cons a l ih =>
    simp only [List.foldr]
    rcases List.mem_cons.mp hj with rfl | hmem
    · exact Nat.add_lt_add_of_lt_of_le hlt (foldr_add_le f g l h)
    · exact Nat.add_lt_add_of_le_of_lt (h a) (ih hmem)

theorem all_apply_not_min {k : Nat} (r w : Fin k → Nat) (pred : Fin k → Fin k)
    (hpred : ∀ j, pred j ≠ j) (hr : ∀ j, 0 < r j) (j0 : Fin k) :
    cycleCost r w pred (fun j => if j = j0 then false else true) < cycleCost r w pred (fun _ => true) := by
  unfold cycleCost
  have hle : ∀ j : Fin k,
      (if (if j = j0 then false else true) = true then r j else if (if pred j = j0 then false else true) = true then 0 else w j)
        ≤ (if true = true then r j else if true = true then 0 else w j) := by
    intro j
    by_cases hj : j = j0
    · subst hj
      have hp : pred j ≠ j := hpred j
      simp [hp]
    · simp [hj]
  have hlt : (if (if j0 = j0 then false else true) = true then r j0 else if (if pred j0 = j0 then false else true) = true then 0 else w j0)
        < (if true = true then r j0 else if true = true then 0 else w j0) := by
    have hp : pred j0 ≠ j0 := hpred j0
    simp [hp]; exact hr j0
  exact foldr_add_lt _ _ _ hle j0 (List.mem_finRange j0) hlt

end Interaction
end PhonologicalRequirements
