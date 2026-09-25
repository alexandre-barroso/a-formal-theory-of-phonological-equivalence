                     
                   
import PhonologicalCalculus.Application.Regularity.BoundedMemory

namespace ShiftRegister

abbrev Register (Z : Type) := Fin 4 → Option Z

def shift {Z : Type} (q : Register Z) (z : Option Z) : Register Z :=
  fun i => if h : i.val < 3 then q ⟨i.val+1,by omega⟩ else z

def agree {Z : Type} (k : ℕ) (q r : Register Z) : Prop :=
  ∀ i, 4-k ≤ i.val → q i = r i

theorem agree_zero {Z : Type} (q r : Register Z) : agree 0 q r := by
  intro i hi
  have := i.isLt
  omega

theorem agree_four {Z : Type} {q r : Register Z} (h : agree 4 q r) : q = r := by
  funext i
  exact h i (by omega)

theorem agree_shift {Z : Type} (k : ℕ) {q r : Register Z} (h : agree k q r) (z : Option Z) :
    agree (k+1) (shift q z) (shift r z) := by
  intro i hi
  simp only [shift]
  split_ifs with hs
  · apply h
    dsimp
    omega
  · rfl

variable {Z D I : Type}

def ecost (charge : Register Z → Option Z → ℕ) (deletion : D → ℕ) :
    Register Z → List (Sum D (Option Z)) → ℕ
  | _, [] => 0
  | q, Sum.inl d :: xs => deletion d + ecost charge deletion q xs
  | q, Sum.inr z :: xs => charge q z + ecost charge deletion (shift q z) xs

theorem cost_bound (charge : Register Z → Option Z → ℕ) (deletion : D → ℕ)
    (C : ℕ) (hc : ∀ q z, charge q z ≤ C) (xs : List (Sum D (Option Z))) :
    ∀ (k : ℕ) (q r : Register Z), agree k q r →
      ecost charge deletion q xs ≤ ecost charge deletion r xs + (4-k)*C := by
  induction xs with
  | nil => intros; simp [ecost]
  | cons a xs ih =>
    intro k q r h
    by_cases hk : 4 ≤ k
    · have e : q = r := by
        apply agree_four
        intro i hi
        exact h i (by omega)
      subst r
      omega
    · cases a with
      | inl d =>
        have hh := ih k q r h
        simpa only [ecost,Nat.add_assoc] using Nat.add_le_add_left hh (deletion d)
      | inr z =>
        have hh := ih (k+1) (shift q z) (shift r z) (agree_shift k h z)
        have hq := hc q z
        have hk' : (4-k)*C = (4-(k+1))*C+C := by
          have : 4-k = (4-(k+1))+1 := by omega
          rw [this,Nat.add_mul,Nat.one_mul]
        simp only [ecost]
        omega

def eventStep (q : Register Z) : Sum D (Option Z) → Register Z
  | Sum.inl _ => q
  | Sum.inr z => shift q z

theorem ecost_append (charge : Register Z → Option Z → ℕ) (deletion : D → ℕ)
    (q : Register Z) (xs ys : List (Sum D (Option Z))) :
    ecost charge deletion q (xs ++ ys) = ecost charge deletion q xs +
      ecost charge deletion (xs.foldl eventStep q) ys := by
  induction xs generalizing q with
  | nil => simp [ecost]
  | cons a xs ih => cases a <;> simp [ecost,eventStep,ih,Nat.add_assoc]

def machine (charge : Register Z → Option Z → ℕ) (deletion : D → ℕ)
    (inp : Sum D Z → I) (ok : Sum D Z → Prop) :
    BoundedMemory.Machine (Register Z) (Sum D Z) I where
  start := fun _ => none
  step := fun q a => match a with
    | Sum.inl _ => q
    | Sum.inr z => shift q (some z)
  weight := fun q a => match a with
    | Sum.inl d => deletion d
    | Sum.inr z => charge q (some z)
  final := fun q => ecost charge deletion q [Sum.inr none,Sum.inr none]
  input := inp
  allowed := ok

def events (xs : List (Sum D Z)) : List (Sum D (Option Z)) := xs.map (Sum.map id some)

theorem state_events (charge : Register Z → Option Z → ℕ) (deletion : D → ℕ)
    (inp : Sum D Z → I) (ok : Sum D Z → Prop) (q : Register Z) (xs : List (Sum D Z)) :
    (machine charge deletion inp ok).state q xs = (events xs).foldl eventStep q := by
  induction xs generalizing q with
  | nil => rfl
  | cons a xs ih => cases a <;> simpa [BoundedMemory.Machine.state,machine,events,eventStep] using ih _

theorem total_events (charge : Register Z → Option Z → ℕ) (deletion : D → ℕ)
    (inp : Sum D Z → I) (ok : Sum D Z → Prop) (q : Register Z) (xs : List (Sum D Z)) :
    (machine charge deletion inp ok).total q xs =
      ecost charge deletion q (events xs ++ [Sum.inr none,Sum.inr none]) := by
  induction xs generalizing q with
  | nil => simp [BoundedMemory.Machine.total,BoundedMemory.Machine.cost,BoundedMemory.Machine.state,machine,events]
  | cons a xs ih =>
    cases a with
    | inl d =>
      simpa [BoundedMemory.Machine.total,BoundedMemory.Machine.cost,BoundedMemory.Machine.state,machine,events,eventStep,ecost,Nat.add_assoc]
        using congrArg (deletion d + ·) (ih q)
    | inr z =>
      simpa [BoundedMemory.Machine.total,BoundedMemory.Machine.cost,BoundedMemory.Machine.state,machine,events,eventStep,ecost,Nat.add_assoc]
        using congrArg (charge q (some z) + ·) (ih (shift q (some z)))

theorem continuation_bound (charge : Register Z → Option Z → ℕ) (deletion : D → ℕ)
    (inp : Sum D Z → I) (ok : Sum D Z → Prop) (C : ℕ) (hc : ∀ q z, charge q z ≤ C) :
    (machine charge deletion inp ok).bounded (4*C) := by
  intro q r xs
  rw [total_events,total_events]
  simpa using cost_bound charge deletion C hc (events xs ++ [Sum.inr none,Sum.inr none]) 0 q r (agree_zero q r)

theorem regular_optimal_alignments [Finite Z] (charge : Register Z → Option Z → ℕ)
    (deletion : D → ℕ) (inp : Sum D Z → I) (ok : Sum D Z → Prop)
    (C : ℕ) (hc : ∀ q z, charge q z ≤ C) :
    Language.IsRegular {xs | (machine charge deletion inp ok).winner xs} :=
  BoundedMemory.Machine.regular_winners _ (4*C) (continuation_bound charge deletion inp ok C hc)

end ShiftRegister
