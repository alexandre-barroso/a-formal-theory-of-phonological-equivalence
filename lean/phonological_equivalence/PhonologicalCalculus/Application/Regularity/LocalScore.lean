                     
                   
import PhonologicalCalculus.Application.Regularity.ShiftRegister

namespace LocalScore

variable {Z D I : Type}

def point (f : Z → Option Z → Option Z → Option Z → Option Z → ℕ)
    (l₂ l₁ c r₁ r₂ : Option Z) : ℕ :=
  match c with
  | none => 0
  | some z => f z l₂ l₁ r₁ r₂

def register (a b c d : Option Z) : ShiftRegister.Register Z := ![a,b,c,d]

def charge (f : Z → Option Z → Option Z → Option Z → Option Z → ℕ)
    (q : ShiftRegister.Register Z) (z : Option Z) : ℕ := point f (q 0) (q 1) (q 2) (q 3) z

def objective (f : Z → Option Z → Option Z → Option Z → Option Z → ℕ)
    (l₂ l₁ : Option Z) : List (Option Z) → ℕ
  | [] => 0
  | c :: xs => point f l₂ l₁ c xs.head! xs.tail.head! + objective f l₁ c xs

@[simp] theorem shift_register (a b c d z : Option Z) :
    ShiftRegister.shift (register a b c d) z = register b c d z := by
  funext i
  rcases i with ⟨i,hi⟩
  interval_cases i <;> rfl

theorem delayed_objective (f : Z → Option Z → Option Z → Option Z → Option Z → ℕ)
    (deletion : D → ℕ) (xs : List (Option Z)) (a b c d : Option Z) :
    ShiftRegister.ecost (charge f) deletion (register a b c d)
      ((xs ++ [none,none]).map Sum.inr) = objective f a b (c :: d :: xs) := by
  induction xs generalizing a b c d with
  | nil => simp [ShiftRegister.ecost,charge,register,ShiftRegister.shift,objective,point]; rfl
  | cons z xs ih =>
    simp only [List.cons_append,List.map_cons,ShiftRegister.ecost,shift_register]
    rw [ih]
    rfl

theorem stream_objective (f : Z → Option Z → Option Z → Option Z → Option Z → ℕ)
    (deletion : D → ℕ) (xs : List (Option Z)) :
    ShiftRegister.ecost (charge f) deletion (fun _ => none)
      ((xs ++ [none,none]).map Sum.inr) = objective f none none xs := by
  have h := delayed_objective f deletion xs none none none none
  have eq : register (Z := Z) none none none none = (fun _ => none) := by
    funext i; rcases i with ⟨i,hi⟩; interval_cases i <;> rfl
  rw [eq] at h
  simpa [objective,point] using h

def deleteCost (deletion : D → ℕ) : List (Sum D Z) → ℕ
  | [] => 0
  | Sum.inl d :: xs => deletion d + deleteCost deletion xs
  | Sum.inr _ :: xs => deleteCost deletion xs

def survivors : List (Sum D Z) → List Z
  | [] => []
  | Sum.inl _ :: xs => survivors xs
  | Sum.inr z :: xs => z :: survivors xs

theorem delete_split (f : Z → Option Z → Option Z → Option Z → Option Z → ℕ)
    (deletion : D → ℕ) (q : ShiftRegister.Register Z) (xs : List (Sum D Z)) :
    ShiftRegister.ecost (charge f) deletion q
      (ShiftRegister.events xs ++ [Sum.inr none,Sum.inr none]) =
      deleteCost deletion xs + ShiftRegister.ecost (charge f) deletion q
        (((survivors xs).map some ++ [none,none]).map Sum.inr) := by
  induction xs generalizing q with
  | nil => simp [ShiftRegister.events,deleteCost,survivors]
  | cons a xs ih =>
    cases a with
    | inl d =>
      change deletion d + ShiftRegister.ecost (charge f) deletion q
          (ShiftRegister.events xs ++ [Sum.inr none,Sum.inr none]) = _
      rw [ih]
      simp [deleteCost,survivors,Nat.add_assoc]
    | inr z =>
      change charge f q (some z) + ShiftRegister.ecost (charge f) deletion (ShiftRegister.shift q (some z))
          (ShiftRegister.events xs ++ [Sum.inr none,Sum.inr none]) = _
      rw [ih]
      simp [deleteCost,survivors,ShiftRegister.ecost,Nat.add_assoc,Nat.add_left_comm]

theorem native_score_bridge (f : Z → Option Z → Option Z → Option Z → Option Z → ℕ)
    (deletion : D → ℕ) (inp : Sum D Z → I) (ok : Sum D Z → Prop) (xs : List (Sum D Z)) :
    (ShiftRegister.machine (charge f) deletion inp ok).total (fun _ => none) xs =
      deleteCost deletion xs + objective f none none ((survivors xs).map some) := by
  rw [ShiftRegister.total_events,delete_split,stream_objective]

theorem local_charge_bound (f : Z → Option Z → Option Z → Option Z → Option Z → ℕ)
    (C : ℕ) (h : ∀ z a b c d, f z a b c d ≤ C) : ∀ q z, charge f q z ≤ C := by
  intro q z
  unfold charge point
  cases q 2 with
  | none => exact Nat.zero_le _
  | some x => exact h x _ _ _ _

theorem regular_local_winners [Finite Z]
    (f : Z → Option Z → Option Z → Option Z → Option Z → ℕ)
    (deletion : D → ℕ) (inp : Sum D Z → I) (ok : Sum D Z → Prop)
    (C : ℕ) (h : ∀ z a b c d, f z a b c d ≤ C) :
    Language.IsRegular {xs |
      (∀ a ∈ xs, ok a) ∧ ∀ ys, (∀ a ∈ ys, ok a) → ys.map inp = xs.map inp →
        deleteCost deletion xs + objective f none none ((survivors xs).map some) ≤
        deleteCost deletion ys + objective f none none ((survivors ys).map some)} := by
  have hr := ShiftRegister.regular_optimal_alignments (charge f) deletion inp ok C
    (local_charge_bound f C h)
  change Language.IsRegular {xs | (∀ a ∈ xs, ok a) ∧ ∀ ys, (∀ a ∈ ys, ok a) →
    ys.map inp = xs.map inp →
    (ShiftRegister.machine (charge f) deletion inp ok).total (fun _ => none) xs ≤
    (ShiftRegister.machine (charge f) deletion inp ok).total (fun _ => none) ys} at hr
  simpa only [native_score_bridge] using hr

theorem finite_local_bound [Finite Z]
    (f : Z → Option Z → Option Z → Option Z → Option Z → ℕ) :
    ∃ C, ∀ z a b c d, f z a b c d ≤ C := by
  let g : (Z × Option Z × Option Z × Option Z × Option Z) → ℕ :=
    fun p => f p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2
  obtain ⟨C,hC⟩ := (Set.finite_range g).bddAbove
  exact ⟨C,fun z a b c d => hC ⟨(z,a,b,c,d),rfl⟩⟩

theorem integer_local_regularity [Finite Z]
    (f : Z → Option Z → Option Z → Option Z → Option Z → ℕ)
    (deletion : D → ℕ) (inp : Sum D Z → I) (ok : Sum D Z → Prop) :
    Language.IsRegular {xs |
      (∀ a ∈ xs, ok a) ∧ ∀ ys, (∀ a ∈ ys, ok a) → ys.map inp = xs.map inp →
        deleteCost deletion xs + objective f none none ((survivors xs).map some) ≤
        deleteCost deletion ys + objective f none none ((survivors ys).map some)} := by
  obtain ⟨C,hC⟩ := finite_local_bound f
  exact regular_local_winners f deletion inp ok C hC

theorem positive_scaling_order (δ : ℝ) (hδ : 0 < δ) (m n : ℕ) :
    δ * m ≤ δ * n ↔ m ≤ n := by
  rw [mul_le_mul_iff_right₀ hδ]
  exact Nat.cast_le

end LocalScore
