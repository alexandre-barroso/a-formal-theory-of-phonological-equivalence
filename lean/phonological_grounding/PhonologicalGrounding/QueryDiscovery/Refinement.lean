                 
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Order.Basic
import PhonologicalGrounding.Basic

universe u v w

namespace PhonologicalGrounding.QueryDiscovery

structure Unary where
  Srt : Type u
  Carrier : Srt → Type v
  Step : Srt → Type w
  tgt : {s : Srt} → Step s → Srt
  act : {s : Srt} → (f : Step s) → Carrier s → Option (Carrier (tgt f))

namespace Unary

variable (S : Unary.{u, v, w})

inductive Chain : S.Srt → S.Srt → Type (max u w)
  | nil (s : S.Srt) : Chain s s
  | cons {s : S.Srt} (f : S.Step s) {t : S.Srt} (rest : Chain (S.tgt f) t) : Chain s t

namespace Chain

variable {S}

def depth : {s t : S.Srt} → S.Chain s t → ℕ
  | _, _, .nil _ => 0
  | _, _, .cons _ rest => rest.depth + 1

def eval : {s t : S.Srt} → S.Chain s t → S.Carrier s → Option (S.Carrier t)
  | _, _, .nil _, x => some x
  | _, _, .cons f rest, x => (S.act f x).bind (eval rest)

@[simp] theorem depth_nil (s : S.Srt) : (Chain.nil (S := S) s).depth = 0 := rfl

@[simp] theorem depth_cons {s t : S.Srt} (f : S.Step s) (rest : S.Chain (S.tgt f) t) :
    (Chain.cons f rest).depth = rest.depth + 1 := rfl

@[simp] theorem eval_nil (s : S.Srt) (x : S.Carrier s) :
    (Chain.nil (S := S) s).eval x = some x := rfl

@[simp] theorem eval_cons {s t : S.Srt} (f : S.Step s) (rest : S.Chain (S.tgt f) t)
    (x : S.Carrier s) :
    (Chain.cons f rest).eval x = (S.act f x).bind rest.eval := rfl

end Chain

variable {S}
variable {Obs : S.Srt → Type*} (ob : (s : S.Srt) → S.Carrier s → Obs s)

def SeparatedAt (n : ℕ) {s : S.Srt} (x y : S.Carrier s) : Prop :=
  ∃ (t : S.Srt) (C : S.Chain s t), C.depth ≤ n ∧
    (C.eval x).map (ob t) ≠ (C.eval y).map (ob t)

theorem separatedAt_mono {m n : ℕ} (h : m ≤ n) {s : S.Srt} {x y : S.Carrier s}
    (hsep : SeparatedAt ob m x y) : SeparatedAt ob n x y := by
  obtain ⟨t, C, hd, hne⟩ := hsep
  exact ⟨t, C, hd.trans h, hne⟩

def OptRel {A B : Type*} (r : A → B → Prop) : Option A → Option B → Prop
  | none, none => True
  | some u, some v => r u v
  | _, _ => False

theorem OptRel.none_none {A B : Type*} (r : A → B → Prop) :
    OptRel r (none : Option A) (none : Option B) := trivial

def R : ℕ → {s : S.Srt} → S.Carrier s → S.Carrier s → Prop
  | 0, s, x, y => ob s x = ob s y
  | n + 1, s, x, y =>
      ob s x = ob s y ∧ ∀ f : S.Step s, OptRel (fun u v => R n u v) (S.act f x) (S.act f y)

@[simp] theorem R_zero {s : S.Srt} (x y : S.Carrier s) :
    R ob 0 x y ↔ ob s x = ob s y := Iff.rfl

@[simp] theorem R_succ {s : S.Srt} (n : ℕ) (x y : S.Carrier s) :
    R ob (n + 1) x y ↔
      (ob s x = ob s y ∧
        ∀ f : S.Step s, OptRel (fun u v => R ob n u v) (S.act f x) (S.act f y)) :=
  Iff.rfl

theorem R_iff_not_separatedAt :
    ∀ (n : ℕ) {s : S.Srt} (x y : S.Carrier s),
      R ob n x y ↔ ¬ SeparatedAt ob n x y := by
  intro n
  induction n with
  | zero =>
      intro s x y
      constructor
      · intro hx ⟨t, C, hd, hne⟩
        cases C with
        | nil s => simp at hne; exact hne hx
        | cons f rest => simp at hd
      · intro h
        by_contra hx
        exact h ⟨s, Chain.nil s, le_rfl, by simpa using hx⟩
  | succ n ih =>
      intro s x y
      constructor
      · rintro ⟨hdirect, hstep⟩ ⟨t, C, hd, hne⟩
        cases C with
        | nil s => simp at hne; exact hne hdirect
        | cons f rest =>
            have hstepf := hstep f
            simp only [Chain.eval_cons] at hne
            cases hx : S.act f x with
            | none =>
                cases hy : S.act f y with
                | none => simp [hx, hy] at hne
                | some v => rw [hx, hy] at hstepf; exact hstepf
            | some u =>
                cases hy : S.act f y with
                | none => rw [hx, hy] at hstepf; exact hstepf
                | some v =>
                    rw [hx, hy] at hstepf
                    have : ¬ SeparatedAt ob n u v := (ih u v).1 hstepf
                    refine this ⟨t, rest, ?_, ?_⟩
                    · simpa using Nat.succ_le_succ_iff.1 hd
                    · simpa [hx, hy] using hne
      · intro h
        refine ⟨?_, ?_⟩
        · by_contra hx
          exact h ⟨s, Chain.nil s, Nat.zero_le _, by simpa using hx⟩
        · intro f
          cases hx : S.act f x with
          | none =>
              cases hy : S.act f y with
              | none => exact trivial
              | some v =>
                  exact absurd
                    (⟨S.tgt f, Chain.cons f (Chain.nil _), by simp, by simp [hx, hy]⟩ :
                      SeparatedAt ob (n + 1) x y) h
          | some u =>
              cases hy : S.act f y with
              | none =>
                  exact absurd
                    (⟨S.tgt f, Chain.cons f (Chain.nil _), by simp, by simp [hx, hy]⟩ :
                      SeparatedAt ob (n + 1) x y) h
              | some v =>
                  show R ob n u v
                  refine (ih u v).2 ?_
                  rintro ⟨t, C, hd, hne⟩
                  exact h ⟨t, Chain.cons f C, by simpa using Nat.succ_le_succ hd,
                    by simpa [hx, hy] using hne⟩

theorem witness_of_not_R {n : ℕ} {s : S.Srt} {x y : S.Carrier s}
    (h : ¬ R ob n x y) :
    ∃ (t : S.Srt) (C : S.Chain s t), C.depth ≤ n ∧
      (C.eval x).map (ob t) ≠ (C.eval y).map (ob t) := by
  by_contra hcon
  exact h ((R_iff_not_separatedAt ob n x y).2 (fun hs => hcon hs))

theorem R_antitone {m n : ℕ} (h : m ≤ n) {s : S.Srt} {x y : S.Carrier s}
    (hn : R ob n x y) : R ob m x y :=
  (R_iff_not_separatedAt ob m x y).2
    (fun hs => (R_iff_not_separatedAt ob n x y).1 hn (separatedAt_mono ob h hs))

theorem minimal_depth_witness {n : ℕ} {s : S.Srt} {x y : S.Carrier s}
    (hkeep : R ob n x y) (hsplit : ¬ R ob (n + 1) x y) :
    (∃ (t : S.Srt) (C : S.Chain s t), C.depth ≤ n + 1 ∧
        (C.eval x).map (ob t) ≠ (C.eval y).map (ob t)) ∧
      ∀ (t : S.Srt) (C : S.Chain s t), C.depth ≤ n →
        (C.eval x).map (ob t) = (C.eval y).map (ob t) := by
  refine ⟨witness_of_not_R ob hsplit, ?_⟩
  intro t C hd
  by_contra hne
  exact (R_iff_not_separatedAt ob n x y).1 hkeep ⟨t, C, hd, hne⟩

theorem R_stabilises_of_fixed {n : ℕ}
    (hfix : ∀ (s : S.Srt) (x y : S.Carrier s), R ob n x y → R ob (n + 1) x y) :
    ∀ (m : ℕ), n ≤ m → ∀ (s : S.Srt) (x y : S.Carrier s), R ob n x y → R ob m x y := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => intro _ _ _ h; exact h
  | succ m _hnm ih =>
      intro s x y h
      have h1 := hfix s x y h
      refine ⟨h1.1, ?_⟩
      intro f
      have hf := h1.2 f
      cases hx : S.act f x with
      | none =>
          cases hy : S.act f y with
          | none => exact trivial
          | some v => rw [hx, hy] at hf; exact hf
      | some u =>
          cases hy : S.act f y with
          | none => rw [hx, hy] at hf; exact hf
          | some v =>
              rw [hx, hy] at hf
              have hn : R ob n u v := hf
              exact ih _ u v hn

theorem R_eq_of_fixed {n : ℕ}
    (hfix : ∀ (s : S.Srt) (x y : S.Carrier s), R ob n x y → R ob (n + 1) x y)
    {m : ℕ} (hm : n ≤ m) {s : S.Srt} (x y : S.Carrier s) :
    R ob n x y ↔ R ob m x y :=
  ⟨R_stabilises_of_fixed ob hfix m hm s x y, R_antitone ob hm⟩

end Unary

namespace RefinementWitness

abbrev S : Unary where
  Srt := Unit
  Carrier := fun _ => Fin 3
  Step := fun _ => Unit
  tgt := fun _ => ()
  act := fun _ x => if x = 0 then some 1 else some 0

abbrev ob : (s : S.Srt) → S.Carrier s → Bool := fun _ x => decide (x = 1)

theorem merged_at_zero :
    Unary.R (S := S) ob 0 (s := ()) (0 : Fin 3) (2 : Fin 3) := by
  show ob () (0 : Fin 3) = ob () (2 : Fin 3)
  decide

theorem split_at_one :
    ¬ Unary.R (S := S) ob 1 (s := ()) (0 : Fin 3) (2 : Fin 3) := by
  rintro ⟨-, hstep⟩
  have h : Unary.OptRel (fun u v => Unary.R (S := S) ob 0 (s := ()) u v)
      (S.act () (0 : Fin 3)) (S.act () (2 : Fin 3)) := hstep ()
  have h2 : ob () (1 : Fin 3) = ob () (0 : Fin 3) := h
  exact absurd h2 (by decide)

theorem minimal_depth_is_one :
    (∃ (t : S.Srt) (C : S.Chain () t), C.depth ≤ 1 ∧
        (C.eval (0 : Fin 3)).map (ob t) ≠ (C.eval (2 : Fin 3)).map (ob t)) ∧
      ∀ (t : S.Srt) (C : S.Chain () t), C.depth ≤ 0 →
        (C.eval (0 : Fin 3)).map (ob t) = (C.eval (2 : Fin 3)).map (ob t) :=
  Unary.minimal_depth_witness ob merged_at_zero split_at_one

end RefinementWitness

end PhonologicalGrounding.QueryDiscovery
