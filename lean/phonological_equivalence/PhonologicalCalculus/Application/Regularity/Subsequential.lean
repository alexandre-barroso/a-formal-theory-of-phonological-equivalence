                   
import PhonologicalCalculus.Application.Regularity.ReferenceWindows

namespace Subsequential

structure Machine (I Q : Type) where
  start : Q
  step : Q → I → Q
  output : Q → I → ℕ
  final : Q → Option ℕ

namespace Machine
variable {I Q : Type} (T : Machine I Q)

def valueFrom : Q → List I → Option ℕ
  | q, [] => T.final q
  | q, i :: us => (valueFrom (T.step q i) us).map (T.output q i + ·)

def value (us : List I) : Option ℕ := T.valueFrom T.start us

def execution (q : Q) (us : List I) : ℕ × Q :=
  us.foldl (fun s i => (s.1+T.output s.2 i,T.step s.2 i)) (0,q)

theorem execution_add (q : Q) (o : ℕ) (us : List I) :
    us.foldl (fun s i => (s.1+T.output s.2 i,T.step s.2 i)) (o,q) =
      (o+(T.execution q us).1,(T.execution q us).2) := by
  induction us generalizing o q with
  | nil => simp [execution]
  | cons i us ih =>
    simp only [List.foldl_cons]
    rw [ih]
    have he : T.execution q (i :: us) =
        (T.output q i+(T.execution (T.step q i) us).1,(T.execution (T.step q i) us).2) := by
      simpa only [execution,List.foldl_cons,zero_add] using ih (T.step q i) (T.output q i)
    rw [he]
    simp [Nat.add_assoc]

theorem valueFrom_execution (q : Q) (us : List I) :
    T.valueFrom q us = (T.final (T.execution q us).2).map ((T.execution q us).1+·) := by
  induction us generalizing q with
  | nil => simp [valueFrom,execution]
  | cons i us ih =>
    rw [valueFrom,ih]
    have he : T.execution q (i :: us) =
        (T.output q i + (T.execution (T.step q i) us).1,(T.execution (T.step q i) us).2) := by
      simpa [execution] using T.execution_add (T.step q i) (T.output q i) us
    rw [he]
    simp [Option.map_map,Function.comp_def,Nat.add_assoc]

end Machine
end Subsequential

namespace DelayedWindows
open ReferenceWindows

inductive Buffer (S : Type)
  | empty (l₂ l₁ : Option S)
  | one (l₂ l₁ : Option S) (c : S)
  | two (l₂ l₁ : Option S) (c d : S)
  deriving Fintype

variable {S Q : Type}

def remaining : Buffer S → List S → List (Window S)
  | .empty a b, xs => annotate a b xs
  | .one a b c, xs => annotate a b (c :: xs)
  | .two a b c d, xs => annotate a b (c :: d :: xs)

def next : Buffer S → S → Buffer S
  | .empty a b, x => .one a b x
  | .one a b c, x => .two a b c x
  | .two a b c d, x => .two b (some c) d x

def emitted : Buffer S → S → List (Window S)
  | .empty _ _, _ => []
  | .one _ _ _, _ => []
  | .two a b c d, x => [⟨a,b,c,some d,some x⟩]

theorem split_remaining (s : Buffer S) (x : S) (xs : List S) :
    remaining s (x :: xs) = emitted s x ++ remaining (next s x) xs := by
  cases s <;> rfl

def windows : Buffer S → List S → List (Window S)
  | s, [] => remaining s []
  | s, x :: xs => emitted s x ++ windows (next s x) xs

theorem windows_remaining (s : Buffer S) (xs : List S) :
    windows s xs = remaining s xs := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih => rw [windows,ih,← split_remaining]

theorem canonical_windows (xs : List S) :
    windows (.empty none none) xs = annotate none none xs := windows_remaining _ xs

def compose (T : Subsequential.Machine (Window S) Q) :
    Subsequential.Machine S (Buffer S × Q) where
  start := (.empty none none,T.start)
  step := fun s x => (next s.1 x,(T.execution s.2 (emitted s.1 x)).2)
  output := fun s x => (T.execution s.2 (emitted s.1 x)).1
  final := fun s => T.valueFrom s.2 (remaining s.1 [])

theorem valueFrom_append (T : Subsequential.Machine (Window S) Q)
    (q : Q) (xs ys : List (Window S)) :
    T.valueFrom q (xs ++ ys) =
      (T.valueFrom (T.execution q xs).2 ys).map ((T.execution q xs).1+·) := by
  induction xs generalizing q with
  | nil => simp [Subsequential.Machine.valueFrom,Subsequential.Machine.execution]
  | cons x xs ih =>
    rw [List.cons_append,Subsequential.Machine.valueFrom,ih]
    have he : T.execution q (x :: xs) =
        (T.output q x+(T.execution (T.step q x) xs).1,(T.execution (T.step q x) xs).2) := by
      simpa [Subsequential.Machine.execution] using T.execution_add (T.step q x) (T.output q x) xs
    rw [he]
    simp [Option.map_map,Function.comp_def,Nat.add_assoc]

theorem composed_valueFrom (T : Subsequential.Machine (Window S) Q)
    (s : Buffer S) (q : Q) (xs : List S) :
    (compose T).valueFrom (s,q) xs = T.valueFrom q (remaining s xs) := by
  induction xs generalizing s q with
  | nil => rfl
  | cons x xs ih =>
    rw [Subsequential.Machine.valueFrom]
    change ((compose T).valueFrom (next s x,(T.execution q (emitted s x)).2) xs).map
      ((T.execution q (emitted s x)).1+·) = _
    rw [ih,← valueFrom_append,← split_remaining]

theorem composed_value (T : Subsequential.Machine (Window S) Q) (xs : List S) :
    (compose T).value xs = T.value (annotate none none xs) := by
  exact composed_valueFrom T (.empty none none) T.start xs

end DelayedWindows
