                                         
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

namespace PhonologicalGrounding.DeclarationLanguage

abbrev K := Option Bool

namespace K

def not : K → K
  | none => none
  | some b => some (!b)

def and : K → K → K
  | some false, _ => some false
  | _, some false => some false
  | none, _ => none
  | _, none => none
  | some true, some true => some true

def or : K → K → K
  | some true, _ => some true
  | _, some true => some true
  | none, _ => none
  | _, none => none
  | some false, some false => some false

def collapse : K → Bool
  | some b => b
  | none => false

@[simp] theorem not_none : not none = none := rfl
@[simp] theorem not_some (b : Bool) : not (some b) = some (!b) := rfl
@[simp] theorem and_false_left (x : K) : and (some false) x = some false := by
  cases x <;> rfl
@[simp] theorem and_false_right (x : K) : and x (some false) = some false := by
  cases x with
  | none => rfl
  | some b => cases b <;> rfl
@[simp] theorem or_true_left (x : K) : or (some true) x = some true := by
  cases x <;> rfl
@[simp] theorem or_true_right (x : K) : or x (some true) = some true := by
  cases x with
  | none => rfl
  | some b => cases b <;> rfl
@[simp] theorem and_none_none : and none none = none := rfl
@[simp] theorem or_none_none : or none none = none := rfl
@[simp] theorem or_false_none : or (some false) none = none := rfl
@[simp] theorem or_none_false : or none (some false) = none := rfl
@[simp] theorem and_true_none : and (some true) none = none := rfl
@[simp] theorem and_none_true : and none (some true) = none := rfl
@[simp] theorem collapse_none : collapse none = false := rfl
@[simp] theorem collapse_some (b : Bool) : collapse (some b) = b := rfl

end K

structure Readers where
  context : Bool
  defined : Bool
  good : Bool
  deriving DecidableEq, Repr

namespace Readers

def pressure (r : Readers) : ℚ := if r.defined ∧ ¬ r.good then 1 else 0

def marked (r : Readers) : ℚ := if r.context ∧ r.defined ∧ ¬ r.good then 1 else 0

theorem pressure_nonneg (r : Readers) : 0 ≤ r.pressure := by
  unfold pressure; split <;> norm_num

theorem marked_nonneg (r : Readers) : 0 ≤ r.marked := by
  unfold marked; split <;> norm_num

theorem marked_le_pressure (r : Readers) : r.marked ≤ r.pressure := by
  unfold marked pressure
  by_cases hc : r.context <;> by_cases hd : r.defined <;> by_cases hg : r.good <;>
    simp [hc, hd, hg]

@[simp] theorem pressure_of_not_defined {r : Readers} (h : r.defined = false) :
    r.pressure = 0 := by
  unfold pressure; simp [h]

@[simp] theorem marked_of_not_defined {r : Readers} (h : r.defined = false) :
    r.marked = 0 := by
  unfold marked; simp [h]

@[simp] theorem pressure_of_good {r : Readers} (h : r.good = true) :
    r.pressure = 0 := by
  unfold pressure; simp [h]

theorem defined_ne_of_pressure_pos {r r' : Readers}
    (h : r.pressure = 1) (h' : r'.defined = false) : r ≠ r' := by
  intro hEq
  rw [hEq, pressure_of_not_defined h'] at h
  norm_num at h

end Readers

def readersOf (consequence : K) (activation : K) : Readers :=
  { context := K.collapse activation
    defined := consequence.isSome
    good := consequence = some true }

@[simp] theorem readersOf_defined_of_none (a : K) :
    (readersOf none a).defined = false := rfl

theorem pressure_readersOf_none (a : K) : (readersOf none a).pressure = 0 :=
  Readers.pressure_of_not_defined (readersOf_defined_of_none a)

end PhonologicalGrounding.DeclarationLanguage
