                                             
import PhonologicalRequirements.Kleene

namespace PhonologicalRequirements.FormulaCertificate

inductive Formula where
  | constant : K → Formula
  | atom : Nat → Formula
  | neg : Formula → Formula
  | conj : Formula → Formula → Formula
  | disj : Formula → Formula → Formula
deriving DecidableEq, Repr

def Formula.eval (values : List K) : Formula → K
  | .constant k => k
  | .atom n => values[n]?.getD .uu
  | .neg t => K.not (t.eval values)
  | .conj t u => K.and (t.eval values) (u.eval values)
  | .disj t u => K.or (t.eval values) (u.eval values)

def assignments : List (List K) → List (List K)
  | [] => [[]]
  | allowed :: tail => allowed.flatMap (fun v => (assignments tail).map (v :: ·))

inductive Permitted : List (List K) → List K → Prop
  | nil : Permitted [] []
  | cons {a tail v values} : v ∈ a → Permitted tail values → Permitted (a :: tail) (v :: values)

theorem assignments_complete (allowed : List (List K)) (values : List K)
    (h : Permitted allowed values) :
    values ∈ assignments allowed := by
  induction h with
  | nil => simp [assignments]
  | @cons a tail v values hv htail ih =>
      simp only [assignments, List.mem_flatMap, List.mem_map]
      exact ⟨v, hv, values, ih, rfl⟩

theorem permitted_lookup {allowed : List (List K)} {values : List K}
    (h : Permitted allowed values) (n : Nat) :
    values[n]?.getD .uu ∈ allowed[n]?.getD [.uu] := by
  induction h generalizing n with
  | nil => cases n <;> simp
  | @cons a tail v values hv ht ih =>
      cases n with
      | zero => simpa using hv
      | succ n => simpa using ih n

def Formula.possible (allowed : List (List K)) : Formula → List K
  | .constant k => [k]
  | .atom n => allowed[n]?.getD [.uu]
  | .neg t => ((t.possible allowed).map K.not).eraseDups
  | .conj t u => ((t.possible allowed).flatMap (fun a =>
      (u.possible allowed).map (K.and a))).eraseDups
  | .disj t u => ((t.possible allowed).flatMap (fun a =>
      (u.possible allowed).map (K.or a))).eraseDups

theorem eval_mem_possible (term : Formula) (allowed : List (List K))
    (values : List K) (h : Permitted allowed values) :
    term.eval values ∈ term.possible allowed := by
  induction term with
  | constant k => simp [Formula.eval, Formula.possible]
  | atom n => exact permitted_lookup h n
  | neg t ih =>
      simp only [Formula.eval, Formula.possible, List.mem_eraseDups, List.mem_map]
      exact ⟨t.eval values, ih, rfl⟩
  | conj t u iht ihu =>
      simp only [Formula.eval, Formula.possible, List.mem_eraseDups, List.mem_flatMap, List.mem_map]
      exact ⟨t.eval values, iht, u.eval values, ihu, rfl⟩
  | disj t u iht ihu =>
      simp only [Formula.eval, Formula.possible, List.mem_eraseDups, List.mem_flatMap, List.mem_map]
      exact ⟨t.eval values, iht, u.eval values, ihu, rfl⟩

def abstractStrict (term : Formula) (allowed : List (List K)) : Bool :=
  !(term.possible allowed).contains .ff

def checkStrict (term : Formula) (allowed : List (List K)) : Bool :=
  (assignments allowed).all (fun values => decide (term.eval values ≠ .ff))

def pressure (k : K) : Nat := if k = .ff then 1 else 0

theorem abstract_certificate_sound (term : Formula) (allowed : List (List K))
    (hcheck : abstractStrict term allowed = true) (values : List K)
    (hallowed : Permitted allowed values) : pressure (term.eval values) = 0 := by
  have hmem := eval_mem_possible term allowed values hallowed
  have hnot : K.ff ∉ term.possible allowed := by
    simpa [abstractStrict] using hcheck
  have hn : term.eval values ≠ .ff := fun heq => hnot (heq ▸ hmem)
  simp [pressure, hn]

inductive Method where
  | abstract | exhaustive | counterexample
deriving DecidableEq, Repr

def permittedCheck : List (List K) → List K → Bool
  | [], [] => true
  | a :: tail, v :: values => a.contains v && permittedCheck tail values
  | _, _ => false

theorem permittedCheck_sound {allowed : List (List K)} {values : List K}
    (h : permittedCheck allowed values = true) : Permitted allowed values := by
  induction allowed generalizing values with
  | nil => cases values <;> simp_all [permittedCheck, Permitted.nil]
  | cons a tail ih =>
      cases values with
      | nil => simp [permittedCheck] at h
      | cons v values =>
          simp only [permittedCheck, Bool.and_eq_true] at h
          exact Permitted.cons (by simpa using h.1) (ih h.2)

structure TestCase where
  term : Formula
  allowed : List (List K)
  expected : Bool
  method : Method
  witness : List K
deriving Repr

def TestCase.checked (c : TestCase) : Bool :=
  match c.method with
  | .abstract => c.expected && abstractStrict c.term c.allowed
  | .exhaustive => checkStrict c.term c.allowed == c.expected
  | .counterexample => !c.expected && permittedCheck c.allowed c.witness &&
      decide (c.term.eval c.witness = .ff)

theorem strict_certificate_sound (term : Formula) (allowed : List (List K))
    (hcheck : checkStrict term allowed = true) (values : List K)
    (hallowed : Permitted allowed values) :
    pressure (term.eval values) = 0 := by
  have h := (List.all_eq_true.mp hcheck) values (assignments_complete allowed values hallowed)
  have hn : term.eval values ≠ .ff := of_decide_eq_true h
  simp [pressure, hn]

theorem checked_positive_sound (c : TestCase) (hc : c.checked = true)
    (he : c.expected = true) (values : List K) (hv : Permitted c.allowed values) :
    pressure (c.term.eval values) = 0 := by
  cases hm : c.method with
  | abstract =>
      have ha : abstractStrict c.term c.allowed = true := by
        simpa [TestCase.checked, hm, he] using hc
      exact abstract_certificate_sound c.term c.allowed ha values hv
  | exhaustive =>
      have ha : checkStrict c.term c.allowed = true := by
        simpa [TestCase.checked, hm, he] using hc
      exact strict_certificate_sound c.term c.allowed ha values hv
  | counterexample => simp [TestCase.checked, hm, he] at hc

theorem checked_counterexample_sound (c : TestCase) (hc : c.checked = true)
    (hm : c.method = .counterexample) :
    Permitted c.allowed c.witness ∧ pressure (c.term.eval c.witness) = 1 := by
  have h : c.expected = false ∧ permittedCheck c.allowed c.witness = true ∧
      c.term.eval c.witness = .ff := by
    simpa [TestCase.checked, hm, Bool.and_eq_true, and_assoc] using hc
  exact ⟨permittedCheck_sound h.2.1, by simp [pressure, h.2.2]⟩

theorem zero_pressure_iff (k : K) : pressure k = 0 ↔ k = .tt ∨ k = .uu := by
  cases k <;> decide

theorem unresolved_can_be_defined :
    (Formula.disj (.constant .tt) (.atom 0)).eval [.uu] = .tt := rfl

theorem strict_does_not_imply_undefined :
    checkStrict (.disj (.constant .tt) (.atom 0)) [[.uu]] = true ∧
    (Formula.disj (.constant .tt) (.atom 0)).eval [.uu] ≠ .uu := by decide

theorem resolves_missing_not_strict :
    checkStrict (.atom 0) [[.ff]] = false := rfl

end PhonologicalRequirements.FormulaCertificate
