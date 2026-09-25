                                                                                
import PhonologicalRequirements.Discharge

namespace PhonologicalRequirements.Definedness

variable {S V : Type} [DecidableEq S]

def UndefStrict (cons : Term S V) (s : S) : Prop :=
  ∀ a : Assign S V, a s = none → cons.eval a = K.uu

theorem undef_strict_subject_strict {cons : Term S V} {s : S}
    (h : UndefStrict cons s) : SubjectStrict cons s := by
  intro a ha
  rw [h a ha]
  decide

theorem undef_strict_not_defined {cons : Term S V} {s : S}
    (h : UndefStrict cons s) (act : Term S V) (a : Assign S V) (ha : a s = none) :
    (readersOf cons act a).def_ = false := by
  simp [readersOf,h a ha]

theorem true_or_missing (s : S) (p : V → K) (a : Assign S V) (h : a s = none) :
    (Term.disj (.const K.tt) (.acc s p)).eval a = K.tt := by
  simp [Term.eval,h,K.or]

theorem false_and_missing (s : S) (p : V → K) (a : Assign S V) (h : a s = none) :
    (Term.conj (.const K.ff) (.acc s p)).eval a = K.ff := by
  simp [Term.eval,h,K.and]

theorem true_or_subject_strict (s : S) (p : V → K) :
    SubjectStrict (Term.disj (.const K.tt) (.acc s p)) s := by
  intro a h
  rw [true_or_missing s p a h]
  decide

theorem strict_can_be_defined (s : S) (p : V → K) (act : Term S V) :
    SubjectStrict (Term.disj (.const K.tt) (.acc s p)) s ∧
    (readersOf (Term.disj (.const K.tt) (.acc s p)) act (fun _ => none)).def_ = true ∧
    (readersOf (Term.disj (.const K.tt) (.acc s p)) act (fun _ => none)).pressure = 0 := by
  refine ⟨true_or_subject_strict s p,?_,?_⟩
  · simp [readersOf,true_or_missing]
  · exact pressure_zero_of_strict (true_or_subject_strict s p) _ rfl

theorem subject_strict_not_undef_strict (s : S) (p : V → K) :
    SubjectStrict (Term.disj (.const K.tt) (.acc s p)) s ∧
      ¬ UndefStrict (Term.disj (.const K.tt) (.acc s p)) s := by
  refine ⟨true_or_subject_strict s p,?_⟩
  intro h
  have hu := h (fun _ => none) rfl
  rw [true_or_missing s p _ rfl] at hu
  contradiction

theorem missing_strict_excludes_pressure_one {cons : Term S V} {s : S}
    (h : SubjectStrict cons s) (act : Term S V) (a : Assign S V) (ha : a s = none) :
    (readersOf cons act a).pressure ≠ 1 := by
  rw [pressure_zero_of_strict h a ha]
  decide

theorem exists_conjunction_not_strict (s : S) (body : Term S V) :
    ¬ SubjectStrict (Term.conj (.exists_ s) body) s := by
  intro h
  exact h (fun _ => none) rfl (exists_form_violated s body _ rfl)

end PhonologicalRequirements.Definedness
