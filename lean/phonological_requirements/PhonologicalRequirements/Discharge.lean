                                                                                          
import PhonologicalRequirements.Terms
import PhonologicalRequirements.Contribution

namespace PhonologicalRequirements

variable {σ V : Type} [DecidableEq σ]

inductive AccOccurs : Term σ V → σ → (V → K) → Prop
  | here  {s p} : AccOccurs (.acc s p) s p
  | neg   {t s p} : AccOccurs t s p → AccOccurs (.neg t) s p
  | conjL {t u s p} : AccOccurs t s p → AccOccurs (.conj t u) s p
  | conjR {t u s p} : AccOccurs u s p → AccOccurs (.conj t u) s p
  | disjL {t u s p} : AccOccurs t s p → AccOccurs (.disj t u) s p
  | disjR {t u s p} : AccOccurs u s p → AccOccurs (.disj t u) s p

def NoUndefConst : Term σ V → Prop
  | .const v   => v ≠ K.uu
  | .exists_ _ => True
  | .acc _ _   => True
  | .neg t     => NoUndefConst t
  | .conj t u  => NoUndefConst t ∧ NoUndefConst u
  | .disj t u  => NoUndefConst t ∧ NoUndefConst u

theorem eval_defined_of_accesses
    (t : Term σ V) (a : Assign σ V) (hc : NoUndefConst t)
    (h : ∀ (s : σ) (p : V → K), AccOccurs t s p → ∃ v, a s = some v ∧ p v ≠ K.uu) :
    t.eval a ≠ K.uu := by
  induction t with
  | const v =>
      intro hv
      simp [Term.eval] at hv
      exact hc hv
  | exists_ s =>
      intro hv
      simp [Term.eval] at hv
      cases hx : a s <;> simp [hx] at hv
  | acc s p =>
      intro hv
      obtain ⟨v, hav, hpv⟩ := h s p AccOccurs.here
      simp [Term.eval, hav] at hv
      exact hpv hv
  | neg t ih =>
      intro hv
      simp [Term.eval] at hv
      have : t.eval a = K.uu := K.not_uu_iff.mp hv
      exact ih hc (fun s p hp => h s p (AccOccurs.neg hp)) this
  | conj t u iht ihu =>
      have ht := iht hc.1 (fun s p hp => h s p (AccOccurs.conjL hp))
      have hu := ihu hc.2 (fun s p hp => h s p (AccOccurs.conjR hp))
      intro hv
      cases hx : t.eval a <;> cases hy : u.eval a <;>
        first
          | (exact ht hx) | (exact hu hy)
          | (rw [Term.eval, hx, hy] at hv; exact absurd hv (by decide))
  | disj t u iht ihu =>
      have ht := iht hc.1 (fun s p hp => h s p (AccOccurs.disjL hp))
      have hu := ihu hc.2 (fun s p hp => h s p (AccOccurs.disjR hp))
      intro hv
      cases hx : t.eval a <;> cases hy : u.eval a <;>
        first
          | (exact ht hx) | (exact hu hy)
          | (rw [Term.eval, hx, hy] at hv; exact absurd hv (by decide))

def SubjectStrict (cons : Term σ V) (s : σ) : Prop :=
  ∀ a : Assign σ V, a s = none → cons.eval a ≠ K.ff

theorem pressure_zero_of_strict
    {cons act : Term σ V} {s : σ} (hs : SubjectStrict cons s)
    (a : Assign σ V) (hnone : a s = none) :
    (readersOf cons act a).pressure = 0 := by
  have h := hs a hnone
  unfold readersOf Readers.pressure
  cases hv : cons.eval a with
  | tt => simp [hv]
  | ff => exact absurd hv h
  | uu => simp [hv]

theorem exists_total (s : σ) (a : Assign σ V) :
    (Term.exists_ (σ := σ) (V := V) s).eval a = K.tt ∨
    (Term.exists_ (σ := σ) (V := V) s).eval a = K.ff := by
  simp [Term.eval]
  cases a s with
  | none => exact Or.inr rfl
  | some _ => exact Or.inl rfl

theorem exists_not_strict (s : σ) [Inhabited V] :
    ¬ SubjectStrict (σ := σ) (V := V) (.exists_ s) s := by
  intro h
  have := h (fun _ => none) rfl
  simp [Term.eval] at this

theorem eval_congr (t : Term σ V) (a a' : Assign σ V) (h : ∀ s, t.mentions s → a s = a' s) :
    t.eval a = t.eval a' := by
  induction t with
  | const v => rfl
  | exists_ s =>
      have := h s (by simp [Term.mentions])
      simp [Term.eval, this]
  | acc s p =>
      have := h s (by simp [Term.mentions])
      simp [Term.eval, this]
  | neg t ih =>
      simp [Term.eval, ih (fun s hs => h s hs)]
  | conj t u iht ihu =>
      simp [Term.eval, iht (fun s hs => h s (Or.inl hs)), ihu (fun s hs => h s (Or.inr hs))]
  | disj t u iht ihu =>
      simp [Term.eval, iht (fun s hs => h s (Or.inl hs)), ihu (fun s hs => h s (Or.inr hs))]

                      
theorem discharge_only_by_relata (cons act : Term σ V) (a a' : Assign σ V)
    (h : ∀ s, cons.mentions s → a s = a' s) :
    (readersOf cons act a).def_ = (readersOf cons act a').def_ ∧
    (readersOf cons act a).good = (readersOf cons act a').good := by
  simp [readersOf, eval_congr cons a a' h]

                          
theorem exists_form_violated (s : σ) (Φ : Term σ V) (a : Assign σ V) (hnone : a s = none) :
    (Term.conj (.exists_ s) Φ).eval a = K.ff := by
  simp [Term.eval, hnone, K.and]

                          
theorem exists_form_pressure (s : σ) (Φ act : Term σ V) (a : Assign σ V) (hnone : a s = none) :
    (readersOf (Term.conj (.exists_ s) Φ) act a).pressure = 1 := by
  simp [readersOf, Readers.pressure, exists_form_violated s Φ a hnone]

                          
theorem antilithuanian {cons act : Term σ V} {s : σ} (hs : SubjectStrict cons s) (a : Assign σ V)
    (hnone : a s = none) (num den w bit ctx : Nat) :
    contrib num den w bit (readersOf cons act a).pressure ctx = 0 := by
  rw [pressure_zero_of_strict hs a hnone]
  simp [contrib]

end PhonologicalRequirements
