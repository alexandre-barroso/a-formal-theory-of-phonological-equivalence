                                    
import PhonologicalGrounding.DeclarationLanguage.Scope

namespace PhonologicalGrounding.DeclarationLanguage

variable {σ Seg : Type}

theorem defined_false_of_unresolved [DecidableEq σ]
    {cls : Classifier Seg} (d : Decl σ Seg) (s : σ)
    (hstrict : d.consequence.strictIn s = true)
    (a : Pos) (st : St Seg)
    (hnone : (d.slots s).resolve a (cls st) = none) :
    (d.readers cls a st).defined = false := by
  have h : d.consequence.eval (d.assign cls a st) st = none :=
    Term.eval_none_of_strictIn _ hstrict (by simpa [Decl.assign] using hnone)
  simp [Decl.readers, readersOf, h]

theorem no_surviving_origins_reader [DecidableEq σ]
    {cls : Classifier Seg} (d : Decl σ Seg) (s : σ)
    (hstrict : d.consequence.strictIn s = true) (a : Pos) :
    ¬ ∃ st : St Seg, (d.slots s).resolve a (cls st) = none
        ∧ (d.readers cls a st).defined = true := by
  rintro ⟨st, hnone, hdef⟩
  rw [defined_false_of_unresolved d s hstrict a st hnone] at hdef
  exact Bool.false_ne_true hdef

theorem pressure_zero_of_unresolved [DecidableEq σ]
    {cls : Classifier Seg} (d : Decl σ Seg) (s : σ)
    (hstrict : d.consequence.strictIn s = true)
    (a : Pos) (st : St Seg)
    (hnone : (d.slots s).resolve a (cls st) = none) :
    (d.readers cls a st).pressure = 0 :=
  Readers.pressure_of_not_defined
    (defined_false_of_unresolved d s hstrict a st hnone)

theorem marked_zero_of_unresolved [DecidableEq σ]
    {cls : Classifier Seg} (d : Decl σ Seg) (s : σ)
    (hstrict : d.consequence.strictIn s = true)
    (a : Pos) (st : St Seg)
    (hnone : (d.slots s).resolve a (cls st) = none) :
    (d.readers cls a st).marked = 0 := by
  have hp := pressure_zero_of_unresolved (cls := cls) d s hstrict a st hnone
  have hle := Readers.marked_le_pressure (d.readers cls a st)
  have hnn := Readers.marked_nonneg (d.readers cls a st)
  linarith [hp, hle, hnn]

theorem contribution_zero_of_unresolved [DecidableEq σ]
    {cls : Classifier Seg} (L : Locus σ Seg) (s : σ)
    (hstrict : L.decl.consequence.strictIn s = true)
    (lam : ℚ) (U st : St Seg)
    (hnone : (L.decl.slots s).resolve L.anchor (cls st) = none) :
    L.contribution cls lam U st = 0 := by
  simp only [Locus.contribution,
    pressure_zero_of_unresolved (cls := cls) L.decl s hstrict L.anchor st hnone,
    marked_zero_of_unresolved (cls := cls) L.decl s hstrict L.anchor st hnone]
  ring

theorem no_discrimination_when_relation_destroyed [DecidableEq σ]
    {cls : Classifier Seg} (L : Locus σ Seg) (s : σ)
    (hstrict : L.decl.consequence.strictIn s = true)
    (lam : ℚ) (U st st' : St Seg)
    (h : (L.decl.slots s).resolve L.anchor (cls st) = none)
    (h' : (L.decl.slots s).resolve L.anchor (cls st') = none) :
    L.contribution cls lam U st = L.contribution cls lam U st' := by
  rw [contribution_zero_of_unresolved L s hstrict lam U st h,
    contribution_zero_of_unresolved L s hstrict lam U st' h']

theorem pressure_zero_of_guarded_unresolved [DecidableEq σ]
    {cls : Classifier Seg} (d : Decl σ Seg) (guard : Term σ Seg) (body : Term σ Seg)
    (s : σ) (hshape : d.consequence = Term.disj guard body)
    (hstrict : body.strictIn s = true)
    (a : Pos) (st : St Seg)
    (hguard : guard.eval (d.assign cls a st) st = some false)
    (hnone : (d.slots s).resolve a (cls st) = none) :
    (d.readers cls a st).pressure = 0 := by
  have hbody : body.eval (d.assign cls a st) st = none :=
    Term.eval_none_of_strictIn _ hstrict (by simpa [Decl.assign] using hnone)
  have : d.consequence.eval (d.assign cls a st) st = none := by
    rw [hshape]; exact Term.eval_disj_none_of_left_false hguard hbody
  simp only [Decl.readers, this]
  exact pressure_readersOf_none _

namespace Witness

inductive Seg2 where
  | plus
  | minus
  deriving DecidableEq, Repr

inductive Slot2 where
  | target
  | trigger
  deriving DecidableEq, Repr

instance : Fintype Slot2 where
  elems := {Slot2.target, Slot2.trigger}
  complete := by intro x; cases x <;> decide

def cls2 : Classifier Seg2 := fun st o =>
  match st o with
  | .plus => Cls.hit
  | .minus => Cls.absent

def targetBased : Decl Slot2 Seg2 where
  slots := fun s => match s with
    | .target => Resolver.anchor
    | .trigger => Resolver.dynamic [1] false
  subject := fun s => match s with
    | .target => true
    | .trigger => false
  activation := Term.conj (Term.resolves Slot2.trigger)
    (Term.unary Slot2.trigger fun v => some (decide (v = Seg2.plus)))
  consequence := Term.unary Slot2.target fun v => some (decide (v = Seg2.plus))

def relational : Decl Slot2 Seg2 where
  slots := fun s => match s with
    | .target => Resolver.anchor
    | .trigger => Resolver.dynamic [1] false
  subject := fun _ => true
  activation := Term.resolves Slot2.trigger
  consequence := Term.binary Slot2.target Slot2.trigger
    fun v w => some (decide (v = w))

def refState : St Seg2 := fun o => if o = 0 then Seg2.minus else Seg2.plus

def lostTrigger : St Seg2 := fun _ => Seg2.minus

theorem target_ref : targetBased.readers cls2 0 refState = ⟨true, true, false⟩ := by
  decide

theorem target_lost :
    targetBased.readers cls2 0 lostTrigger = ⟨false, true, false⟩ := by
  decide

theorem targetBased_contribution (w lam : ℚ) :
    (Locus.mk targetBased 0 w).contribution cls2 lam refState lostTrigger = w := by
  simp [Locus.contribution, target_ref, target_lost, Readers.marked,
    Readers.pressure]

theorem relational_ref : relational.readers cls2 0 refState = ⟨true, true, false⟩ := by
  decide

theorem relational_unresolved :
    (relational.slots Slot2.trigger).resolve 0 (cls2 lostTrigger) = none := by
  decide

theorem relational_strict :
    (relational.consequence).strictIn Slot2.trigger = true := by decide

theorem relational_contribution (w lam : ℚ) :
    (Locus.mk relational 0 w).contribution cls2 lam refState lostTrigger = 0 :=
  contribution_zero_of_unresolved (cls := cls2) (Locus.mk relational 0 w)
    Slot2.trigger relational_strict lam refState lostTrigger relational_unresolved

theorem persistence_asymmetry (w lam : ℚ) (hw : w ≠ 0) :
    (Locus.mk targetBased 0 w).contribution cls2 lam refState lostTrigger
      ≠ (Locus.mk relational 0 w).contribution cls2 lam refState lostTrigger := by
  rw [targetBased_contribution, relational_contribution]
  exact hw

theorem relational_realises_R :
    (relational.readers cls2 0 refState).defined = true
      ∧ (relational.readers cls2 0 lostTrigger).defined = false :=
  ⟨by decide,
   defined_false_of_unresolved (cls := cls2) relational Slot2.trigger
     relational_strict 0 lostTrigger relational_unresolved⟩

theorem relational_excludes_S :
    ¬ ∃ st : St Seg2, (relational.slots Slot2.trigger).resolve 0 (cls2 st) = none
        ∧ (relational.readers cls2 0 st).defined = true :=
  no_surviving_origins_reader (cls := cls2) relational Slot2.trigger
    relational_strict 0

end Witness

end PhonologicalGrounding.DeclarationLanguage
