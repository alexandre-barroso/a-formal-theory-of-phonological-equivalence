                                        
import PhonologicalGrounding.DeclarationLanguage.Kleene

namespace PhonologicalGrounding.DeclarationLanguage

abbrev Pos := Nat

abbrev St (Seg : Type) := Pos → Seg

inductive Cls where
  | absent
  | skip
  | hit
  deriving DecidableEq, Repr

def scanList (c : Pos → Cls) (stop : Bool) : List Pos → Option Pos
  | [] => none
  | x :: xs =>
      match c x with
      | .hit => some x
      | .absent => scanList c stop xs
      | .skip => if stop then none else scanList c stop xs

theorem scanList_mem {c : Pos → Cls} {stop : Bool} :
    ∀ {l : List Pos} {o : Pos}, scanList c stop l = some o → o ∈ l := by
  intro l
  induction l with
  | nil => intro o h; simp [scanList] at h
  | cons x xs ih =>
      intro o h
      simp only [scanList] at h
      cases hx : c x with
      | hit => rw [hx] at h; simp at h; simp [h]
      | absent => rw [hx] at h; exact List.mem_cons_of_mem _ (ih h)
      | skip =>
          rw [hx] at h
          cases stop with
          | true => simp at h
          | false => simp only [Bool.false_eq_true, if_false] at h
                     exact List.mem_cons_of_mem _ (ih h)

theorem scanList_congr {c c' : Pos → Cls} {stop : Bool} :
    ∀ {l : List Pos}, (∀ x ∈ l, c x = c' x) → scanList c stop l = scanList c' stop l := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons x xs ih =>
      intro h
      have hx : c x = c' x := h x (List.mem_cons_self ..)
      have hxs : ∀ y ∈ xs, c y = c' y := fun y hy => h y (List.mem_cons_of_mem _ hy)
      simp only [scanList, hx]
      cases c' x <;> simp [ih hxs]

def allAbsent (c : Pos → Cls) : List Pos → Bool
  | [] => true
  | x :: xs => match c x with
      | .absent => allAbsent c xs
      | _ => false

theorem allAbsent_congr {c c' : Pos → Cls} :
    ∀ {l : List Pos}, (∀ x ∈ l, c x = c' x) → allAbsent c l = allAbsent c' l := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons x xs ih =>
      intro h
      have hx : c x = c' x := h x (List.mem_cons_self ..)
      have hxs : ∀ y ∈ xs, c y = c' y := fun y hy => h y (List.mem_cons_of_mem _ hy)
      simp only [allAbsent, hx]
      cases c' x <;> simp [ih hxs]

inductive Resolver where
  | anchor
  | dynamic (domain : List Pos) (stop : Bool)
  | frozen (partner : Pos) (gap : List Pos) (witness : Bool)
  deriving Repr

def Resolver.footprint : Resolver → Pos → List Pos
  | .anchor, a => [a]
  | .dynamic D _, a => a :: D
  | .frozen p g _, a => a :: p :: g

def Resolver.resolve : Resolver → Pos → (Pos → Cls) → Option Pos
  | .anchor, a, _ => some a
  | .dynamic D stop, _, c => scanList c stop D
  | .frozen p g wit, a, c =>
      if c a = .absent then none
      else if c p = .absent then none
      else if wit && !allAbsent c g then none
      else some p

theorem Resolver.resolve_mem_footprint :
    ∀ (r : Resolver) (a : Pos) (c : Pos → Cls) {o : Pos},
      r.resolve a c = some o → o ∈ r.footprint a := by
  intro r a c o h
  cases r with
  | anchor => simp [Resolver.resolve] at h; simp [Resolver.footprint, h]
  | dynamic D stop =>
      simp only [Resolver.resolve] at h
      exact List.mem_cons_of_mem _ (scanList_mem h)
  | frozen p g wit =>
      simp only [Resolver.resolve] at h
      split at h
      · simp at h
      · split at h
        · simp at h
        · split at h
          · simp at h
          · simp only [Option.some.injEq] at h
            subst h
            simp [Resolver.footprint]

theorem Resolver.resolve_congr (r : Resolver) (a : Pos) {c c' : Pos → Cls}
    (h : ∀ x ∈ r.footprint a, c x = c' x) : r.resolve a c = r.resolve a c' := by
  cases r with
  | anchor => rfl
  | dynamic D stop =>
      simp only [Resolver.resolve]
      exact scanList_congr (fun x hx => h x (List.mem_cons_of_mem _ hx))
  | frozen p g wit =>
      have ha : c a = c' a := h a (by simp [Resolver.footprint])
      have hp : c p = c' p := h p (by simp [Resolver.footprint])
      have hg : ∀ x ∈ g, c x = c' x := fun x hx => h x (by
        simp [Resolver.footprint]; exact Or.inr (Or.inr hx))
      simp only [Resolver.resolve, ha, hp, allAbsent_congr hg]

inductive Term (σ Seg : Type) where
  | const (v : K)
  | resolves (s : σ)
  | unary (s : σ) (p : Seg → K)
  | binary (s t : σ) (p : Seg → Seg → K)
  | neg (a : Term σ Seg)
  | conj (a b : Term σ Seg)
  | disj (a b : Term σ Seg)

namespace Term

variable {σ Seg : Type}

def eval : Term σ Seg → (σ → Option Pos) → St Seg → K
  | .const v, _, _ => v
  | .resolves s, α, _ => some (α s).isSome
  | .unary s p, α, st => match α s with
      | none => none
      | some o => p (st o)
  | .binary s t p, α, st => match α s, α t with
      | some o, some o' => p (st o) (st o')
      | _, _ => none
  | .neg a, α, st => K.not (eval a α st)
  | .conj a b, α, st => K.and (eval a α st) (eval b α st)
  | .disj a b, α, st => K.or (eval a α st) (eval b α st)

theorem eval_congr (t : Term σ Seg) {α α' : σ → Option Pos} {st st' : St Seg}
    (hα : ∀ s, α s = α' s) (hst : ∀ s o, α s = some o → st o = st' o) :
    eval t α st = eval t α' st' := by
  induction t with
  | const v => rfl
  | resolves s => simp [eval, hα s]
  | unary s p =>
      simp only [eval, ← hα s]
      cases hs : α s with
      | none => rfl
      | some o => simp [hst s o hs]
  | binary s u p =>
      simp only [eval, ← hα s, ← hα u]
      cases hs : α s with
      | none => rfl
      | some o =>
          cases hu : α u with
          | none => rfl
          | some o' => simp [hst s o hs, hst u o' hu]
  | neg a ih => simp [eval, ih]
  | conj a b iha ihb => simp [eval, iha, ihb]
  | disj a b iha ihb => simp [eval, iha, ihb]

def strictIn [DecidableEq σ] (s : σ) : Term σ Seg → Bool
  | .const _ => false
  | .resolves _ => false
  | .unary t _ => decide (t = s)
  | .binary t u _ => decide (t = s) || decide (u = s)
  | .neg a => strictIn s a
  | .conj a b => strictIn s a && strictIn s b
  | .disj a b => strictIn s a && strictIn s b

theorem eval_none_of_strictIn [DecidableEq σ] {s : σ} (t : Term σ Seg)
    (hstrict : strictIn s t = true) {α : σ → Option Pos} {st : St Seg}
    (hnone : α s = none) : eval t α st = none := by
  induction t with
  | const v => simp [strictIn] at hstrict
  | resolves u => simp [strictIn] at hstrict
  | unary u p =>
      simp only [strictIn, decide_eq_true_eq] at hstrict
      subst hstrict
      simp [eval, hnone]
  | binary u w p =>
      simp only [strictIn, Bool.or_eq_true, decide_eq_true_eq] at hstrict
      rcases hstrict with h | h
      · subst h; simp [eval, hnone]
      · subst h; simp only [eval, hnone]
        cases α u <;> rfl
  | neg a ih =>
      simp only [strictIn] at hstrict
      simp [eval, ih hstrict]
  | conj a b iha ihb =>
      simp only [strictIn, Bool.and_eq_true] at hstrict
      simp [eval, iha hstrict.1, ihb hstrict.2]
  | disj a b iha ihb =>
      simp only [strictIn, Bool.and_eq_true] at hstrict
      simp [eval, iha hstrict.1, ihb hstrict.2]

theorem eval_disj_none_of_left_false {a b : Term σ Seg}
    {α : σ → Option Pos} {st : St Seg}
    (ha : eval a α st = some false) (hb : eval b α st = none) :
    eval (Term.disj a b) α st = none := by
  simp [eval, ha, hb]

end Term

end PhonologicalGrounding.DeclarationLanguage
