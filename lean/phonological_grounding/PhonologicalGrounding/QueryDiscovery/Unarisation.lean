                       
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Insert
import Mathlib.Logic.Function.Basic
import PhonologicalGrounding.QueryDiscovery.Refinement

universe v w

set_option linter.checkUnivs false
set_option linter.unusedSectionVars false

namespace PhonologicalGrounding.QueryDiscovery

namespace Unary

variable {S : Unary}

def Chain.snoc : {s t : S.Srt} → S.Chain s t → (f : S.Step t) → S.Chain s (S.tgt f)
  | _, _, .nil _, f => .cons f (.nil _)
  | _, _, .cons g rest, f => .cons g (rest.snoc f)

theorem Chain.eval_snoc :
    ∀ {s t : S.Srt} (C : S.Chain s t) (f : S.Step t) (x : S.Carrier s),
      (C.snoc f).eval x = (C.eval x).bind (S.act f)
  | _, _, .nil _, f, x => by simp [Chain.snoc]
  | _, _, .cons g rest, f, x => by
      simp [Chain.snoc, Chain.eval_snoc rest f, Option.bind_assoc]

variable {Obs : S.Srt → Type*} (ob : (s : S.Srt) → S.Carrier s → Obs s)

theorem R_of_invariant (E : (s : S.Srt) → S.Carrier s → S.Carrier s → Prop)
    (hob : ∀ s x y, E s x y → ob s x = ob s y)
    (hstep : ∀ (s : S.Srt) (f : S.Step s) (x y : S.Carrier s), E s x y →
      OptRel (E (S.tgt f)) (S.act f x) (S.act f y)) :
    ∀ (n : ℕ) (s : S.Srt) (x y : S.Carrier s), E s x y → R ob n x y := by
  intro n
  induction n with
  | zero => intro s x y h; exact hob s x y h
  | succ k ih =>
      intro s x y h
      refine ⟨hob s x y h, ?_⟩
      intro f
      have := hstep s f x y h
      cases hx : S.act f x with
      | none =>
          cases hy : S.act f y with
          | none => exact trivial
          | some v => rw [hx, hy] at this; exact this
      | some u =>
          cases hy : S.act f y with
          | none => rw [hx, hy] at this; exact this
          | some v =>
              rw [hx, hy] at this
              exact ih _ u v this

theorem not_separated_of_invariant (E : (s : S.Srt) → S.Carrier s → S.Carrier s → Prop)
    (hob : ∀ s x y, E s x y → ob s x = ob s y)
    (hstep : ∀ (s : S.Srt) (f : S.Step s) (x y : S.Carrier s), E s x y →
      OptRel (E (S.tgt f)) (S.act f x) (S.act f y))
    {s : S.Srt} {x y : S.Carrier s} (hxy : E s x y) (n : ℕ) :
    ¬ SeparatedAt ob n x y :=
  (R_iff_not_separatedAt ob n x y).1 (R_of_invariant ob E hob hstep n s x y hxy)

theorem OptRel.trans {A : Type*} {r : A → A → Prop}
    (htr : ∀ a b c : A, r a b → r b c → r a c) :
    ∀ p q t : Option A, OptRel r p q → OptRel r q t → OptRel r p t := by
  rintro (_ | a) (_ | b) (_ | c) h1 h2
  · exact trivial
  · exact h2.elim
  · exact h1.elim
  · exact h1.elim
  · exact h1.elim
  · exact h1.elim
  · exact h2.elim
  · exact htr a b c h1 h2

end Unary

structure MultiSig where
  Carrier : Type v
  Op : Type w
  arity : Op → ℕ
  act : (o : Op) → (Fin (arity o) → Carrier) → Option Carrier

namespace MultiSig

variable (M : MultiSig.{v, w})

inductive Ctx : Type (max v w)
  | hole : Ctx
  | extend (o : M.Op) (i : Fin (M.arity o)) (prior : Ctx)
      (fixed : Fin (M.arity o) → M.Carrier) : Ctx

structure ParameterPolicy where
  allowed : (o : M.Op) → (Fin (M.arity o) → M.Carrier) → Prop

def completePolicy : M.ParameterPolicy := ⟨fun _ _ => True⟩

variable {M}

def Ctx.eval : M.Ctx → M.Carrier → Option M.Carrier
  | .hole, x => some x
  | .extend o i prior fixed, x =>
      (prior.eval x).bind fun u => M.act o (Function.update fixed i u)

@[simp] theorem Ctx.eval_hole (x : M.Carrier) : (Ctx.hole (M := M)).eval x = some x := rfl

@[simp] theorem Ctx.eval_extend (o : M.Op) (i : Fin (M.arity o)) (prior : M.Ctx)
    (fixed : Fin (M.arity o) → M.Carrier) (x : M.Carrier) :
    (Ctx.extend o i prior fixed).eval x =
      (prior.eval x).bind fun u => M.act o (Function.update fixed i u) := rfl

def Ctx.Licensed (P : M.ParameterPolicy) : M.Ctx → Prop
  | .hole => True
  | .extend o _ prior fixed => P.allowed o fixed ∧ prior.Licensed P

def Ctx.precompose (o : M.Op) (i : Fin (M.arity o))
    (fixed : Fin (M.arity o) → M.Carrier) : M.Ctx → M.Ctx
  | .hole => .extend o i .hole fixed
  | .extend o' i' prior fixed' => .extend o' i' (prior.precompose o i fixed) fixed'

theorem Ctx.eval_precompose (o : M.Op) (i : Fin (M.arity o))
    (fixed : Fin (M.arity o) → M.Carrier) :
    ∀ (C : M.Ctx) (x : M.Carrier),
      (C.precompose o i fixed).eval x =
        (M.act o (Function.update fixed i x)).bind C.eval := by
  intro C
  induction C with
  | hole => intro x; cases h : M.act o (Function.update fixed i x) <;> simp [Ctx.precompose, h]
  | extend o' i' prior fixed' ih =>
      intro x
      simp only [Ctx.precompose, Ctx.eval_extend, ih x, Option.bind_assoc]

theorem Ctx.licensed_precompose {P : M.ParameterPolicy} (o : M.Op) (i : Fin (M.arity o))
    (fixed : Fin (M.arity o) → M.Carrier) (hfixed : P.allowed o fixed) :
    ∀ (C : M.Ctx), C.Licensed P → (C.precompose o i fixed).Licensed P := by
  intro C
  induction C with
  | hole => intro _; exact ⟨hfixed, trivial⟩
  | extend o' i' prior fixed' ih =>
      rintro ⟨h1, h2⟩
      exact ⟨h1, ih h2⟩

def ParameterPolicy.Adequate (P : M.ParameterPolicy) : Prop :=
  ∀ (o : M.Op) (i : Fin (M.arity o)) (a : Fin (M.arity o) → M.Carrier),
    ∃ a', P.allowed o a' ∧
      ∀ x : M.Carrier,
        M.act o (Function.update a i x) = M.act o (Function.update a' i x)

theorem completePolicy_adequate : (completePolicy M).Adequate :=
  fun _ _ a => ⟨a, trivial, fun _ => rfl⟩

theorem exists_licensed_eval_eq {P : M.ParameterPolicy} (hP : P.Adequate) :
    ∀ C : M.Ctx, ∃ D : M.Ctx, D.Licensed P ∧ ∀ x, D.eval x = C.eval x := by
  intro C
  induction C with
  | hole => exact ⟨.hole, trivial, fun _ => rfl⟩
  | extend o i prior fixed ih =>
      obtain ⟨D, hD, hDeval⟩ := ih
      obtain ⟨a', ha', hsection⟩ := hP o i fixed
      refine ⟨.extend o i D a', ⟨ha', hD⟩, ?_⟩
      intro x
      simp only [Ctx.eval_extend, hDeval x]
      cases h : prior.eval x with
      | none => simp
      | some u => simp [(hsection u).symm]

@[reducible] def unarise (P : M.ParameterPolicy) : Unary where
  Srt := Unit
  Carrier := fun _ => M.Carrier
  Step := fun _ => Σ o : M.Op, Fin (M.arity o) × {a : Fin (M.arity o) → M.Carrier // P.allowed o a}
  tgt := fun _ => ()
  act := fun f x => M.act f.1 (Function.update f.2.2.1 f.2.1 x)

theorem licensed_ctx_is_unary_chain {P : M.ParameterPolicy} :
    ∀ C : M.Ctx, C.Licensed P →
      ∃ D : (unarise P).Chain () (), ∀ x, D.eval x = C.eval x := by
  intro C
  induction C with
  | hole =>
      intro _
      exact ⟨Unary.Chain.nil (S := unarise P) (), fun _ => rfl⟩
  | extend o i prior fixed ih =>
      rintro ⟨hfixed, hprior⟩
      obtain ⟨D, hD⟩ := ih hprior
      refine ⟨D.snoc ⟨o, i, ⟨fixed, hfixed⟩⟩, ?_⟩
      intro x
      calc (D.snoc ⟨o, i, ⟨fixed, hfixed⟩⟩).eval x
          = (D.eval x).bind ((unarise P).act ⟨o, i, ⟨fixed, hfixed⟩⟩) :=
            Unary.Chain.eval_snoc D _ x
        _ = (prior.eval x).bind (fun u => M.act o (Function.update fixed i u)) := by
            rw [hD x]
        _ = (Ctx.extend o i prior fixed).eval x := rfl

theorem unary_chain_is_licensed_ctx {P : M.ParameterPolicy} :
    ∀ {s t : (unarise P).Srt} (D : (unarise P).Chain s t),
      ∃ C : M.Ctx, C.Licensed P ∧ ∀ x, C.eval x = D.eval x := by
  intro s t D
  induction D with
  | nil _ => exact ⟨.hole, trivial, fun _ => rfl⟩
  | cons f rest ih =>
      obtain ⟨C, hC, hCeval⟩ := ih
      refine ⟨C.precompose f.1 f.2.1 f.2.2.1,
        Ctx.licensed_precompose f.1 f.2.1 f.2.2.1 f.2.2.2 C hC, ?_⟩
      intro x
      rw [Ctx.eval_precompose, Unary.Chain.eval_cons]
      have hact : (unarise P).act f x
          = M.act f.1 (Function.update f.2.2.1 f.2.1 x) := rfl
      rw [hact]
      cases h : M.act f.1 (Function.update f.2.2.1 f.2.1 x) with
      | none => simp
      | some u => simp [hCeval u]

theorem ctx_iff_chain_of_adequate {P : M.ParameterPolicy} (hP : P.Adequate)
    (x y : M.Carrier) {Ω : Type*} (ob : M.Carrier → Ω) :
    (∀ C : M.Ctx, (C.eval x).map ob = (C.eval y).map ob) ↔
      (∀ D : (unarise P).Chain () (), (D.eval x).map ob = (D.eval y).map ob) := by
  constructor
  · intro h D
    obtain ⟨C, _, hC⟩ := unary_chain_is_licensed_ctx D
    rw [← hC x, ← hC y]
    exact h C
  · intro h C
    obtain ⟨D, hD, hDeval⟩ := exists_licensed_eval_eq hP C
    obtain ⟨E, hE⟩ := licensed_ctx_is_unary_chain D hD
    rw [← hDeval x, ← hDeval y, ← hE x, ← hE y]
    exact h E

theorem act_congr_of_pointwise (rel : M.Carrier → M.Carrier → Prop)
    (hrefl : ∀ a, rel a a)
    (htrans : ∀ {a b c : M.Carrier}, rel a b → rel b c → rel a c)
    (hsingle : ∀ (o : M.Op) (i : Fin (M.arity o)) (a : Fin (M.arity o) → M.Carrier)
      (u v : M.Carrier), rel u v →
        Unary.OptRel rel (M.act o (Function.update a i u)) (M.act o (Function.update a i v)))
    (o : M.Op) (a b : Fin (M.arity o) → M.Carrier) (h : ∀ i, rel (a i) (b i)) :
    Unary.OptRel rel (M.act o a) (M.act o b) := by
  classical
  have key : ∀ s : Finset (Fin (M.arity o)),
      Unary.OptRel rel (M.act o a)
        (M.act o (fun i => if i ∈ s then b i else a i)) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        have : (fun i => if i ∈ (∅ : Finset (Fin (M.arity o))) then b i else a i) = a := by
          funext i; simp
        rw [this]
        cases hact : M.act o a with
        | none => simp [Unary.OptRel]
        | some u => simpa [Unary.OptRel] using hrefl u
    | insert j s hj ih =>
        have hmix : (fun i => if i ∈ insert j s then b i else a i) =
            Function.update (fun i => if i ∈ s then b i else a i) j (b j) := by
          funext i
          by_cases hij : i = j
          · subst hij; simp
          · simp [Finset.mem_insert, hij]
        have hmix' : Function.update (fun i => if i ∈ s then b i else a i) j (a j)
            = (fun i => if i ∈ s then b i else a i) := by
          funext i
          by_cases hij : i = j
          · subst hij; simp [hj]
          · simp [Function.update_of_ne hij]
        have step := hsingle o j (fun i => if i ∈ s then b i else a i) (a j) (b j) (h j)
        rw [hmix'] at step
        rw [hmix]
        exact Unary.OptRel.trans (r := rel) (fun _ _ _ h1 h2 => htrans h1 h2) _ _ _ ih step
  have huniv := key Finset.univ
  have : (fun i => if i ∈ (Finset.univ : Finset (Fin (M.arity o))) then b i else a i) = b := by
    funext i; simp
  rwa [this] at huniv

end MultiSig

namespace Counterexample

open MultiSig

abbrev counterSig : MultiSig where
  Carrier := Fin 3
  Op := Unit
  arity := fun _ => 2
  act := fun _ a => if a 0 = 1 ∧ a 1 = 1 then some 2 else some 0

abbrev ob : Fin 3 → Bool := fun z => decide (z = 2)

abbrev poorPolicy : counterSig.ParameterPolicy := ⟨fun _ a => a = fun _ => 0⟩

abbrev sep : counterSig.Ctx :=
  .extend () 0 .hole (fun i => if i = 1 then 1 else 0)

theorem sep_separates :
    (sep.eval (0 : Fin 3)).map ob ≠ (sep.eval (1 : Fin 3)).map ob := by
  decide

theorem states_agree_on_reader : ob (0 : Fin 3) = ob (1 : Fin 3) := by decide

theorem poor_steps_constant (f : (unarise poorPolicy).Step ()) (x : Fin 3) :
    (unarise poorPolicy).act f x = some (0 : Fin 3) := by
  obtain ⟨⟨⟩, i, a, ha⟩ := f
  subst ha
  revert x
  revert i
  decide

theorem restricted_policy_strictly_coarser :
    ((sep.eval (0 : Fin 3)).map ob ≠ (sep.eval (1 : Fin 3)).map ob) ∧
      (∀ n : ℕ, ¬ Unary.SeparatedAt (S := unarise poorPolicy)
        (fun _ => ob) n (s := ()) (0 : Fin 3) (1 : Fin 3)) := by
  refine ⟨sep_separates, ?_⟩
  intro n
  refine Unary.not_separated_of_invariant (S := unarise poorPolicy) (fun _ => ob)
    (fun _ x y => ob x = ob y) (fun _ _ _ h => h) ?_ (s := ())
    (x := (0 : Fin 3)) (y := (1 : Fin 3)) states_agree_on_reader n
  intro s f x y _
  rw [poor_steps_constant f x, poor_steps_constant f y]
  exact rfl

theorem poorPolicy_not_adequate : ¬ poorPolicy.Adequate := by
  intro h
  obtain ⟨a', ha', hsec⟩ := h () 0 (fun i => if i = 1 then 1 else 0)
  subst ha'
  have := hsec 1
  revert this
  decide

end Counterexample

end PhonologicalGrounding.QueryDiscovery
