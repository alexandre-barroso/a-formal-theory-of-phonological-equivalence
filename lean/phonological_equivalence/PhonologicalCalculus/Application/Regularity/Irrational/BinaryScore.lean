                  
                   
import PhonologicalCalculus.Application.Regularity.Irrational.MechanicalWords

namespace NativeIrrational
noncomputable def unary (x y : Bool) : ℝ := if y then (if x then 0 else 1) else (if x then beta else 0)
noncomputable def switch (p : Option Bool) (y : Bool) : ℝ :=
  match p with
  | none => 0
  | some z => if z=y then 0 else 8
noncomputable def run (p : Option Bool × ℝ) (xy : Bool × Bool) : Option Bool × ℝ :=
  (some xy.2, p.2 + unary xy.1 xy.2 + switch p.1 xy.2)
noncomputable def finalRun (w : List (Bool × Bool)) : Option Bool × ℝ := w.foldl run (none,0)
noncomputable def score (w : List (Bool × Bool)) : ℝ := (finalRun w).2
noncomputable def lastOutput (w : List (Bool × Bool)) : Option Bool := (finalRun w).1
def input (w : List (Bool × Bool)) : List Bool := w.map Prod.fst
def output (w : List (Bool × Bool)) : List Bool := w.map Prod.snd
noncomputable def unaryTotals (u : List Bool) : ℝ × ℝ :=
  ((u.map (fun x => unary x false)).sum,(u.map (fun x => unary x true)).sum)
noncomputable def step (d : ℝ × ℝ) (x : Bool) : ℝ × ℝ :=
  (min d.1 (d.2+8) + unary x false, min d.2 (d.1+8)+unary x true)
noncomputable def dp (u : List Bool) : ℝ × ℝ := u.foldl step (0,0)
noncomputable def coord (d : ℝ × ℝ) (b : Bool) : ℝ := if b then d.2 else d.1

def indicator (p : Bool) : ℝ := if p then 1 else 0
noncomputable def retainedCell (a c p : Bool) : ℝ := indicator a * indicator p + (1-indicator a)*indicator c*indicator p

def active (target : Bool) (prev : Option Bool) (x : Bool) : Bool := (x == target) && (prev == some (!target))
def pressure (target : Bool) (prev : Option Bool) (y : Bool) : Bool := (prev == some (!target)) && !(y == !target)
noncomputable def nativeLocal (refprev curprev : Option Bool) (x y : Bool) : ℝ :=
  unary x y + 8 * (retainedCell (active true refprev x) (active true curprev y) (pressure true curprev y) +
    retainedCell (active false refprev x) (active false curprev y) (pressure false curprev y))

theorem native_local_exact (rp cp : Option Bool) (x y : Bool) :
    nativeLocal rp cp x y = unary x y + switch cp y := by
  cases rp with
  | none => cases cp with
    | none => cases x <;> cases y <;> norm_num [nativeLocal,retainedCell,indicator,active,pressure,switch]
    | some z => cases z <;> cases x <;> cases y <;> norm_num [nativeLocal,retainedCell,indicator,active,pressure,switch]
  | some z => cases z <;> cases cp with
    | none => cases x <;> cases y <;> norm_num [nativeLocal,retainedCell,indicator,active,pressure,switch]
    | some t => cases t <;> cases x <;> cases y <;> norm_num [nativeLocal,retainedCell,indicator,active,pressure,switch]

@[simp] theorem score_nil : score [] = 0 := rfl
@[simp] theorem last_nil : lastOutput [] = none := rfl
@[simp] theorem score_snoc (w : List (Bool × Bool)) (x y : Bool) :
    score (w++[(x,y)]) = score w + unary x y + switch (lastOutput w) y := by
  simp [score,finalRun,List.foldl_append,run,lastOutput]
@[simp] theorem last_snoc (w : List (Bool × Bool)) (x y : Bool) :
    lastOutput (w++[(x,y)]) = some y := by simp [lastOutput,finalRun,List.foldl_append,run]
@[simp] theorem input_snoc (w : List (Bool × Bool)) (x y : Bool) :
    input (w++[(x,y)]) = input w ++ [x] := by simp [input]
@[simp] theorem dp_snoc (u : List Bool) (x : Bool) : dp (u++[x]) = step (dp u) x := by
  simp [dp,List.foldl_append]
@[simp] theorem totals_append (u v : List Bool) :
    unaryTotals (u++v) = ((unaryTotals u).1+(unaryTotals v).1,(unaryTotals u).2+(unaryTotals v).2) := by
  simp [unaryTotals]

theorem totals_balance (u : List Bool) : (unaryTotals u).1-(unaryTotals u).2 = balance u := by
  induction u with
  | nil => simp [unaryTotals,balance]
  | cons x u ih => cases x <;> simp [unaryTotals,balance,delta,unary] at * <;> linarith

theorem step_coord (d : ℝ × ℝ) (x y : Bool) :
    coord (step d x) y = min (coord d y) (coord d (!y)+8) + unary x y := by
  cases y <;> rfl

theorem last_none_iff (w : List (Bool × Bool)) : lastOutput w = none ↔ w=[] := by
  induction w using List.reverseRecOn with
  | nil => simp
  | append_singleton w xy ih => obtain ⟨x,y⟩ := xy; simp

theorem dp_lower (w : List (Bool × Bool)) :
    ∀ b, lastOutput w = some b → coord (dp (input w)) b ≤ score w := by
  induction w using List.reverseRecOn with
  | nil => simp
  | append_singleton w xy ih =>
    obtain ⟨x,y⟩ := xy
    intro b hb
    simp only [last_snoc,Option.some.injEq] at hb
    subst b
    rw [input_snoc,dp_snoc,step_coord,score_snoc]
    cases he : lastOutput w with
    | none =>
      have hw := (last_none_iff w).mp he
      subst w
      simp [input,dp,coord,switch]
    | some z =>
      have hz := ih z he
      by_cases hzy : z=y
      · subst z
        simp only [switch,ite_true,add_zero]
        linarith [min_le_left (coord (dp (input w)) y) (coord (dp (input w)) (!y)+8)]
      · have hz' : z = !y := by cases z <;> cases y <;> simp_all
        rw [hz'] at hz
        simp only [switch,if_neg hzy]
        linarith [min_le_right (coord (dp (input w)) y) (coord (dp (input w)) (!y)+8)]

theorem dp_min_lower (w : List (Bool × Bool)) :
    min (dp (input w)).1 (dp (input w)).2 ≤ score w := by
  cases he : lastOutput w with
  | none => have hw := (last_none_iff w).mp he; subst w; simp [input,dp]
  | some b =>
    have h := dp_lower w b he
    cases b
    · exact (min_le_left _ _).trans h
    · exact (min_le_right _ _).trans h
end NativeIrrational
