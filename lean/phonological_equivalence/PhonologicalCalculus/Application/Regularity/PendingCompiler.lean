                     
                   
import PhonologicalCalculus.Application.Regularity.LocalScore

namespace PendingCompiler

variable {Z : Type}
abbrev Record (Z : Type) := Z × Option Z × Option Z
abbrev State (Z : Type) := Option (Record Z) × Option (Record Z)

def sym (r : Option (Record Z)) : Option Z := r.map Prod.fst

def project (q : ShiftRegister.Register Z) : State Z :=
  ((q 2).map (fun z => (z,q 1,q 0)),(q 3).map (fun z => (z,q 2,q 1)))

def step (s : State Z) (z : Z) : State Z :=
  (s.2,some (z,sym s.2,sym s.1))

def cost (f : Z → Option Z → Option Z → Option Z → Option Z → ℕ)
    (s : State Z) (z : Z) : ℕ :=
  match s.1 with
  | none => 0
  | some (c,l₁,l₂) => f c l₂ l₁ (sym s.2) (some z)

def finish (f : Z → Option Z → Option Z → Option Z → Option Z → ℕ)
    (s : State Z) : ℕ :=
  (match s.1 with
   | none => 0
   | some (c,l₁,l₂) => f c l₂ l₁ (sym s.2) none) +
  (match s.2 with
   | none => 0
   | some (c,l₁,l₂) => f c l₂ l₁ none none)

theorem project_start : project (Z := Z) (fun _ => none) = (none,none) := rfl

theorem sym_project (q : ShiftRegister.Register Z) :
    sym (project q).1 = q 2 ∧ sym (project q).2 = q 3 := by
  simp [sym,project,Option.map_map,Function.comp_def]

theorem project_step (q : ShiftRegister.Register Z) (z : Z) :
    project (ShiftRegister.shift q (some z)) = step (project q) z := by
  simp [project,step,sym,ShiftRegister.shift,Option.map_map,Function.comp_def]

theorem cost_project (f : Z → Option Z → Option Z → Option Z → Option Z → ℕ)
    (q : ShiftRegister.Register Z) (z : Z) :
    cost f (project q) z = LocalScore.charge f q (some z) := by
  simp [cost,project,sym,LocalScore.charge,LocalScore.point,Option.map_map,Function.comp_def]
  cases q 2 <;> cases q 3 <;> rfl

theorem finish_project (f : Z → Option Z → Option Z → Option Z → Option Z → ℕ)
    (q : ShiftRegister.Register Z) :
    finish f (project q) = LocalScore.charge f q none +
      LocalScore.charge f (ShiftRegister.shift q none) none := by
  simp [finish,project,sym,LocalScore.charge,LocalScore.point,ShiftRegister.shift,Option.map_map,Function.comp_def]
  cases q 2 <;> cases q 3 <;> rfl

def compiledCost {D : Type}
    (f : Z → Option Z → Option Z → Option Z → Option Z → ℕ) (deletion : D → ℕ) :
    State Z → List (Sum D Z) → ℕ
  | s, [] => finish f s
  | s, Sum.inl d :: xs => deletion d + compiledCost f deletion s xs
  | s, Sum.inr z :: xs => cost f s z + compiledCost f deletion (step s z) xs

theorem compiled_cost_bridge {D I : Type}
    (f : Z → Option Z → Option Z → Option Z → Option Z → ℕ) (deletion : D → ℕ)
    (inp : Sum D Z → I) (ok : Sum D Z → Prop) (q : ShiftRegister.Register Z) (xs : List (Sum D Z)) :
    compiledCost f deletion (project q) xs =
      (ShiftRegister.machine (LocalScore.charge f) deletion inp ok).total q xs := by
  induction xs generalizing q with
  | nil => simp [compiledCost,finish_project,BoundedMemory.Machine.total,BoundedMemory.Machine.cost,
      BoundedMemory.Machine.state,ShiftRegister.machine,ShiftRegister.ecost]
  | cons a xs ih =>
    cases a with
    | inl d =>
      simpa [compiledCost,BoundedMemory.Machine.total,BoundedMemory.Machine.cost,
        BoundedMemory.Machine.state,ShiftRegister.machine,Nat.add_assoc] using congrArg (deletion d + ·) (ih q)
    | inr z =>
      rw [compiledCost,cost_project,← project_step,ih]
      simp [BoundedMemory.Machine.total,BoundedMemory.Machine.cost,
        BoundedMemory.Machine.state,ShiftRegister.machine,Nat.add_assoc]

theorem compiled_native_score {D I : Type}
    (f : Z → Option Z → Option Z → Option Z → Option Z → ℕ) (deletion : D → ℕ)
    (inp : Sum D Z → I) (ok : Sum D Z → Prop) (xs : List (Sum D Z)) :
    compiledCost f deletion (none,none) xs =
      LocalScore.deleteCost deletion xs + LocalScore.objective f none none
        ((LocalScore.survivors xs).map some) := by
  rw [← project_start,compiled_cost_bridge f deletion inp ok,LocalScore.native_score_bridge]

end PendingCompiler
