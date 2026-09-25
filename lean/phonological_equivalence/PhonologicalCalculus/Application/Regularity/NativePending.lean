                     
                   
import PhonologicalCalculus.Application.Regularity.PendingCompiler
import PhonologicalCalculus.Application.Regularity.RegularProjection

namespace NativePending

variable {Z O D : Type}

abbrev Record (Z O : Type) := Z × Option O × Option O
abbrev State (Z O : Type) := Option (Record Z O) × Option (Record Z O)

def eraseRecord (out : Z → O) (r : PendingCompiler.Record Z) : Record Z O :=
  (r.1,r.2.1.map out,r.2.2.map out)

def erase (out : Z → O) (s : PendingCompiler.State Z) : State Z O :=
  (s.1.map (eraseRecord out),s.2.map (eraseRecord out))

def sym (out : Z → O) (r : Option (Record Z O)) : Option O := r.map (out ∘ Prod.fst)

def step (out : Z → O) (s : State Z O) (z : Z) : State Z O :=
  (s.2,some (z,sym out s.2,sym out s.1))

def lift (out : Z → O) (g : Z → Option O → Option O → Option O → Option O → ℕ)
    (z : Z) (a b c d : Option Z) : ℕ := g z (a.map out) (b.map out) (c.map out) (d.map out)

def cost (out : Z → O) (g : Z → Option O → Option O → Option O → Option O → ℕ)
    (s : State Z O) (z : Z) : ℕ :=
  match s.1 with
  | none => 0
  | some (c,l₁,l₂) => g c l₂ l₁ (sym out s.2) (some (out z))

def finish (out : Z → O) (g : Z → Option O → Option O → Option O → Option O → ℕ)
    (s : State Z O) : ℕ :=
  (match s.1 with
   | none => 0
   | some (c,l₁,l₂) => g c l₂ l₁ (sym out s.2) none) +
  (match s.2 with
   | none => 0
   | some (c,l₁,l₂) => g c l₂ l₁ none none)

theorem sym_erase (out : Z → O) (r : Option (PendingCompiler.Record Z)) :
    sym out (r.map (eraseRecord out)) = (PendingCompiler.sym r).map out := by
  simp [sym,eraseRecord,PendingCompiler.sym,Option.map_map,Function.comp_def]

theorem erase_step (out : Z → O) (s : PendingCompiler.State Z) (z : Z) :
    erase out (PendingCompiler.step s z) = step out (erase out s) z := by
  simp [erase,eraseRecord,PendingCompiler.step,step,sym_erase]

theorem cost_erase (out : Z → O) (g : Z → Option O → Option O → Option O → Option O → ℕ)
    (s : PendingCompiler.State Z) (z : Z) :
    cost out g (erase out s) z = PendingCompiler.cost (lift out g) s z := by
  rcases s with ⟨a,b⟩
  cases a <;> simp [cost,erase,eraseRecord,PendingCompiler.cost,lift,sym_erase]

theorem finish_erase (out : Z → O) (g : Z → Option O → Option O → Option O → Option O → ℕ)
    (s : PendingCompiler.State Z) :
    finish out g (erase out s) = PendingCompiler.finish (lift out g) s := by
  rcases s with ⟨a,b⟩
  cases a <;> cases b <;>
    simp [finish,erase,eraseRecord,PendingCompiler.finish,lift,sym,PendingCompiler.sym,Function.comp_def]

def compiledCost (out : Z → O) (g : Z → Option O → Option O → Option O → Option O → ℕ)
    (deletion : D → ℕ) : State Z O → List (Sum D Z) → ℕ
  | s, [] => finish out g s
  | s, Sum.inl d :: xs => deletion d + compiledCost out g deletion s xs
  | s, Sum.inr z :: xs => cost out g s z + compiledCost out g deletion (step out s z) xs

theorem compiled_erase (out : Z → O) (g : Z → Option O → Option O → Option O → Option O → ℕ)
    (deletion : D → ℕ) (s : PendingCompiler.State Z) (xs : List (Sum D Z)) :
    compiledCost out g deletion (erase out s) xs = PendingCompiler.compiledCost (lift out g) deletion s xs := by
  induction xs generalizing s with
  | nil => exact finish_erase out g s
  | cons a xs ih =>
    cases a with
    | inl d => simp [compiledCost,PendingCompiler.compiledCost,ih]
    | inr z => rw [compiledCost,← erase_step,ih,cost_erase,PendingCompiler.compiledCost]

theorem native_score (out : Z → O) (g : Z → Option O → Option O → Option O → Option O → ℕ)
    (deletion : D → ℕ) (xs : List (Sum D Z)) :
    compiledCost out g deletion (none,none) xs =
      LocalScore.deleteCost deletion xs + LocalScore.objective (lift out g) none none
        ((LocalScore.survivors xs).map some) := by
  have h := compiled_erase out g deletion (none,none) xs
  rw [PendingCompiler.compiled_native_score (lift out g) deletion (fun _ => ()) (fun _ => True)] at h
  exact h


variable {S : Type}

def winner
    (g : (ReferenceWindows.Window S × O) → Option O → Option O → Option O → Option O → ℕ)
    (del : ReferenceWindows.Window S → ℕ) (ok : S → Option O → Prop)
    (xs : List (RegularProjection.Token S O)) : Prop :=
  ReferenceWindows.valid (xs.map RegularProjection.input) ∧
    (∀ t ∈ xs, ok (RegularProjection.input t).c (RegularProjection.output t)) ∧
    ∀ ys, ReferenceWindows.valid (ys.map RegularProjection.input) →
      (∀ t ∈ ys, ok (RegularProjection.input t).c (RegularProjection.output t)) →
      ys.map (fun t => (RegularProjection.input t).c) = xs.map (fun t => (RegularProjection.input t).c) →
      compiledCost Prod.snd g del (none,none) xs ≤ compiledCost Prod.snd g del (none,none) ys

theorem regular_native_compiler [Fintype S] [Fintype O]
    (g : (ReferenceWindows.Window S × O) → Option O → Option O → Option O → Option O → ℕ)
    (del : ReferenceWindows.Window S → ℕ) (ok : S → Option O → Prop) :
    Language.IsRegular (List.map RegularProjection.raw '' {xs | winner g del ok xs}) := by
  have h := RegularProjection.regular_native_alignments (lift Prod.snd g) del ok
  convert h using 1
  congr 1
  ext xs
  simp only [winner,RegularProjection.nativeWinner,native_score,RegularProjection.nativeScore]

end NativePending
