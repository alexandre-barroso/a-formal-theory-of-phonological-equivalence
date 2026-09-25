                     
                   
import PhonologicalCalculus.Application.Regularity.RegularProjection

namespace LatticeScore

variable {Z D S O : Type}

def objective (f : Z → Option Z → Option Z → Option Z → Option Z → ℝ)
    (a b : Option Z) : List (Option Z) → ℝ
  | [] => 0
  | c :: xs => (match c with
      | none => 0
      | some z => f z a b xs.head! xs.tail.head!) + objective f b c xs

def deleteCost (f : D → ℝ) : List (Sum D Z) → ℝ
  | [] => 0
  | Sum.inl d :: xs => f d + deleteCost f xs
  | Sum.inr _ :: xs => deleteCost f xs

theorem objective_scale (δ : ℝ)
    (f : Z → Option Z → Option Z → Option Z → Option Z → ℝ)
    (g : Z → Option Z → Option Z → Option Z → Option Z → ℕ)
    (h : ∀ z a b c d, f z a b c d = δ * g z a b c d)
    (xs : List (Option Z)) (a b : Option Z) :
    objective f a b xs = δ * LocalScore.objective g a b xs := by
  induction xs generalizing a b with
  | nil => simp [objective,LocalScore.objective]
  | cons c xs ih => cases c <;> simp [objective,LocalScore.objective,LocalScore.point,ih,h,Nat.cast_add,mul_add]

theorem delete_scale (δ : ℝ) (f : D → ℝ) (g : D → ℕ) (h : ∀ d, f d = δ * g d)
    (xs : List (Sum D Z)) : deleteCost f xs = δ * LocalScore.deleteCost g xs := by
  induction xs with
  | nil => simp [deleteCost,LocalScore.deleteCost]
  | cons a xs ih => cases a <;> simp [deleteCost,LocalScore.deleteCost,ih,h,Nat.cast_add,mul_add]

def nativeScore
    (f : (ReferenceWindows.Window S × O) → Option (ReferenceWindows.Window S × O) →
      Option (ReferenceWindows.Window S × O) → Option (ReferenceWindows.Window S × O) →
      Option (ReferenceWindows.Window S × O) → ℝ)
    (del : ReferenceWindows.Window S → ℝ) (xs : List (RegularProjection.Token S O)) : ℝ :=
  deleteCost del xs + objective f none none ((LocalScore.survivors xs).map some)

def nativeWinner
    (f : (ReferenceWindows.Window S × O) → Option (ReferenceWindows.Window S × O) →
      Option (ReferenceWindows.Window S × O) → Option (ReferenceWindows.Window S × O) →
      Option (ReferenceWindows.Window S × O) → ℝ)
    (del : ReferenceWindows.Window S → ℝ) (ok : S → Option O → Prop)
    (xs : List (RegularProjection.Token S O)) : Prop :=
  ReferenceWindows.valid (xs.map RegularProjection.input) ∧
    (∀ t ∈ xs, ok (RegularProjection.input t).c (RegularProjection.output t)) ∧
    ∀ ys, ReferenceWindows.valid (ys.map RegularProjection.input) →
      (∀ t ∈ ys, ok (RegularProjection.input t).c (RegularProjection.output t)) →
      ys.map (fun t => (RegularProjection.input t).c) = xs.map (fun t => (RegularProjection.input t).c) →
      nativeScore f del xs ≤ nativeScore f del ys

theorem commensurable_regularity [Fintype S] [Fintype O]
    (f : (ReferenceWindows.Window S × O) → Option (ReferenceWindows.Window S × O) →
      Option (ReferenceWindows.Window S × O) → Option (ReferenceWindows.Window S × O) →
      Option (ReferenceWindows.Window S × O) → ℝ)
    (del : ReferenceWindows.Window S → ℝ) (ok : S → Option O → Prop)
    (δ : ℝ) (hδ : 0 < δ)
    (hf : ∀ z a b c d, ∃ n : ℕ, f z a b c d = δ*n)
    (hd : ∀ d, ∃ n : ℕ, del d = δ*n) :
    Language.IsRegular (List.map RegularProjection.raw '' {xs | nativeWinner f del ok xs}) := by
  classical
  choose g hg using hf
  choose dd hdd using hd
  have hscore (xs : List (RegularProjection.Token S O)) :
      nativeScore f del xs = δ * RegularProjection.nativeScore g dd xs := by
    rw [nativeScore,delete_scale δ del dd hdd,objective_scale δ f g hg]
    simp [RegularProjection.nativeScore,Nat.cast_add,mul_add]
  have hw (xs : List (RegularProjection.Token S O)) :
      nativeWinner f del ok xs ↔ RegularProjection.nativeWinner g dd ok xs := by
    simp only [nativeWinner,RegularProjection.nativeWinner,hscore,LocalScore.positive_scaling_order δ hδ]
  have h := RegularProjection.regular_native_alignments g dd ok
  convert h using 1
  congr 1
  ext xs
  exact hw xs

end LatticeScore
