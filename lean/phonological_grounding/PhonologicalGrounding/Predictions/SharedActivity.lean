                      
import Mathlib.Data.Rat.Defs
import Mathlib.Data.List.Basic
import Mathlib.Tactic
import PhonologicalGrounding.Predictions.Threshold

namespace PhonologicalGrounding.Predictions.SharedActivity

open PhonologicalGrounding.Predictions.Threshold

abbrev Tier := List Bool

def runLengths : Tier → List Nat
  | [] => []
  | b :: bs =>
    match runLengths bs with
    | [] => [1]
    | n :: ns => if bs.head? = some b then (n + 1) :: ns else 1 :: n :: ns

@[simp] theorem runLengths_nil : runLengths [] = [] := rfl

@[simp] theorem runLengths_singleton (b : Bool) : runLengths [b] = [1] := rfl

theorem runLengths_cons_cons (a b : Bool) (rest : Tier) :
    runLengths (a :: b :: rest) =
      (match runLengths (b :: rest) with
       | [] => [1]
       | n :: ns => if (b :: rest).head? = some a then (n + 1) :: ns else 1 :: n :: ns) := rfl

theorem runLengths_replicate (b : Bool) :
    ∀ n : Nat, 0 < n → runLengths (List.replicate n b) = [n] := by
  intro n
  induction n with
  | zero => intro h; exact absurd h (lt_irrefl 0)
  | succ k ih =>
    intro _
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; simp [List.replicate]
    · have hk' : List.replicate k b = b :: List.replicate (k - 1) b := by
        cases k with
        | zero => exact absurd hk (lt_irrefl 0)
        | succ j => simp [List.replicate]
      have hrec : runLengths (List.replicate k b) = [k] := ih hk
      rw [List.replicate_succ]
      rw [show (b :: List.replicate k b) = (b :: b :: List.replicate (k - 1) b) by rw [← hk']]
      rw [runLengths_cons_cons]
      rw [show runLengths (b :: List.replicate (k - 1) b) = [k] by rw [← hk']; exact hrec]
      simp

theorem runLengths_transparent (v1 v3 : Nat) (h : 0 < v1 + v3 + 1) :
    runLengths (List.replicate (v1 + v3 + 1) false) = [v1 + v3 + 1] :=
  runLengths_replicate false _ h

theorem runLengths_opaque (v3 : Nat) :
    ∀ a : Nat,
      runLengths (List.replicate a false ++ true :: List.replicate (v3 + 1) false)
        = (if a = 0 then [1, v3 + 1] else [a, 1, v3 + 1]) := by
  have htail : runLengths (true :: List.replicate (v3 + 1) false)
      = [1, v3 + 1] := by
    rw [show (true :: List.replicate (v3 + 1) false)
          = (true :: false :: List.replicate v3 false) by simp [List.replicate_succ]]
    rw [runLengths_cons_cons]
    rw [show runLengths (false :: List.replicate v3 false) = [v3 + 1] by
      rw [show (false :: List.replicate v3 false) = List.replicate (v3 + 1) false by
        simp [List.replicate_succ]]
      exact runLengths_replicate false _ (Nat.succ_pos v3)]
    simp
  intro a
  induction a with
  | zero => simpa using htail
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      rw [show (List.replicate 1 false ++ true :: List.replicate (v3 + 1) false)
            = (false :: true :: List.replicate (v3 + 1) false) by simp [List.replicate]]
      rw [runLengths_cons_cons, htail]
      simp
    · have hstep : runLengths (List.replicate k false ++ true :: List.replicate (v3 + 1) false)
          = [k, 1, v3 + 1] := by
        have hne : k ≠ 0 := by omega
        rw [ih]; simp [hne]
      have hsplit : List.replicate (k + 1) false ++ true :: List.replicate (v3 + 1) false
          = false :: (List.replicate k false ++ true :: List.replicate (v3 + 1) false) := by
        simp [List.replicate_succ]
      have hk' : List.replicate k false ++ true :: List.replicate (v3 + 1) false
          = false :: (List.replicate (k - 1) false ++ true :: List.replicate (v3 + 1) false) := by
        cases k with
        | zero => exact absurd hk (lt_irrefl 0)
        | succ j => simp [List.replicate_succ]
      rw [hsplit, show (false :: (List.replicate k false ++ true :: List.replicate (v3 + 1) false))
            = (false :: false :: (List.replicate (k - 1) false
                ++ true :: List.replicate (v3 + 1) false)) by rw [← hk']]
      rw [runLengths_cons_cons]
      rw [show runLengths (false :: (List.replicate (k - 1) false
              ++ true :: List.replicate (v3 + 1) false)) = [k, 1, v3 + 1] by
        rw [← hk']; exact hstep]
      simp

theorem opaque_trigger_block (v1 v3 : Nat) (_h1 : 1 ≤ v1) :
    (runLengths (List.replicate (v1 - 1) false
      ++ true :: List.replicate (v3 + 1) false)).getLast? = some (v3 + 1) := by
  rw [runLengths_opaque v3 (v1 - 1)]
  by_cases h : v1 - 1 = 0 <;> simp [h]

theorem transparent_trigger_block (v1 v3 : Nat) (_h1 : 1 ≤ v1) :
    (runLengths (List.replicate (v1 + v3 + 1) false)).getLast? = some (v1 + v3 + 1) := by
  rw [runLengths_transparent v1 v3 (by omega)]; simp

theorem selection (g m q : ℚ) (v1 v3 : Nat) (h1 : 1 ≤ v1) :
    opaquePenalty g m q (v1 : ℚ) (v3 : ℚ) < transparentPenalty g q (v1 : ℚ) (v3 : ℚ)
      ↔ m * (((v3 : ℚ) + 1) * ((v1 : ℚ) + v3 + 1)) < g * (v1 : ℚ) := by
  have hv1 : (1 : ℚ) ≤ (v1 : ℚ) := by exact_mod_cast h1
  have hv3 : (0 : ℚ) ≤ (v3 : ℚ) := Nat.cast_nonneg v3
  exact opaque_lt_transparent_iff g m q _ _ hv1 hv3

end PhonologicalGrounding.Predictions.SharedActivity
