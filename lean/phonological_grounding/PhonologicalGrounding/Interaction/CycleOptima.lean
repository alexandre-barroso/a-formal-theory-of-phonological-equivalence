                 
import PhonologicalGrounding.Interaction.Cycles
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace CycleScope
open PhonologicalGrounding.Cycles

def realCost {k : ℕ} (r w : ℝ) (pred : Fin k → Fin k) (S : Finset (Fin k)) : ℝ :=
  r * S.card + w * (uncovered pred S).card

theorem real_cost_lower {k : ℕ} (r w : ℝ) (hr : 0 ≤ r) (hw : r ≤ w)
    (pred : Fin k → Fin k) (hp : Function.Injective pred) (S : Finset (Fin k)) :
    r * ((k + 1) / 2 : ℕ) ≤ realCost r w pred S := by
  have h := length_bound pred hp S
  have hn : (k+1)/2 ≤ S.card + (uncovered pred S).card := by omega
  have hc : (((k+1)/2 : ℕ) : ℝ) ≤ (S.card : ℝ) + ((uncovered pred S).card : ℝ) := by exact_mod_cast hn
  have hu : 0 ≤ ((uncovered pred S).card : ℝ) := Nat.cast_nonneg _
  unfold realCost
  nlinarith [mul_nonneg (sub_nonneg.mpr hw) hu, mul_le_mul_of_nonneg_left hc hr]

theorem real_minimum_iff {k : ℕ} (r w : ℝ) (hr : 0 < r) (hw : r < w)
    (pred : Fin k → Fin k) (hp : Function.Injective pred) (S : Finset (Fin k)) :
    realCost r w pred S = r * ((k+1)/2 : ℕ) ↔
      (uncovered pred S).card = 0 ∧ S.card = (k+1)/2 := by
  have hb := length_bound pred hp S
  have hn : (k+1)/2 ≤ S.card + (uncovered pred S).card := by omega
  have hc : (((k+1)/2 : ℕ) : ℝ) ≤ (S.card : ℝ) + ((uncovered pred S).card : ℝ) := by exact_mod_cast hn
  constructor
  · intro he
    have hu : (uncovered pred S).card = 0 := by
      by_contra h
      have hpos : 0 < ((uncovered pred S).card : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero h
      have hh := mul_pos (sub_pos.mpr hw) hpos
      have hh2 := mul_le_mul_of_nonneg_left hc (le_of_lt hr)
      unfold realCost at he
      nlinarith
    refine ⟨hu, ?_⟩
    unfold realCost at he
    rw [hu] at he
    simp only [Nat.cast_zero,mul_zero,add_zero] at he
    have := (mul_left_cancel₀ (ne_of_gt hr) he)
    exact_mod_cast this
  · rintro ⟨hu,hs⟩
    simp [realCost,hu,hs]

def evens (k : ℕ) : Finset (Fin k) := Finset.univ.filter (fun j => j.val % 2 = 0)

theorem even_card (k : ℕ) : (evens k).card = (k+1)/2 := by
  induction k with
  | zero => simp [evens]
  | succ k ih =>
    have he : evens (k+1) =
      (evens k).map (Fin.castLEEmb (Nat.le_succ k)) ∪
      (if k % 2 = 0 then {⟨k, by omega⟩} else ∅) := by
      ext j
      simp only [evens,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_union,Finset.mem_map]
      constructor
      · intro h
        by_cases hj : j.val < k
        · left; exact ⟨⟨j.val,hj⟩,h,by apply Fin.ext; rfl⟩
        · right
          have je : j.val = k := by omega
          have hk : k % 2 = 0 := by omega
          simp only [hk,ite_true,Finset.mem_singleton]
          apply Fin.ext
          exact je
      · rintro (⟨i,hi,he⟩ | h)
        · subst j; exact hi
        · split_ifs at h with hk
          · have je := Finset.mem_singleton.mp h
            subst j; exact hk
          · simp at h
    have hd : Disjoint ((evens k).map (Fin.castLEEmb (Nat.le_succ k)))
       (if k % 2 = 0 then {⟨k, by omega⟩} else ∅) := by
      apply Finset.disjoint_left.mpr
      intro j hj hk
      obtain ⟨i,hi,he⟩ := Finset.mem_map.mp hj
      subst j
      split_ifs at hk with h
      · have hx := congrArg Fin.val (Finset.mem_singleton.mp hk)
        change i.val = k at hx
        omega
      · simp at hk
    rw [he,Finset.card_union_of_disjoint hd,Finset.card_map,ih]
    split_ifs <;> simp only [Finset.card_singleton,Finset.card_empty] <;> omega

theorem even_uncovered (n : ℕ) : uncovered (rot n) (evens (n+1)) = ∅ := by
  ext j
  simp only [uncovered,Finset.mem_filter,Finset.mem_univ,true_and,Finset.notMem_empty,iff_false,not_and]
  intro hj hp
  have hodd : j.val % 2 ≠ 0 := by simpa [evens] using hj
  have hpred : (rot n j).val % 2 ≠ 0 := by simpa [evens] using hp
  simp only [rot] at hpred
  split_ifs at hpred <;> omega

theorem cycle_attains (n : ℕ) (r w : ℝ) :
    realCost r w (rot n) (evens (n+1)) = r * ((n+2)/2 : ℕ) := by
  unfold realCost
  rw [even_card,even_uncovered]
  simp only [Finset.card_empty,Nat.cast_zero,mul_zero,add_zero]

theorem cycle_argmin_iff (n : ℕ) (r w : ℝ) (hr : 0<r) (hw : r<w)
    (S : Finset (Fin (n+1))) :
    (∀ T, realCost r w (rot n) S ≤ realCost r w (rot n) T) ↔
    (uncovered (rot n) S).card = 0 ∧ S.card = (n+2)/2 := by
  constructor
  · intro h
    apply (real_minimum_iff r w hr hw (rot n) (rot_injective n) S).mp
    apply le_antisymm
    · have hh := h (evens (n+1))
      rw [cycle_attains] at hh
      exact hh
    · exact real_cost_lower r w (le_of_lt hr) (le_of_lt hw) (rot n) (rot_injective n) S
  · intro h T
    rw [(real_minimum_iff r w hr hw (rot n) (rot_injective n) S).mpr h]
    exact real_cost_lower r w (le_of_lt hr) (le_of_lt hw) (rot n) (rot_injective n) T

def varyingCost {k : ℕ} (r w : Fin k → ℝ) (pred : Fin k → Fin k)
    (S : Fin k → Bool) : ℝ := ∑ j, if S j then r j else if S (pred j) then 0 else w j

theorem real_all_apply_beaten {k : ℕ} (r w : Fin k → ℝ) (pred : Fin k → Fin k)
    (j0 : Fin k) (hp : pred j0 ≠ j0) (hr : 0 < r j0) :
    varyingCost r w pred (fun j => if j = j0 then false else true) <
    varyingCost r w pred (fun _ => true) := by
  unfold varyingCost
  apply Finset.sum_lt_sum
  · intro j _
    by_cases hj : j = j0
    · subst j; simp [hp]; exact le_of_lt hr
    · simp [hj]
  · refine ⟨j0,Finset.mem_univ _,?_⟩
    simpa [hp] using hr

end CycleScope
