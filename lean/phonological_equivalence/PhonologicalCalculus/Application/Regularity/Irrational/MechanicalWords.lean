                  
                   
import PhonologicalCalculus.Application.Regularity.Irrational.Density

namespace NativeIrrational
noncomputable def level (n : ℕ) : ℕ := ⌊(n:ℝ)*beta⌋₊
noncomputable def block (n : ℕ) : List Bool := true :: List.replicate (level (n+1)-level n) false
noncomputable def word : ℕ → List Bool
  | 0 => []
  | n+1 => word n ++ block n
noncomputable def delta (b : Bool) : ℝ := if b then beta else -1
noncomputable def balance (w : List Bool) : ℝ := (w.map delta).sum

@[simp] theorem balance_nil : balance [] = 0 := rfl
@[simp] theorem balance_cons (b : Bool) (w : List Bool) :
    balance (b::w) = delta b + balance w := by simp [balance]
@[simp] theorem balance_append (u v : List Bool) :
    balance (u++v) = balance u + balance v := by simp [balance]
@[simp] theorem balance_false (n : ℕ) : balance (List.replicate n false) = -(n:ℝ) := by
  simp [balance,delta,nsmul_eq_mul]

theorem level_mono (n : ℕ) : level n ≤ level (n+1) := by
  apply Nat.floor_mono
  have := beta_bounds.1
  push_cast
  nlinarith

theorem residue_level (n : ℕ) : residue n = (n:ℝ)*beta - level n := by
  rw [residue,Int.fract]
  congr 1
  exact (natCast_floor_eq_intCast_floor (mul_nonneg (Nat.cast_nonneg n) (le_of_lt (lt_trans (by norm_num) beta_bounds.1)) : (0:ℝ) ≤ (n:ℝ)*beta)).symm

theorem balance_word (n : ℕ) : balance (word n) = residue n := by
  induction n with
  | zero => simp [word,residue]
  | succ n ih =>
    rw [word,balance_append,ih]
    simp only [block,balance_cons,balance_false,delta,ite_true]
    rw [Nat.cast_sub (level_mono n),residue_level,residue_level]
    push_cast
    ring

theorem prefix_word_bounds (n j : ℕ) :
    0 ≤ balance ((word n).take j) ∧ balance ((word n).take j) < 1+beta := by
  induction n with
  | zero => simp [word]; linarith [beta_bounds.1]
  | succ n ih =>
    by_cases hj : j ≤ (word n).length
    · simpa only [word,List.take_append_of_le_length hj] using ih
    · have hj' : (word n).length ≤ j := by omega
      rw [word,List.take_append,List.take_of_length_le hj',balance_append,balance_word]
      cases he : j - (word n).length with
      | zero => simp; exact ⟨(residue_bounds n).1, by linarith [(residue_bounds n).2,beta_bounds.1]⟩
      | succ k =>
        simp only [block,List.take_succ_cons,List.take_replicate,balance_cons,balance_false,delta,ite_true]
        have hm : ((min k (level (n+1)-level n):ℕ):ℝ) ≤ (level (n+1):ℝ)-level n := by
          rw [← Nat.cast_sub (level_mono n)]
          exact_mod_cast Nat.min_le_right k (level (n+1)-level n)
        have hn := (residue_bounds (n+1)).1
        rw [residue_level] at hn
        have hr := (residue_bounds n).2
        rw [residue_level n]
        push_cast at hn
        constructor
        · linarith
        · have hmin : (0:ℝ) ≤ ((min k (level (n+1)-level n):ℕ):ℝ) := Nat.cast_nonneg _
          rw [residue_level] at hr
          linarith

noncomputable def suffix (k : ℕ) : List Bool := word k ++ [false]

theorem balance_suffix (k : ℕ) : balance (suffix k) = residue k - 1 := by
  simp [suffix,balance_word,delta]; ring

theorem prefix_concat_bounds (n k j : ℕ) :
    -1 ≤ balance ((word n ++ suffix k).take j) ∧
      balance ((word n ++ suffix k).take j) < 2+beta := by
  by_cases hj : j ≤ (word n).length
  · rw [List.take_append_of_le_length hj]
    have h := prefix_word_bounds n j
    constructor <;> linarith
  · have hj' : (word n).length ≤ j := by omega
    rw [List.take_append,List.take_of_length_le hj',balance_append,balance_word]
    let t := j - (word n).length
    change -1 ≤ residue n + balance ((suffix k).take t) ∧ _
    by_cases ht : t ≤ (word k).length
    · rw [suffix,List.take_append_of_le_length ht]
      have h := prefix_word_bounds k t
      have hn := residue_bounds n
      constructor <;> linarith
    · have hlen : (suffix k).length ≤ t := by simp only [suffix,List.length_append,List.length_singleton]; omega
      rw [List.take_of_length_le hlen,balance_suffix]
      have hn := residue_bounds n
      have hk := residue_bounds k
      constructor <;> linarith [beta_bounds.1]
end NativeIrrational
