        
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Range
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace PokoComparison

noncomputable def countScore (n : ℕ) (f h : ℝ) (retained : Finset (Fin n)) : ℝ :=
  f * retained.card + h * (n-retained.card : ℕ)

def singleDeletion (n : ℕ) (i : Fin n) : Finset (Fin n) := Finset.univ.erase i

theorem equal_card_tie {n : ℕ} (f h : ℝ) (a b : Finset (Fin n))
    (hc : a.card = b.card) : countScore n f h a = countScore n f h b := by
  simp only [countScore, hc]

theorem single_deletion_card {n : ℕ} (i : Fin n) :
    (singleDeletion n i).card = n-1 := by
  simp [singleDeletion]

theorem all_single_deletions_tie {n : ℕ} (f h : ℝ) (i j : Fin n) :
    countScore n f h (singleDeletion n i) = countScore n f h (singleDeletion n j) := by
  apply equal_card_tie
  simp [single_deletion_card]

noncomputable def alignment {n : ℕ} (retained : Finset (Fin n)) : ℝ :=
  ∑ i ∈ retained, ((n-1-i.val : ℕ) : ℝ)

theorem alignment_single_deletion {n : ℕ} (i : Fin n) :
    alignment (singleDeletion n i) + ((n-1-i.val : ℕ) : ℝ) =
      alignment (Finset.univ : Finset (Fin n)) := by
  exact Finset.sum_erase_add _ _ (Finset.mem_univ i)

theorem single_deletion_alignment_order {n : ℕ} (i j : Fin n) :
    alignment (singleDeletion n i) < alignment (singleDeletion n j) ↔ i.val < j.val := by
  have hi := alignment_single_deletion i
  have hj := alignment_single_deletion j
  have hi' : i.val ≤ n-1 := by omega
  have hj' : j.val ≤ n-1 := by omega
  rw [Nat.cast_sub hi'] at hi
  rw [Nat.cast_sub hj'] at hj
  have hh : alignment (singleDeletion n i) - alignment (singleDeletion n j) =
      (i.val : ℝ) - j.val := by linarith
  constructor
  · intro h; have : (i.val : ℝ) < j.val := by linarith
    exact_mod_cast this
  · intro h; have : (i.val : ℝ) < j.val := by exact_mod_cast h
    linarith

theorem positive_alignment_breaks_tie {n : ℕ} (f h w : ℝ) (hw : 0 < w)
    (i j : Fin n) (hij : i.val < j.val) :
    countScore n f h (singleDeletion n i) + w*alignment (singleDeletion n i) <
      countScore n f h (singleDeletion n j) + w*alignment (singleDeletion n j) := by
  rw [all_single_deletions_tie f h i j]
  exact add_lt_add_right (mul_lt_mul_of_pos_left
    ((single_deletion_alignment_order i j).mpr hij) hw) _

def sourceRows : List (ℕ × ℕ × ℕ × ℕ) :=
  [(1,0,0,0), (0,1,1,1), (2,0,0,0), (1,1,1,1)]

noncomputable def sourceScore (h d m a : ℝ) (row : ℕ × ℕ × ℕ × ℕ) : ℝ :=
  row.1*h + row.2.1*d + row.2.2.1*m + row.2.2.2*a

theorem positive_pair (h d m a : ℝ) :
    sourceScore h d m a (0,1,1,1) < sourceScore h d m a (1,0,0,0) ↔ d+m+a<h := by
  simp [sourceScore]

theorem negative_pair (h d m a : ℝ) :
    sourceScore h d m a (2,0,0,0) < sourceScore h d m a (1,1,1,1) ↔ h<d+m+a := by
  simp [sourceScore]; constructor <;> intro h' <;> linarith

theorem shared_strict_impossible (h d m a : ℝ) :
    ¬ (sourceScore h d m a (0,1,1,1) < sourceScore h d m a (1,0,0,0) ∧
       sourceScore h d m a (2,0,0,0) < sourceScore h d m a (1,1,1,1)) := by
  rw [positive_pair, negative_pair]
  exact fun hc => (lt_asymm hc.1 hc.2)

theorem weak_boundary (h d m a : ℝ) :
    (d+m+a ≤ h ∧ 2*h ≤ h+d+m+a) ↔ h=d+m+a := by
  constructor
  · rintro ⟨h1,h2⟩; linarith
  · intro hc; constructor <;> linarith

theorem half_sum_not_necessary :
    sourceScore 3 2 1 1 (2,0,0,0) < sourceScore 3 2 1 1 (1,1,1,1) ∧
      ¬ (3 : ℝ) < (2+1+1)/2 := by norm_num [sourceScore]

end PokoComparison
