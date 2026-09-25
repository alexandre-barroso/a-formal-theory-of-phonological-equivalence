                                   
namespace PhonologicalRequirements
namespace Splice

variable {α : Type}

abbrev Window (α : Type) := Option α × Option α × Option α × Option α × Option α

def window (v : List α) (i : Nat) : Window α :=
  (if 2 ≤ i then v[i - 2]? else none, if 1 ≤ i then v[i - 1]? else none, v[i]?, v[i + 1]?, v[i + 2]?)

def sumRange (g : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sumRange g n + g n

def score (f : Window α → Nat) (v : List α) : Nat := sumRange (fun i => f (window v i)) v.length

def settled (f : Window α → Nat) (v : List α) (k : Nat) : Nat := sumRange (fun i => f (window v i)) k

def suffix (f : Window α → Nat) (v : List α) (k : Nat) : Nat := sumRange (fun j => f (window v (k + j))) (v.length - k)

theorem sumRange_add (g : Nat → Nat) (a : Nat) : ∀ b, sumRange g (a + b) = sumRange g a + sumRange (fun j => g (a + j)) b
  | 0 => by simp [sumRange]
  | b + 1 => by
    rw [← Nat.add_assoc, sumRange, sumRange_add g a b, sumRange]
    omega

theorem sumRange_le (g g' : Nat → Nat) (n : Nat) (h : ∀ i, i < n → g i ≤ g' i) : sumRange g n ≤ sumRange g' n := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    simp only [sumRange]
    exact Nat.add_le_add (ih (fun i hi => h i (Nat.lt_succ_of_lt hi))) (h n (Nat.lt_succ_self n))

theorem sumRange_congr (g g' : Nat → Nat) (n : Nat) (h : ∀ i, i < n → g i = g' i) : sumRange g n = sumRange g' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sumRange]
    rw [ih (fun i hi => h i (Nat.lt_succ_of_lt hi)), h n (Nat.lt_succ_self n)]

theorem sumRange_mono_len (g : Nat → Nat) {a b : Nat} (hab : a ≤ b) : sumRange g a ≤ sumRange g b := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hab
  rw [sumRange_add]
  exact Nat.le_add_right _ _

theorem sumRange_le_const (g : Nat → Nat) (c : Nat) (h : ∀ i, g i ≤ c) : ∀ n, sumRange g n ≤ n * c
  | 0 => by simp [sumRange]
  | n + 1 => by
    simp only [sumRange, Nat.succ_mul]
    exact Nat.add_le_add (sumRange_le_const g c h n) (h n)

theorem getElem?_splice_left (v1 v2 : List α) (k j : Nat) (hk : k ≤ v1.length) (hj : j < k) :
    (v1.take k ++ v2.drop k)[j]? = v1[j]? := by
  rw [List.getElem?_append_left (by rw [List.length_take]; omega), List.getElem?_take_of_lt hj]

theorem getElem?_splice_right (v1 v2 : List α) (k j : Nat) (hk : k ≤ v1.length) (hj : k ≤ j) :
    (v1.take k ++ v2.drop k)[j]? = v2[j]? := by
  rw [List.getElem?_append_right (by rw [List.length_take]; omega), List.getElem?_drop, List.length_take]
  congr 1
  omega

theorem window_splice_left (v1 v2 : List α) (k i : Nat) (hk : k ≤ v1.length) (hi : i + 2 < k) :
    window (v1.take k ++ v2.drop k) i = window v1 i := by
  unfold window
  rw [getElem?_splice_left v1 v2 k i hk (by omega), getElem?_splice_left v1 v2 k (i + 1) hk (by omega),
    getElem?_splice_left v1 v2 k (i + 2) hk (by omega)]
  by_cases h2 : 2 ≤ i
  · rw [if_pos h2, if_pos h2, getElem?_splice_left v1 v2 k (i - 2) hk (by omega)]
    by_cases h1 : 1 ≤ i
    · rw [if_pos h1, if_pos h1, getElem?_splice_left v1 v2 k (i - 1) hk (by omega)]
    · rw [if_neg h1, if_neg h1]
  · rw [if_neg h2, if_neg h2]
    by_cases h1 : 1 ≤ i
    · rw [if_pos h1, if_pos h1, getElem?_splice_left v1 v2 k (i - 1) hk (by omega)]
    · rw [if_neg h1, if_neg h1]

theorem window_splice_right (v1 v2 : List α) (k i : Nat) (hk : k ≤ v1.length) (hi : k + 2 ≤ i) :
    window (v1.take k ++ v2.drop k) i = window v2 i := by
  unfold window
  have h2 : 2 ≤ i := by omega
  have h1 : 1 ≤ i := by omega
  rw [if_pos h2, if_pos h2, if_pos h1, if_pos h1,
    getElem?_splice_right v1 v2 k (i - 2) hk (by omega), getElem?_splice_right v1 v2 k (i - 1) hk (by omega),
    getElem?_splice_right v1 v2 k i hk (by omega), getElem?_splice_right v1 v2 k (i + 1) hk (by omega),
    getElem?_splice_right v1 v2 k (i + 2) hk (by omega)]

theorem splice_length (v1 v2 : List α) (k : Nat) (h1 : k ≤ v1.length) (h2 : k ≤ v2.length) :
    (v1.take k ++ v2.drop k).length = v2.length := by
  rw [List.length_append, List.length_take, List.length_drop]
  omega

                  
theorem splice_bound (f : Window α → Nat) (cmax : Nat) (hf : ∀ w, f w ≤ cmax) (v1 v2 : List α) (k : Nat)
    (h1 : k ≤ v1.length) (h2 : k + 2 ≤ v2.length) (hk : 2 ≤ k) :
    score f (v1.take k ++ v2.drop k) ≤ settled f v1 k + 4 * cmax + suffix f v2 k := by
  unfold score settled suffix
  have hlen : (v1.take k ++ v2.drop k).length = k - 2 + (4 + (v2.length - (k + 2))) := by
    rw [splice_length v1 v2 k h1 (by omega)]
    omega
  rw [hlen, sumRange_add, sumRange_add]
  have hA : sumRange (fun i => f (window (v1.take k ++ v2.drop k) i)) (k - 2) ≤ sumRange (fun i => f (window v1 i)) k := by
    have e : sumRange (fun i => f (window (v1.take k ++ v2.drop k) i)) (k - 2) = sumRange (fun i => f (window v1 i)) (k - 2) :=
      sumRange_congr _ _ _ (fun i hi => by rw [window_splice_left v1 v2 k i h1 (by omega)])
    rw [e]
    exact sumRange_mono_len _ (Nat.sub_le k 2)
  have hB : sumRange (fun j => f (window (v1.take k ++ v2.drop k) (k - 2 + j))) 4 ≤ 4 * cmax := by
    have := sumRange_le_const (fun j => f (window (v1.take k ++ v2.drop k) (k - 2 + j))) cmax (fun j => hf _) 4
    omega
  have hC : sumRange (fun j => f (window (v1.take k ++ v2.drop k) (k - 2 + (4 + j)))) (v2.length - (k + 2))
      ≤ sumRange (fun j => f (window v2 (k + j))) (v2.length - k) := by
    have e : sumRange (fun j => f (window (v1.take k ++ v2.drop k) (k - 2 + (4 + j)))) (v2.length - (k + 2))
        = sumRange (fun j => f (window v2 (k + (2 + j)))) (v2.length - (k + 2)) :=
      sumRange_congr _ _ _ (fun j hj => by
        rw [show k - 2 + (4 + j) = k + (2 + j) by omega, window_splice_right v1 v2 k (k + (2 + j)) h1 (by omega)])
    rw [e]
    have : v2.length - k = 2 + (v2.length - (k + 2)) := by omega
    rw [this, sumRange_add]
    exact Nat.le_add_left _ _
  omega

end Splice
end PhonologicalRequirements
