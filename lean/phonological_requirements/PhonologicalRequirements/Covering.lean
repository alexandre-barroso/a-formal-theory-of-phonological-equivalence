                    
namespace PhonologicalRequirements
namespace Covering

def cost (wI w : Nat) : Bool → List Bool → Nat
  | _, [] => 0
  | prev, b :: bs => (if b then wI else if prev then 0 else w) + cost wI w b bs

def uncovered : Bool → List Bool → Nat
  | _, [] => 0
  | prev, b :: bs => (if b then 0 else if prev then 0 else 1) + uncovered b bs

def deletions : List Bool → Nat
  | [] => 0
  | b :: bs => (if b then 1 else 0) + deletions bs

def doubles : Bool → List Bool → Nat
  | _, [] => 0
  | prev, b :: bs => (if b && prev then 1 else 0) + doubles b bs

def alternating : Bool → Nat → List Bool
  | _, 0 => []
  | d, n + 1 => d :: alternating (!d) n

theorem cost_eq (wI w : Nat) : ∀ (prev : Bool) (l : List Bool),
    cost wI w prev l = wI * deletions l + w * uncovered prev l
  | _, [] => by simp [cost, deletions, uncovered]
  | prev, b :: bs => by
    have ih := cost_eq wI w b bs
    cases b <;> cases prev <;> simp [cost, deletions, uncovered, Nat.mul_add] <;> omega

theorem length_bound : ∀ (prev : Bool) (l : List Bool),
    l.length ≤ 2 * deletions l + uncovered prev l + (if prev then 1 else 0)
  | _, [] => by simp [deletions, uncovered]
  | prev, b :: bs => by
    have ih := length_bound b bs
    cases b <;> cases prev <;> simp [deletions, uncovered] at ih ⊢ <;> omega

theorem length_bound_false (l : List Bool) : l.length ≤ 2 * deletions l + uncovered false l := by
  have := length_bound false l
  simpa using this

theorem covered_deletions (l : List Bool) (h : uncovered false l = 0) : (l.length + 1) / 2 ≤ deletions l := by
  have := length_bound_false l
  omega

theorem cost_lower (wI w : Nat) (hw : wI ≤ w) (l : List Bool) :
    wI * ((l.length + 1) / 2) ≤ cost wI w false l := by
  rw [cost_eq]
  have hlen := length_bound_false l
  have h1 : (l.length + 1) / 2 ≤ deletions l + uncovered false l := by omega
  have h2 := Nat.mul_le_mul_left wI h1
  have h3 : wI * uncovered false l ≤ w * uncovered false l := Nat.mul_le_mul_right _ hw
  rw [Nat.mul_add] at h2
  omega

theorem cost_lower_strict (wI w : Nat) (hw : wI < w) (l : List Bool) (hu : 0 < uncovered false l) :
    wI * ((l.length + 1) / 2) < cost wI w false l := by
  rw [cost_eq]
  have hlen := length_bound_false l
  have h1 : (l.length + 1) / 2 ≤ deletions l + uncovered false l := by omega
  have h2 := Nat.mul_le_mul_left wI h1
  have h3 : wI * uncovered false l < w * uncovered false l := Nat.mul_lt_mul_of_pos_right hw hu
  rw [Nat.mul_add] at h2
  omega

theorem minimum_iff (wI w : Nat) (hI : 0 < wI) (hw : wI < w) (l : List Bool) :
    cost wI w false l = wI * ((l.length + 1) / 2) ↔
      uncovered false l = 0 ∧ deletions l = (l.length + 1) / 2 := by
  constructor
  · intro h
    have hu : uncovered false l = 0 := by
      rcases Nat.eq_zero_or_pos (uncovered false l) with h0 | h0
      · exact h0
      · have := cost_lower_strict wI w hw l h0
        omega
    refine ⟨hu, ?_⟩
    rw [cost_eq, hu] at h
    simp at h
    have hd : wI * deletions l = wI * ((l.length + 1) / 2) := h
    exact Nat.eq_of_mul_eq_mul_left hI hd
  · rintro ⟨hu, hd⟩
    rw [cost_eq, hu, hd]
    simp

theorem alternating_length (d : Bool) : ∀ n, (alternating d n).length = n
  | 0 => rfl
  | n + 1 => by simp [alternating, alternating_length (!d) n]

theorem alternating_stats : ∀ n,
    (deletions (alternating true n) = (n + 1) / 2 ∧ deletions (alternating false n) = n / 2) ∧
    (uncovered false (alternating true n) = 0 ∧ uncovered true (alternating false n) = 0) ∧
    (doubles false (alternating true n) = 0 ∧ doubles true (alternating false n) = 0)
  | 0 => by simp [alternating, deletions, uncovered, doubles]
  | n + 1 => by
    have ih := alternating_stats n
    simp only [alternating, Bool.not_true, Bool.not_false, deletions, uncovered, doubles] at ih ⊢
    simp
    omega

theorem alternating_of_covered_nodouble : ∀ (prev : Bool) (l : List Bool),
    uncovered prev l = 0 → doubles prev l = 0 → l = alternating (!prev) l.length
  | _, [], _, _ => rfl
  | false, false :: bs, hu, _ => by simp [uncovered] at hu
  | false, true :: bs, hu, hd => by
      simp [uncovered] at hu
      simp [doubles] at hd
      simp [alternating]
      exact alternating_of_covered_nodouble true bs hu hd
  | true, false :: bs, hu, hd => by
      simp [uncovered] at hu
      simp [doubles] at hd
      simp [alternating]
      exact alternating_of_covered_nodouble false bs hu hd
  | true, true :: bs, _, hd => by simp [doubles] at hd

def cost' (wI w wC num den : Nat) (l : List Bool) : Nat :=
  den * cost wI w false l + num * wC * doubles false l

theorem alternating_unique (wI w wC num den : Nat) (hw : wI < w) (hC : 0 < wC) (hn : 0 < num) (hd : 0 < den)
    (l : List Bool) (hne : l ≠ alternating true l.length) :
    cost' wI w wC num den (alternating true l.length) < cost' wI w wC num den l := by
  obtain ⟨⟨hdel, _⟩, ⟨hunc, _⟩, ⟨hdbl, _⟩⟩ := alternating_stats l.length
  have hA : cost' wI w wC num den (alternating true l.length) = den * (wI * ((l.length + 1) / 2)) := by
    simp only [cost', hdbl, Nat.mul_zero, Nat.add_zero]
    rw [cost_eq, hdel, hunc]
    simp
  rw [hA]
  simp only [cost']
  rcases Nat.eq_zero_or_pos (uncovered false l) with hu | hu
  · rcases Nat.eq_zero_or_pos (doubles false l) with hb | hb
    · exact absurd (by simpa using alternating_of_covered_nodouble false l hu hb) hne
    · have h1 := cost_lower wI w (Nat.le_of_lt hw) l
      have h2 := Nat.mul_le_mul_left den h1
      have h3 : 0 < num * wC * doubles false l := Nat.mul_pos (Nat.mul_pos hn hC) hb
      omega
  · have h1 := cost_lower_strict wI w hw l hu
    have h2 := Nat.mul_lt_mul_of_pos_left h1 hd
    omega

theorem alternating_get (d : Bool) : ∀ (n k : Nat), k < n →
    (alternating d n)[k]? = some (if k % 2 = 0 then d else !d)
  | 0, k, hk => by omega
  | n + 1, 0, _ => by simp [alternating]
  | n + 1, k + 1, hk => by
    simp only [alternating, List.getElem?_cons_succ]
    rw [alternating_get (!d) n k (by omega)]
    rcases Nat.mod_two_eq_zero_or_one k with h | h
    · have h1 : (k + 1) % 2 = 1 := by omega
      simp [h, h1]
    · have h1 : (k + 1) % 2 = 0 := by omega
      simp [h, h1]

theorem odd_positions_deleted (n k : Nat) (hk : k < n) :
    (alternating true n)[k]? = some (decide (k % 2 = 0)) := by
  rw [alternating_get true n k hk]
  rcases Nat.mod_two_eq_zero_or_one k with h | h <;> simp [h]

def lastDeleted : List Bool → Nat
  | [] => 0
  | [b] => if b then 1 else 0
  | _ :: c :: bs => lastDeleted (c :: bs)

theorem length_identity : ∀ (prev : Bool) (l : List Bool),
    l.length + doubles prev l + lastDeleted l =
      2 * deletions l + uncovered prev l + (if prev && !l.isEmpty then 1 else 0)
  | _, [] => by simp [doubles, lastDeleted, deletions, uncovered]
  | prev, [b] => by
    cases b <;> cases prev <;> simp [doubles, lastDeleted, deletions, uncovered]
  | prev, b :: c :: bs => by
    have ih := length_identity b (c :: bs)
    cases b <;> cases prev <;> simp [doubles, lastDeleted, deletions, uncovered] at ih ⊢ <;> omega

theorem length_identity_false (l : List Bool) :
    l.length + doubles false l + lastDeleted l = 2 * deletions l + uncovered false l := by
  have := length_identity false l
  simpa using this

theorem even_minimiser_unique (l : List Bool) (heven : l.length % 2 = 0)
    (hu : uncovered false l = 0) (hd : deletions l = (l.length + 1) / 2) :
    l = alternating true l.length := by
  have h := length_identity_false l
  have hdb : doubles false l = 0 := by omega
  simpa using alternating_of_covered_nodouble false l hu hdb

theorem odd_minimiser_seam (l : List Bool) (hodd : l.length % 2 = 1)
    (hu : uncovered false l = 0) (hd : deletions l = (l.length + 1) / 2) :
    doubles false l + lastDeleted l = 1 := by
  have h := length_identity_false l
  omega

def vec : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (vec n).flatMap (fun v => [true :: v, false :: v])

def minimisers (n : Nat) : Nat :=
  ((vec n).filter (fun v => uncovered false v == 0 && deletions v == (n + 1) / 2)).length

theorem minimisers_1 : minimisers 1 = 1 := by decide +kernel
theorem minimisers_2 : minimisers 2 = 1 := by decide +kernel
theorem minimisers_3 : minimisers 3 = 2 := by decide +kernel
theorem minimisers_4 : minimisers 4 = 1 := by decide +kernel
theorem minimisers_5 : minimisers 5 = 3 := by decide +kernel
theorem minimisers_6 : minimisers 6 = 1 := by decide +kernel
theorem minimisers_7 : minimisers 7 = 4 := by decide +kernel
theorem minimisers_8 : minimisers 8 = 1 := by decide +kernel
theorem minimisers_9 : minimisers 9 = 5 := by decide +kernel
theorem minimisers_10 : minimisers 10 = 1 := by decide +kernel
theorem minimisers_11 : minimisers 11 = 6 := by decide +kernel
theorem minimisers_12 : minimisers 12 = 1 := by decide +kernel

theorem tie_counts_bounded (n : Nat) (h1 : 1 ≤ n) (h2 : n ≤ 12) :
    minimisers n = (if n % 2 = 0 then 1 else (n + 1) / 2) := by
  match n with
  | 0 => omega
  | 1 => simp [minimisers_1]
  | 2 => simp [minimisers_2]
  | 3 => simp [minimisers_3]
  | 4 => simp [minimisers_4]
  | 5 => simp [minimisers_5]
  | 6 => simp [minimisers_6]
  | 7 => simp [minimisers_7]
  | 8 => simp [minimisers_8]
  | 9 => simp [minimisers_9]
  | 10 => simp [minimisers_10]
  | 11 => simp [minimisers_11]
  | 12 => simp [minimisers_12]
  | n + 13 => omega

end Covering
end PhonologicalRequirements
