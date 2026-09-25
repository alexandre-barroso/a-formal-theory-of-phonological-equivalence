                 
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Prod

namespace PhonologicalGrounding
namespace Cycles

variable {k : ℕ}

def cost (r w : ℕ) (pred : Fin k → Fin k) (S : Finset (Fin k)) : ℕ :=
  r * S.card + w * (Finset.univ.filter (fun j => j ∉ S ∧ pred j ∉ S)).card

def covered (pred : Fin k → Fin k) (S : Finset (Fin k)) : Finset (Fin k) :=
  Finset.univ.filter (fun j => j ∉ S ∧ pred j ∈ S)

def uncovered (pred : Fin k → Fin k) (S : Finset (Fin k)) : Finset (Fin k) :=
  Finset.univ.filter (fun j => j ∉ S ∧ pred j ∉ S)

theorem covered_le (pred : Fin k → Fin k) (hp : Function.Injective pred) (S : Finset (Fin k)) :
    (covered pred S).card ≤ S.card := by
  refine Finset.card_le_card_of_injOn pred ?_ ?_
  · intro j hj
    exact (Finset.mem_filter.mp hj).2.2
  · exact hp.injOn

theorem kept_split (pred : Fin k → Fin k) (S : Finset (Fin k)) :
    (covered pred S).card + (uncovered pred S).card = k - S.card := by
  have h := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter (fun j : Fin k => j ∉ S)) (p := fun j => pred j ∈ S)
  rw [Finset.filter_filter, Finset.filter_filter] at h
  have hc : (covered pred S) = Finset.univ.filter (fun j => j ∉ S ∧ pred j ∈ S) := rfl
  have hu : (uncovered pred S) = Finset.univ.filter (fun j => j ∉ S ∧ pred j ∉ S) := rfl
  rw [hc, hu]
  have hk : (Finset.univ.filter (fun j : Fin k => j ∉ S)).card = k - S.card := by
    rw [Finset.filter_not, Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.card_univ_sdiff, Fintype.card_fin]
  rw [hk] at h
  simpa using h

theorem length_bound (pred : Fin k → Fin k) (hp : Function.Injective pred) (S : Finset (Fin k)) :
    k ≤ 2 * S.card + (uncovered pred S).card := by
  have h1 := covered_le pred hp S
  have h2 := kept_split pred S
  have h3 : S.card ≤ k := by
    have := Finset.card_le_univ S
    simpa using this
  omega

theorem cost_lower (r w : ℕ) (hw : r ≤ w) (pred : Fin k → Fin k) (hp : Function.Injective pred)
    (S : Finset (Fin k)) : r * ((k + 1) / 2) ≤ cost r w pred S := by
  unfold cost
  have h := length_bound pred hp S
  have hu : (Finset.univ.filter (fun j => j ∉ S ∧ pred j ∉ S)).card = (uncovered pred S).card := rfl
  rw [hu]
  have h1 : (k + 1) / 2 ≤ S.card + (uncovered pred S).card := by omega
  have h2 := Nat.mul_le_mul_left r h1
  have h3 : r * (uncovered pred S).card ≤ w * (uncovered pred S).card := Nat.mul_le_mul_right _ hw
  rw [Nat.mul_add] at h2
  omega

theorem minimum_iff (r w : ℕ) (hr : 0 < r) (hw : r < w) (pred : Fin k → Fin k) (hp : Function.Injective pred)
    (S : Finset (Fin k)) :
    cost r w pred S = r * ((k + 1) / 2) ↔ (uncovered pred S).card = 0 ∧ S.card = (k + 1) / 2 := by
  have hb := length_bound pred hp S
  have hu : (Finset.univ.filter (fun j => j ∉ S ∧ pred j ∉ S)).card = (uncovered pred S).card := rfl
  constructor
  · intro h
    unfold cost at h
    rw [hu] at h
    rcases Nat.eq_zero_or_pos (uncovered pred S).card with h0 | h0
    · refine ⟨h0, ?_⟩
      rw [h0, Nat.mul_zero, Nat.add_zero] at h
      exact Nat.eq_of_mul_eq_mul_left hr h
    · exfalso
      have h1 : (k + 1) / 2 ≤ S.card + (uncovered pred S).card := by omega
      have h2 := Nat.mul_le_mul_left r h1
      have h3 : r * (uncovered pred S).card < w * (uncovered pred S).card :=
        Nat.mul_lt_mul_of_pos_right hw h0
      rw [Nat.mul_add] at h2
      omega
  · rintro ⟨h0, hc⟩
    unfold cost
    rw [hu, h0, hc]
    simp

theorem all_apply_never (r w : ℕ) (hr : 0 < r) (hw : r < w) (hk : 2 ≤ k) (pred : Fin k → Fin k)
    (hp : Function.Injective pred) :
    ¬ cost r w pred Finset.univ = r * ((k + 1) / 2) := by
  intro h
  have := (minimum_iff r w hr hw pred hp Finset.univ).mp h
  rw [Finset.card_univ, Fintype.card_fin] at this
  omega

theorem all_apply_beaten (r w : ℕ) (hr : 0 < r) (pred : Fin k → Fin k) (j : Fin k) (hj : pred j ≠ j) :
    cost r w pred (Finset.univ.erase j) < cost r w pred Finset.univ := by
  unfold cost
  have h1 : (Finset.univ.filter (fun i : Fin k => i ∉ (Finset.univ : Finset (Fin k)) ∧
      pred i ∉ (Finset.univ : Finset (Fin k)))) = ∅ := by
    ext i
    simp
  have h2 : (Finset.univ.filter (fun i : Fin k => i ∉ Finset.univ.erase j ∧ pred i ∉ Finset.univ.erase j)) = ∅ := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_true, not_not,
      Finset.notMem_empty, iff_false, not_and]
    intro hij hpj
    exact hj (hij ▸ hpj)
  rw [h1, h2, Finset.card_empty, Nat.mul_zero, Nat.add_zero, Nat.add_zero,
    Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin]
  have hk : 0 < k := Fin.pos j
  exact Nat.mul_lt_mul_of_pos_left (Nat.sub_lt hk Nat.one_pos) hr

def rot (n : ℕ) : Fin (n + 1) → Fin (n + 1) :=
  fun j => ⟨if j.val = 0 then n else j.val - 1, by split <;> omega⟩

theorem rot_injective (n : ℕ) : Function.Injective (rot n) := by
  intro a b h
  simp only [rot, Fin.mk.injEq] at h
  apply Fin.ext
  have ha := a.isLt
  have hb := b.isLt
  split at h <;> split at h <;> omega

def vec : ℕ → List (List Bool)
  | 0 => [[]]
  | n + 1 => (vec n).flatMap (fun v => [true :: v, false :: v])

def uncov : Bool → List Bool → ℕ
  | _, [] => 0
  | prev, b :: bs => (if b then 0 else if prev then 0 else 1) + uncov b bs

def dels : List Bool → ℕ
  | [] => 0
  | b :: bs => (if b then 1 else 0) + dels bs

def lastOf : List Bool → Bool
  | [] => false
  | [b] => b
  | _ :: bs => lastOf bs

def cyclicMinimisers (n : ℕ) : ℕ :=
  ((vec n).filter (fun v => uncov (lastOf v) v == 0 && dels v == (n + 1) / 2)).length

theorem cyclic_counts :
    cyclicMinimisers 2 = 2 ∧ cyclicMinimisers 3 = 3 ∧ cyclicMinimisers 4 = 2 ∧ cyclicMinimisers 5 = 5 ∧
    cyclicMinimisers 6 = 2 ∧ cyclicMinimisers 7 = 7 ∧ cyclicMinimisers 8 = 2 ∧ cyclicMinimisers 9 = 9 ∧
    cyclicMinimisers 10 = 2 ∧ cyclicMinimisers 11 = 11 ∧ cyclicMinimisers 12 = 2 := by
  decide +kernel

end Cycles
end PhonologicalGrounding
