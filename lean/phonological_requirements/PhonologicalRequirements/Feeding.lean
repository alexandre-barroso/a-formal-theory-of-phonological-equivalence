                                            
namespace PhonologicalRequirements
namespace Feeding

def cost (den num w wI n k : Nat) : Nat :=
  if k = 0 then den * w else if k < n then den * (k * wI) + num * w else den * (n * wI)

theorem cost_zero (den num w wI n : Nat) : cost den num w wI n 0 = den * w := by
  simp [cost]

theorem cost_mid (den num w wI n k : Nat) (h1 : 1 ≤ k) (h2 : k < n) :
    cost den num w wI n k = den * (k * wI) + num * w := by
  have hk : k ≠ 0 := by omega
  simp [cost, hk, h2]

theorem cost_end (den num w wI n : Nat) (hn : 1 ≤ n) : cost den num w wI n n = den * (n * wI) := by
  have hn' : n ≠ 0 := by omega
  simp [cost, hn']

theorem mid_ge_first (den num w wI : Nat) {k : Nat} (h1 : 1 ≤ k) :
    den * wI + num * w ≤ den * (k * wI) + num * w := by
  have h : wI ≤ k * wI := by
    have := Nat.mul_le_mul_right wI h1
    simpa using this
  have := Nat.mul_le_mul_left den h
  omega

theorem runs_to_end_iff (den num w wI n : Nat) (hn : 2 ≤ n)
    (hforced : den * wI + num * w < den * w) :
    (∀ k, k ≤ n → cost den num w wI n n ≤ cost den num w wI n k) ↔
      den * (n * wI) ≤ den * wI + num * w := by
  constructor
  · intro h
    have h1 := h 1 (by omega)
    rw [cost_end den num w wI n (by omega), cost_mid den num w wI n 1 (by omega) (by omega)] at h1
    simpa using h1
  · intro h k hk
    rw [cost_end den num w wI n (by omega)]
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · subst h0
      rw [cost_zero]
      omega
    · rcases Nat.lt_or_ge k n with hk2 | hk2
      · rw [cost_mid den num w wI n k h0 hk2]
        have := mid_ge_first den num w wI h0
        omega
      · have : k = n := by omega
        subst this
        rw [cost_end den num w wI k (by omega)]
        exact Nat.le_refl _

theorem stops_after_first (den num w wI n : Nat) (hd : 0 < den) (hI : 0 < wI) (hn : 2 ≤ n)
    (hforced : den * wI + num * w < den * w) (h : den * wI + num * w < den * (n * wI)) :
    ∀ k, k ≤ n → k ≠ 1 → cost den num w wI n 1 < cost den num w wI n k := by
  intro k hk h1
  rw [cost_mid den num w wI n 1 (by omega) (by omega)]
  simp only [Nat.one_mul]
  rcases Nat.eq_zero_or_pos k with h0 | h0
  · subst h0
    rw [cost_zero]
    exact hforced
  · rcases Nat.lt_or_ge k n with hk2 | hk2
    · rw [cost_mid den num w wI n k h0 hk2]
      have h2 : 2 ≤ k := by omega
      have h3 : 2 * wI ≤ k * wI := Nat.mul_le_mul_right wI h2
      have h4 := Nat.mul_le_mul_left den h3
      have e : den * (2 * wI) = 2 * (den * wI) := by ac_rfl
      have hpos : 0 < den * wI := Nat.mul_pos hd hI
      omega
    · have : k = n := by omega
      subst this
      rw [cost_end den num w wI k (by omega)]
      exact h

end Feeding
end PhonologicalRequirements
