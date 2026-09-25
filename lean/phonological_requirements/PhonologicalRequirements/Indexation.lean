                     
namespace PhonologicalRequirements
namespace Indexation

theorem saturated_count (m j : Nat) (h1 : 1 ≤ j) (h2 : j < m) : min (m - j) 1 = min m 1 := by
  have ha : 1 ≤ m - j := by omega
  have hb : 1 ≤ m := by omega
  rw [Nat.min_eq_right ha, Nat.min_eq_right hb]

theorem partial_repair_worse (w F c m j : Nat) (hc : 0 < c) (h1 : 1 ≤ j) (h2 : j < m) :
    w * min m 1 + F < w * min (m - j) 1 + (F + j * c) := by
  rw [saturated_count m j h1 h2]
  have : 0 < j * c := Nat.mul_pos (by omega) hc
  omega

theorem full_repair_clears (m : Nat) : min (m - m) 1 = 0 := by simp

end Indexation
end PhonologicalRequirements
