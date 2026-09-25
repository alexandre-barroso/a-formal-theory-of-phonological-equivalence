                   
namespace PhonologicalRequirements
namespace Majority

theorem edits_bounded (wR wI : Nat) (cost : Nat → Nat) (hlow : ∀ j, j * wI ≤ cost j) (h0 : cost 0 = wR)
    (j : Nat) (hmin : ∀ k, cost j ≤ cost k) : j * wI ≤ wR := by
  have := hmin 0
  rw [h0] at this
  exact Nat.le_trans (hlow j) this

theorem boundary_bound (den num wR wI : Nat) (cost : Nat → Nat) (hlow : ∀ j, den * (j * wI) ≤ cost j)
    (h1 : cost 1 = den * wI + num * wR) (j : Nat) (hmin : ∀ k, cost j ≤ cost k) :
    den * (j * wI) ≤ den * wI + num * wR := by
  have := hmin 1
  rw [h1] at this
  exact Nat.le_trans (hlow j) this

theorem majority_not_selected (wR wI : Nat) (cost : Nat → Nat) (hlow : ∀ j, j * wI ≤ cost j)
    (h0 : cost 0 = wR) (p q : Nat) (hpq : wR < min p q * wI) : ¬ ∀ k, cost (min p q) ≤ cost k := by
  intro hmin
  have := edits_bounded wR wI cost hlow h0 (min p q) hmin
  omega

end Majority
end PhonologicalRequirements
