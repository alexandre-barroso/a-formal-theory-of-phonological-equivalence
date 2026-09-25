                    
namespace PhonologicalRequirements
namespace Modes

def neither (wA wB : Nat) : Nat := wA + wB
def aOnly (rA wB : Nat) (cB : Bool) : Nat := rA + (if cB then 0 else wB)
def bOnly (rB wA : Nat) (cA : Bool) : Nat := rB + (if cA then 0 else wA)
def both (rA rB : Nat) : Nat := rA + rB

theorem counterbleeding_iff (rA rB wA : Nat) : both rA rB < bOnly rB wA false ↔ rA < wA := by
  simp only [both, bOnly, Bool.false_eq_true, ↓reduceIte]
  omega

theorem counterbleeding_never (rA rB wA : Nat) : ¬ both rA rB < bOnly rB wA true := by
  simp only [both, bOnly, ↓reduceIte]
  omega

theorem bleeding_iff (rA rB wA : Nat) (h : rA < wA) (cA : Bool) :
    bOnly rB wA cA < both rA rB ↔ (cA = true ∧ 0 < rA) := by
  cases cA <;> simp only [both, bOnly, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte, true_and, false_and]
    <;> constructor <;> intro h' <;> first | omega | exact h'.elim

theorem mutual_both_apply_iff (rA rB wA wB : Nat) (cA cB : Bool) :
    (both rA rB < aOnly rA wB cB ∧ both rA rB < bOnly rB wA cA ∧ both rA rB < neither wA wB) ↔
    (cA = false ∧ cB = false ∧ rA < wA ∧ rB < wB) := by
  cases cA <;> cases cB
    <;> simp only [both, aOnly, bOnly, neither, Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte, true_and, false_and, and_false, and_true]
    <;> constructor <;> intro h' <;> first | omega | exact h'.elim

def createdUnrepaired (num wB : Nat) : Nat := num * wB
def createdRepaired (den rB : Nat) : Nat := den * rB

theorem feeds_iff (num den wB rB : Nat) :
    createdRepaired den rB < createdUnrepaired num wB ↔ den * rB < num * wB := Iff.rfl

theorem feeding_needs_positive_attenuation (num den wB rB : Nat)
    (h : createdRepaired den rB < createdUnrepaired num wB) : 0 < num := by
  rcases Nat.eq_zero_or_pos num with h0 | h0
  · subst h0
    simp [createdRepaired, createdUnrepaired] at h
  · exact h0

theorem counterfeeding_needs_attenuation_below_one (num den wB rB : Nat) (hB : rB < wB)
    (h : createdUnrepaired num wB < createdRepaired den rB) : num < den := by
  simp only [createdUnrepaired, createdRepaired] at h
  have hd : 0 < den := by
    rcases Nat.eq_zero_or_pos den with h0 | h0
    · subst h0; simp at h
    · exact h0
  have h1 : den * rB < den * wB := Nat.mul_lt_mul_of_pos_left hB hd
  have h2 : num * wB < den * wB := Nat.lt_trans h h1
  exact Nat.lt_of_mul_lt_mul_right h2

end Modes
end PhonologicalRequirements
