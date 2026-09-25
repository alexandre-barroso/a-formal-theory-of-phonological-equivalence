                                        
namespace PhonologicalRequirements

structure Score where
  created : Nat
  restF   : Nat
  mark    : Nat

def Score.total (delta : Nat) (s : Score) : Nat :=
  delta * s.created + s.restF + s.mark

theorem excluded_of_many_created
    {delta B : Nat} (hd : 0 < delta) (s : Score)
    (h : B / delta < s.created) : B < s.total delta := by
  have h1 : B / delta + 1 <= s.created := h
  have h2 : delta * (B / delta + 1) <= delta * s.created :=
    Nat.mul_le_mul_left delta h1
  have hmod : B % delta < delta := Nat.mod_lt _ hd
  have h3 : B < delta * (B / delta + 1) := by
    rw [Nat.mul_succ]
    calc B = delta * (B / delta) + B % delta := (Nat.div_add_mod B delta).symm
      _ < delta * (B / delta) + delta := Nat.add_lt_add_left hmod _
  have h4 : B < delta * s.created := Nat.lt_of_lt_of_le h3 h2
  unfold Score.total
  exact Nat.lt_of_lt_of_le h4
    (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _))

theorem reduction_fails_at_zero (k : Nat) :
    (Score.total 0 ⟨k, 0, 0⟩) = 0 := by
  unfold Score.total; simp

end PhonologicalRequirements
