                       
import PhonologicalRequirements.Terms

namespace PhonologicalRequirements

def contrib (num den w a p c : Nat) : Nat :=
  w * (den * (a * p) + num * ((1 - a) * (c * p)))

def contribExempt (den w p c : Nat) : Nat := w * (den * (c * p))

                     
theorem contrib_a_one (num den w p c : Nat) :
    contrib num den w 1 p c = w * (den * p) := by
  unfold contrib
  simp

                    
theorem contrib_a_zero_gauge (num den w p c : Nat) :
    den * contrib num den w 0 p c = num * contribExempt den w p c := by
  unfold contrib contribExempt
  simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

                       
theorem transfer_gap (num den w p c : Nat)
    (hp : p = 1) (hc : c = 1) (hw : 0 < w) (hlt : num < den) :
    contrib num den w 0 p c < contrib num den w 1 p c := by
  subst hp; subst hc
  unfold contrib
  simp
  exact (Nat.mul_lt_mul_left hw).mpr hlt

end PhonologicalRequirements
