                                                                                                                    
import PhonologicalRequirements.Contribution
import PhonologicalRequirements.Transient

namespace PhonologicalRequirements
namespace Cells

structure Cell where
  a : Bool
  ctx : Bool
  p : Bool
deriving DecidableEq, Repr

def bit (b : Bool) : Nat := if b then 1 else 0

def charge (num den w : Nat) (c : Cell) : Nat :=
  contrib num den w (bit c.a) (bit c.p) (bit c.ctx)

def current (c : Cell) : Nat := bit c.ctx * bit c.p

theorem charge_true_true (num den w : Nat) (ctx : Bool) :
    charge num den w ⟨true, ctx, true⟩ = w * den := by
  cases ctx <;> simp [charge, bit, contrib]

theorem charge_true_false (num den w : Nat) (ctx : Bool) :
    charge num den w ⟨true, ctx, false⟩ = 0 := by
  cases ctx <;> simp [charge, bit, contrib]

theorem charge_false_false (num den w : Nat) (p : Bool) :
    charge num den w ⟨false, false, p⟩ = 0 := by
  cases p <;> simp [charge, bit, contrib]

theorem charge_false_true_true (num den w : Nat) :
    charge num den w ⟨false, true, true⟩ = w * num := by
  simp [charge, bit, contrib]

theorem charge_false_true_false (num den w : Nat) :
    charge num den w ⟨false, true, false⟩ = 0 := by
  simp [charge, bit, contrib]

                           
theorem overapplication_iff (num den w : Nat) (hw : 0 < w) (hd : 0 < den) (c : Cell) :
    (0 < charge num den w c ∧ current c = 0) ↔ c = ⟨true, false, true⟩ := by
  rcases c with ⟨a, ctx, p⟩
  cases a <;> cases ctx <;> cases p <;> simp [charge, bit, contrib, current]
  exact Nat.mul_pos hw hd

                           
theorem underapplication_iff (c : Cell) :
    (current c = 1 ∧ c.a = false) ↔ c = ⟨false, true, true⟩ := by
  rcases c with ⟨a, ctx, p⟩
  cases a <;> cases ctx <;> cases p <;> simp [current, bit]

                              
theorem current_general (ws ms : List Nat) (F F' : Nat) (h : F' < F) :
    F' + dot (ws.zip ms) < F + dot (ws.zip ms) :=
  Nat.add_lt_add_right h _

                             
theorem tolerate_iff (num den w r : Nat) :
    charge num den w ⟨false, true, true⟩ < den * r ↔ w * num < den * r := by
  rw [charge_false_true_true]

                             
theorem lost_context_separated_by_a (num den w : Nat) :
    charge num den w ⟨true, false, true⟩ = w * den ∧ charge num den w ⟨false, false, true⟩ = 0 :=
  ⟨charge_true_true num den w false, charge_false_false num den w true⟩

                                    
theorem uniform_reparametrisation (n d n' d' w w' p c : Nat) (h : w * n * d' = w' * n' * d) :
    contrib n d w 0 p c * d' = contrib n' d' w' 0 p c * d := by
  simp only [contrib, Nat.zero_mul, Nat.mul_zero, Nat.zero_add, Nat.sub_zero, Nat.one_mul]
  calc w * (n * (c * p)) * d' = (w * n * d') * (c * p) := by ac_rfl
    _ = (w' * n' * d) * (c * p) := by rw [h]
    _ = w' * (n' * (c * p)) * d := by ac_rfl

                                    
theorem attenuation_enters_one_cell (num num' den w : Nat) (c : Cell)
    (hc : c ≠ ⟨false, true, true⟩) : charge num den w c = charge num' den w c := by
  rcases c with ⟨a, ctx, p⟩
  cases a <;> cases ctx <;> cases p <;> simp [charge, bit, contrib]
  exact absurd rfl hc

end Cells
end PhonologicalRequirements
