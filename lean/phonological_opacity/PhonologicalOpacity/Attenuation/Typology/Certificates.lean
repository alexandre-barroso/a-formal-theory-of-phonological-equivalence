import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
namespace InteractionCertificates
noncomputable def dot {n : Nat} (r w : Fin n → ℝ) : ℝ := ∑i,r i*w i
theorem dominance {n : Nat} (r s w : Fin n → ℝ) (hw : ∀i,0≤w i)
    (hrs : ∀i,r i≤s i) : dot r w≤dot s w := by
  exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hrs i) (hw i))
theorem pruning {n : Nat} (rows kept : List (Fin n → ℝ)) (w : Fin n → ℝ)
    (hw : ∀i,0≤w i) (subset : ∀r∈kept,r∈rows)
    (cover : ∀r∈rows,∃s∈kept,∀i,s i≤r i) (good : ℝ) :
    (∀r∈rows,good<dot r w) ↔ (∀s∈kept,good<dot s w) := by
  constructor
  · intro h s hs;exact h s (subset s hs)
  · intro h r hr
    obtain ⟨s,hs,hdom⟩ := cover r hr
    exact lt_of_lt_of_le (h s hs) (dominance s r w hw hdom)
theorem affine_dominance {n : Nat} (a b c d w : Fin n → ℝ) (l : ℝ)
    (hl : 0≤l) (hw : ∀i,0≤w i) (ha : ∀i,a i≤c i) (hb : ∀i,b i≤d i) :
    dot (fun i => a i+l*b i) w ≤ dot (fun i => c i+l*d i) w := by
  apply dominance _ _ w hw
  intro i
  exact add_le_add (ha i) (mul_le_mul_of_nonneg_left (hb i) hl)
end InteractionCertificates
