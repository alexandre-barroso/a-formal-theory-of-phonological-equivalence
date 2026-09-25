                                                                                                                    
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

namespace PhonologicalCalculus.Application.CellScope

open Finset

def bit (b : Bool) : ℝ := if b then 1 else 0

def charge (w lam : ℝ) (a c p : Bool) : ℝ :=
  w * (bit a * bit p + lam * (1-bit a) * bit c * bit p)

theorem old_charge_without_current (w lam : ℝ) (hw : 0 < w) (a c p : Bool) :
    (0 < charge w lam a c p ∧ bit c * bit p = 0) ↔
      a=true ∧ c=false ∧ p=true := by
  cases a <;> cases c <;> cases p <;> simp [charge,bit,hw]

theorem current_new_cell (a c p : Bool) :
    (a=false ∧ bit c * bit p=1) ↔ a=false ∧ c=true ∧ p=true := by
  cases a <;> cases c <;> cases p <;> simp [bit]

theorem zero_reference_markedness_not_absent_context :
    bit true * bit false = 0 ∧ bit true ≠ 0 := by norm_num [bit]

theorem equal_markedness_fixed_faithfulness {ι : Type*} [Fintype ι]
    (w m m' : ι → ℝ) (f f' : ℝ) (hm : ∀ i, m i=m' i) (hf : f'<f) :
    (∑ i, w i*m' i)+f' < (∑ i, w i*m i)+f := by
  simp_rw [hm]
  linarith

theorem componentwise_weak_dominance {ι : Type*} [Fintype ι]
    (w f f' : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hf : ∀ i, f' i ≤ f i) :
    (∑ i, w i*f' i) ≤ ∑ i, w i*f i :=
  Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hf i) (hw i)

theorem componentwise_strict_dominance {ι : Type*} [Fintype ι]
    (w f f' : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hf : ∀ i, f' i ≤ f i)
    (j : ι) (hwj : 0 < w j) (hfj : f' j < f j) :
    (∑ i, w i*f' i) < ∑ i, w i*f i := by
  exact Finset.sum_lt_sum (fun i _ => mul_le_mul_of_nonneg_left (hf i) (hw i))
    ⟨j,mem_univ j,mul_lt_mul_of_pos_left hfj hwj⟩

theorem reweighting_reverses_order :
    (2:ℝ)*0+1*1 < 2*1+1*0 ∧ 1*0+2*1 > 1*1+2*0 ∧
    (0:ℝ)*0+0*1 = 0*1+0*0 := by norm_num

theorem isolated_repair_comparison (common lam w r : ℝ) :
    (common+lam*w < common+r ↔ lam*w<r) ∧
    (common+lam*w = common+r ↔ lam*w=r) ∧
    (common+r < common+lam*w ↔ r<lam*w) := by
  constructor
  · constructor <;> intro h <;> linarith
  constructor <;> constructor <;> intro h <;> linarith

theorem other_markedness_changes_comparison :
    (1:ℝ)/8*4 < 1 ∧ 1/8*4+2 > 1 := by norm_num

noncomputable def reweight {ι : Type*} (newOnly : ι → Bool) (lam lam' : ℝ) (w : ι → ℝ) : ι → ℝ :=
  fun i => if newOnly i then (lam/lam')*w i else w i

theorem reweight_nonnegative {ι : Type*} (newOnly : ι → Bool)
    (lam lam' : ℝ) (hl : 0 ≤ lam) (hl' : 0 < lam')
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) : ∀ i, 0 ≤ reweight newOnly lam lam' w i := by
  intro i
  unfold reweight
  split_ifs
  · exact mul_nonneg (div_nonneg hl hl'.le) (hw i)
  · exact hw i

theorem separated_columns_same_score {ι : Type*} [Fintype ι]
    (newOnly : ι → Bool) (a b w : ι → ℝ) (lam lam' : ℝ) (hl' : lam'≠0)
    (ha : ∀ i, newOnly i=true → a i=0)
    (hb : ∀ i, newOnly i=false → b i=0) :
    (∑ i, reweight newOnly lam lam' w i * (a i+lam'*b i)) =
      ∑ i, w i*(a i+lam*b i) := by
  apply Finset.sum_congr rfl
  intro i _
  cases hi : newOnly i with
  | false => simp [reweight,hi,hb i hi]
  | true =>
    simp only [reweight,hi,if_true,ha i hi,zero_add]
    field_simp

end PhonologicalCalculus.Application.CellScope
