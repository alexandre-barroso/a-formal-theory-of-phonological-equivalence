                    
                
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace TransientScope

def selectsBattery (l w f d v : ℝ) : Prop :=
  0 ≤ w ∧ 0 ≤ f ∧ 0 ≤ d ∧ 0 ≤ v ∧
  f < w ∧ l*w < f ∧ d+l*w < v

theorem battery_region (l : ℝ) (hl : 0 ≤ l) :
    (∃ w f d v, selectsBattery l w f d v) ↔ l < 1 := by
  constructor
  · rintro ⟨w,f,d,v,hw,hf,hd,hv,hfw,hlw,hdv⟩
    have hwpos : 0 < w := lt_of_le_of_lt hf hfw
    nlinarith
  · intro h
    refine ⟨2,1+l,1,2+2*l,?_⟩
    unfold selectsBattery
    constructor <;> try linarith
    constructor <;> try linarith
    constructor <;> try linarith
    constructor <;> try linarith
    constructor <;> try linarith
    constructor <;> linarith

theorem frozen_witness : selectsBattery (1/4) 4 2 1 3 := by
  norm_num [selectsBattery]

theorem entire_derived_competition (l w f d v : ℝ)
    (h : selectsBattery l w f d v) :
    d+l*w < v ∧ d+l*w < d+f ∧ d+l*w < v+f := by
  rcases h with ⟨hw,hf,hd,hv,hfw,hlw,hdv⟩
  exact ⟨hdv,by linarith,by linarith⟩

theorem inactive_term (l w p : ℝ) : w * (0*p + l*(1-0)*0*p) = 0 := by simp

theorem strict_effective (l w os ns ot nt : ℝ)
    (hl : 0 ≤ l) (hw : 0 ≤ w) (ho : ot ≤ os) (hn : nt ≤ ns)
    (hs : (0<w ∧ ot<os) ∨ (0<l*w ∧ nt<ns)) :
    w*(ot+l*nt) < w*(os+l*ns) := by
  have h1 := mul_nonneg hw (sub_nonneg.mpr ho)
  have h2 := mul_nonneg (mul_nonneg hl hw) (sub_nonneg.mpr hn)
  rcases hs with ⟨hw,ho⟩ | ⟨hw,hn⟩
  · have hh := mul_pos hw (sub_pos.mpr ho); nlinarith
  · have hh := mul_pos hw (sub_pos.mpr hn); nlinarith

theorem weighted_dominance {I : Type} [Fintype I]
    (l : ℝ) (w os ns ot nt : I → ℝ) (hl : 0 ≤ l)
    (hw : ∀ i, 0 ≤ w i) (ho : ∀ i, ot i ≤ os i) (hn : ∀ i, nt i ≤ ns i) :
    ∑ i, w i * (ot i + l * nt i) ≤ ∑ i, w i * (os i + l * ns i) := by
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_left (add_le_add (ho i) (mul_le_mul_of_nonneg_left (hn i) hl)) (hw i)

theorem weighted_dominance_strict {I : Type} [Fintype I]
    (l : ℝ) (w os ns ot nt : I → ℝ) (hl : 0 ≤ l)
    (hw : ∀ i, 0 ≤ w i) (ho : ∀ i, ot i ≤ os i) (hn : ∀ i, nt i ≤ ns i)
    (hs : ∃ i, (0 < w i ∧ ot i < os i) ∨ (0 < l * w i ∧ nt i < ns i)) :
    ∑ i, w i * (ot i + l * nt i) < ∑ i, w i * (os i + l * ns i) := by
  obtain ⟨i, hi⟩ := hs
  apply Finset.sum_lt_sum
  · intro j _
    exact mul_le_mul_of_nonneg_left (add_le_add (ho j) (mul_le_mul_of_nonneg_left (hn j) hl)) (hw j)
  · exact ⟨i, Finset.mem_univ i, strict_effective l (w i) (os i) (ns i) (ot i) (nt i) hl (hw i) (ho i) (hn i) hi⟩

theorem zero_new_tie : (1:ℝ)*(0+0*1) = 1*(0+0*0) := by norm_num

theorem cheaper_admissible_excludes {S : Type} (P : S → ℝ) (s t : S)
    (h : P t < P s) : ¬ (∀ u, P s ≤ P u) := by
  intro hmin
  exact (not_le_of_gt h) (hmin t)

theorem product_unique {I : Type} [Fintype I] (p q : I → ℝ)
    (h : ∀ i, p i ≤ q i) (hs : ∃ i, p i < q i) :
    ∑ i, p i < ∑ i, q i := by
  obtain ⟨i,hi⟩ := hs
  exact Finset.sum_lt_sum (fun j _ => h j) ⟨i,Finset.mem_univ i,hi⟩

end TransientScope
