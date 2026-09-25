                       
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

namespace HuaianOdds

noncomputable section

abbrev Tone := Fin 4
abbrev Triple := Fin 3 → Tone

structure Weights where
  s33 : ℝ
  s11 : ℝ
  s44 : ℝ
  reg : ℝ
  cont : ℝ
  right : ℝ
  final : ℝ

def marked (u un v vn before after : Tone) (l : ℝ) : ℝ :=
  (if u = before ∧ un = before then 1 else
    if v = before ∧ vn = before then l else 0) *
  (if vn = before ∧ v ≠ after then 1 else 0)

def high (v : Tone) : ℕ := if v.val = 0 ∨ v.val = 3 then 1 else 0

@[simp] theorem high_one : high (1 : Tone) = 0 := rfl
@[simp] theorem high_two : high (2 : Tone) = 0 := rfl

def score (u v : Triple) (w : Weights) (l : ℝ) : ℝ :=
  w.s33 * (marked (u 0) (u 1) (v 0) (v 1) 2 1 l +
    marked (u 1) (u 2) (v 1) (v 2) 2 1 l) +
  w.s11 * (marked (u 0) (u 1) (v 0) (v 1) 0 2 l +
    marked (u 1) (u 2) (v 1) (v 2) 0 2 l) +
  w.s44 * (marked (u 0) (u 1) (v 0) (v 1) 3 2 l +
    marked (u 1) (u 2) (v 1) (v 2) 3 2 l) +
  w.reg * (∑ i : Fin 3, if high (u i) = high (v i) then 0 else 1) +
  w.cont * (∑ i : Fin 3, if u i = v i then 0 else 1) +
  w.right * ((if u 0 = u 1 ∧ u 1 ≠ v 1 then 1 else 0) +
    (if u 1 = u 2 ∧ u 2 ≠ v 2 then 1 else 0)) +
  w.final * (if u 2 = v 2 then 0 else 1)

def u333 : Triple := ![2, 2, 2]
def v223 : Triple := ![1, 1, 2]
def v323 : Triple := ![2, 1, 2]

theorem score_223 (w : Weights) (l : ℝ) :
    score u333 v223 w l = 2 * w.cont + w.right := by
  norm_num [score, marked, u333, v223, Fin.sum_univ_succ,
    Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Fin.ext_iff]
  ring

theorem score_323 (w : Weights) (l : ℝ) :
    score u333 v323 w l = w.cont + w.right := by
  norm_num [score, marked, u333, v323, Fin.sum_univ_succ,
    Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Fin.ext_iff]

theorem score_gap (w : Weights) (l : ℝ) :
    score u333 v223 w l - score u333 v323 w l = w.cont := by
  rw [score_223, score_323]
  ring

def mass (u v : Triple) (w : Weights) (l : ℝ) : ℝ :=
  Real.exp (-score u v w l)

def partition (u : Triple) (w : Weights) (l : ℝ) : ℝ :=
  ∑ v : Triple, mass u v w l

def probability (u v : Triple) (w : Weights) (l : ℝ) : ℝ :=
  mass u v w l / partition u w l

theorem partition_pos (u : Triple) (w : Weights) (l : ℝ) :
    0 < partition u w l := by
  unfold partition
  exact Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty

theorem full_support_count : Fintype.card Triple = 64 := by decide

theorem mass_order (w : Weights) (l : ℝ) (h : 0 ≤ w.cont) :
    mass u333 v223 w l ≤ mass u333 v323 w l := by
  simp only [mass, Real.exp_le_exp]
  have := score_gap w l
  linarith

theorem full_probability_order (w : Weights) (l : ℝ) (h : 0 ≤ w.cont) :
    probability u333 v223 w l ≤ probability u333 v323 w l := by
  exact div_le_div_of_nonneg_right (mass_order w l h) (le_of_lt (partition_pos _ _ _))

theorem conditional_bound (w : Weights) (l : ℝ) (h : 0 ≤ w.cont) :
    mass u333 v223 w l / (mass u333 v223 w l + mass u333 v323 w l) ≤ 1 / 2 := by
  have ha : 0 < mass u333 v223 w l := Real.exp_pos _
  have hb : 0 < mass u333 v323 w l := Real.exp_pos _
  have ho := mass_order w l h
  apply (div_le_iff₀ (by linarith : 0 < mass u333 v223 w l + mass u333 v323 w l)).2
  linarith

theorem finite_mixture_order {I : Type*} [Fintype I] (a b r : I → ℝ)
    (hr : ∀ i, 0 ≤ r i) (h : ∀ i, a i ≤ b i) :
    (∑ i, r i * a i) ≤ ∑ i, r i * b i := by
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (h i) (hr i)

theorem symmetric_noise_bound (p e : ℝ) (hp : p ≤ 1/2)
    (he : 0 ≤ e) (he' : e ≤ 1/2) : e + (1-2*e)*p ≤ 1/2 := by
  nlinarith

theorem asymmetric_noise_bound (p fp fn : ℝ) (hp : p ≤ 1/2)
    (hh : fp + fn ≤ 1) : fp + (1-fp-fn)*p ≤ (1+fp-fn)/2 := by
  nlinarith

theorem corruption_bound (p observed epsilon : ℝ) (hp : p ≤ 1/2)
    (he : observed - p ≤ epsilon) : observed - 1/2 ≤ epsilon := by
  linarith

end
end HuaianOdds
