                             
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Prod

namespace OCPGraphRegion

abbrev Candidate := Bool × Bool × Bool × Bool × Bool × Bool

def coefficients (c : Candidate) : Nat × Nat × Nat × Nat :=
  let (p,q,e00,e01,e10,e11) := c
  ((if p then 0 else 1) + (if q then 0 else 1),
   (if e00 then 0 else 1) + (if e11 then 0 else 1),
   if p && q && e00 && e11 then 1 else 0,
   if p && q && e10 && e01 then 1 else 0)

noncomputable def score (t a w l : ℝ) (c : Candidate) : ℝ :=
  let q := coefficients c
  q.1*t + q.2.1*a + q.2.2.1*w + q.2.2.2*l*w

def good (c : Candidate) : Prop :=
  (coefficients c).2.2.1 = 0 ∧ (coefficients c).2.2.2 = 0

def minimal (t a w l : ℝ) (c : Candidate) : Prop :=
  ∀ d, score t a w l c ≤ score t a w l d

def selects (t a w l : ℝ) : Prop :=
  ∀ c, minimal t a w l c → good c

theorem candidate_count : Fintype.card Candidate = 64 := by decide +kernel

theorem single_tone_free (p q e00 e01 e10 e11 : Bool) (h : p = false ∨ q = false) :
    good (p,q,e00,e01,e10,e11) := by
  rcases h with rfl | rfl <;> simp [good,coefficients]

theorem lower_bound (t a w l : ℝ) (ht : 0 ≤ t) (ha : 0 ≤ a)
    (hw : 0 ≤ w) (hl : 0 ≤ l) (c : Candidate) :
    min w (min t a) ≤ score t a w l c := by
  have h1 := min_le_left w (min t a)
  have h2 := (min_le_right w (min t a)).trans (min_le_left t a)
  have h3 := (min_le_right w (min t a)).trans (min_le_right t a)
  have h4 := mul_nonneg hl hw
  generalize hm : min w (min t a) = m at h1 h2 h3 ⊢
  rcases c with ⟨p,q,e00,e01,e10,e11⟩
  cases p <;> cases q <;> cases e00 <;> cases e01 <;> cases e10 <;> cases e11 <;>
    norm_num [score,coefficients] <;> linarith

theorem minimal_iff (t a w l : ℝ) (ht : 0 ≤ t) (ha : 0 ≤ a)
    (hw : 0 ≤ w) (hl : 0 ≤ l) (c : Candidate) :
    minimal t a w l c ↔ score t a w l c = min w (min t a) := by
  constructor
  · intro h
    have h1 := h (true,true,true,false,false,true)
    have h2 := h (true,false,true,false,false,true)
    have h3 := h (true,true,false,false,false,true)
    have s1 : score t a w l (true,true,true,false,false,true) = w := by norm_num [score,coefficients]
    have s2 : score t a w l (true,false,true,false,false,true) = t := by norm_num [score,coefficients]
    have s3 : score t a w l (true,true,false,false,false,true) = a := by norm_num [score,coefficients]
    rw [s1] at h1
    rw [s2] at h2
    rw [s3] at h3
    exact le_antisymm (le_min h1 (le_min h2 h3)) (lower_bound t a w l ht ha hw hl c)
  · intro h d
    rw [h]
    exact lower_bound t a w l ht ha hw hl d

theorem bad_lower (t a w l : ℝ) (_ht : 0 ≤ t) (ha : 0 ≤ a)
    (hw : 0 ≤ w) (hl : 0 ≤ l) (c : Candidate) (hc : ¬ good c) :
    w ≤ score t a w l c ∨ a+l*w ≤ score t a w l c := by
  have hprod := mul_nonneg hl hw
  rcases c with ⟨p,q,e00,e01,e10,e11⟩
  cases p <;> cases q <;> cases e00 <;> cases e01 <;> cases e10 <;> cases e11 <;>
    norm_num [good,coefficients] at hc <;> norm_num [score,coefficients] <;>
    first | left; linarith | right; linarith

theorem exact_region (t a w l : ℝ) (ht : 0 ≤ t) (ha : 0 ≤ a)
    (hw : 0 ≤ w) (hl : 0 ≤ l) :
    selects t a w l ↔ min t a < w ∧ min t a < a+l*w := by
  have hlow := lower_bound t a w l ht ha hw hl (true,true,true,true,true,false)
  have sr : score t a w l (true,true,true,true,true,false) = a+l*w := by norm_num [score,coefficients]
  rw [sr] at hlow
  constructor
  · intro h
    have hw' : min t a < w := by
      by_contra hn
      have hwle : w ≤ min t a := le_of_not_gt hn
      have hb := h (true,true,true,false,false,true)
      have hm : minimal t a w l (true,true,true,false,false,true) := by
        rw [minimal_iff t a w l ht ha hw hl]
        norm_num [score,coefficients,min_eq_left hwle]
      have hg := hb hm
      norm_num [good,coefficients] at hg
    refine ⟨hw',?_⟩
    rw [min_eq_right (le_of_lt hw')] at hlow
    by_contra hn
    have he : a+l*w = min t a := le_antisymm (le_of_not_gt hn) hlow
    have hm : minimal t a w l (true,true,true,true,true,false) := by
      rw [minimal_iff t a w l ht ha hw hl,min_eq_right (le_of_lt hw')]
      norm_num [score,coefficients]
      exact he
    have hg := h (true,true,true,true,true,false) hm
    norm_num [good,coefficients] at hg
  · rintro ⟨hw',hr'⟩ c hc
    rw [minimal_iff t a w l ht ha hw hl,min_eq_right (le_of_lt hw')] at hc
    by_contra hn
    rcases bad_lower t a w l ht ha hw hl c hn with hb | hb <;> linarith

theorem expanded_zero_boundary_counterexample : ¬ selects 2 1 2 0 := by
  rw [exact_region 2 1 2 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  norm_num


end OCPGraphRegion
