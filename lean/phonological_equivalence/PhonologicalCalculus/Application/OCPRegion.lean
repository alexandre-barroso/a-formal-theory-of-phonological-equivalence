        
import PhonologicalCalculus.Application.AccentRegion
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Prod

namespace OCPRegion

abbrev Candidate := Bool × Bool × Fin 3 × Fin 3

def coefficients (c : Candidate) : Nat × Nat × Nat × Nat :=
  ((if c.1 then 0 else 1) + (if c.2.1 then 0 else 1),
   (if c.2.2.1 = 0 then 0 else 1) + (if c.2.2.2 = 1 then 0 else 1),
   if c.1 && c.2.1 && c.2.2.1 == 0 && c.2.2.2 == 1 then 1 else 0,
   if c.1 && c.2.1 && c.2.2.1 == 1 && c.2.2.2 == 0 then 1 else 0)

noncomputable def score (t a w l : ℝ) (c : Candidate) : ℝ :=
  let q := coefficients c
  q.1*t + q.2.1*a + q.2.2.1*w + q.2.2.2*l*w

def good (c : Candidate) : Prop :=
  ¬ (c.1 = true ∧ c.2.1 = true ∧
    ((c.2.2.1 = 0 ∧ c.2.2.2 = 1) ∨ (c.2.2.1 = 1 ∧ c.2.2.2 = 0)))

instance (c : Candidate) : Decidable (good c) :=
  inferInstanceAs (Decidable (¬ _))

def minimal (t a w l : ℝ) (c : Candidate) : Prop :=
  ∀ d, score t a w l c ≤ score t a w l d

def selects (t a w l : ℝ) : Prop :=
  ∀ c, minimal t a w l c → good c

theorem candidate_count : Fintype.card Candidate = 36 := by decide

theorem lower_bound (t a w l : ℝ) (ht : 0 ≤ t) (ha : 0 ≤ a)
    (hw : 0 ≤ w) (hl : 0 ≤ l) (c : Candidate) :
    min w (min t a) ≤ score t a w l c := by
  have h1 := min_le_left w (min t a)
  have h2 := (min_le_right w (min t a)).trans (min_le_left t a)
  have h3 := (min_le_right w (min t a)).trans (min_le_right t a)
  have h4 := mul_nonneg hl hw
  generalize hm : min w (min t a) = m at h1 h2 h3 ⊢
  rcases c with ⟨p,q,i,j⟩
  cases p <;> cases q <;> fin_cases i <;> fin_cases j <;>
    norm_num [score, coefficients, Fin.ext_iff] <;> linarith

theorem minimal_iff (t a w l : ℝ) (ht : 0 ≤ t) (ha : 0 ≤ a)
    (hw : 0 ≤ w) (hl : 0 ≤ l) (c : Candidate) :
    minimal t a w l c ↔ score t a w l c = min w (min t a) := by
  constructor
  · intro h
    have h1 := h (true,true,0,1)
    have h2 := h (true,false,0,1)
    have h3 := h (true,true,2,1)
    have s1 : score t a w l (true,true,0,1) = w := by norm_num [score, coefficients, Fin.ext_iff]
    have s2 : score t a w l (true,false,0,1) = t := by norm_num [score, coefficients, Fin.ext_iff]
    have s3 : score t a w l (true,true,2,1) = a := by norm_num [score, coefficients, Fin.ext_iff]
    rw [s1] at h1
    rw [s2] at h2
    rw [s3] at h3
    exact le_antisymm (le_min h1 (le_min h2 h3)) (lower_bound t a w l ht ha hw hl c)
  · intro h d
    rw [h]
    exact lower_bound t a w l ht ha hw hl d

theorem bad_fiber (c : Candidate) :
    ¬ good c ↔ c = (true,true,0,1) ∨ c = (true,true,1,0) := by
  rcases c with ⟨p,q,i,j⟩
  cases p <;> cases q <;> fin_cases i <;> fin_cases j <;> decide

theorem exact_region (t a w l : ℝ) (ht : 0 ≤ t) (ha : 0 ≤ a)
    (hw : 0 ≤ w) (hl : 0 ≤ l) :
    selects t a w l ↔ min t a < w ∧ min t a < 2*a+l*w := by
  have hlow := lower_bound t a w l ht ha hw hl (true,true,1,0)
  have sr : score t a w l (true,true,1,0) = 2*a+l*w := by norm_num [score, coefficients, Fin.ext_iff]
  rw [sr] at hlow
  have hb : ¬ good (true,true,0,1) := by decide
  have hr : ¬ good (true,true,1,0) := by decide
  constructor
  · intro h
    have hw' : min t a < w := by
      by_contra hn
      have hwle : w ≤ min t a := le_of_not_gt hn
      apply hb
      apply h
      rw [minimal_iff t a w l ht ha hw hl]
      norm_num [score, coefficients, min_eq_left hwle]
    refine ⟨hw', ?_⟩
    rw [min_eq_right (le_of_lt hw')] at hlow
    by_contra hn
    have he : 2*a+l*w = min t a := le_antisymm (le_of_not_gt hn) hlow
    apply hr
    apply h
    rw [minimal_iff t a w l ht ha hw hl]
    norm_num [score, coefficients, min_eq_right (le_of_lt hw')]
    exact he
  · rintro ⟨hw',hr'⟩ c hc
    rw [minimal_iff t a w l ht ha hw hl, min_eq_right (le_of_lt hw')] at hc
    by_contra hn
    rcases (bad_fiber c).mp hn with rfl | rfl <;>
      norm_num [score, coefficients, Fin.ext_iff] at hc <;> linarith

theorem reverse_minimum_iff (t a w l : ℝ) (ht : 0 ≤ t) (ha : 0 ≤ a)
    (hl : 0 ≤ l) (h : min t a < w) :
    2*a+l*w = min t a ↔ a = 0 ∧ l = 0 := by
  have hm : 0 ≤ min t a := le_min ht ha
  have hw : 0 < w := lt_of_le_of_lt hm h
  have hp := mul_nonneg hl (le_of_lt hw)
  have hma := min_le_right t a
  constructor
  · intro he
    have az : a = 0 := by linarith
    have pz : l*w = 0 := by rw [az] at he hma; linarith
    exact ⟨az,(mul_eq_zero.mp pz).resolve_right (ne_of_gt hw)⟩
  · rintro ⟨rfl,rfl⟩
    simp [min_eq_right ht]

theorem above_threshold_minimizers (t a w₁ w₂ l : ℝ) (ht : 0 ≤ t) (ha : 0 ≤ a)
    (hl : 0 ≤ l) (h₁ : min t a < w₁) (h₂ : min t a < w₂) (c : Candidate) :
    minimal t a w₁ l c ↔ minimal t a w₂ l c := by
  have hm : 0 ≤ min t a := le_min ht ha
  rw [minimal_iff t a w₁ l ht ha (le_trans hm (le_of_lt h₁)) hl,
      minimal_iff t a w₂ l ht ha (le_trans hm (le_of_lt h₂)) hl,
      min_eq_right (le_of_lt h₁), min_eq_right (le_of_lt h₂)]
  have hr := (reverse_minimum_iff t a w₁ l ht ha hl h₁).trans
    (reverse_minimum_iff t a w₂ l ht ha hl h₂).symm
  rcases c with ⟨p,q,i,j⟩
  cases p <;> cases q <;> fin_cases i <;> fin_cases j <;>
    norm_num [score, coefficients, Fin.ext_iff] <;> first | exact hr | constructor <;> intro he <;> linarith

theorem zero_boundary_counterexample :
    ¬ selects 1 0 1 0 := by
  rw [exact_region 1 0 1 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  norm_num

end OCPRegion
