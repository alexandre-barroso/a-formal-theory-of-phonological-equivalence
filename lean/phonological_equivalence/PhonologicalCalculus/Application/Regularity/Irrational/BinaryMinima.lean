                  
                   
import PhonologicalCalculus.Application.Regularity.Irrational.BinaryScore
import Mathlib.Computability.DFA

namespace NativeIrrational
noncomputable def minimum (u : List Bool) : ℝ := min (dp u).1 (dp u).2
def constant (u : List Bool) (b : Bool) : List (Bool × Bool) := u.map (fun x => (x,b))
@[simp] theorem input_constant (u : List Bool) (b : Bool) : input (constant u b) = u := by
  simp [input,constant,List.map_map,Function.comp_def]
@[simp] theorem constant_snoc (u : List Bool) (x b : Bool) :
    constant (u++[x]) b = constant u b ++ [(x,b)] := by simp [constant]

theorem last_constant (u : List Bool) (b : Bool) :
    lastOutput (constant u b) = if u=[] then none else some b := by
  induction u using List.reverseRecOn with
  | nil => simp [constant]
  | append_singleton u x ih => simp

theorem constant_score (u : List Bool) (b : Bool) :
    score (constant u b) = coord (unaryTotals u) b := by
  induction u using List.reverseRecOn with
  | nil => simp [constant,unaryTotals,coord]
  | append_singleton u x ih =>
    rw [constant_snoc,score_snoc,ih,last_constant]
    have h : switch (if u=[] then none else some b) b = 0 := by
      split <;> simp [switch]
    rw [h]
    cases b <;> simp [unaryTotals,coord]

theorem dp_attained (u : List Bool) :
    ∀ b, ∃ w, input w=u ∧ score w=coord (dp u) b ∧ (u≠[] → lastOutput w=some b) := by
  induction u using List.reverseRecOn with
  | nil => intro b; refine ⟨[],rfl,?_,by simp⟩; cases b <;> simp [dp,coord]
  | append_singleton u x ih =>
    intro b
    by_cases hu : u=[]
    · subst u
      refine ⟨[(x,b)],by simp [input],?_,by simp [lastOutput,finalRun,run]⟩
      cases b <;> simp [score,finalRun,run,switch,dp,step,coord]
    · by_cases h : coord (dp u) b ≤ coord (dp u) (!b)+8
      · obtain ⟨w,hw,hc,hl⟩ := ih b
        refine ⟨w++[(x,b)],by simp [hw],?_,by simp⟩
        rw [score_snoc,hc,hl hu,dp_snoc,step_coord,min_eq_left h]
        simp [switch]
      · obtain ⟨w,hw,hc,hl⟩ := ih (!b)
        refine ⟨w++[(x,b)],by simp [hw],?_,by simp⟩
        rw [score_snoc,hc,hl hu,dp_snoc,step_coord,min_eq_right (le_of_not_ge h)]
        have hn : (!b) ≠ b := by cases b <;> decide
        simp only [switch,if_neg hn]
        ring

theorem minimum_exact (u : List Bool) :
    (∃ w, input w=u ∧ score w=minimum u) ∧
    ∀ w, input w=u → minimum u ≤ score w := by
  constructor
  · by_cases h : (dp u).1 ≤ (dp u).2
    · obtain ⟨w,hw,hc,_⟩ := dp_attained u false
      exact ⟨w,hw,by simpa [minimum,coord,min_eq_left h] using hc⟩
    · obtain ⟨w,hw,hc,_⟩ := dp_attained u true
      exact ⟨w,hw,by simpa [minimum,coord,min_eq_right (le_of_not_ge h)] using hc⟩
  · intro w hw
    simpa only [← hw,minimum] using dp_min_lower w

def stablePrefixes (u : List Bool) : Prop :=
  ∀ j, -8 ≤ balance (u.take j) ∧ balance (u.take j) ≤ 8

theorem dp_stable (u : List Bool) (h : stablePrefixes u) : dp u = unaryTotals u := by
  induction u using List.reverseRecOn with
  | nil => rfl
  | append_singleton u x ih =>
    have hp : stablePrefixes u := by
      intro j
      by_cases hj : j ≤ u.length
      · simpa only [List.take_append_of_le_length hj] using h j
      · have hl := h u.length
        rw [List.take_append_of_le_length (le_refl _),List.take_length] at hl
        simpa only [List.take_of_length_le (by omega : u.length ≤ j)] using hl
    have he := h u.length
    rw [List.take_append_of_le_length (le_refl _),List.take_length,← totals_balance] at he
    rw [dp_snoc,ih hp]
    have ha : (unaryTotals u).1 ≤ (unaryTotals u).2 + 8 := by linarith [he.2]
    have hb : (unaryTotals u).2 ≤ (unaryTotals u).1 + 8 := by linarith [he.1]
    simp only [step,min_eq_left ha,min_eq_left hb]
    simp [unaryTotals]

def winnerLanguage : Language (Bool × Bool) :=
  {w | ∀ v, input v=input w → score w ≤ score v}
def constantLanguage : Language Bool := {u | constant u false ∈ winnerLanguage}

theorem winner_iff_minimum (w : List (Bool × Bool)) :
    w ∈ winnerLanguage ↔ score w = minimum (input w) := by
  constructor
  · intro h
    obtain ⟨v,hv,hc⟩ := (minimum_exact (input w)).1
    apply le_antisymm
    · rw [← hc]; exact h v hv
    · exact (minimum_exact (input w)).2 w rfl
  · intro h v hv
    rw [h]
    exact (minimum_exact (input w)).2 v hv

theorem constant_winner_stable (u : List Bool) (h : stablePrefixes u) :
    u ∈ constantLanguage ↔ balance u ≤ 0 := by
  change constant u false ∈ winnerLanguage ↔ _
  rw [winner_iff_minimum,constant_score,input_constant]
  simp only [minimum,dp_stable u h,coord,Bool.false_eq_true,ite_false]
  rw [eq_comm,min_eq_left_iff]
  have hb := totals_balance u
  constructor
  · intro hp; linarith
  · intro hp; linarith

theorem word_stable (n : ℕ) : stablePrefixes (word n) := by
  intro j
  have h := prefix_word_bounds n j
  constructor <;> linarith [beta_bounds.2]

theorem concat_stable (n k : ℕ) : stablePrefixes (word n ++ suffix k) := by
  intro j
  have h := prefix_concat_bounds n k j
  constructor <;> linarith [beta_bounds.2]
end NativeIrrational
