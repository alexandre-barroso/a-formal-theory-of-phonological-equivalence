                        
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace PhonologicalCalculus.SchwaAttenuation

def wordLogit (l S B G M D C x y : ℝ) : ℝ :=
  C*(1-x)+B*x+G*y-l*S-D

def cliticLogit (l S B G M D C x y : ℝ) : ℝ :=
  l*(C*(1-x)+B*x+G*y)+M-S

theorem full_chart_projection (l S B G M D C x y : ℝ) :
    wordLogit l S B G M D C x y = (C-l*S-D)+(B-C)*x+G*y ∧
    cliticLogit l S B G M D C x y = (l*C+M-S)+l*(B-C)*x+l*G*y := by
  constructor <;> simp only [wordLogit, cliticLogit] <;> ring

theorem cluster_contrast (l S B G M D C y : ℝ) :
    wordLogit l S B G M D C 1 y - wordLogit l S B G M D C 0 y = B-C ∧
    cliticLogit l S B G M D C 1 y - cliticLogit l S B G M D C 0 y = l*(B-C) := by
  constructor <;> simp only [wordLogit, cliticLogit] <;> ring

theorem stress_contrast (l S B G M D C x : ℝ) :
    wordLogit l S B G M D C x 1 - wordLogit l S B G M D C x 0 = G ∧
    cliticLogit l S B G M D C x 1 - cliticLogit l S B G M D C x 0 = l*G := by
  constructor <;> simp only [wordLogit, cliticLogit] <;> ring

theorem common_effect_identity (l S B G M D C x₀ x₁ y₀ y₁ : ℝ) :
    cliticLogit l S B G M D C x₁ y₁ - cliticLogit l S B G M D C x₀ y₀ =
    l * (wordLogit l S B G M D C x₁ y₁ - wordLogit l S B G M D C x₀ y₀) := by
  simp only [wordLogit, cliticLogit]
  ring

theorem nonzero_contrast_identifies (l₁ l₂ b : ℝ) (hb : b ≠ 0)
    (h : l₁*b = l₂*b) : l₁=l₂ := by
  exact mul_right_cancel₀ hb h

theorem restricted_chart_nonpositive (l S B G M : ℝ) (hl : 0 ≤ l) (hS : 0 ≤ S) :
    wordLogit l S B G M 0 0 0 0 ≤ 0 := by
  simp only [wordLogit]
  nlinarith [mul_nonneg hl hS]

theorem full_chart_positive_witness (l : ℝ) :
    wordLogit l 0 0 0 0 0 1 0 0 = 1 := by
  simp [wordLogit]

theorem full_chart_interior (l aW aC beta gamma : ℝ)
    (hl : 0 ≤ l) (hl1 : l < 1) (hg : 0 ≤ gamma) :
    ∃ S B G M D C : ℝ,
      0 ≤ S ∧ 0 ≤ B ∧ 0 ≤ G ∧ 0 ≤ M ∧ 0 ≤ D ∧ 0 ≤ C ∧
      (∀ x y, wordLogit l S B G M D C x y = aW+beta*x+gamma*y) ∧
      (∀ x y, cliticLogit l S B G M D C x y = aC+l*beta*x+l*gamma*y) := by
  have hp : 0 < 1-l*l := by nlinarith
  let C := max 0 (max (-beta) (max aW ((aW-l*aC)/(1-l*l))))
  have hc0 : 0 ≤ C := le_max_left _ _
  have hcb : -beta ≤ C := le_trans (le_max_left _ _) (le_max_right _ _)
  have hcw : aW ≤ C := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hcf : (aW-l*aC)/(1-l*l) ≤ C :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hc : aW-l*aC ≤ C*(1-l*l) := (div_le_iff₀ hp).mp hcf
  let S := max 0 (l*C-aC)
  have hs0 : 0 ≤ S := le_max_left _ _
  have hsm : l*C-aC ≤ S := le_max_right _ _
  have hd : 0 ≤ C-l*S-aW := by
    by_cases h : 0 ≤ l*C-aC
    · have hs : S=l*C-aC := max_eq_right h
      rw [hs]
      nlinarith only [hc]
    · have hs : S=0 := max_eq_left (le_of_not_ge h)
      rw [hs]
      linarith
  refine ⟨S,beta+C,gamma,aC-l*C+S,C-l*S-aW,C,hs0,?_,hg,?_,hd,hc0,?_,?_⟩
  · linarith
  · linarith
  · intro x y
    simp only [wordLogit]
    ring
  · intro x y
    simp only [cliticLogit]
    ring

theorem full_chart_endpoint_necessary (S B G M D C : ℝ) (hM : 0 ≤ M) (hD : 0 ≤ D) :
    wordLogit 1 S B G M D C 0 0 ≤ cliticLogit 1 S B G M D C 0 0 := by
  simp only [wordLogit, cliticLogit]
  linarith

theorem full_chart_endpoint_sufficient (aW aC beta gamma : ℝ)
    (h : aW ≤ aC) (hg : 0 ≤ gamma) :
    ∃ S B G M D C : ℝ,
      0 ≤ S ∧ 0 ≤ B ∧ 0 ≤ G ∧ 0 ≤ M ∧ 0 ≤ D ∧ 0 ≤ C ∧
      (∀ x y, wordLogit 1 S B G M D C x y = aW+beta*x+gamma*y) ∧
      (∀ x y, cliticLogit 1 S B G M D C x y = aC+beta*x+gamma*y) := by
  let C := max 0 (max (-beta) aW)
  have hc0 : 0 ≤ C := le_max_left _ _
  have hcb : -beta ≤ C := le_trans (le_max_left _ _) (le_max_right _ _)
  have hcw : aW ≤ C := le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨C-aW,beta+C,gamma,aC-aW,0,C,?_,?_,hg,?_,le_refl _,hc0,?_,?_⟩
  · linarith
  · linarith
  · linarith
  · intro x y
    simp only [wordLogit]
    ring
  · intro x y
    simp only [cliticLogit]
    ring

noncomputable def probabilityFromOdds (o : ℝ) : ℝ := o/(1+o)
noncomputable def oddsFromProbability (p : ℝ) : ℝ := p/(1-p)

theorem pooled_attenuation_counterexample :
    (probabilityFromOdds (1/3) + probabilityFromOdds 3)/2 = 1/2 ∧
    (probabilityFromOdds 3 + probabilityFromOdds 27)/2 = 6/7 ∧
    (probabilityFromOdds 1 + probabilityFromOdds 9)/2 = 7/10 ∧
    (oddsFromProbability (7/10))^2 ≠ oddsFromProbability (6/7) := by
  norm_num [probabilityFromOdds, oddsFromProbability]

theorem aligned_labels_indistinguishable {Obs Label Result : Type*}
    (process task : Obs → Label) (h : ∀ o, process o = task o)
    (kernel : Obs → Label → Result) :
    (fun o => kernel o (process o)) = (fun o => kernel o (task o)) := by
  funext o
  rw [h o]

noncomputable def binaryProbability (hZero hSchwa : ℝ) : ℝ :=
  Real.exp (-hSchwa) / (Real.exp (-hZero) + Real.exp (-hSchwa))

theorem binary_logit (hZero hSchwa : ℝ) :
    Real.log (oddsFromProbability (binaryProbability hZero hSchwa)) = hZero-hSchwa := by
  have h0 := Real.exp_pos (-hZero)
  have h1 := Real.exp_pos (-hSchwa)
  have hden : Real.exp (-hZero) + Real.exp (-hSchwa) ≠ 0 := by positivity
  have hratio : oddsFromProbability (binaryProbability hZero hSchwa) =
      Real.exp (-hSchwa) / Real.exp (-hZero) := by
    unfold oddsFromProbability binaryProbability
    field_simp
    ring
  rw [hratio, Real.log_div h1.ne' h0.ne', Real.log_exp, Real.log_exp]
  ring

theorem individual_half_attenuation (o : ℝ) (ho : 0 < o) :
    Real.log (3*o)-Real.log o = (1/2:ℝ)*(Real.log (9*o)-Real.log o) := by
  rw [Real.log_mul (by norm_num) ho.ne', Real.log_mul (by norm_num) ho.ne']
  have h : Real.log (9:ℝ) = 2*Real.log 3 := by
    simpa only [show (3:ℝ)^2=9 by norm_num, Nat.cast_ofNat] using Real.log_pow (3:ℝ) 2
  rw [h]
  ring

theorem pooled_half_attenuation_fails :
    Real.log (oddsFromProbability (7/10)) - Real.log (oddsFromProbability (1/2)) ≠
      (1/2:ℝ)*(Real.log (oddsFromProbability (6/7)) - Real.log (oddsFromProbability (1/2))) := by
  norm_num [oddsFromProbability]
  intro h
  have hp : Real.log ((7/3:ℝ)^2) = Real.log (6:ℝ) := by
    rw [Real.log_pow]
    norm_num
    linarith
  have he : (7/3:ℝ)^2 = 6 := Real.log_injOn_pos (by norm_num) (by norm_num) hp
  norm_num at he

theorem word_probability_law (l S B G M D C x y : ℝ) :
    Real.log (oddsFromProbability (binaryProbability (C*(1-x)+B*x+G*y) (l*S+D))) =
      wordLogit l S B G M D C x y := by
  rw [binary_logit]
  simp only [wordLogit]
  ring

theorem clitic_probability_law (l S B G M D C x y : ℝ) :
    Real.log (oddsFromProbability (binaryProbability (l*(C*(1-x)+B*x+G*y)+M) S)) =
      cliticLogit l S B G M D C x y := by
  rw [binary_logit]
  rfl

end PhonologicalCalculus.SchwaAttenuation
