                                  
import PhonologicalCalculus.ContinuousHG.PhaseProfile
import PhonologicalCalculus.ContinuousHG.UniformLattice

namespace PhonologicalCalculus.ContinuousHG

theorem quadratic_phase_four_iff_ratio_cell
    {h m : ℝ} (hh : 0 < h) (hm : 0 < m) :
    QuadraticPhaseCell h m 4 ↔ 3 < h / m ∧ h / m ≤ 5 := by
  unfold QuadraticPhaseCell
  constructor
  · rintro ⟨_, _, _, hlower, hupper⟩
    constructor
    · rw [lt_div_iff₀ hm]
      norm_num at hlower ⊢
      linarith
    · rw [div_le_iff₀ hm]
      norm_num at hupper ⊢
      linarith
  · rintro ⟨hlower, hupper⟩
    refine ⟨by norm_num, hh, hm, ?_, ?_⟩
    · rw [lt_div_iff₀ hm] at hlower
      norm_num at hlower ⊢
      linarith
    · rw [div_le_iff₀ hm] at hupper
      norm_num at hupper ⊢
      linarith

theorem powered_gap_recovers_ratio
    {p rho gap indexGap : ℝ}
    (hp : 0 < p) (hrho : 0 < rho) (hindex : 0 < indexGap)
    (hgap : gap = indexGap / (p * rho)) :
    rho = indexGap / (p * gap) := by
  have hpRho : p * rho ≠ 0 := ne_of_gt (mul_pos hp hrho)
  have hgapPos : 0 < gap := by
    rw [hgap]
    positivity
  have hpGap : p * gap ≠ 0 := ne_of_gt (mul_pos hp hgapPos)
  field_simp [hpRho, hpGap] at hgap ⊢
  nlinarith

theorem powered_gap_pair_consistency
    {p rho gap₁ gap₂ indexGap₁ indexGap₂ : ℝ}
    (hp : 0 < p) (hrho : 0 < rho)
    (hi₁ : 0 < indexGap₁) (hi₂ : 0 < indexGap₂)
    (hg₁ : gap₁ = indexGap₁ / (p * rho))
    (hg₂ : gap₂ = indexGap₂ / (p * rho)) :
    indexGap₁ / (p * gap₁) = indexGap₂ / (p * gap₂) := by
  rw [← powered_gap_recovers_ratio hp hrho hi₁ hg₁,
    ← powered_gap_recovers_ratio hp hrho hi₂ hg₂]

theorem common_positive_scale_ratio
    {lambda h m : ℝ} (hlambda : 0 < lambda) (hm : 0 < m) :
    (lambda * h) / (lambda * m) = h / m := by
  have hlambda0 : lambda ≠ 0 := ne_of_gt hlambda
  have hm0 : m ≠ 0 := ne_of_gt hm
  field_simp [hlambda0, hm0]

theorem chg_b11_phase_01 :
    QuadraticPhaseCell 5 1 4 ∧ (3 : ℝ) < 5 / 1 ∧ 5 / 1 ≤ 5 := by
  norm_num [QuadraticPhaseCell]

theorem chg_b11_ratio_02 :
    let d₁ : ℝ := 2 / 5
    let d₂ : ℝ := 3 / 10
    1 / (2 * (d₁ - d₂)) = 5 := by
  norm_num

theorem chg_b11_triple_03 :
    let a : ℝ := 3 / 5
    let b : ℝ := 1 / 2
    let c : ℝ := 2 / 5
    (a / b) ^ (0 : ℝ) + (c / b) ^ (0 : ℝ) = 2 ∧
    (a / b) ^ (1 : ℝ) + (c / b) ^ (1 : ℝ) = 2 ∧
    b ^ 2 > a * c := by
  norm_num

theorem chg_b11_scale_04 (x y : List ℝ) :
    (35 : ℝ) / 7 = 5 / 1 ∧
    (pathHarmony quadraticPenalty 35 7 x ≤
        pathHarmony quadraticPenalty 35 7 y ↔
      pathHarmony quadraticPenalty 5 1 x ≤
        pathHarmony quadraticPenalty 5 1 y) := by
  constructor
  · norm_num
  · have hscale := chg_b7_common_scale_preorder quadraticPenalty
      (lambda := (7 : ℝ)) (by norm_num) 5 1 x y
    norm_num at hscale
    exact hscale

theorem chg_b11_algebraic_identifiability
    {p rho gap indexGap lambda h m : ℝ}
    (hp : 0 < p) (hrho : 0 < rho) (hindex : 0 < indexGap)
    (hgap : gap = indexGap / (p * rho))
    (hlambda : 0 < lambda) (hm : 0 < m) :
    rho = indexGap / (p * gap) ∧
      (lambda * h) / (lambda * m) = h / m := by
  exact ⟨powered_gap_recovers_ratio hp hrho hindex hgap,
    common_positive_scale_ratio hlambda hm⟩

end PhonologicalCalculus.ContinuousHG
