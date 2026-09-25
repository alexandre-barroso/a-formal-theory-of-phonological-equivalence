                                       
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

namespace PhonologicalGrounding.Predictions.Threshold

noncomputable def idPlusG (n : ℚ) : ℚ := 1 - 1 / n

noncomputable def opaquePenalty (g m q : ℚ) (_v1 v3 : ℚ) : ℚ :=
  g * idPlusG (v3 + 1) + m + q

noncomputable def transparentPenalty (g q : ℚ) (v1 v3 : ℚ) : ℚ :=
  g * idPlusG (v1 + v3 + 1) + q

noncomputable def thresholdRatio (v1 v3 : ℚ) : ℚ :=
  v1 / ((v3 + 1) * (v1 + v3 + 1))

theorem opaque_lt_transparent_iff (g m q v1 v3 : ℚ)
    (h1 : 1 ≤ v1) (h3 : 0 ≤ v3) :
    opaquePenalty g m q v1 v3 < transparentPenalty g q v1 v3
      ↔ m * ((v3 + 1) * (v1 + v3 + 1)) < g * v1 := by
  have ha : (0 : ℚ) < v3 + 1 := by linarith
  have hb : (0 : ℚ) < v1 + v3 + 1 := by linarith
  unfold opaquePenalty transparentPenalty idPlusG
  rw [show g * (1 - 1 / (v3 + 1)) + m + q < g * (1 - 1 / (v1 + v3 + 1)) + q
        ↔ m < g * (1 / (v3 + 1)) - g * (1 / (v1 + v3 + 1)) by constructor <;> intro h <;> linarith]
  rw [show g * (1 / (v3 + 1)) - g * (1 / (v1 + v3 + 1))
        = g * v1 / ((v3 + 1) * (v1 + v3 + 1)) by field_simp; ring]
  rw [lt_div_iff₀ (by positivity)]

theorem opaque_lt_transparent_iff_ratio (g m q v1 v3 : ℚ)
    (hg : 0 < g) (h1 : 1 ≤ v1) (h3 : 0 ≤ v3) :
    opaquePenalty g m q v1 v3 < transparentPenalty g q v1 v3
      ↔ m / g < thresholdRatio v1 v3 := by
  have ha : (0 : ℚ) < v3 + 1 := by linarith
  have hb : (0 : ℚ) < v1 + v3 + 1 := by linarith
  rw [opaque_lt_transparent_iff g m q v1 v3 h1 h3, thresholdRatio,
    div_lt_div_iff₀ hg (by positivity)]
  constructor <;> intro h <;> nlinarith [h]

theorem thresholdRatio_antitone_in_v3 (v1 v3 : ℚ) (h1 : 1 ≤ v1) (h3 : 0 ≤ v3) :
    thresholdRatio v1 (v3 + 1) < thresholdRatio v1 v3 := by
  have ha : (0 : ℚ) < v3 + 1 := by linarith
  have hb : (0 : ℚ) < v1 + v3 + 1 := by linarith
  unfold thresholdRatio
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith [h1, h3]

theorem thresholdRatio_monotone_in_v1 (v1 v3 : ℚ) (h1 : 1 ≤ v1) (h3 : 0 ≤ v3) :
    thresholdRatio v1 v3 < thresholdRatio (v1 + 1) v3 := by
  have ha : (0 : ℚ) < v3 + 1 := by linarith
  have hb : (0 : ℚ) < v1 + v3 + 1 := by linarith
  unfold thresholdRatio
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith [h1, h3]

theorem eventually_transparent (g m : ℚ) (hg : 0 ≤ g) (hm : 0 < m)
    (v1 : ℚ) (h1 : 1 ≤ v1) :
    ∃ V : ℚ, 0 ≤ V ∧ ∀ v3 : ℚ, V ≤ v3 →
      ¬ (m * ((v3 + 1) * (v1 + v3 + 1)) < g * v1) := by
  refine ⟨max 0 (g * v1 / m), le_max_left _ _, fun v3 hv3 => ?_⟩
  have h3 : (0 : ℚ) ≤ v3 := le_trans (le_max_left _ _) hv3
  have hge : g * v1 / m ≤ v3 := le_trans (le_max_right _ _) hv3
  have hbase : g * v1 ≤ m * v3 := by
    rw [div_le_iff₀ hm] at hge; linarith
  have hfac : m * v3 ≤ m * ((v3 + 1) * (v1 + v3 + 1)) := by
    have : v3 ≤ (v3 + 1) * (v1 + v3 + 1) := by nlinarith
    exact mul_le_mul_of_nonneg_left this (le_of_lt hm)
  intro hcontra
  linarith

theorem development_bound : thresholdRatio 2 3 = 1 / 12 := by
  norm_num [thresholdRatio]

theorem cell_ratios :
    thresholdRatio 1 2 = 1 / 12 ∧ thresholdRatio 1 3 = 1 / 20 ∧
    thresholdRatio 1 4 = 1 / 30 ∧ thresholdRatio 2 2 = 2 / 15 ∧
    thresholdRatio 2 3 = 1 / 12 ∧ thresholdRatio 2 4 = 2 / 35 := by
  norm_num [thresholdRatio]

theorem forced_opaque_cells :
    (1 : ℚ) / 12 ≤ thresholdRatio 1 2 ∧
    (1 : ℚ) / 12 ≤ thresholdRatio 2 2 ∧
    (1 : ℚ) / 12 ≤ thresholdRatio 2 3 := by
  norm_num [thresholdRatio]

theorem informative_cells :
    thresholdRatio 1 3 < (1 : ℚ) / 12 ∧
    thresholdRatio 1 4 < (1 : ℚ) / 12 ∧
    thresholdRatio 2 4 < (1 : ℚ) / 12 := by
  norm_num [thresholdRatio]

theorem equivalence_corner (r : ℚ) (hr : 0 < r) (hlt : r < 1 / 30) :
    r < thresholdRatio 1 2 ∧ r < thresholdRatio 1 3 ∧ r < thresholdRatio 1 4 ∧
    r < thresholdRatio 2 2 ∧ r < thresholdRatio 2 3 ∧ r < thresholdRatio 2 4 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> · rw [thresholdRatio]; norm_num; linarith

theorem thresholdRatio_pos (v1 v3 : ℚ) (h1 : 1 ≤ v1) (h3 : 0 ≤ v3) :
    0 < thresholdRatio v1 v3 := by
  unfold thresholdRatio
  have : (0 : ℚ) < (v3 + 1) * (v1 + v3 + 1) := by positivity
  exact div_pos (by linarith) this

theorem exists_admitted_ratio_below_all (cells : List (ℚ × ℚ))
    (hcells : ∀ c ∈ cells, 1 ≤ c.1 ∧ 0 ≤ c.2) :
    ∃ r : ℚ, 0 < r ∧ r < 1 / 12 ∧ ∀ c ∈ cells, r < thresholdRatio c.1 c.2 := by
  induction cells with
  | nil => exact ⟨1 / 24, by norm_num, by norm_num, fun c hc => absurd hc (List.not_mem_nil)⟩
  | cons c cs ih =>
      obtain ⟨r, hr0, hr12, hr⟩ := ih (fun d hd => hcells d (List.mem_cons_of_mem c hd))
      have hc := hcells c (List.mem_cons_self ..)
      have hpos := thresholdRatio_pos c.1 c.2 hc.1 hc.2
      refine ⟨min r (thresholdRatio c.1 c.2 / 2), ?_, ?_, ?_⟩
      · exact lt_min hr0 (by linarith)
      · exact lt_of_le_of_lt (min_le_left _ _) hr12
      · intro d hd
        rcases List.mem_cons.mp hd with rfl | hd
        · exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
        · exact lt_of_le_of_lt (min_le_left _ _) (hr d hd)

end PhonologicalGrounding.Predictions.Threshold
