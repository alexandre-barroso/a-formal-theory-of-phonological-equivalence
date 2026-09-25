import PhonologicalOpacity.Attenuation.FreeWeights.Core
import PhonologicalOpacity.Gua.Select.G34b
import PhonologicalOpacity.Gua.Select.G37c
namespace FreeWeights
open Retained Deletion
set_option maxRecDepth 100000
theorem coeff_G34b_957 : coefficients g34b 0 957 = [(0,0),(1,0),(1,0),(0,0),(0,1),(0,0),(0,0),(0,0),(0,0)] := by decide +kernel
theorem coeff_G34b_1126 : coefficients g34b 0 1126 = [(0,0),(2,0),(1,0),(0,0),(0,0),(0,0),(0,0),(0,0),(0,0)] := by decide +kernel
theorem coeff_G37c_1584 : coefficients g37 0 1584 = [(0,0),(1,0),(0,0),(1,0),(0,1),(0,0),(0,0),(0,0),(0,0)] := by decide +kernel
theorem coeff_G37c_1571 : coefficients g37 0 1571 = [(0,0),(0,0),(0,0),(1,0),(1,0),(0,0),(0,0),(0,0),(0,0)] := by decide +kernel
theorem critical_G34b (w : Fin 9 → ℝ) (l : ℝ) :
    pressure g34b w l 1126 - pressure g34b w l 957 = w 1-l*w 4 := by
  simp [pressure, realPressure, coeff_G34b_957, coeff_G34b_1126, Fin.sum_univ_succ]
  ring

theorem critical_G37c (w : Fin 9 → ℝ) (l : ℝ) :
    pressure g37 w l 1571 - pressure g37 w l 1584 = (1-l)*w 4-w 1 := by
  simp [pressure, realPressure, coeff_G37c_1584, coeff_G37c_1571, Fin.sum_univ_succ]
  ring

theorem necessary_bound (w : Fin 9 → ℝ) (l : ℝ) (hw : 0 ≤ w 4)
    (h34 : Exclusive g34b (pressure g34b w l) "afɪsoohili")
    (h37 : Exclusive g37 (pressure g37 w l) "ɔtʃʊsejbie") : l < 1/2 := by
  have h34' : pressure g34b w l 957 < pressure g34b w l 1126 :=
    exclusive_strict h34 fiber_G34b (by decide) (by decide +kernel)
  have h37' : pressure g37 w l 1584 < pressure g37 w l 1571 :=
    exclusive_strict h37 fiber_G37c (by decide) (by decide +kernel)
  have ha := critical_G34b w l
  have hb := critical_G37c w l
  by_contra hn
  have hhalf : 1/2 ≤ l := le_of_not_gt hn
  have hprod : 0 ≤ (2*l-1)*w 4 := mul_nonneg (by linarith) hw
  nlinarith
end FreeWeights

