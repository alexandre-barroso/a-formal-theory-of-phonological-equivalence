import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace PhonologicalCalculus.Flux

noncomputable def periodicFluxGauge (delta epsilon y : ℝ) : ℝ :=
  y + epsilon * delta / (2 * Real.pi) *
    Real.sin ((2 * Real.pi / delta) * y)

noncomputable def periodicFluxPotential (c delta epsilon d : ℝ) : ℝ :=
  c * d ^ 2 / 2 + epsilon * delta ^ 2 / (4 * Real.pi ^ 2 * c) *
    (1 - Real.cos ((2 * Real.pi * c / delta) * d))

def ShiftEquivariant (F : ℝ → ℝ) (lambda : ℝ) : Prop :=
  ∀ y, F (y + lambda) = F y + lambda

def gaugeDeviation (F : ℝ → ℝ) (y : ℝ) : ℝ :=
  F y - y

def baselineResidual (lambda y z : ℝ) : ℝ :=
  y - z + lambda

def transformedResidual (F : ℝ → ℝ) (lambda y z : ℝ) : ℝ :=
  F y - F z + lambda

                   
theorem periodicFluxGauge_shift (delta epsilon y : ℝ) (hdelta : delta ≠ 0) :
    periodicFluxGauge delta epsilon (y + delta) -
        periodicFluxGauge delta epsilon y = delta := by
  have hangle :
      (2 * Real.pi / delta) * (y + delta) =
        (2 * Real.pi / delta) * y + 2 * Real.pi := by
    field_simp [hdelta]
  rw [periodicFluxGauge, periodicFluxGauge, hangle, Real.sin_add_two_pi]
  ring

theorem periodicFluxGauge_shiftEquivariant (delta epsilon : ℝ)
    (hdelta : delta ≠ 0) :
    ShiftEquivariant (periodicFluxGauge delta epsilon) delta := by
  intro y
  have h := periodicFluxGauge_shift delta epsilon y hdelta
  linarith

                   
theorem periodicFluxGauge_hasDerivAt (delta epsilon y : ℝ)
    (hdelta : delta ≠ 0) :
    HasDerivAt (periodicFluxGauge delta epsilon)
      (1 + epsilon * Real.cos (2 * Real.pi * y / delta)) y := by
  let A : ℝ := epsilon * delta / (2 * Real.pi)
  let B : ℝ := 2 * Real.pi / delta
  have hinner : HasDerivAt (fun x : ℝ => B * x) B y :=
    hasDerivAt_const_mul B
  have hsin : HasDerivAt (fun x : ℝ => Real.sin (B * x))
      (B * Real.cos (B * y)) y := by
    have hraw := hinner.sin
    exact hraw.congr_deriv (mul_comm _ _)
  have htotal : HasDerivAt
      (fun x : ℝ => x + A * Real.sin (B * x))
      (1 + A * (B * Real.cos (B * y))) y :=
    (hasDerivAt_id y).add (hsin.const_mul A)
  have hfunction : periodicFluxGauge delta epsilon =
      fun x : ℝ => x + A * Real.sin (B * x) := by
    funext x
    simp only [periodicFluxGauge]
    dsimp [A, B]
  rw [hfunction]
  apply htotal.congr_deriv
  dsimp [A, B]
  field_simp [hdelta, Real.pi_ne_zero]

                   
theorem periodicFluxGauge_strictMono {delta epsilon : ℝ}
    (hdelta : delta ≠ 0) (hepsilon : |epsilon| < 1) :
    StrictMono (periodicFluxGauge delta epsilon) := by
  apply strictMono_of_deriv_pos
  intro y
  rw [(periodicFluxGauge_hasDerivAt delta epsilon y hdelta).deriv]
  have hcos : |Real.cos (2 * Real.pi * y / delta)| ≤ 1 :=
    Real.abs_cos_le_one _
  have hproduct : |epsilon * Real.cos (2 * Real.pi * y / delta)| < 1 := by
    rw [abs_mul]
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hcos (abs_nonneg epsilon))
      (by simpa using hepsilon)
  have hlower : -1 < epsilon * Real.cos (2 * Real.pi * y / delta) :=
    (abs_lt.mp hproduct).1
  linarith

                   
theorem flux_d1_shift_01 {delta epsilon : ℝ}
    (hdelta : 0 < delta) (hepsilon : |epsilon| < 1) :
    (∀ y, periodicFluxGauge delta epsilon (y + delta) -
        periodicFluxGauge delta epsilon y = delta) ∧
      StrictMono (periodicFluxGauge delta epsilon) := by
  exact ⟨fun y => periodicFluxGauge_shift delta epsilon y hdelta.ne',
    periodicFluxGauge_strictMono hdelta.ne' hepsilon⟩

                       
theorem periodicFluxPotential_hasDerivAt
    (c delta epsilon d : ℝ) (hc : c ≠ 0) (_hdelta : delta ≠ 0) :
    HasDerivAt (periodicFluxPotential c delta epsilon)
      (periodicFluxGauge delta epsilon (c * d)) d := by
  let A : ℝ := epsilon * delta ^ 2 / (4 * Real.pi ^ 2 * c)
  let B : ℝ := 2 * Real.pi * c / delta
  have hquad : HasDerivAt (fun x : ℝ => c / 2 * x ^ 2) (c * d) d := by
    exact (((hasDerivAt_id d).pow 2).const_mul (c / 2)).congr_deriv
      (by simp; ring)
  have hinner : HasDerivAt (fun x : ℝ => B * x) B d :=
    hasDerivAt_const_mul B
  have hcos : HasDerivAt (fun x : ℝ => Real.cos (B * x))
      (-Real.sin (B * d) * B) d :=
    (Real.hasDerivAt_cos (B * d)).comp d hinner
  have hsecond : HasDerivAt
      (fun x : ℝ => A * (1 - Real.cos (B * x)))
      (A * (Real.sin (B * d) * B)) d := by
    exact (((hasDerivAt_const d 1).sub hcos).const_mul A).congr_deriv
      (by ring)
  have htotal := hquad.add hsecond
  have hfunction : periodicFluxPotential c delta epsilon =
      fun x : ℝ => c / 2 * x ^ 2 + A * (1 - Real.cos (B * x)) := by
    funext x
    simp only [periodicFluxPotential]
    dsimp [A, B]
    ring
  rw [hfunction]
  have hderiv : c * d + A * (Real.sin (B * d) * B) =
      periodicFluxGauge delta epsilon (c * d) := by
    dsimp [A, B, periodicFluxGauge]
    field_simp [hc, _hdelta, Real.pi_ne_zero]
    ring
  exact htotal.congr_deriv hderiv

                       
theorem periodicFluxPotential_zero (c delta epsilon : ℝ) :
    periodicFluxPotential c delta epsilon 0 = 0 := by
  simp [periodicFluxPotential]

                       
theorem flux_d1_potential_02 {c delta epsilon : ℝ}
    (hc : 0 < c) (hdelta : 0 < delta) :
    periodicFluxPotential c delta epsilon 0 = 0 ∧
      ∀ d, HasDerivAt (periodicFluxPotential c delta epsilon)
        (periodicFluxGauge delta epsilon (c * d)) d := by
  exact ⟨periodicFluxPotential_zero c delta epsilon,
    fun d => periodicFluxPotential_hasDerivAt c delta epsilon d hc.ne' hdelta.ne'⟩

          
theorem shiftEquivariant_iff_periodic_deviation (F : ℝ → ℝ) (lambda : ℝ) :
    ShiftEquivariant F lambda ↔
      Function.Periodic (gaugeDeviation F) lambda := by
  constructor
  · intro h y
    rw [gaugeDeviation, gaugeDeviation, h y]
    ring
  · intro h y
    have hp := h y
    rw [gaugeDeviation, gaugeDeviation] at hp
    linarith

theorem shiftEquivariant_iff_probe_zeros (F : ℝ → ℝ) (lambda : ℝ) :
    ShiftEquivariant F lambda ↔
      ∀ y, transformedResidual F lambda y (y + lambda) = 0 := by
  constructor
  · intro h y
    rw [transformedResidual, h y]
    ring
  · intro h y
    have hy := h y
    rw [transformedResidual] at hy
    linarith

                       
theorem flux_d1_necessity_04 (F : ℝ → ℝ) (lambda : ℝ) :
    (∀ y, transformedResidual F lambda y (y + lambda) = 0) ↔
      ShiftEquivariant F lambda := by
  exact (shiftEquivariant_iff_probe_zeros F lambda).symm

theorem residual_signs_preserved {F : ℝ → ℝ} {lambda : ℝ}
    (hmono : StrictMono F) (hshift : ShiftEquivariant F lambda) (y z : ℝ) :
    (transformedResidual F lambda y z < 0 ↔
        baselineResidual lambda y z < 0) ∧
    (transformedResidual F lambda y z = 0 ↔
        baselineResidual lambda y z = 0) ∧
    (0 < transformedResidual F lambda y z ↔
        0 < baselineResidual lambda y z) := by
  have hrewrite : transformedResidual F lambda y z = F (y + lambda) - F z := by
    rw [transformedResidual, hshift y]
    ring
  have hbase : baselineResidual lambda y z = y + lambda - z := by
    rw [baselineResidual]
    ring
  rw [hrewrite, hbase]
  constructor
  · simpa [sub_lt_zero] using hmono.lt_iff_lt
  · constructor
    · constructor
      · intro h
        have : F (y + lambda) = F z := sub_eq_zero.mp h
        exact sub_eq_zero.mpr (hmono.injective this)
      · intro h
        exact sub_eq_zero.mpr (congrArg F (sub_eq_zero.mp h))
    · simpa [sub_pos] using hmono.lt_iff_lt

noncomputable def candidateOrderReversalDifference : ℝ :=
  1 / 100 + (-9 + Real.sqrt 5) / (32 * Real.pi ^ 2)

                      
theorem flux_d1_reversal_03 :
    candidateOrderReversalDifference =
        1 / 100 + (-9 + Real.sqrt 5) / (32 * Real.pi ^ 2) ∧
      candidateOrderReversalDifference < 0 := by
  constructor
  · rfl
  · unfold candidateOrderReversalDifference
    have hpi0 : 0 < Real.pi := Real.pi_pos
    have hpi4 : Real.pi < 4 := Real.pi_lt_four
    have hpiSq : Real.pi ^ 2 < 16 := by nlinarith
    have hsqrtNonnegative : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
    have hsqrtSq : (Real.sqrt 5) ^ 2 = 5 := by norm_num
    have hsqrtThree : Real.sqrt 5 < 3 := by nlinarith
    have hden : 0 < 32 * Real.pi ^ 2 := by positivity
    have hnumerator :
        (32 * Real.pi ^ 2) / 100 + (-9 + Real.sqrt 5) < 0 := by
      nlinarith
    have hrearrange :
        1 / 100 + (-9 + Real.sqrt 5) / (32 * Real.pi ^ 2) =
          ((32 * Real.pi ^ 2) / 100 + (-9 + Real.sqrt 5)) /
            (32 * Real.pi ^ 2) := by
      field_simp [ne_of_gt hden]
    rw [hrearrange]
    exact div_neg_of_neg_of_pos hnumerator hden

                  
theorem flux_d2_star_02 :
    2 * periodicFluxGauge 1 (1 / 2) (-1 / 4) +
        periodicFluxGauge 1 (1 / 2) (-1 / 2) + 1 =
      -1 / (2 * Real.pi) ∧
    -1 / (2 * Real.pi) ≠ 0 := by
  constructor
  · unfold periodicFluxGauge
    rw [show (2 * Real.pi / 1) * (-1 / 4 : ℝ) = -Real.pi / 2 by ring,
      show (2 * Real.pi / 1) * (-1 / 2 : ℝ) = -Real.pi by ring]
    have hsQuarter : Real.sin (-Real.pi / 2) = -1 := by
      rw [show -Real.pi / 2 = -(Real.pi / 2) by ring,
        Real.sin_neg, Real.sin_pi_div_two]
    have hsHalf : Real.sin (-Real.pi) = 0 := by
      rw [Real.sin_neg, Real.sin_pi, neg_zero]
    rw [hsQuarter, hsHalf]
    field_simp [Real.pi_ne_zero]
    ring
  · have hden : (2 * Real.pi : ℝ) ≠ 0 :=
      mul_ne_zero (by norm_num) Real.pi_ne_zero
    simpa only [neg_div] using
      neg_ne_zero.mpr (div_ne_zero one_ne_zero hden)

                    
theorem flux_d2_period_01 :
    (1 / 5 : ℚ) / (1 / 105) = 21 ∧
      (1 / 21 : ℚ) / (1 / 105) = 5 := by
  norm_num

end PhonologicalCalculus.Flux
