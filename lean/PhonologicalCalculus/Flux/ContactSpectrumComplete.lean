import PhonologicalCalculus.Flux.ContactResponse
import PhonologicalCalculus.Flux.PeriodicGauge
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Data.Nat.Choose.Central

/-!
# Complete odd contact spectrum

This module formalizes the analytic-order core of the raised-cosine response
spectrum used by `FLUX-D4`.  The marginal family is normalized separately
from its primitive so that every algebraic dependency is visible: the sine
factor has order one, its even power has order `2 * r`, and any analytic
primitive with this derivative has contact order `2 * r + 1`.

The normalization is positive and therefore cannot change the contact order.
The final theorem is stated for an arbitrary analytic primitive satisfying the
displayed derivative identity; a constructive trigonometric primitive and its
translation law are developed below.
-/

namespace PhonologicalCalculus.Flux

open Filter Set
open scoped ENNReal Topology

/-- The positive normalization `4^r / choose (2r,r)` in the sine form of the
raised-cosine marginal. -/
noncomputable def oddContactScale (r : ℕ) : ℝ :=
  (4 : ℝ) ^ r / (Nat.choose (2 * r) r : ℝ)

/-- The normalized analytic marginal.  It is equivalent to
`(1 - cos (2*pi*z/lambda))^r / (choose (2r,r)/2^r)`. -/
noncomputable def oddContactMarginal (lambda : ℝ) (r : ℕ) (z : ℝ) : ℝ :=
  oddContactScale r * Real.sin (Real.pi / lambda * z) ^ (2 * r)

/-- Equation (D4.6) in its printed raised-cosine normalization. -/
noncomputable def raisedCosineMarginal (lambda : ℝ) (r : ℕ) (z : ℝ) : ℝ :=
  (1 - Real.cos (2 * Real.pi / lambda * z)) ^ r /
    ((Nat.choose (2 * r) r : ℝ) / (2 : ℝ) ^ r)

theorem oddContactScale_pos (r : ℕ) : 0 < oddContactScale r := by
  unfold oddContactScale
  have hchoose : 0 < Nat.choose (2 * r) r := Nat.choose_pos (by omega)
  exact div_pos (pow_pos (by norm_num) r) (by exact_mod_cast hchoose)

theorem oddContactScale_ne_zero (r : ℕ) : oddContactScale r ≠ 0 :=
  (oddContactScale_pos r).ne'

/-- Successive central-binomial normalizers obey the integration-by-parts
recurrence used by the constructive primitive. -/
theorem oddContactScale_succ_relation (r : ℕ) :
    oddContactScale (r + 1) * (2 * r + 1) =
      oddContactScale r * (2 * r + 2) := by
  have hcentral := Nat.succ_mul_centralBinom_succ r
  have hcentralReal :
      ((r + 1 : ℕ) : ℝ) * (Nat.centralBinom (r + 1) : ℝ) =
        2 * (2 * (r : ℝ) + 1) * (Nat.centralBinom r : ℝ) := by
    exact_mod_cast hcentral
  have hcurr : (Nat.centralBinom r : ℝ) ≠ 0 := by
    exact_mod_cast Nat.centralBinom_ne_zero r
  have hnext : (Nat.centralBinom (r + 1) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.centralBinom_ne_zero (r + 1)
  have hcurrChoose : (Nat.choose (2 * r) r : ℝ) ≠ 0 := by
    simpa [Nat.centralBinom] using hcurr
  have hnextChoose :
      (Nat.choose (2 * (r + 1)) (r + 1) : ℝ) ≠ 0 := by
    simpa [Nat.centralBinom] using hnext
  simp only [Nat.centralBinom] at hcentralReal
  unfold oddContactScale
  field_simp [hcurrChoose, hnextChoose]
  rw [pow_succ]
  norm_num at hcentralReal ⊢
  linear_combination -2 * 4 ^ r * hcentralReal

/-- The sine-power and raised-cosine presentations are exactly equal.  This
bridge prevents the Lean construction from silently changing equation
`(D4.6)`. -/
theorem raisedCosineMarginal_eq_oddContactMarginal
    (lambda : ℝ) (r : ℕ) (z : ℝ) :
    raisedCosineMarginal lambda r z = oddContactMarginal lambda r z := by
  have hchoose : (Nat.choose (2 * r) r : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos (by omega : r ≤ 2 * r)))
  unfold raisedCosineMarginal oddContactMarginal oddContactScale
  rw [show 2 * Real.pi / lambda * z =
      2 * (Real.pi / lambda * z) by ring,
    Real.cos_two_mul_eq_one_sub]
  rw [show 1 - (1 - 2 * Real.sin (Real.pi / lambda * z) ^ 2) =
      2 * Real.sin (Real.pi / lambda * z) ^ 2 by ring,
    mul_pow, ← pow_mul]
  field_simp [hchoose]
  have hpow : (2 : ℝ) ^ (r * 2) = 4 ^ r := by
    rw [pow_mul']
    norm_num
  have hpow' : ((2 : ℝ) ^ r) ^ 2 = 4 ^ r := by
    rw [← pow_mul, hpow]
  rw [hpow']
  ring

/-- The trigonometric correction appearing in the primitive recursion. -/
noncomputable def oddContactCorrection
    (lambda : ℝ) (r : ℕ) (z : ℝ) : ℝ :=
  Real.sin (Real.pi / lambda * z) ^ (2 * r + 1) *
    Real.cos (Real.pi / lambda * z)

/-- A recursively normalized trigonometric primitive.  The recursion is the
standard even-sine integration recurrence, written so that the shift law is
inherited without evaluating an integral. -/
noncomputable def oddContactGauge (lambda : ℝ) : ℕ → ℝ → ℝ
  | 0 => fun z => z
  | r + 1 => fun z =>
      oddContactGauge lambda r z -
        oddContactScale (r + 1) /
            ((Real.pi / lambda) * (2 * r + 2)) *
          oddContactCorrection lambda r z

/-- Each recursive correction is periodic with the declared lattice step. -/
theorem oddContactCorrection_periodic
    {lambda : ℝ} (hlambda : lambda ≠ 0) (r : ℕ) :
    Function.Periodic (oddContactCorrection lambda r) lambda := by
  intro z
  have hangle : Real.pi / lambda * (z + lambda) =
      Real.pi / lambda * z + Real.pi := by
    field_simp [hlambda]
  unfold oddContactCorrection
  rw [hangle, Real.sin_add_pi, Real.cos_add_pi,
    (show Odd (2 * r + 1) from ⟨r, rfl⟩).neg_pow]
  ring

theorem oddContactCorrection_hasDerivAt
    {lambda : ℝ} (_hlambda : lambda ≠ 0) (r : ℕ) (z : ℝ) :
    HasDerivAt (oddContactCorrection lambda r)
      ((Real.pi / lambda) *
        ((2 * r + 1) *
            Real.sin (Real.pi / lambda * z) ^ (2 * r) *
            Real.cos (Real.pi / lambda * z) ^ 2 -
          Real.sin (Real.pi / lambda * z) ^ (2 * r + 2))) z := by
  let a : ℝ := Real.pi / lambda
  have hinner : HasDerivAt (fun x : ℝ => a * x) a z :=
    hasDerivAt_const_mul a
  have hsin := hinner.sin
  have hcos := hinner.cos
  have hpow := hsin.pow (2 * r + 1)
  have hprod := hpow.mul hcos
  unfold oddContactCorrection
  apply hprod.congr_deriv
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one,
    Nat.add_sub_cancel, Pi.pow_apply]
  rw [show 2 * r + 2 = (2 * r + 1) + 1 by omega, pow_succ]
  dsimp [a]
  ring

/-- Every recursively constructed gauge is globally real analytic. -/
theorem oddContactGauge_analytic (lambda : ℝ) :
    ∀ r z, AnalyticAt ℝ (oddContactGauge lambda r) z := by
  intro r
  induction r with
  | zero =>
      intro z
      simp [oddContactGauge]
      fun_prop
  | succ r ih =>
      intro z
      simp only [oddContactGauge]
      exact (ih z).sub (by
        unfold oddContactCorrection
        fun_prop)

/-- Every recursive primitive has the exact affine translation law. -/
theorem oddContactGauge_shiftEquivariant
    {lambda : ℝ} (hlambda : lambda ≠ 0) :
    ∀ r, ShiftEquivariant (oddContactGauge lambda r) lambda := by
  intro r
  induction r with
  | zero =>
      intro z
      simp [oddContactGauge]
  | succ r ih =>
      intro z
      simp only [oddContactGauge]
      rw [ih z, oddContactCorrection_periodic hlambda r z]
      ring

/-- The recursive primitive has exactly the normalized marginal as its first
derivative. -/
theorem oddContactGauge_hasDerivAt {lambda : ℝ} (hlambda : lambda ≠ 0) :
    ∀ r z, HasDerivAt (oddContactGauge lambda r)
      (oddContactMarginal lambda r z) z := by
  intro r
  induction r with
  | zero =>
      intro z
      norm_num [oddContactGauge, oddContactMarginal, oddContactScale]
      exact hasDerivAt_id' z
  | succ r ih =>
      intro z
      let a : ℝ := Real.pi / lambda
      let s : ℝ := Real.sin (a * z)
      let c : ℝ := Real.cos (a * z)
      let D : ℝ := 2 * r + 2
      have ha : a ≠ 0 := div_ne_zero Real.pi_ne_zero hlambda
      have hD : D ≠ 0 := by
        dsimp [D]
        positivity
      have hscale := oddContactScale_succ_relation r
      have hscale' : oddContactScale r =
          oddContactScale (r + 1) * (2 * r + 1) / D := by
        apply (eq_div_iff hD).2
        simpa [D, mul_comm] using hscale.symm
      have hcorrection := oddContactCorrection_hasDerivAt hlambda r z
      have hstep := (ih z).sub (hcorrection.const_mul
        (oddContactScale (r + 1) / (a * D)))
      simp only [oddContactGauge]
      apply hstep.congr_deriv
      unfold oddContactMarginal
      change
        oddContactScale r * s ^ (2 * r) -
            oddContactScale (r + 1) / (a * D) *
              (a * ((2 * r + 1) * s ^ (2 * r) * c ^ 2 -
                s ^ (2 * r + 2))) =
          oddContactScale (r + 1) * s ^ (2 * (r + 1))
      rw [hscale']
      rw [show 2 * r + 2 = 2 * r + 1 + 1 by omega, pow_succ,
        show 2 * (r + 1) = 2 * r + 2 by omega,
        show s ^ (2 * r + 2) = s ^ (2 * r) * s ^ 2 by
          rw [show 2 * r + 2 = 2 * r + 2 by rfl, pow_add]]
      have htrig : s ^ 2 + c ^ 2 = 1 := by
        dsimp [s, c, a]
        exact Real.sin_sq_add_cos_sq _
      have hzero : oddContactScale (r + 1) * s ^ (2 * r) *
          (2 * r + 1) * (s ^ 2 + c ^ 2 - 1) = 0 := by
        rw [htrig]
        ring
      field_simp [ha, hD]
      ring_nf at hzero ⊢
      linarith

/-- The normalized marginal is nonnegative everywhere. -/
theorem oddContactMarginal_nonneg (lambda : ℝ) (r : ℕ) (z : ℝ) :
    0 ≤ oddContactMarginal lambda r z := by
  unfold oddContactMarginal
  exact mul_nonneg (oddContactScale_pos r).le
    (Even.pow_nonneg (even_two_mul r) _)

/-- A monotone globally analytic translation gauge with a nonzero shift is
strictly monotone.  If it had a flat interval, the analytic identity theorem
would make it constant globally, contradicting translation equivariance. -/
theorem strictMono_of_monotone_analytic_shift
    {F : ℝ → ℝ} {lambda : ℝ} (hlambda : lambda ≠ 0)
    (hmono : Monotone F) (hanalytic : ∀ z, AnalyticAt ℝ F z)
    (hshift : ShiftEquivariant F lambda) : StrictMono F := by
  apply hmono.strictMono_of_injective
  intro x y hxy
  by_contra hne
  have forceConstant : ∀ {a b : ℝ}, a < b → F a = F b → False := by
    intro a b hab habEq
    have hconst : ∀ z ∈ Icc a b, F z = F a := by
      intro z hz
      apply le_antisymm
      · calc
          F z ≤ F b := hmono hz.2
          _ = F a := habEq.symm
      · exact hmono hz.1
    let midpoint : ℝ := (a + b) / 2
    have hmid : midpoint ∈ Ioo a b := by
      dsimp [midpoint]
      constructor <;> linarith
    have hevent : F =ᶠ[𝓝 midpoint] (fun _ : ℝ => F a) := by
      filter_upwards [isOpen_Ioo.mem_nhds hmid] with z hz
      exact hconst z ⟨hz.1.le, hz.2.le⟩
    have hglobal : F = (fun _ : ℝ => F a) :=
      AnalyticOnNhd.eq_of_eventuallyEq
        (fun z _ => hanalytic z) analyticOnNhd_const hevent
    have hconstShift : F (a + lambda) = F a := by
      rw [hglobal]
    have htranslated := hshift a
    apply hlambda
    linarith
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact (forceConstant hlt hxy).elim
  · exact (forceConstant hgt hxy.symm).elim

/-- Every member of the constructive odd-contact family is strictly
increasing. -/
theorem oddContactGauge_strictMono
    {lambda : ℝ} (hlambda : lambda ≠ 0) (r : ℕ) :
    StrictMono (oddContactGauge lambda r) := by
  have hderiv := oddContactGauge_hasDerivAt hlambda
  have hmono : Monotone (oddContactGauge lambda r) :=
    monotone_of_hasDerivAt_nonneg (hderiv r)
      (fun z => oddContactMarginal_nonneg lambda r z)
  exact strictMono_of_monotone_analytic_shift hlambda hmono
    (oddContactGauge_analytic lambda r)
    (oddContactGauge_shiftEquivariant hlambda r)

/-- The constructive gauge is normalized at the lattice origin. -/
theorem oddContactGauge_zero (lambda : ℝ) :
    ∀ r, oddContactGauge lambda r 0 = 0 := by
  intro r
  induction r with
  | zero => simp [oddContactGauge]
  | succ r ih => simp [oddContactGauge, oddContactCorrection, ih]

/-- The derivative of the constructive gauge as an equality of functions. -/
theorem deriv_oddContactGauge
    {lambda : ℝ} (hlambda : lambda ≠ 0) (r : ℕ) :
    deriv (oddContactGauge lambda r) = oddContactMarginal lambda r := by
  funext z
  exact (oddContactGauge_hasDerivAt hlambda r z).deriv

/-- The scaled sine coordinate is analytic and has a simple zero at the
lattice origin whenever the period is nonzero. -/
theorem scaledSin_analyticOrderAt_zero {lambda : ℝ} (hlambda : lambda ≠ 0) :
    analyticOrderAt (fun z : ℝ => Real.sin (Real.pi / lambda * z)) 0 = 1 := by
  let a : ℝ := Real.pi / lambda
  have ha : a ≠ 0 := div_ne_zero Real.pi_ne_zero hlambda
  have hanalytic : AnalyticAt ℝ (fun z : ℝ => Real.sin (a * z)) 0 := by
    fun_prop
  have hzero : Real.sin (a * 0) = 0 := by simp
  have hderiv : deriv (fun z : ℝ => Real.sin (a * z)) 0 = a := by
    have hinner : HasDerivAt (fun z : ℝ => a * z) a 0 :=
      hasDerivAt_const_mul a
    simpa using hinner.sin.deriv
  change analyticOrderAt (fun z : ℝ => Real.sin (a * z)) 0 = 1
  exact hanalytic.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hzero
    (hderiv.trans_ne ha)

/-- Multiplication by the positive central-binomial normalization preserves
the exact even order of the normalized marginal. -/
theorem oddContactMarginal_analyticOrderAt_zero
    {lambda : ℝ} (hlambda : lambda ≠ 0) (r : ℕ) :
    analyticOrderAt (oddContactMarginal lambda r) 0 = (2 * r : ℕ) := by
  let s : ℝ → ℝ := fun _ => oddContactScale r
  let u : ℝ → ℝ := fun z => Real.sin (Real.pi / lambda * z) ^ (2 * r)
  have hsAnalytic : AnalyticAt ℝ s 0 := by
    dsimp [s]
    fun_prop
  have huAnalytic : AnalyticAt ℝ u 0 := by
    dsimp [u]
    fun_prop
  have hsOrder : analyticOrderAt s 0 = 0 := by
    apply AnalyticAt.analyticOrderAt_eq_zero hsAnalytic |>.2
    exact oddContactScale_ne_zero r
  have huOrder : analyticOrderAt u 0 = (2 * r : ℕ) := by
    let v : ℝ → ℝ := fun z => Real.sin (Real.pi / lambda * z)
    have hvAnalytic : AnalyticAt ℝ v 0 := by
      dsimp [v]
      fun_prop
    change analyticOrderAt (v ^ (2 * r)) 0 = (2 * r : ℕ)
    rw [analyticOrderAt_pow hvAnalytic,
      show analyticOrderAt v 0 = 1 by
        exact scaledSin_analyticOrderAt_zero hlambda]
    simp
  change analyticOrderAt (s * u) 0 = (2 * r : ℕ)
  rw [analyticOrderAt_mul hsAnalytic huAnalytic, hsOrder, huOrder]
  simp

/-- Every analytic primitive of the normalized marginal has exact contact
order `2*r+1` after subtracting its value at the lattice point. -/
theorem analyticPrimitive_has_odd_contact_order
    {lambda : ℝ} (hlambda : lambda ≠ 0) (r : ℕ)
    {F : ℝ → ℝ} (hF : AnalyticAt ℝ F 0)
    (hderiv : deriv F = oddContactMarginal lambda r) :
    analyticOrderAt (fun z => F z - F 0) 0 = (2 * r + 1 : ℕ) := by
  have horder := hF.analyticOrderAt_deriv_add_one
  rw [hderiv, oddContactMarginal_analyticOrderAt_zero hlambda r] at horder
  simpa [Nat.cast_add, Nat.cast_mul] using horder.symm

/-- **FLUX-D4.NORMALFORM.03, all-order analytic core.**  For every natural
`r`, the displayed normalized marginal has exact analytic order `2*r`, and
every analytic primitive realizing it has exact positive odd contact order
`2*r+1`. -/
theorem flux_d4_complete_odd_contact_spectrum
    {lambda : ℝ} (hlambda : lambda ≠ 0) (r : ℕ) :
    analyticOrderAt (oddContactMarginal lambda r) 0 = (2 * r : ℕ) ∧
      ∀ {F : ℝ → ℝ}, AnalyticAt ℝ F 0 →
        deriv F = oddContactMarginal lambda r →
        analyticOrderAt (fun z => F z - F 0) 0 = (2 * r + 1 : ℕ) := by
  exact ⟨oddContactMarginal_analyticOrderAt_zero hlambda r,
    fun hF hderiv => analyticPrimitive_has_odd_contact_order hlambda r hF hderiv⟩

/-- **FLUX-D4.PERTURBATION.04, constructive spectrum.**  For every natural
`r`, one explicit globally analytic gauge is normalized at zero, is strictly
increasing, obeys the affine lattice shift, has exactly the printed
raised-cosine derivative, and realizes contact order `2*r+1`. -/
theorem flux_d4_constructive_odd_gauge
    {lambda : ℝ} (hlambda : lambda ≠ 0) (r : ℕ) :
    oddContactGauge lambda r 0 = 0 ∧
      ShiftEquivariant (oddContactGauge lambda r) lambda ∧
      StrictMono (oddContactGauge lambda r) ∧
      deriv (oddContactGauge lambda r) = raisedCosineMarginal lambda r ∧
      analyticOrderAt
          (fun z => oddContactGauge lambda r z - oddContactGauge lambda r 0) 0 =
        (2 * r + 1 : ℕ) := by
  have hderiv : deriv (oddContactGauge lambda r) =
      oddContactMarginal lambda r := deriv_oddContactGauge hlambda r
  have hraised : deriv (oddContactGauge lambda r) =
      raisedCosineMarginal lambda r := by
    funext z
    rw [hderiv]
    exact (raisedCosineMarginal_eq_oddContactMarginal lambda r z).symm
  have hcontact : analyticOrderAt
      (fun z => oddContactGauge lambda r z - oddContactGauge lambda r 0) 0 =
        (2 * r + 1 : ℕ) :=
    analyticPrimitive_has_odd_contact_order hlambda r
      (oddContactGauge_analytic lambda r 0) hderiv
  exact ⟨oddContactGauge_zero lambda r,
    oddContactGauge_shiftEquivariant hlambda r,
    oddContactGauge_strictMono hlambda r, hraised, hcontact⟩

end PhonologicalCalculus.Flux
