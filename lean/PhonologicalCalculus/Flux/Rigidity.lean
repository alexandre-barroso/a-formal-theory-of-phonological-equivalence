import Mathlib.Algebra.Ring.Periodic
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import PhonologicalCalculus.Flux.PeriodicGauge

/-!
# Load and branching rigidity

This module formalizes the universal functional-equation core of the load- and
branching-rigidity result.  Two irrationally related shift loads make the
period subgroup dense, so continuity forces the deviation from the identity
to be constant.  Independently, the complete degree-three star equation first
recovers the path shift law and then additivity; continuity and a nonzero load
force the unique remaining linear map to be the identity.
-/

namespace PhonologicalCalculus.Flux

open Set

/-- The additive subgroup of all periods of a function. -/
def periodSubgroup (f : ℝ → ℝ) : AddSubgroup ℝ where
  carrier := {a | Function.Periodic f a}
  zero_mem' := by
    intro x
    simp
  add_mem' := by
    intro a b ha hb
    exact ha.add_period hb
  neg_mem' := by
    intro a ha
    exact ha.neg

/-- A continuous real function with two irrationally related periods is
constant. -/
theorem continuous_of_two_irrational_periods_constant {P : ℝ → ℝ}
    {a b : ℝ} (hP : Continuous P) (ha : Function.Periodic P a)
    (hb : Function.Periodic P b) (hirrational : Irrational (a / b)) :
    P = fun _ => P 0 := by
  have hperiods : ({a, b} : Set ℝ) ⊆ (periodSubgroup P : Set ℝ) := by
    intro x hx
    rcases hx with (rfl | hx)
    · exact ha
    · simpa using hx ▸ hb
  have hclosure : AddSubgroup.closure {a, b} ≤ periodSubgroup P :=
    (AddSubgroup.closure_le (periodSubgroup P)).2 hperiods
  have hdense : Dense (AddSubgroup.closure {a, b} : Set ℝ) :=
    dense_addSubgroupClosure_pair_iff.mpr hirrational
  apply Continuous.ext_on hdense hP continuous_const
  intro x hx
  exact (hclosure hx).eq

/-- Two irrationally related shift-equivariance laws identify a continuous,
normalized flux recoding with the identity. -/
theorem incommensurate_shift_rigidity {F : ℝ → ℝ} {a b : ℝ}
    (hF : Continuous F) (hzero : F 0 = 0)
    (ha : ShiftEquivariant F a) (hb : ShiftEquivariant F b)
    (hirrational : Irrational (a / b)) :
    F = id := by
  have hdeviation : Continuous (gaugeDeviation F) := by
    exact hF.sub continuous_id
  have hconstant := continuous_of_two_irrational_periods_constant hdeviation
    ((shiftEquivariant_iff_periodic_deviation F a).mp ha)
    ((shiftEquivariant_iff_periodic_deviation F b).mp hb) hirrational
  funext x
  have hx := congrFun hconstant x
  simp only [gaugeDeviation, hzero, sub_zero] at hx
  simpa [id_eq] using sub_eq_zero.mp hx

/-- A shift law at one load propagates to every integral multiple of that
load.  Thus any finite commensurate-load family retains the same periodic
gauge freedom. -/
theorem shiftEquivariant_int_mul {F : ℝ → ℝ} {delta : ℝ}
    (hshift : ShiftEquivariant F delta) (n : ℤ) :
    ShiftEquivariant F (n * delta) := by
  apply (shiftEquivariant_iff_periodic_deviation _ _).mpr
  exact ((shiftEquivariant_iff_periodic_deviation F delta).mp hshift).int_mul n

/-- Universal stationarity equation supplied by complete equality of the
degree-three star response at a fixed load. -/
def CompleteStarEquation (F : ℝ → ℝ) (lambda : ℝ) : Prop :=
  ∀ r s, F r + F s + F (-lambda - r - s) + lambda = 0

/-- Oddness supplies normalization at the origin. -/
theorem odd_zero {F : ℝ → ℝ} (hodd : Function.Odd F) : F 0 = 0 := by
  have h := hodd 0
  simp only [neg_zero] at h
  linarith

/-- The complete star equation recovers the path shift law. -/
theorem completeStarEquation_shift {F : ℝ → ℝ} {lambda : ℝ}
    (hodd : Function.Odd F) (hstar : CompleteStarEquation F lambda) :
    ShiftEquivariant F lambda := by
  have hzero := odd_zero hodd
  intro r
  have h := hstar r 0
  have hneg : F (-lambda - r - 0) = -F (r + lambda) := by
    rw [show -lambda - r - 0 = -(r + lambda) by ring]
    exact hodd (r + lambda)
  rw [hzero, hneg] at h
  linarith

/-- The complete star equation, together with oddness, forces additivity. -/
theorem completeStarEquation_additive {F : ℝ → ℝ} {lambda : ℝ}
    (hodd : Function.Odd F) (hstar : CompleteStarEquation F lambda) :
    ∀ r s, F (r + s) = F r + F s := by
  have hshift := completeStarEquation_shift hodd hstar
  intro r s
  have h := hstar r s
  have hneg : F (-lambda - r - s) = -F ((r + s) + lambda) := by
    rw [show -lambda - r - s = -((r + s) + lambda) by ring]
    exact hodd ((r + s) + lambda)
  rw [hneg, hshift (r + s)] at h
  linarith

/-- A continuous complete star response at a nonzero load admits no
nonidentity odd constitutive gauge. -/
theorem complete_star_rigidity {F : ℝ → ℝ} {lambda : ℝ}
    (hF : Continuous F) (hodd : Function.Odd F)
    (hlambda : lambda ≠ 0) (hstar : CompleteStarEquation F lambda) :
    F = id := by
  have hzero := odd_zero hodd
  have hadd := completeStarEquation_additive hodd hstar
  let A : ℝ →+ ℝ :=
    { toFun := F
      map_zero' := hzero
      map_add' := hadd }
  have hlinear (x : ℝ) : F x = x * F 1 := by
    have h := map_real_smul A hF x 1
    simpa [A] using h
  have hload : F lambda = lambda := by
    have hshift := completeStarEquation_shift hodd hstar
    simpa [hzero] using hshift 0
  have hone : F 1 = 1 := by
    have h := hlinear lambda
    rw [hload] at h
    apply (mul_left_cancel₀ hlambda)
    linarith
  funext x
  rw [hlinear x, hone, mul_one]
  rfl

/-- **FLUX-D2.RIGIDITY.03.**  The two universal rigidity routes, stated
without suppressing their distinct hypotheses. -/
theorem flux_d2_rigidity_03 :
    (∀ (F : ℝ → ℝ) (a b : ℝ),
      Continuous F → F 0 = 0 →
      ShiftEquivariant F a → ShiftEquivariant F b →
      Irrational (a / b) → F = id) ∧
    (∀ (F : ℝ → ℝ) (lambda : ℝ),
      Continuous F → Function.Odd F → lambda ≠ 0 →
      CompleteStarEquation F lambda → F = id) := by
  constructor
  · intro F a b hF hzero ha hb hirrational
    exact incommensurate_shift_rigidity hF hzero ha hb hirrational
  · intro F lambda hF hodd hlambda hstar
    exact complete_star_rigidity hF hodd hlambda hstar

/-- The registered rational loads share a nonidentity analytic gauge.  This is
the commensurate-load witness complementary to the two rigidity theorems. -/
theorem commensurate_load_nonidentity_witness :
    ShiftEquivariant (periodicFluxGauge (1 / 105) (1 / 2)) (1 / 5) ∧
      ShiftEquivariant (periodicFluxGauge (1 / 105) (1 / 2)) (1 / 21) ∧
      periodicFluxGauge (1 / 105) (1 / 2) ≠ id := by
  have hbase : ShiftEquivariant
      (periodicFluxGauge (1 / 105) (1 / 2)) (1 / 105) :=
    periodicFluxGauge_shiftEquivariant (1 / 105) (1 / 2) (by norm_num)
  have hperiod :=
    (shiftEquivariant_iff_periodic_deviation
      (periodicFluxGauge (1 / 105) (1 / 2)) (1 / 105)).mp hbase
  have hfirstPeriod := hperiod.nat_mul 21
  have hsecondPeriod := hperiod.nat_mul 5
  norm_num at hfirstPeriod hsecondPeriod
  have hfirst : ShiftEquivariant
      (periodicFluxGauge (1 / 105) (1 / 2)) (1 / 5) := by
    apply (shiftEquivariant_iff_periodic_deviation _ _).mpr
    exact hfirstPeriod
  have hsecond : ShiftEquivariant
      (periodicFluxGauge (1 / 105) (1 / 2)) (1 / 21) := by
    apply (shiftEquivariant_iff_periodic_deviation _ _).mpr
    exact hsecondPeriod
  refine ⟨hfirst, hsecond, ?_⟩
  intro heq
  have hpoint := congrFun heq (1 / 420)
  simp only [periodicFluxGauge, id_eq] at hpoint
  rw [show (2 * Real.pi / (1 / 105)) * (1 / 420 : ℝ) =
      Real.pi / 2 by ring, Real.sin_pi_div_two] at hpoint
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp [hpi] at hpoint
  linarith

end PhonologicalCalculus.Flux
