import PhonologicalCalculus.ContinuousHG.Quadratic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic.FieldSimp

/-!
# Endpoint obstruction for directional harmony

This module formalizes the registered one-follower endpoint result.  A
right-hand little-o premise is represented by an exact filter limit.  The
limit yields a punctured interval on which the inward perturbation has lower
harmony.  The quadratic specialization then identifies the unique clipped
optimizer on the unit interval.
-/

namespace PhonologicalCalculus.ContinuousHG

open Filter Set

/-- Exact right-hand little-o condition at zero. -/
def IsRightLittleOAtZero (phi : ℝ → ℝ) : Prop :=
  Tendsto (fun epsilon => phi epsilon / epsilon)
    (nhdsWithin 0 (Ioi 0)) (nhds 0)

/-- A directional penalty that is little-o of the inward displacement cannot
protect the all-back endpoint against positive linear markedness. -/
theorem endpointPerturbation_eventually_negative
    {phi : ℝ → ℝ} {h m : ℝ}
    (hh : 0 < h) (hm : 0 < m) (hphi : IsRightLittleOAtZero phi) :
    ∃ delta > 0, ∀ epsilon, 0 < epsilon → epsilon < delta →
      h * phi epsilon - m * epsilon < 0 := by
  have hbound : 0 < m / (2 * h) := by positivity
  have heventually :
      ∀ᶠ epsilon in nhdsWithin (0 : ℝ) (Ioi 0),
        phi epsilon / epsilon < m / (2 * h) :=
    (tendsto_order.1 hphi).2 (m / (2 * h)) hbound
  change {epsilon : ℝ | phi epsilon / epsilon < m / (2 * h)} ∈
    nhdsWithin (0 : ℝ) (Ioi 0) at heventually
  rw [Metric.mem_nhdsWithin_iff] at heventually
  rcases heventually with ⟨delta, hdelta, hball⟩
  refine ⟨delta, hdelta, ?_⟩
  intro epsilon hepsilon hepsilonDelta
  have hmember : epsilon ∈ Metric.ball (0 : ℝ) delta ∩ Ioi 0 := by
    constructor
    · simpa [Real.dist_eq, abs_of_pos hepsilon] using hepsilonDelta
    · exact hepsilon
  have hquotient := hball hmember
  change phi epsilon / epsilon < m / (2 * h) at hquotient
  have hepsilonNe : epsilon ≠ 0 := ne_of_gt hepsilon
  have hphiIdentity : phi epsilon = epsilon * (phi epsilon / epsilon) := by
    field_simp [hepsilonNe]
  have hscale : 2 * h * (m / (2 * h)) = m := by
    field_simp [ne_of_gt hh]
  have hscaled :
      h * epsilon * (phi epsilon / epsilon) <
        h * epsilon * (m / (2 * h)) :=
    mul_lt_mul_of_pos_left hquotient (mul_pos hh hepsilon)
  rw [hphiIdentity]
  nlinarith

/-- One-follower quadratic harmony on the unit interval. -/
def oneFollowerQuadraticCost (h m x : ℝ) : ℝ :=
  h * (1 - x) ^ 2 + m * x

/-- Clipped stationary point of the one-follower quadratic harmony. -/
noncomputable def clippedQuadraticOptimizer (h m : ℝ) : ℝ :=
  max 0 (1 - m / (2 * h))

/-- A scalar point is the unique minimizer of an objective on a carrier. -/
def IsUniqueScalarMinimizerOn (carrier : ℝ → Prop)
    (objective : ℝ → ℝ) (u : ℝ) : Prop :=
  carrier u ∧
    ∀ x, carrier x →
      objective u ≤ objective x ∧
      (objective x = objective u → x = u)

theorem clippedQuadraticOptimizer_mem_unit
    {h m : ℝ} (hh : 0 < h) (hm : 0 < m) :
    clippedQuadraticOptimizer h m ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact le_max_left _ _
  · unfold clippedQuadraticOptimizer
    apply max_le
    · norm_num
    · have hquotient : 0 < m / (2 * h) := by positivity
      linarith

/-- The clipped stationary point is the unique optimizer of the complete
one-follower quadratic competition on `[0,1]`. -/
theorem clippedQuadraticOptimizer_unique_minimizer
    {h m : ℝ} (hh : 0 < h) (hm : 0 < m) :
    IsUniqueScalarMinimizerOn (fun x : ℝ => x ∈ Set.Icc (0 : ℝ) 1)
      (oneFollowerQuadraticCost h m) (clippedQuadraticOptimizer h m) := by
  refine ⟨clippedQuadraticOptimizer_mem_unit hh hm, ?_⟩
  intro x hx
  rcases hx with ⟨hx0, hx1⟩
  by_cases hinterior : m < 2 * h
  · have hoptimizer :
        clippedQuadraticOptimizer h m = 1 - m / (2 * h) := by
      unfold clippedQuadraticOptimizer
      rw [max_eq_right]
      have : 0 < 1 - m / (2 * h) := by
        have htwo : 0 < 2 * h := by positivity
        apply sub_pos.mpr
        exact (div_lt_one htwo).2 hinterior
      exact this.le
    rw [hoptimizer]
    have hgap :
        oneFollowerQuadraticCost h m x -
            oneFollowerQuadraticCost h m (1 - m / (2 * h)) =
          h * (x - (1 - m / (2 * h))) ^ 2 := by
      unfold oneFollowerQuadraticCost
      field_simp [ne_of_gt hh]
      ring
    constructor
    · have : 0 ≤ h * (x - (1 - m / (2 * h))) ^ 2 :=
        mul_nonneg hh.le (sq_nonneg _)
      linarith
    · intro hequality
      have hsquare : (x - (1 - m / (2 * h))) ^ 2 = 0 := by
        rw [hequality, sub_self] at hgap
        nlinarith
      have hx : x = 1 - m / (2 * h) := by nlinarith
      simpa [hoptimizer] using hx
  · have hboundary : 2 * h ≤ m := le_of_not_gt hinterior
    have hoptimizer : clippedQuadraticOptimizer h m = 0 := by
      unfold clippedQuadraticOptimizer
      rw [max_eq_left]
      have htwo : 0 < 2 * h := by positivity
      have : 1 ≤ m / (2 * h) := (one_le_div htwo).2 hboundary
      linarith
    rw [hoptimizer]
    have hgap :
        oneFollowerQuadraticCost h m x - oneFollowerQuadraticCost h m 0 =
          x * (h * x + (m - 2 * h)) := by
      unfold oneFollowerQuadraticCost
      ring
    have hfactor : 0 ≤ h * x + (m - 2 * h) := by
      nlinarith
    constructor
    · apply sub_nonneg.mp
      rw [hgap]
      exact mul_nonneg hx0 hfactor
    · intro hequality
      have hzero : x * (h * x + (m - 2 * h)) = 0 := by
        rw [hequality, sub_self] at hgap
        exact hgap.symm
      rcases mul_eq_zero.mp hzero with hxZero | hfactorZero
      · simpa [hxZero]
      · have : x = 0 := by nlinarith
        simpa [this]

/-- Registered universal content of `CHG-B4`. -/
theorem chg_b4_endpoint_obstruction
    {phi : ℝ → ℝ} {h m : ℝ}
    (hh : 0 < h) (hm : 0 < m) (hphi : IsRightLittleOAtZero phi) :
    (∃ delta > 0, ∀ epsilon, 0 < epsilon → epsilon < delta →
      h * phi epsilon - m * epsilon < 0) ∧
    IsUniqueScalarMinimizerOn (fun x : ℝ => x ∈ Set.Icc (0 : ℝ) 1)
      (oneFollowerQuadraticCost h m) (clippedQuadraticOptimizer h m) := by
  exact ⟨endpointPerturbation_eventually_negative hh hm hphi,
    clippedQuadraticOptimizer_unique_minimizer hh hm⟩

end PhonologicalCalculus.ContinuousHG
