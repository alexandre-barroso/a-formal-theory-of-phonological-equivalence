import Mathlib
import Mathlib.Tactic

/-!
# Bellman telescoping for exact continuation

An exact continuation value turns each local edge-and-site comparison into a
telescoping global lower bound.  This module separates that universal step
from the family-specific scalar inequality and decay equation.
-/

namespace PhonologicalCalculus.Support

open Filter Finset
open scoped Topology

/-- Local Bellman inequalities telescope over every finite prefix. -/
theorem bellman_prefix_lower_bound
    (cost potential : ℕ → ℝ)
    (localBound : ∀ index, potential index ≤ cost index + potential (index + 1)) :
    ∀ horizon,
      potential 0 ≤ ∑ index ∈ range horizon, cost index + potential horizon := by
  intro horizon
  induction horizon with
  | zero => simp
  | succ horizon inductionHypothesis =>
      rw [sum_range_succ]
      have finalStep := localBound horizon
      linarith

/-- Local Bellman equalities telescope to an exact finite value identity. -/
theorem bellman_prefix_identity
    (cost potential : ℕ → ℝ)
    (localIdentity : ∀ index, potential index = cost index + potential (index + 1)) :
    ∀ horizon,
      potential 0 = ∑ index ∈ range horizon, cost index + potential horizon := by
  intro horizon
  induction horizon with
  | zero => simp
  | succ horizon inductionHypothesis =>
      rw [sum_range_succ]
      have finalStep := localIdentity horizon
      linarith

/-- Exact local continuation identities and a vanishing residual force the
partial costs to converge to the initial continuation value. -/
theorem bellman_partial_costs_converge
    (cost potential : ℕ → ℝ)
    (localIdentity : ∀ index, potential index = cost index + potential (index + 1))
    (residualVanishing : Tendsto potential atTop (nhds 0)) :
    Tendsto (fun horizon => ∑ index ∈ range horizon, cost index)
      atTop (nhds (potential 0)) := by
  have pointwiseIdentity :
      (fun horizon => ∑ index ∈ range horizon, cost index) =
        fun horizon => potential 0 - potential horizon := by
    funext horizon
    have telescoped := bellman_prefix_identity cost potential localIdentity horizon
    linarith
  rw [pointwiseIdentity]
  simpa using tendsto_const_nhds.sub residualVanishing

/-- If partial costs converge and the residual continuation value vanishes,
the initial continuation value is a global lower bound for the infinite
cost. -/
theorem bellman_limit_lower_bound
    (cost potential : ℕ → ℝ) (total : ℝ)
    (localBound : ∀ index, potential index ≤ cost index + potential (index + 1))
    (costConvergence :
      Tendsto (fun horizon => ∑ index ∈ range horizon, cost index)
        atTop (nhds total))
    (residualVanishing : Tendsto potential atTop (nhds 0)) :
    potential 0 ≤ total := by
  have combinedConvergence := costConvergence.add residualVanishing
  have eventualBound :
      ∀ᶠ horizon in atTop,
        potential 0 ≤
          (∑ index ∈ range horizon, cost index) + potential horizon :=
    Filter.Eventually.of_forall
      (bellman_prefix_lower_bound cost potential localBound)
  have limitBound : potential 0 ≤ total + 0 :=
    ge_of_tendsto combinedConvergence eventualBound
  simpa using limitBound

/-- Exact local continuation identities, convergence of partial costs, and a
vanishing residual identify the infinite value exactly. -/
theorem bellman_limit_identity
    (cost potential : ℕ → ℝ) (total : ℝ)
    (localIdentity : ∀ index, potential index = cost index + potential (index + 1))
    (costConvergence :
      Tendsto (fun horizon => ∑ index ∈ range horizon, cost index)
        atTop (nhds total))
    (residualVanishing : Tendsto potential atTop (nhds 0)) :
    total = potential 0 := by
  have combinedConvergence :
      Tendsto
        (fun horizon =>
          (∑ index ∈ range horizon, cost index) + potential horizon)
        atTop (nhds (total + 0)) :=
    costConvergence.add residualVanishing
  have pointwiseIdentity :
      (fun horizon =>
        (∑ index ∈ range horizon, cost index) + potential horizon) =
        fun _ => potential 0 := by
    funext horizon
    exact (bellman_prefix_identity cost potential localIdentity horizon).symm
  rw [pointwiseIdentity] at combinedConvergence
  have uniqueLimit : total + 0 = potential 0 :=
    tendsto_nhds_unique combinedConvergence tendsto_const_nhds
  simpa using uniqueLimit

/-! ## Quadratic matched-power scalar proof -/

/-- The quadratic decay equation in a denominator-free form. -/
def QuadraticDecayEquation (h m lambda : ℝ) : Prop :=
  m * lambda = h * (1 - lambda) ^ 2

/-- Under the quadratic decay equation, the local Bellman remainder is one
positive square. -/
theorem quadratic_bellman_remainder
    (h m lambda a b : ℝ)
    (lambdaNonzero : lambda ≠ 0)
    (decay : QuadraticDecayEquation h m lambda) :
    h * (a - b) ^ 2 + m * b ^ 2 +
        (h * (1 - lambda)) * b ^ 2 -
        (h * (1 - lambda)) * a ^ 2 =
      (h / lambda) * (b - lambda * a) ^ 2 := by
  unfold QuadraticDecayEquation at decay
  field_simp [lambdaNonzero]
  nlinarith

/-- Positive quadratic edge weight and decay ratio make the Bellman
remainder nonnegative. -/
theorem quadratic_bellman_lower_bound
    (h m lambda a b : ℝ)
    (hPositive : 0 < h) (lambdaPositive : 0 < lambda)
    (decay : QuadraticDecayEquation h m lambda) :
    (h * (1 - lambda)) * a ^ 2 ≤
      h * (a - b) ^ 2 + m * b ^ 2 +
        (h * (1 - lambda)) * b ^ 2 := by
  have identity := quadratic_bellman_remainder h m lambda a b
    (ne_of_gt lambdaPositive) decay
  have coefficientPositive : 0 < h / lambda := div_pos hPositive lambdaPositive
  nlinarith [sq_nonneg (b - lambda * a)]

/-- Equality in the positive quadratic Bellman bound holds exactly at the
geometric successor `b = lambda*a`. -/
theorem quadratic_bellman_equality_iff
    (h m lambda a b : ℝ)
    (hPositive : 0 < h) (lambdaPositive : 0 < lambda)
    (decay : QuadraticDecayEquation h m lambda) :
    h * (a - b) ^ 2 + m * b ^ 2 +
        (h * (1 - lambda)) * b ^ 2 =
        (h * (1 - lambda)) * a ^ 2 ↔
      b = lambda * a := by
  have identity := quadratic_bellman_remainder h m lambda a b
    (ne_of_gt lambdaPositive) decay
  have coefficientPositive : 0 < h / lambda := div_pos hPositive lambdaPositive
  constructor
  · intro equality
    have squareZero : (b - lambda * a) ^ 2 = 0 := by
      nlinarith
    nlinarith
  · intro equality
    subst b
    nlinarith

/-- Edge-and-site cost of the quadratic geometric continuation candidate. -/
noncomputable def quadraticGeometricCost
    (h m lambda : ℝ) (index : ℕ) : ℝ :=
  h * (lambda ^ index - lambda ^ (index + 1)) ^ 2 +
    m * (lambda ^ (index + 1)) ^ 2

/-- Continuation potential along the quadratic geometric candidate. -/
noncomputable def quadraticGeometricPotential
    (h lambda : ℝ) (index : ℕ) : ℝ :=
  (h * (1 - lambda)) * (lambda ^ index) ^ 2

/-- The quadratic geometric candidate satisfies the local continuation
identity at every edge. -/
theorem quadratic_geometric_local_identity
    (h m lambda : ℝ)
    (hPositive : 0 < h) (lambdaPositive : 0 < lambda)
    (decay : QuadraticDecayEquation h m lambda) (index : ℕ) :
    quadraticGeometricPotential h lambda index =
      quadraticGeometricCost h m lambda index +
        quadraticGeometricPotential h lambda (index + 1) := by
  have equality := (quadratic_bellman_equality_iff h m lambda
    (lambda ^ index) (lambda ^ (index + 1)) hPositive lambdaPositive decay).2
      (by rw [pow_succ]; ring)
  simpa [quadraticGeometricPotential, quadraticGeometricCost] using equality.symm

/-- For a decay ratio strictly between zero and one, the geometric
continuation potential vanishes. -/
theorem quadratic_geometric_potential_vanishes
    (h lambda : ℝ) (lambdaNonnegative : 0 ≤ lambda) (lambdaBelowOne : lambda < 1) :
    Tendsto (quadraticGeometricPotential h lambda) atTop (nhds 0) := by
  have squaredBelowOne : lambda ^ 2 < 1 := by
    nlinarith
  have powersVanish :
      Tendsto (fun index : ℕ => (lambda ^ 2) ^ index) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (sq_nonneg lambda) squaredBelowOne
  have scaled := powersVanish.const_mul (h * (1 - lambda))
  have scaledIdentity :
      (fun index : ℕ => (h * (1 - lambda)) * (lambda ^ 2) ^ index) =
        quadraticGeometricPotential h lambda := by
    funext index
    simp only [quadraticGeometricPotential]
    congr 1
    rw [← pow_mul, Nat.mul_comm, pow_mul]
  rw [scaledIdentity] at scaled
  simpa using scaled

/-- The partial quadratic matched-power costs of the geometric candidate
converge exactly to the continuation coefficient. -/
theorem quadratic_geometric_cost_converges
    (h m lambda : ℝ)
    (hPositive : 0 < h) (lambdaPositive : 0 < lambda)
    (lambdaBelowOne : lambda < 1)
    (decay : QuadraticDecayEquation h m lambda) :
    Tendsto
      (fun horizon =>
        ∑ index ∈ range horizon, quadraticGeometricCost h m lambda index)
      atTop (nhds (h * (1 - lambda))) := by
  have localIdentity := quadratic_geometric_local_identity h m lambda
    hPositive lambdaPositive decay
  have residualVanishing := quadratic_geometric_potential_vanishes h lambda
    (le_of_lt lambdaPositive) lambdaBelowOne
  simpa [quadraticGeometricPotential] using
    bellman_partial_costs_converge
      (quadraticGeometricCost h m lambda)
      (quadraticGeometricPotential h lambda)
      localIdentity residualVanishing

end PhonologicalCalculus.Support
