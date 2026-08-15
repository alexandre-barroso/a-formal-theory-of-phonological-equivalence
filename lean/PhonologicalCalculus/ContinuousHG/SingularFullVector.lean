import PhonologicalCalculus.ContinuousHG.GeneralPowerOptimizer
import PhonologicalCalculus.ContinuousHG.SingularBoundary
import PhonologicalCalculus.ContinuousHG.SingularOptimizerBridge

/-!
# Full-vector singular limit of the directional power optimizer

This module lifts the scalar exponent-one boundary calculation to the complete
fixed finite directional path.  It identifies an exact finite-dimensional
optimizer on every relevant approach path, proves that all decreases after the
initial one vanish, and reconstructs the limit of every follower activity.
-/

namespace PhonologicalCalculus.ContinuousHG

open Filter Finset Set
open scoped BigOperators Topology

/-- Activity of follower `i`, reconstructed from a zero-based finite decrease
vector.  Every decrease through `i` has already occurred at that follower. -/
noncomputable def singularActivityAt {N : ℕ} (d : Fin N → ℝ) (i : Fin N) : ℝ :=
  1 - ∑ j : Fin N, if j.1 ≤ i.1 then d j else 0

/-- Under the singular reparameterization `p = 1 + 1/x`, a zero-multiplier
path decrease is exactly the scalar fixed-ratio expression with coefficient
`weight/rho`. -/
theorem powerPathDecrease_zero_eq_fixedRatioUnclipped
    {N : ℕ} {rho x : ℝ} (hrho : 0 < rho) (hx : 0 < x) (i : Fin N) :
    powerPathDecrease rho 1 (1 + 1 / x) 0 N i =
      fixedRatioUnclippedDecrease (powerPathWeight N i / rho) x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hp : 1 < 1 + 1 / x := by
    linarith [one_div_pos.mpr hx]
  have hweight : 0 < powerPathWeight N i := powerPathWeight_positive i
  unfold powerPathDecrease powerKKTDecrease fixedRatioUnclippedDecrease
  rw [sub_zero, one_mul, max_eq_left hweight.le]
  have hexponent : powerShiftExponent (1 + 1 / x) = x := by
    unfold powerShiftExponent
    field_simp [hx0]
    ring
  rw [hexponent]
  congr 1
  field_simp [ne_of_gt hrho, ne_of_gt (lt_trans zero_lt_one hp)]

/-- A later zero-multiplier decrease vanishes whenever its positional
coefficient is strictly smaller than the harmony ratio. -/
theorem powerPathDecrease_zero_tendsto_zero
    {N : ℕ} {rho : ℝ} (hrho : 0 < rho) (i : Fin N)
    (hweight : powerPathWeight N i < rho) :
    Tendsto
      (fun x : ℝ => powerPathDecrease rho 1 (1 + 1 / x) 0 N i)
      atTop (nhds 0) := by
  have hratioPositive : 0 < powerPathWeight N i / rho :=
    div_pos (powerPathWeight_positive i) hrho
  have hratioBelow : powerPathWeight N i / rho < 1 :=
    (div_lt_one hrho).2 hweight
  have hscalar := tendsto_rpow_atTop_of_base_lt_one
    (powerPathWeight N i / rho) (by linarith) hratioBelow
  have heq :
      (fun x : ℝ => powerPathDecrease rho 1 (1 + 1 / x) 0 N i) =ᶠ[atTop]
        (fun x : ℝ => fixedRatioUnclippedDecrease
          (powerPathWeight N i / rho) x) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact powerPathDecrease_zero_eq_fixedRatioUnclipped hrho hx i
  have hboundary := equalityBoundaryDecrease_tendsto
  have hproduct :
      Tendsto
        (fun x : ℝ =>
          (powerPathWeight N i / rho) ^ x * equalityBoundaryDecrease x)
        atTop (nhds 0) := by
    convert hscalar.mul hboundary using 1
    norm_num
  have hunclipped :
      Tendsto
        (fun x : ℝ => fixedRatioUnclippedDecrease
          (powerPathWeight N i / rho) x)
        atTop (nhds 0) := by
    apply hproduct.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact (fixedRatioUnclippedDecrease_eq hratioPositive.le hx).symm
  exact hunclipped.congr' heq.symm

theorem powerPathWeight_lt_horizon_of_pos
    {N : ℕ} (i : Fin N) (hi : 0 < i.1) :
    powerPathWeight N i < (N : ℝ) := by
  unfold powerPathWeight
  exact_mod_cast Nat.sub_lt (Nat.zero_lt_of_lt i.2) hi

/-- Pointwise convergence of a finite decrease vector transports exactly to
every reconstructed follower activity. -/
theorem singularActivityAt_tendsto
    {N : ℕ} {d : ℝ → Fin N → ℝ} {limit : Fin N → ℝ}
    (hd : ∀ j, Tendsto (fun x => d x j) atTop (nhds (limit j))) (i : Fin N) :
    Tendsto (fun x => singularActivityAt (d x) i) atTop
      (nhds (1 - ∑ j : Fin N, if j.1 ≤ i.1 then limit j else 0)) := by
  unfold singularActivityAt
  apply tendsto_const_nhds.sub
  apply tendsto_finsetSum Finset.univ
  intro j _hj
  by_cases hji : j.1 ≤ i.1
  · simpa [hji] using hd j
  · simp [hji]

/-- When every fixed-horizon decrease vanishes, the total zero-multiplier
mass vanishes as well. -/
theorem powerPathMass_zero_tendsto_zero_of_ratio_above_horizon
    {N : ℕ} {rho : ℝ} (hrho : (N : ℝ) < rho) :
    Tendsto
      (fun x : ℝ => powerPathMass rho 1 (1 + 1 / x) 0 N)
      atTop (nhds 0) := by
  have hrho0 : 0 < rho := lt_of_le_of_lt (Nat.cast_nonneg N) hrho
  change Tendsto
    (fun x : ℝ => ∑ i : Fin N,
      powerPathDecrease rho 1 (1 + 1 / x) 0 N i) atTop (nhds 0)
  have hsum := tendsto_finsetSum Finset.univ (fun i _ =>
    powerPathDecrease_zero_tendsto_zero hrho0 i
      ((powerPathWeight_le_horizon i).trans_lt hrho))
  simpa using hsum

/-- Above the critical horizon, the full zero-multiplier vector is eventually
the unique optimizer, every decrease vanishes, and every follower activity
converges to the all-back value one. -/
theorem singular_fullVector_ratio_above
    {N : ℕ} {rho : ℝ} (_hN : 0 < N) (hrho : (N : ℝ) < rho) :
    (∀ᶠ x : ℝ in atTop,
      IsUniqueMinimizerOn (SolidSimplex : (Fin N → ℝ) → Prop)
        (powerReducedObjective rho 1 (1 + 1 / x) (powerPathWeight N))
        (powerPathDecrease rho 1 (1 + 1 / x) 0 N)) ∧
    (∀ j : Fin N,
      Tendsto
        (fun x : ℝ => powerPathDecrease rho 1 (1 + 1 / x) 0 N j)
        atTop (nhds 0)) ∧
    (∀ i : Fin N,
      Tendsto
        (fun x : ℝ => singularActivityAt
          (powerPathDecrease rho 1 (1 + 1 / x) 0 N) i)
        atTop (nhds 1)) := by
  have hrho0 : 0 < rho := lt_of_le_of_lt (Nat.cast_nonneg N) hrho
  have hdecrease : ∀ j : Fin N,
      Tendsto
        (fun x : ℝ => powerPathDecrease rho 1 (1 + 1 / x) 0 N j)
        atTop (nhds 0) := fun j =>
    powerPathDecrease_zero_tendsto_zero hrho0 j
      ((powerPathWeight_le_horizon j).trans_lt hrho)
  have hmass :=
    powerPathMass_zero_tendsto_zero_of_ratio_above_horizon hrho
  have hmassEventually :
      ∀ᶠ x : ℝ in atTop,
        powerPathMass rho 1 (1 + 1 / x) 0 N ≤ 1 := by
    exact (hmass.eventually (eventually_lt_nhds zero_lt_one)).mono
      (fun _ hx => hx.le)
  have hoptimizer :
      ∀ᶠ x : ℝ in atTop,
        IsUniqueMinimizerOn (SolidSimplex : (Fin N → ℝ) → Prop)
          (powerReducedObjective rho 1 (1 + 1 / x) (powerPathWeight N))
          (powerPathDecrease rho 1 (1 + 1 / x) 0 N) := by
    filter_upwards [hmassEventually, eventually_gt_atTop (0 : ℝ)] with x hmx hx
    have hp : 1 < 1 + 1 / x := by linarith [one_div_pos.mpr hx]
    change IsUniqueMinimizerOn (SolidSimplex : (Fin N → ℝ) → Prop)
      (powerReducedObjective rho 1 (1 + 1 / x) (powerPathWeight N))
      (powerKKTDecrease rho 1 (1 + 1 / x) 0 (powerPathWeight N))
    exact powerKKTDecrease_zero_unique_minimizer (powerPathWeight N)
      hrho0 hp (by simpa [powerPathMass] using hmx)
  refine ⟨hoptimizer, hdecrease, ?_⟩
  intro i
  have hactivity := singularActivityAt_tendsto hdecrease i
  simpa using hactivity

/-- The initial path coordinate at a nonempty horizon. -/
def singularFirstIndex {N : ℕ} (hN : 0 < N) : Fin N := ⟨0, hN⟩

theorem powerPathWeight_first {N : ℕ} (hN : 0 < N) :
    powerPathWeight N (singularFirstIndex hN) = (N : ℝ) := by
  simp [powerPathWeight, singularFirstIndex]

theorem fin_value_pos_of_ne_first
    {N : ℕ} (hN : 0 < N) (i : Fin N)
    (hi : i ≠ singularFirstIndex hN) : 0 < i.1 := by
  by_contra hnot
  have hizero : i.1 = 0 := Nat.eq_zero_of_not_pos hnot
  apply hi
  apply Fin.ext
  simpa [singularFirstIndex] using hizero

/-- On the critical equality line, the first zero-multiplier decrease is
exactly the scalar equality-boundary decrease. -/
theorem powerPathDecrease_zero_first_eq_equalityBoundaryDecrease
    {N : ℕ} (hN : 0 < N) {x : ℝ} (hx : 0 < x) :
    powerPathDecrease (N : ℝ) 1 (1 + 1 / x) 0 N
        (singularFirstIndex hN) = equalityBoundaryDecrease x := by
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  rw [powerPathDecrease_zero_eq_fixedRatioUnclipped hNreal hx,
    powerPathWeight_first]
  rw [div_self (ne_of_gt hNreal)]
  have hfactor := fixedRatioUnclippedDecrease_eq
    (r := (1 : ℝ)) (x := x) (by positivity) hx
  simpa using hfactor

/-- At the critical fixed ratio, the complete decrease vector converges to
`exp (-1)` in its first coordinate and to zero in every later coordinate. -/
theorem singular_equality_decrease_tendsto
    {N : ℕ} (hN : 0 < N) (j : Fin N) :
    Tendsto
      (fun x : ℝ => powerPathDecrease (N : ℝ) 1
        (1 + 1 / x) 0 N j)
      atTop
      (nhds (if j = singularFirstIndex hN then Real.exp (-1) else 0)) := by
  by_cases hj : j = singularFirstIndex hN
  · subst j
    have heq :
        (fun x : ℝ => powerPathDecrease (N : ℝ) 1
          (1 + 1 / x) 0 N (singularFirstIndex hN)) =ᶠ[atTop]
          equalityBoundaryDecrease := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      exact powerPathDecrease_zero_first_eq_equalityBoundaryDecrease hN hx
    simpa using equalityBoundaryDecrease_tendsto.congr' heq.symm
  · have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
    have hjpos := fin_value_pos_of_ne_first hN j hj
    have hweight : powerPathWeight N j < (N : ℝ) :=
      powerPathWeight_lt_horizon_of_pos j hjpos
    simpa [hj] using powerPathDecrease_zero_tendsto_zero hNreal j hweight

theorem singular_equality_mass_tendsto
    {N : ℕ} (hN : 0 < N) :
    Tendsto
      (fun x : ℝ => powerPathMass (N : ℝ) 1 (1 + 1 / x) 0 N)
      atTop (nhds (Real.exp (-1))) := by
  change Tendsto
    (fun x : ℝ => ∑ j : Fin N,
      powerPathDecrease (N : ℝ) 1 (1 + 1 / x) 0 N j)
    atTop (nhds (Real.exp (-1)))
  have hsum := tendsto_finsetSum Finset.univ
    (fun j _ => singular_equality_decrease_tendsto hN j)
  have hlimit :
      (∑ j : Fin N,
        if j = singularFirstIndex hN then Real.exp (-1) else 0) =
        Real.exp (-1) := by
    rw [Finset.sum_eq_single (singularFirstIndex hN)]
    · simp
    · intro b _hb hbne
      simp [hbne]
    · simp
  simpa [hlimit] using hsum

/-- At fixed equality, the full zero-multiplier vector is eventually the
unique optimizer and every follower activity converges to `1-exp (-1)`. -/
theorem singular_fullVector_ratio_equal
    {N : ℕ} (hN : 0 < N) :
    (∀ᶠ x : ℝ in atTop,
      IsUniqueMinimizerOn (SolidSimplex : (Fin N → ℝ) → Prop)
        (powerReducedObjective (N : ℝ) 1 (1 + 1 / x)
          (powerPathWeight N))
        (powerPathDecrease (N : ℝ) 1 (1 + 1 / x) 0 N)) ∧
    (∀ j : Fin N, j ≠ singularFirstIndex hN →
      Tendsto
        (fun x : ℝ => powerPathDecrease (N : ℝ) 1
          (1 + 1 / x) 0 N j)
        atTop (nhds 0)) ∧
    (∀ i : Fin N,
      Tendsto
        (fun x : ℝ => singularActivityAt
          (powerPathDecrease (N : ℝ) 1 (1 + 1 / x) 0 N) i)
        atTop (nhds (1 - Real.exp (-1)))) := by
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hmass := singular_equality_mass_tendsto hN
  have hexpBelowOne : Real.exp (-1) < 1 :=
    Real.exp_lt_one_iff.mpr (by norm_num)
  have hmassEventually :
      ∀ᶠ x : ℝ in atTop,
        powerPathMass (N : ℝ) 1 (1 + 1 / x) 0 N ≤ 1 := by
    exact (hmass.eventually (eventually_lt_nhds hexpBelowOne)).mono
      (fun _ hx => hx.le)
  have hoptimizer :
      ∀ᶠ x : ℝ in atTop,
        IsUniqueMinimizerOn (SolidSimplex : (Fin N → ℝ) → Prop)
          (powerReducedObjective (N : ℝ) 1 (1 + 1 / x)
            (powerPathWeight N))
          (powerPathDecrease (N : ℝ) 1 (1 + 1 / x) 0 N) := by
    filter_upwards [hmassEventually, eventually_gt_atTop (0 : ℝ)] with x hmx hx
    have hp : 1 < 1 + 1 / x := by linarith [one_div_pos.mpr hx]
    change IsUniqueMinimizerOn (SolidSimplex : (Fin N → ℝ) → Prop)
      (powerReducedObjective (N : ℝ) 1 (1 + 1 / x) (powerPathWeight N))
      (powerKKTDecrease (N : ℝ) 1 (1 + 1 / x) 0 (powerPathWeight N))
    exact powerKKTDecrease_zero_unique_minimizer (powerPathWeight N)
      hNreal hp (by simpa [powerPathMass] using hmx)
  refine ⟨hoptimizer, ?_, ?_⟩
  · intro j hj
    simpa [hj] using singular_equality_decrease_tendsto hN j
  · intro i
    have hactivity := singularActivityAt_tendsto
      (d := fun x => powerPathDecrease (N : ℝ) 1 (1 + 1 / x) 0 N)
      (limit := fun j =>
        if j = singularFirstIndex hN then Real.exp (-1) else 0)
      (singular_equality_decrease_tendsto hN) i
    have hsum :
        (∑ j : Fin N, if j.1 ≤ i.1 then
          (if j = singularFirstIndex hN then Real.exp (-1) else 0) else 0) =
          Real.exp (-1) := by
      rw [Finset.sum_eq_single (singularFirstIndex hN)]
      · simp [singularFirstIndex]
      · intro b _hb hbne
        simp [hbne]
      · simp
    rw [hsum] at hactivity
    exact hactivity

/-- Along the first-order joint path `rho_x = N(1+c/x)`, every full-vector
decrease factors into a fixed positional ratio and the scalar joint-boundary
decrease. -/
theorem powerPathDecrease_joint_factorization
    {N : ℕ} (hN : 0 < N) {c x : ℝ} (hx : 0 < x) (hxc : 0 < x + c)
    (i : Fin N) :
    powerPathDecrease ((N : ℝ) * (1 + c / x)) 1 (1 + 1 / x) 0 N i =
      (powerPathWeight N i / (N : ℝ)) ^ x * jointBoundaryDecrease c x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hp : 0 < 1 + 1 / x := by linarith [one_div_pos.mpr hx]
  have hcbase : 0 < 1 + c / x := by
    have heq : 1 + c / x = (x + c) / x := by
      field_simp [hx0]
    rw [heq]
    positivity
  have hweight : 0 < powerPathWeight N i := powerPathWeight_positive i
  have hden : 0 < (1 + 1 / x) * ((N : ℝ) * (1 + c / x)) := by positivity
  have hratio : 0 ≤ powerPathWeight N i / (N : ℝ) := by positivity
  let topBase : ℝ := 1 / ((1 + 1 / x) * (1 + c / x))
  have htopBase : 0 ≤ topBase := by
    dsimp [topBase]
    positivity
  have hbaseIdentity :
      powerPathWeight N i /
          ((1 + 1 / x) * ((N : ℝ) * (1 + c / x))) =
        (powerPathWeight N i / (N : ℝ)) * topBase := by
    dsimp [topBase]
    field_simp [hx0, ne_of_gt hNreal, ne_of_gt hp, ne_of_gt hcbase]
  have htopPower : topBase ^ x = jointBoundaryDecrease c x := by
    dsimp [topBase]
    unfold jointBoundaryDecrease
    have hproduct : 0 ≤ (1 + 1 / x) * (1 + c / x) := by positivity
    rw [Real.rpow_neg hproduct]
    have hdiv := Real.div_rpow (show 0 ≤ (1 : ℝ) by norm_num)
      hproduct x
    simpa [div_eq_mul_inv] using hdiv
  unfold powerPathDecrease powerKKTDecrease
  rw [sub_zero, one_mul, max_eq_left hweight.le]
  have hexponent : powerShiftExponent (1 + 1 / x) = x := by
    unfold powerShiftExponent
    field_simp [hx0]
    ring
  rw [hexponent, hbaseIdentity, Real.mul_rpow hratio htopBase, htopPower]

/-- The first coordinate of every admitted joint path is exactly the scalar
joint-boundary decrease. -/
theorem powerPathDecrease_joint_first
    {N : ℕ} (hN : 0 < N) {c x : ℝ} (hx : 0 < x) (hxc : 0 < x + c) :
    powerPathDecrease ((N : ℝ) * (1 + c / x)) 1 (1 + 1 / x) 0 N
        (singularFirstIndex hN) = jointBoundaryDecrease c x := by
  rw [powerPathDecrease_joint_factorization hN hx hxc,
    powerPathWeight_first, div_self]
  · simp
  · exact_mod_cast hN.ne'

/-- Every decrease after the first vanishes along an admitted first-order
joint path. -/
theorem powerPathDecrease_joint_later_tendsto_zero
    {N : ℕ} (hN : 0 < N) {c : ℝ} (j : Fin N)
    (hj : j ≠ singularFirstIndex hN) :
    Tendsto
      (fun x : ℝ => powerPathDecrease
        ((N : ℝ) * (1 + c / x)) 1 (1 + 1 / x) 0 N j)
      atTop (nhds 0) := by
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hjpos := fin_value_pos_of_ne_first hN j hj
  have hweight := powerPathWeight_lt_horizon_of_pos j hjpos
  have hratioPositive : 0 < powerPathWeight N j / (N : ℝ) :=
    div_pos (powerPathWeight_positive j) hNreal
  have hratioBelow : powerPathWeight N j / (N : ℝ) < 1 :=
    (div_lt_one hNreal).2 hweight
  have hratioLimit := tendsto_rpow_atTop_of_base_lt_one
    (powerPathWeight N j / (N : ℝ)) (by linarith) hratioBelow
  have hproduct := hratioLimit.mul (jointBoundaryDecrease_tendsto c)
  have heq :
      (fun x : ℝ => powerPathDecrease
        ((N : ℝ) * (1 + c / x)) 1 (1 + 1 / x) 0 N j) =ᶠ[atTop]
      (fun x : ℝ =>
        (powerPathWeight N j / (N : ℝ)) ^ x *
          jointBoundaryDecrease c x) := by
    filter_upwards [eventually_gt_atTop (max 0 (-c))] with x hx
    have hx0 : 0 < x := lt_of_le_of_lt (le_max_left 0 (-c)) hx
    have hxc : 0 < x + c := by
      have hnegc : -c < x := lt_of_le_of_lt (le_max_right 0 (-c)) hx
      linarith
    exact powerPathDecrease_joint_factorization hN hx0 hxc j
  have hzero : (0 : ℝ) * Real.exp (-(1 + c)) = 0 := by ring
  rw [hzero] at hproduct
  exact hproduct.congr' heq.symm

/-- The total decrease mass on a joint path converges to its surviving first
coordinate. -/
theorem singular_joint_mass_tendsto
    {N : ℕ} (hN : 0 < N) (c : ℝ) :
    Tendsto
      (fun x : ℝ => powerPathMass ((N : ℝ) * (1 + c / x)) 1
        (1 + 1 / x) 0 N)
      atTop (nhds (Real.exp (-(1 + c)))) := by
  change Tendsto
    (fun x : ℝ => ∑ j : Fin N,
      powerPathDecrease ((N : ℝ) * (1 + c / x)) 1
        (1 + 1 / x) 0 N j)
    atTop (nhds (Real.exp (-(1 + c))))
  have hcoordinate : ∀ j : Fin N,
      Tendsto
        (fun x : ℝ => powerPathDecrease ((N : ℝ) * (1 + c / x)) 1
          (1 + 1 / x) 0 N j)
        atTop
        (nhds (if j = singularFirstIndex hN then
          Real.exp (-(1 + c)) else 0)) := by
    intro j
    by_cases hj : j = singularFirstIndex hN
    · subst j
      have heq :
          (fun x : ℝ => powerPathDecrease ((N : ℝ) * (1 + c / x)) 1
            (1 + 1 / x) 0 N (singularFirstIndex hN)) =ᶠ[atTop]
          jointBoundaryDecrease c := by
        filter_upwards [eventually_gt_atTop (max 0 (-c))] with x hx
        have hx0 : 0 < x := lt_of_le_of_lt (le_max_left 0 (-c)) hx
        have hxc : 0 < x + c := by
          have hnegc : -c < x := lt_of_le_of_lt (le_max_right 0 (-c)) hx
          linarith
        exact powerPathDecrease_joint_first hN hx0 hxc
      simpa using (jointBoundaryDecrease_tendsto c).congr' heq.symm
    · simpa [hj] using powerPathDecrease_joint_later_tendsto_zero hN j hj
  have hsum := tendsto_finsetSum Finset.univ (fun j _ => hcoordinate j)
  have hlimit :
      (∑ j : Fin N, if j = singularFirstIndex hN then
        Real.exp (-(1 + c)) else 0) = Real.exp (-(1 + c)) := by
    rw [Finset.sum_eq_single (singularFirstIndex hN)]
    · simp
    · intro b _hb hbne
      simp [hbne]
    · simp
  simpa [hlimit] using hsum

/-- Every first-order joint path with `c > -1` is eventually an unsaturated
unique full-vector optimizer; all later decreases vanish, and every follower
activity converges to the selected strict interior tie member. -/
theorem singular_fullVector_joint_path
    {N : ℕ} (hN : 0 < N) {c : ℝ} (hc : -1 < c) :
    (∀ᶠ x : ℝ in atTop,
      IsUniqueMinimizerOn (SolidSimplex : (Fin N → ℝ) → Prop)
        (powerReducedObjective ((N : ℝ) * (1 + c / x)) 1
          (1 + 1 / x) (powerPathWeight N))
        (powerPathDecrease ((N : ℝ) * (1 + c / x)) 1
          (1 + 1 / x) 0 N)) ∧
    (∀ j : Fin N, j ≠ singularFirstIndex hN →
      Tendsto
        (fun x : ℝ => powerPathDecrease ((N : ℝ) * (1 + c / x)) 1
          (1 + 1 / x) 0 N j)
        atTop (nhds 0)) ∧
    (∀ i : Fin N,
      Tendsto
        (fun x : ℝ => singularActivityAt
          (powerPathDecrease ((N : ℝ) * (1 + c / x)) 1
            (1 + 1 / x) 0 N) i)
        atTop (nhds (1 - Real.exp (-(1 + c))))) := by
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hmass := singular_joint_mass_tendsto hN c
  have hlimitBelowOne : Real.exp (-(1 + c)) < 1 := by
    apply Real.exp_lt_one_iff.mpr
    linarith
  have hmassEventually :
      ∀ᶠ x : ℝ in atTop,
        powerPathMass ((N : ℝ) * (1 + c / x)) 1
          (1 + 1 / x) 0 N ≤ 1 := by
    exact (hmass.eventually (eventually_lt_nhds hlimitBelowOne)).mono
      (fun _ hx => hx.le)
  have hoptimizer :
      ∀ᶠ x : ℝ in atTop,
        IsUniqueMinimizerOn (SolidSimplex : (Fin N → ℝ) → Prop)
          (powerReducedObjective ((N : ℝ) * (1 + c / x)) 1
            (1 + 1 / x) (powerPathWeight N))
          (powerPathDecrease ((N : ℝ) * (1 + c / x)) 1
            (1 + 1 / x) 0 N) := by
    filter_upwards [hmassEventually,
      eventually_gt_atTop (max 0 (-c))] with x hmx hx
    have hx0 : 0 < x := lt_of_le_of_lt (le_max_left 0 (-c)) hx
    have hxc : 0 < x + c := by
      have hnegc : -c < x := lt_of_le_of_lt (le_max_right 0 (-c)) hx
      linarith
    have hp : 1 < 1 + 1 / x := by linarith [one_div_pos.mpr hx0]
    have hcbase : 0 < 1 + c / x := by
      have heq : 1 + c / x = (x + c) / x := by
        field_simp [ne_of_gt hx0]
      rw [heq]
      positivity
    have hrho : 0 < (N : ℝ) * (1 + c / x) := mul_pos hNreal hcbase
    change IsUniqueMinimizerOn (SolidSimplex : (Fin N → ℝ) → Prop)
      (powerReducedObjective ((N : ℝ) * (1 + c / x)) 1
        (1 + 1 / x) (powerPathWeight N))
      (powerKKTDecrease ((N : ℝ) * (1 + c / x)) 1
        (1 + 1 / x) 0 (powerPathWeight N))
    exact powerKKTDecrease_zero_unique_minimizer (powerPathWeight N)
      hrho hp (by simpa [powerPathMass] using hmx)
  refine ⟨hoptimizer, fun j hj =>
    powerPathDecrease_joint_later_tendsto_zero hN j hj, ?_⟩
  intro i
  have hcoordinate : ∀ j : Fin N,
      Tendsto
        (fun x : ℝ => powerPathDecrease ((N : ℝ) * (1 + c / x)) 1
          (1 + 1 / x) 0 N j)
        atTop
        (nhds (if j = singularFirstIndex hN then
          Real.exp (-(1 + c)) else 0)) := by
    intro j
    by_cases hj : j = singularFirstIndex hN
    · subst j
      have heq :
          (fun x : ℝ => powerPathDecrease ((N : ℝ) * (1 + c / x)) 1
            (1 + 1 / x) 0 N (singularFirstIndex hN)) =ᶠ[atTop]
          jointBoundaryDecrease c := by
        filter_upwards [eventually_gt_atTop (max 0 (-c))] with x hx
        have hx0 : 0 < x := lt_of_le_of_lt (le_max_left 0 (-c)) hx
        have hxc : 0 < x + c := by
          have hnegc : -c < x := lt_of_le_of_lt (le_max_right 0 (-c)) hx
          linarith
        exact powerPathDecrease_joint_first hN hx0 hxc
      simpa using (jointBoundaryDecrease_tendsto c).congr' heq.symm
    · simpa [hj] using powerPathDecrease_joint_later_tendsto_zero hN j hj
  have hactivity := singularActivityAt_tendsto hcoordinate i
  have hsum :
      (∑ j : Fin N, if j.1 ≤ i.1 then
        (if j = singularFirstIndex hN then Real.exp (-(1 + c)) else 0)
        else 0) = Real.exp (-(1 + c)) := by
    rw [Finset.sum_eq_single (singularFirstIndex hN)]
    · simp [singularFirstIndex]
    · intro b _hb hbne
      simp [hbne]
    · simp
  rw [hsum] at hactivity
  exact hactivity

/-! ## Saturated branch below the critical horizon -/

theorem exists_singularSaturatedMultiplier
    {N : ℕ} {rho x : ℝ} (hrho : 0 < rho) (hx : 0 < x)
    (hmass : 1 ≤ powerPathMass rho 1 (1 + 1 / x) 0 N) :
    ∃ eta : ℝ, 0 ≤ eta ∧ eta ≤ (N : ℝ) ∧
      powerPathMass rho 1 (1 + 1 / x) eta N = 1 := by
  have hp : 1 < 1 + 1 / x := by linarith [one_div_pos.mpr hx]
  have hupper : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  have hclips : ∀ i : Fin N,
      (1 : ℝ) * powerPathWeight N i ≤ (N : ℝ) := by
    intro i
    simpa using powerPathWeight_le_horizon i
  obtain ⟨eta, heta, hetaUpper, hetaMass⟩ :=
    exists_powerKKT_multiplier (powerPathWeight N) hrho hp hupper
      hclips (by simpa [powerPathMass] using hmass)
  exact ⟨eta, heta, hetaUpper, by simpa [powerPathMass] using hetaMass⟩

/- A canonical chosen multiplier for the saturated branch.  Outside the
positive, superlinear, mass-saturated domain it is defined to be zero; each
result below exposes the admission predicate explicitly. -/
noncomputable def singularSaturatedMultiplier (N : ℕ) (rho x : ℝ) : ℝ :=
  if h : 0 < rho ∧ 0 < x ∧
      1 ≤ powerPathMass rho 1 (1 + 1 / x) 0 N then
    Classical.choose (exists_singularSaturatedMultiplier h.1 h.2.1 h.2.2)
  else 0

theorem singularSaturatedMultiplier_spec
    {N : ℕ} {rho x : ℝ} (hrho : 0 < rho) (hx : 0 < x)
    (hmass : 1 ≤ powerPathMass rho 1 (1 + 1 / x) 0 N) :
    0 ≤ singularSaturatedMultiplier N rho x ∧
      singularSaturatedMultiplier N rho x ≤ (N : ℝ) ∧
      powerPathMass rho 1 (1 + 1 / x)
        (singularSaturatedMultiplier N rho x) N = 1 := by
  have h : 0 < rho ∧ 0 < x ∧
      1 ≤ powerPathMass rho 1 (1 + 1 / x) 0 N := ⟨hrho, hx, hmass⟩
  rw [singularSaturatedMultiplier, dif_pos h]
  exact Classical.choose_spec
    (exists_singularSaturatedMultiplier hrho hx hmass)

/-- Below the critical horizon, the zero-multiplier mass eventually exceeds
one, so the solid-simplex constraint is active. -/
theorem singular_ratio_below_mass_eventually_saturated
    {N : ℕ} {rho : ℝ} (hrho : 0 < rho) (hrhoN : rho < (N : ℝ)) :
    ∀ᶠ x : ℝ in atTop,
      1 ≤ powerPathMass rho 1 (1 + 1 / x) 0 N := by
  have hN : 0 < N := by
    have hNreal : 0 < (N : ℝ) := lt_trans hrho hrhoN
    exact_mod_cast hNreal
  let first := singularFirstIndex hN
  have hratio : 1 < (N : ℝ) / rho := (one_lt_div hrho).2 hrhoN
  have hfirstAtTop :
      Tendsto
        (fun x : ℝ => powerPathDecrease rho 1 (1 + 1 / x) 0 N first)
        atTop atTop := by
    have heq :
        (fun x : ℝ => powerPathDecrease rho 1 (1 + 1 / x) 0 N first) =ᶠ[atTop]
        (fun x : ℝ => fixedRatioUnclippedDecrease ((N : ℝ) / rho) x) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      dsimp [first]
      rw [powerPathDecrease_zero_eq_fixedRatioUnclipped hrho hx,
        powerPathWeight_first hN]
    exact (fixedRatioUnclippedDecrease_tendsto_atTop hratio).congr' heq.symm
  have hfirstLarge := hfirstAtTop.eventually_ge_atTop 1
  filter_upwards [hfirstLarge, eventually_gt_atTop (0 : ℝ)] with x hfirst hx
  have hp : 1 < 1 + 1 / x := by linarith [one_div_pos.mpr hx]
  have hnonnegative : ∀ j : Fin N,
      0 ≤ powerPathDecrease rho 1 (1 + 1 / x) 0 N j :=
    fun j => powerKKTDecrease_nonnegative (powerPathWeight N) hrho hp j
  have hleMass :
      powerPathDecrease rho 1 (1 + 1 / x) 0 N first ≤
        powerPathMass rho 1 (1 + 1 / x) 0 N := by
    change powerPathDecrease rho 1 (1 + 1 / x) 0 N first ≤
      ∑ j : Fin N, powerPathDecrease rho 1 (1 + 1 / x) 0 N j
    exact Finset.single_le_sum (fun j _ => hnonnegative j)
      (Finset.mem_univ first)
  exact hfirst.trans hleMass

theorem singularSaturatedMultiplier_eventually_spec
    {N : ℕ} {rho : ℝ} (hrho : 0 < rho) (hrhoN : rho < (N : ℝ)) :
    ∀ᶠ x : ℝ in atTop,
      0 < x ∧
      0 ≤ singularSaturatedMultiplier N rho x ∧
      singularSaturatedMultiplier N rho x ≤ (N : ℝ) ∧
      powerPathMass rho 1 (1 + 1 / x)
        (singularSaturatedMultiplier N rho x) N = 1 := by
  filter_upwards [singular_ratio_below_mass_eventually_saturated hrho hrhoN,
    eventually_gt_atTop (0 : ℝ)] with x hmass hx
  exact ⟨hx, singularSaturatedMultiplier_spec hrho hx hmass⟩

theorem saturatedMultiplier_lt_horizon_of_mass_one
    {N : ℕ} {rho x eta : ℝ} (_hrho : 0 < rho) (hx : 0 < x)
    (_heta : 0 ≤ eta) (hetaUpper : eta ≤ (N : ℝ))
    (hmass : powerPathMass rho 1 (1 + 1 / x) eta N = 1) :
    eta < (N : ℝ) := by
  have hp : 1 < 1 + 1 / x := by linarith [one_div_pos.mpr hx]
  by_contra hnot
  have hetaEq : eta = (N : ℝ) := le_antisymm hetaUpper (le_of_not_gt hnot)
  have hallZero : ∀ i : Fin N,
      powerPathDecrease rho 1 (1 + 1 / x) eta N i = 0 := by
    intro i
    have hnum : (1 : ℝ) * powerPathWeight N i - eta ≤ 0 := by
      rw [hetaEq, one_mul]
      exact sub_nonpos.mpr (powerPathWeight_le_horizon i)
    unfold powerPathDecrease powerKKTDecrease
    rw [max_eq_right hnum, zero_div,
      Real.zero_rpow (powerShiftExponent_positive hp).ne']
  have hmassZero : powerPathMass rho 1 (1 + 1 / x) eta N = 0 := by
    change (∑ i : Fin N,
      powerPathDecrease rho 1 (1 + 1 / x) eta N i) = 0
    exact Finset.sum_eq_zero (fun i _ => hallZero i)
  linarith

/-- Every saturated decrease is nonnegative and at most one. -/
theorem saturatedDecrease_mem_Icc
    {N : ℕ} {rho x eta : ℝ} (hrho : 0 < rho) (hx : 0 < x)
    (hmass : powerPathMass rho 1 (1 + 1 / x) eta N = 1)
    (i : Fin N) :
    powerPathDecrease rho 1 (1 + 1 / x) eta N i ∈ Icc (0 : ℝ) 1 := by
  have hp : 1 < 1 + 1 / x := by linarith [one_div_pos.mpr hx]
  have hnonnegative : ∀ j : Fin N,
      0 ≤ powerPathDecrease rho 1 (1 + 1 / x) eta N j :=
    fun j => powerKKTDecrease_nonnegative (powerPathWeight N) hrho hp j
  constructor
  · exact hnonnegative i
  · have hleSum :
        powerPathDecrease rho 1 (1 + 1 / x) eta N i ≤
          ∑ j : Fin N, powerPathDecrease rho 1 (1 + 1 / x) eta N j :=
      Finset.single_le_sum (fun j _ => hnonnegative j) (Finset.mem_univ i)
    change (∑ j : Fin N,
      powerPathDecrease rho 1 (1 + 1 / x) eta N j) = 1 at hmass
    linarith

/-- Exact ratio factorization of every saturated coordinate through the
first decrease. -/
theorem saturatedDecrease_eq_first_mul_ratio_rpow
    {N : ℕ} (hN : 0 < N) {rho x eta : ℝ}
    (hrho : 0 < rho) (hx : 0 < x) (_heta : 0 ≤ eta)
    (hetaN : eta < (N : ℝ)) (i : Fin N) :
    powerPathDecrease rho 1 (1 + 1 / x) eta N i =
      powerPathDecrease rho 1 (1 + 1 / x) eta N
          (singularFirstIndex hN) *
        (max (powerPathWeight N i - eta) 0 / ((N : ℝ) - eta)) ^ x := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hp : 1 < 1 + 1 / x := by linarith [one_div_pos.mpr hx]
  have hp0 : 0 < 1 + 1 / x := lt_trans zero_lt_one hp
  have hden : 0 < (1 + 1 / x) * rho := mul_pos hp0 hrho
  have htopNumerator : 0 < (N : ℝ) - eta := sub_pos.mpr hetaN
  have htopWeight :
      (1 : ℝ) * powerPathWeight N (singularFirstIndex hN) - eta =
        (N : ℝ) - eta := by rw [one_mul, powerPathWeight_first]
  have hratioNonnegative :
      0 ≤ max (powerPathWeight N i - eta) 0 / ((N : ℝ) - eta) :=
    div_nonneg (le_max_right _ _) htopNumerator.le
  have htopBaseNonnegative :
      0 ≤ ((N : ℝ) - eta) / ((1 + 1 / x) * rho) := by positivity
  have hbaseIdentity :
      max (powerPathWeight N i - eta) 0 / ((1 + 1 / x) * rho) =
        (((N : ℝ) - eta) / ((1 + 1 / x) * rho)) *
          (max (powerPathWeight N i - eta) 0 / ((N : ℝ) - eta)) := by
    field_simp [ne_of_gt htopNumerator, ne_of_gt hden]
  unfold powerPathDecrease powerKKTDecrease
  rw [one_mul]
  have hexponent : powerShiftExponent (1 + 1 / x) = x := by
    unfold powerShiftExponent
    field_simp [hx0]
    ring
  rw [hexponent, htopWeight, max_eq_left htopNumerator.le,
    hbaseIdentity, Real.mul_rpow htopBaseNonnegative hratioNonnegative]

/-- For every later coordinate, the saturated decrease ratio is bounded by
the fixed geometric constant `(N-1)/N`, uniformly in the multiplier. -/
theorem saturatedDecrease_ratio_le_geometric
    {N : ℕ} (hN : 0 < N) {eta : ℝ} (heta : 0 ≤ eta)
    (hetaN : eta < (N : ℝ)) (i : Fin N)
    (hi : i ≠ singularFirstIndex hN) :
    max (powerPathWeight N i - eta) 0 / ((N : ℝ) - eta) ≤
      ((N : ℝ) - 1) / (N : ℝ) := by
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hden : 0 < (N : ℝ) - eta := sub_pos.mpr hetaN
  have hipos := fin_value_pos_of_ne_first hN i hi
  have hNone : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hweight : powerPathWeight N i ≤ (N : ℝ) - 1 := by
    unfold powerPathWeight
    have hnat : N - i.1 ≤ N - 1 := by omega
    calc
      ((N - i.1 : ℕ) : ℝ) ≤ ((N - 1 : ℕ) : ℝ) := by
        exact_mod_cast hnat
      _ = (N : ℝ) - 1 := by
        rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hN.ne')]
        norm_num
  by_cases hnum : powerPathWeight N i - eta ≤ 0
  · rw [max_eq_right hnum, zero_div]
    exact div_nonneg (sub_nonneg.mpr hNone) hNreal.le
  · have hnumPos : 0 < powerPathWeight N i - eta := lt_of_not_ge hnum
    rw [max_eq_left hnumPos.le]
    apply (div_le_div_iff₀ hden hNreal).2
    nlinarith

/-- In the saturated branch, every decrease after the first is uniformly
geometrically dominated and therefore vanishes as the exponent approaches
one. -/
theorem singular_ratio_below_later_tendsto_zero
    {N : ℕ} {rho : ℝ} (hrho : 0 < rho) (hrhoN : rho < (N : ℝ))
    (j : Fin N) (hj : j ≠ singularFirstIndex
      (by
        have hNreal : 0 < (N : ℝ) := lt_trans hrho hrhoN
        exact_mod_cast hNreal)) :
    Tendsto
      (fun x : ℝ => powerPathDecrease rho 1 (1 + 1 / x)
        (singularSaturatedMultiplier N rho x) N j)
      atTop (nhds 0) := by
  have hN : 0 < N := by
    have hNreal : 0 < (N : ℝ) := lt_trans hrho hrhoN
    exact_mod_cast hNreal
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hj' : j ≠ singularFirstIndex hN := by simpa using hj
  let geometric : ℝ := ((N : ℝ) - 1) / (N : ℝ)
  have hgeometricNonnegative : 0 ≤ geometric := by
    dsimp [geometric]
    have hNone : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    positivity
  have hgeometricBelow : geometric < 1 := by
    dsimp [geometric]
    rw [div_lt_one hNreal]
    linarith
  have hgeometricLimit :
      Tendsto (fun x : ℝ => geometric ^ x) atTop (nhds 0) :=
    tendsto_rpow_atTop_of_base_lt_one geometric (by linarith) hgeometricBelow
  have hbounds :
      ∀ᶠ x : ℝ in atTop,
        0 ≤ powerPathDecrease rho 1 (1 + 1 / x)
            (singularSaturatedMultiplier N rho x) N j ∧
        powerPathDecrease rho 1 (1 + 1 / x)
            (singularSaturatedMultiplier N rho x) N j ≤ geometric ^ x := by
    filter_upwards [singularSaturatedMultiplier_eventually_spec hrho hrhoN]
      with x hspec
    rcases hspec with ⟨hx, heta, hetaUpper, hmass⟩
    have hp : 1 < 1 + 1 / x := by linarith [one_div_pos.mpr hx]
    have hetaN := saturatedMultiplier_lt_horizon_of_mass_one
      hrho hx heta hetaUpper hmass
    have hratio := saturatedDecrease_ratio_le_geometric hN heta hetaN j hj'
    have hratioNonnegative :
        0 ≤ max (powerPathWeight N j - singularSaturatedMultiplier N rho x) 0 /
          ((N : ℝ) - singularSaturatedMultiplier N rho x) := by
      exact div_nonneg (le_max_right _ _) (sub_nonneg.mpr hetaN.le)
    have hratioPower :
        (max (powerPathWeight N j - singularSaturatedMultiplier N rho x) 0 /
            ((N : ℝ) - singularSaturatedMultiplier N rho x)) ^ x ≤
          geometric ^ x :=
      Real.rpow_le_rpow hratioNonnegative hratio hx.le
    have hfirstMem := saturatedDecrease_mem_Icc hrho hx hmass
      (singularFirstIndex hN)
    have hfactor := saturatedDecrease_eq_first_mul_ratio_rpow hN hrho hx
      heta hetaN j
    constructor
    · exact powerKKTDecrease_nonnegative (powerPathWeight N) hrho hp j
    · rw [hfactor]
      calc
        powerPathDecrease rho 1 (1 + 1 / x)
              (singularSaturatedMultiplier N rho x) N (singularFirstIndex hN) *
            (max (powerPathWeight N j - singularSaturatedMultiplier N rho x) 0 /
              ((N : ℝ) - singularSaturatedMultiplier N rho x)) ^ x ≤
            1 * (max (powerPathWeight N j - singularSaturatedMultiplier N rho x) 0 /
              ((N : ℝ) - singularSaturatedMultiplier N rho x)) ^ x := by
                exact mul_le_mul_of_nonneg_right hfirstMem.2
                  (Real.rpow_nonneg hratioNonnegative _)
        _ ≤ 1 * geometric ^ x := mul_le_mul_of_nonneg_left hratioPower zero_le_one
        _ = geometric ^ x := one_mul _
  exact squeeze_zero' (hbounds.mono (fun _ h => h.1))
    (hbounds.mono (fun _ h => h.2)) hgeometricLimit

/-- Since the saturated mass is exactly one and every later decrease
vanishes, the first decrease converges to one. -/
theorem singular_ratio_below_first_tendsto_one
    {N : ℕ} {rho : ℝ} (hrho : 0 < rho) (hrhoN : rho < (N : ℝ)) :
    Tendsto
      (fun x : ℝ => powerPathDecrease rho 1 (1 + 1 / x)
        (singularSaturatedMultiplier N rho x) N
        (singularFirstIndex
          (by
            have hNreal : 0 < (N : ℝ) := lt_trans hrho hrhoN
            exact_mod_cast hNreal)))
      atTop (nhds 1) := by
  have hN : 0 < N := by
    have hNreal : 0 < (N : ℝ) := lt_trans hrho hrhoN
    exact_mod_cast hNreal
  let first := singularFirstIndex hN
  let tail : ℝ → ℝ := fun x =>
    ∑ j ∈ (Finset.univ.erase first),
      powerPathDecrease rho 1 (1 + 1 / x)
        (singularSaturatedMultiplier N rho x) N j
  have htail : Tendsto tail atTop (nhds 0) := by
    dsimp [tail]
    have hsum := tendsto_finsetSum (Finset.univ.erase first) (fun j hj => by
      have hjne : j ≠ first := Finset.ne_of_mem_erase hj
      have hj' : j ≠ singularFirstIndex hN := by simpa [first] using hjne
      exact singular_ratio_below_later_tendsto_zero hrho hrhoN j hj')
    simpa using hsum
  have heq :
      (fun x : ℝ => powerPathDecrease rho 1 (1 + 1 / x)
        (singularSaturatedMultiplier N rho x) N first) =ᶠ[atTop]
      (fun x => 1 - tail x) := by
    filter_upwards [singularSaturatedMultiplier_eventually_spec hrho hrhoN]
      with x hspec
    rcases hspec with ⟨_hx, _heta, _hetaUpper, hmass⟩
    change (∑ j : Fin N, powerPathDecrease rho 1 (1 + 1 / x)
      (singularSaturatedMultiplier N rho x) N j) = 1 at hmass
    have hsplit :
        (∑ j : Fin N, powerPathDecrease rho 1 (1 + 1 / x)
          (singularSaturatedMultiplier N rho x) N j) =
        powerPathDecrease rho 1 (1 + 1 / x)
            (singularSaturatedMultiplier N rho x) N first + tail x := by
      have herase := Finset.sum_erase_add Finset.univ
        (fun j : Fin N => powerPathDecrease rho 1 (1 + 1 / x)
          (singularSaturatedMultiplier N rho x) N j)
        (Finset.mem_univ first)
      dsimp [tail]
      rw [← herase]
      ring
    rw [hsplit] at hmass
    linarith
  have hlimit : Tendsto (fun x : ℝ => (1 : ℝ) - tail x) atTop (nhds 1) := by
    simpa using (tendsto_const_nhds.sub htail)
  simpa [first] using hlimit.congr' heq.symm

/-- Complete fixed-ratio branch below the critical horizon: the chosen KKT
vector is eventually the unique optimizer, its first decrease tends to one,
every later decrease tends to zero, and every follower activity tends to
zero. -/
theorem singular_fullVector_ratio_below
    {N : ℕ} {rho : ℝ} (hrho : 0 < rho) (hrhoN : rho < (N : ℝ)) :
    let hN : 0 < N := by
      have hNreal : 0 < (N : ℝ) := lt_trans hrho hrhoN
      exact_mod_cast hNreal
    (∀ᶠ x : ℝ in atTop,
      IsUniqueMinimizerOn (SolidSimplex : (Fin N → ℝ) → Prop)
        (powerReducedObjective rho 1 (1 + 1 / x) (powerPathWeight N))
        (powerPathDecrease rho 1 (1 + 1 / x)
          (singularSaturatedMultiplier N rho x) N)) ∧
    Tendsto
      (fun x : ℝ => powerPathDecrease rho 1 (1 + 1 / x)
        (singularSaturatedMultiplier N rho x) N (singularFirstIndex hN))
      atTop (nhds 1) ∧
    (∀ j : Fin N, j ≠ singularFirstIndex hN →
      Tendsto
        (fun x : ℝ => powerPathDecrease rho 1 (1 + 1 / x)
          (singularSaturatedMultiplier N rho x) N j)
        atTop (nhds 0)) ∧
    (∀ i : Fin N,
      Tendsto
        (fun x : ℝ => singularActivityAt
          (powerPathDecrease rho 1 (1 + 1 / x)
            (singularSaturatedMultiplier N rho x) N) i)
        atTop (nhds 0)) := by
  dsimp only
  have hN : 0 < N := by
    have hNreal : 0 < (N : ℝ) := lt_trans hrho hrhoN
    exact_mod_cast hNreal
  have hoptimizer :
      ∀ᶠ x : ℝ in atTop,
        IsUniqueMinimizerOn (SolidSimplex : (Fin N → ℝ) → Prop)
          (powerReducedObjective rho 1 (1 + 1 / x) (powerPathWeight N))
          (powerPathDecrease rho 1 (1 + 1 / x)
            (singularSaturatedMultiplier N rho x) N) := by
    filter_upwards [singularSaturatedMultiplier_eventually_spec hrho hrhoN]
      with x hspec
    rcases hspec with ⟨hx, heta, _hetaUpper, hmass⟩
    have hp : 1 < 1 + 1 / x := by linarith [one_div_pos.mpr hx]
    change IsUniqueMinimizerOn (SolidSimplex : (Fin N → ℝ) → Prop)
      (powerReducedObjective rho 1 (1 + 1 / x) (powerPathWeight N))
      (powerKKTDecrease rho 1 (1 + 1 / x)
        (singularSaturatedMultiplier N rho x) (powerPathWeight N))
    exact powerKKTDecrease_unique_minimizer (powerPathWeight N)
      hrho hp heta (by simpa [powerPathMass] using hmass)
  have hfirst : Tendsto
      (fun x : ℝ => powerPathDecrease rho 1 (1 + 1 / x)
        (singularSaturatedMultiplier N rho x) N (singularFirstIndex hN))
      atTop (nhds 1) := by
    simpa using singular_ratio_below_first_tendsto_one hrho hrhoN
  have hlater : ∀ j : Fin N, j ≠ singularFirstIndex hN →
      Tendsto
        (fun x : ℝ => powerPathDecrease rho 1 (1 + 1 / x)
          (singularSaturatedMultiplier N rho x) N j)
        atTop (nhds 0) := by
    intro j hj
    simpa using singular_ratio_below_later_tendsto_zero hrho hrhoN j hj
  refine ⟨hoptimizer, hfirst, hlater, ?_⟩
  intro i
  have hcoordinate : ∀ j : Fin N,
      Tendsto
        (fun x : ℝ => powerPathDecrease rho 1 (1 + 1 / x)
          (singularSaturatedMultiplier N rho x) N j)
        atTop (nhds (if j = singularFirstIndex hN then 1 else 0)) := by
    intro j
    by_cases hj : j = singularFirstIndex hN
    · simpa [hj] using hfirst
    · simpa [hj] using hlater j hj
  have hactivity := singularActivityAt_tendsto hcoordinate i
  have hsum :
      (∑ j : Fin N, if j.1 ≤ i.1 then
        (if j = singularFirstIndex hN then (1 : ℝ) else 0) else 0) = 1 := by
    rw [Finset.sum_eq_single (singularFirstIndex hN)]
    · simp [singularFirstIndex]
    · intro b _hb hbne
      simp [hbne]
    · simp
  rw [hsum] at hactivity
  simpa using hactivity

/-! ## Integrated canonical package -/

def SingularFixedRatioAboveProof (N : ℕ) (rho : ℝ) : Prop :=
  (∀ᶠ x : ℝ in atTop,
    IsUniqueMinimizerOn (SolidSimplex : (Fin N → ℝ) → Prop)
      (powerReducedObjective rho 1 (1 + 1 / x) (powerPathWeight N))
      (powerPathDecrease rho 1 (1 + 1 / x) 0 N)) ∧
  (∀ j : Fin N,
    Tendsto (fun x : ℝ => powerPathDecrease rho 1
      (1 + 1 / x) 0 N j) atTop (nhds 0)) ∧
  (∀ i : Fin N,
    Tendsto (fun x : ℝ => singularActivityAt
      (powerPathDecrease rho 1 (1 + 1 / x) 0 N) i)
      atTop (nhds 1))

def SingularFixedRatioEqualityProof (N : ℕ) (hN : 0 < N) : Prop :=
  (∀ᶠ x : ℝ in atTop,
    IsUniqueMinimizerOn (SolidSimplex : (Fin N → ℝ) → Prop)
      (powerReducedObjective (N : ℝ) 1 (1 + 1 / x) (powerPathWeight N))
      (powerPathDecrease (N : ℝ) 1 (1 + 1 / x) 0 N)) ∧
  Tendsto (fun x : ℝ => powerPathDecrease (N : ℝ) 1
      (1 + 1 / x) 0 N (singularFirstIndex hN))
    atTop (nhds (Real.exp (-1))) ∧
  (∀ j : Fin N, j ≠ singularFirstIndex hN →
    Tendsto (fun x : ℝ => powerPathDecrease (N : ℝ) 1
      (1 + 1 / x) 0 N j) atTop (nhds 0)) ∧
  (∀ i : Fin N,
    Tendsto (fun x : ℝ => singularActivityAt
      (powerPathDecrease (N : ℝ) 1 (1 + 1 / x) 0 N) i)
      atTop (nhds (1 - Real.exp (-1))))

def SingularFixedRatioBelowProof
    (N : ℕ) (rho : ℝ) (hN : 0 < N) : Prop :=
  (∀ᶠ x : ℝ in atTop,
    IsUniqueMinimizerOn (SolidSimplex : (Fin N → ℝ) → Prop)
      (powerReducedObjective rho 1 (1 + 1 / x) (powerPathWeight N))
      (powerPathDecrease rho 1 (1 + 1 / x)
        (singularSaturatedMultiplier N rho x) N)) ∧
  Tendsto (fun x : ℝ => powerPathDecrease rho 1 (1 + 1 / x)
      (singularSaturatedMultiplier N rho x) N (singularFirstIndex hN))
    atTop (nhds 1) ∧
  (∀ j : Fin N, j ≠ singularFirstIndex hN →
    Tendsto (fun x : ℝ => powerPathDecrease rho 1 (1 + 1 / x)
      (singularSaturatedMultiplier N rho x) N j) atTop (nhds 0)) ∧
  (∀ i : Fin N,
    Tendsto (fun x : ℝ => singularActivityAt
      (powerPathDecrease rho 1 (1 + 1 / x)
        (singularSaturatedMultiplier N rho x) N) i)
      atTop (nhds 0))

def SingularJointPathProof
    (N : ℕ) (c : ℝ) (hN : 0 < N) : Prop :=
  (∀ᶠ x : ℝ in atTop,
    IsUniqueMinimizerOn (SolidSimplex : (Fin N → ℝ) → Prop)
      (powerReducedObjective ((N : ℝ) * (1 + c / x)) 1
        (1 + 1 / x) (powerPathWeight N))
      (powerPathDecrease ((N : ℝ) * (1 + c / x)) 1
        (1 + 1 / x) 0 N)) ∧
  Tendsto (fun x : ℝ => powerPathDecrease
      ((N : ℝ) * (1 + c / x)) 1 (1 + 1 / x) 0 N
      (singularFirstIndex hN))
    atTop (nhds (Real.exp (-(1 + c)))) ∧
  (∀ j : Fin N, j ≠ singularFirstIndex hN →
    Tendsto (fun x : ℝ => powerPathDecrease
      ((N : ℝ) * (1 + c / x)) 1 (1 + 1 / x) 0 N j)
      atTop (nhds 0)) ∧
  (∀ i : Fin N,
    Tendsto (fun x : ℝ => singularActivityAt
      (powerPathDecrease ((N : ℝ) * (1 + c / x)) 1
        (1 + 1 / x) 0 N) i)
      atTop (nhds (1 - Real.exp (-(1 + c)))))

/-- Full finite-dimensional CHG-B15 optimizer package.  It proves the two
off-equality endpoints, fixed-equality interior selection, and every admitted
first-order joint-path selection through actual unique path optimizers.  In
all four branches every coordinate after the first is proved to vanish. -/
theorem chg_b15_full_vector_optimizer_boundary_law :
    (∀ (N : ℕ) (rho : ℝ), 0 < N → (N : ℝ) < rho →
      SingularFixedRatioAboveProof N rho) ∧
    (∀ (N : ℕ) (hN : 0 < N),
      SingularFixedRatioEqualityProof N hN) ∧
    (∀ (N : ℕ) (rho : ℝ) (hN : 0 < N),
      0 < rho → rho < (N : ℝ) →
        SingularFixedRatioBelowProof N rho hN) ∧
    (∀ (N : ℕ) (c : ℝ) (hN : 0 < N), -1 < c →
      SingularJointPathProof N c hN) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro N rho hN hrho
    exact singular_fullVector_ratio_above hN hrho
  · intro N hN
    rcases singular_fullVector_ratio_equal hN with
      ⟨hoptimizer, hlater, hactivity⟩
    refine ⟨hoptimizer, ?_, hlater, hactivity⟩
    simpa using singular_equality_decrease_tendsto hN (singularFirstIndex hN)
  · intro N rho hN hrho hrhoN
    have hbelow := singular_fullVector_ratio_below hrho hrhoN
    simpa [SingularFixedRatioBelowProof] using hbelow
  · intro N c hN hc
    rcases singular_fullVector_joint_path hN hc with
      ⟨hoptimizer, hlater, hactivity⟩
    refine ⟨hoptimizer, ?_, hlater, hactivity⟩
    have heq :
        (fun x : ℝ => powerPathDecrease ((N : ℝ) * (1 + c / x)) 1
          (1 + 1 / x) 0 N (singularFirstIndex hN)) =ᶠ[atTop]
        jointBoundaryDecrease c := by
      filter_upwards [eventually_gt_atTop (max 0 (-c))] with x hx
      have hx0 : 0 < x := lt_of_le_of_lt (le_max_left 0 (-c)) hx
      have hxc : 0 < x + c := by
        have hnegc : -c < x := lt_of_le_of_lt (le_max_right 0 (-c)) hx
        linarith
      exact powerPathDecrease_joint_first hN hx0 hxc
    exact (jointBoundaryDecrease_tendsto c).congr' heq.symm

end PhonologicalCalculus.ContinuousHG
