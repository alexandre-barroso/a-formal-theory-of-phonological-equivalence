import PhonologicalCalculus.ContinuousHG.Quadratic
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Quadratic projection sensitivity

Completing the square sends the quadratic reduced objective to Euclidean
projection of a ratio-scaled weight vector.  This file proves the exact
pre-projection metric identity and the registered finite sensitivity
result.  Nonexpansiveness of projection can then only decrease this
distance.
-/

namespace PhonologicalCalculus.ContinuousHG

open scoped BigOperators InnerProductSpace

/-- Any two points satisfying the variational characterization of projection
onto the same set obey the Hilbert-space nonexpansiveness bound.  Convexity
and closedness are needed to obtain such points, but the metric implication
uses only these two variational inequalities. -/
theorem variational_projection_nonexpansive
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {K : Set E} {u v pu pv : E}
    (hpuK : pu ∈ K) (hpvK : pv ∈ K)
    (hpu : ∀ z, z ∈ K → ⟪u - pu, z - pu⟫_ℝ ≤ 0)
    (hpv : ∀ z, z ∈ K → ⟪v - pv, z - pv⟫_ℝ ≤ 0) :
    ‖pu - pv‖ ≤ ‖u - v‖ := by
  have hpuDirection : 0 ≤ ⟪u - pu, pu - pv⟫_ℝ := by
    have h := hpu pv hpvK
    have hneg : pv - pu = -(pu - pv) := by abel
    rw [hneg, inner_neg_right] at h
    linarith
  have hpvDirection : ⟪v - pv, pu - pv⟫_ℝ ≤ 0 :=
    hpv pu hpuK
  have hidentity :
      ⟪pu - pv, pu - pv⟫_ℝ =
        ⟪u - v, pu - pv⟫_ℝ -
          ⟪u - pu, pu - pv⟫_ℝ +
          ⟪v - pv, pu - pv⟫_ℝ := by
    simp only [inner_sub_left]
    ring
  have hinner :
      ⟪pu - pv, pu - pv⟫_ℝ ≤ ⟪u - v, pu - pv⟫_ℝ := by
    rw [hidentity]
    linarith
  by_cases hzero : pu - pv = 0
  · simp [hzero]
  · have hnormPositive : 0 < ‖pu - pv‖ := norm_pos_iff.mpr hzero
    have hcauchy := real_inner_le_norm (u - v) (pu - pv)
    rw [real_inner_self_eq_norm_mul_norm] at hinner
    nlinarith

/-- Metric projections onto a common convex carrier are nonexpansive whenever
the two minimizing points exist.  This is the exact projection theorem used
by the quadratic ratio-sensitivity argument. -/
theorem convex_metric_projection_nonexpansive
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {K : Set E} {u v pu pv : E}
    (hK : Convex ℝ K) (hpuK : pu ∈ K) (hpvK : pv ∈ K)
    (hpu : ‖u - pu‖ = ⨅ z : K, ‖u - z‖)
    (hpv : ‖v - pv‖ = ⨅ z : K, ‖v - z‖) :
    ‖pu - pv‖ ≤ ‖u - v‖ := by
  apply variational_projection_nonexpansive hpuK hpvK
  · exact (norm_eq_iInf_iff_real_inner_le_zero hK hpuK).1 hpu
  · exact (norm_eq_iInf_iff_real_inner_le_zero hK hpvK).1 hpv

/-- Completing the quadratic square identifies every constrained minimizer
with the Euclidean metric projection of the unconstrained stationary point
onto the solid simplex.  This is the formal bridge between the objective
minimizer proved in the quadratic module and the Hilbert-space projection
result above. -/
theorem quadratic_minimizer_is_metric_projection
    {ι : Type*} [Fintype ι] {h m : ℝ} (hh : 0 < h)
    (weight u : ι → ℝ)
    (hu : IsUniqueMinimizerOn (SolidSimplex : (ι → ℝ) → Prop)
      (quadraticReducedObjective h m weight) u) :
    let center : EuclideanSpace ℝ ι :=
      WithLp.toLp 2 (fun i ↦ m * weight i / (2 * h))
    let projected : EuclideanSpace ℝ ι := WithLp.toLp 2 u
    let carrier : Set (EuclideanSpace ℝ ι) :=
      {z | SolidSimplex (fun i ↦ z i)}
    ‖center - projected‖ = ⨅ z : carrier, ‖center - z‖ := by
  classical
  dsimp only
  let carrier : Set (EuclideanSpace ℝ ι) :=
    {z | SolidSimplex (fun i ↦ z i)}
  change
    ‖(WithLp.toLp 2 (fun i ↦ m * weight i / (2 * h)) :
        EuclideanSpace ℝ ι) - WithLp.toLp 2 u‖ =
      ⨅ z : carrier,
        ‖(WithLp.toLp 2 (fun i ↦ m * weight i / (2 * h)) :
          EuclideanSpace ℝ ι) - z‖
  let projectedPoint : carrier :=
    ⟨WithLp.toLp 2 u, by
      change SolidSimplex u
      exact hu.1⟩
  letI : Nonempty carrier := ⟨projectedPoint⟩
  apply le_antisymm
  · apply le_ciInf
    intro z
    let centerRaw : ι → ℝ := fun i ↦ m * weight i / (2 * h)
    let competitor : ι → ℝ := fun i ↦ z.1 i
    have hz : SolidSimplex competitor := z.2
    have hobjective := (hu.2 competitor hz).1
    have hgapU :
        quadraticReducedObjective h m weight u -
            quadraticReducedObjective h m weight centerRaw =
          h * ∑ i, (u i - centerRaw i) ^ 2 := by
      simpa [centerRaw] using
        quadratic_unconstrained_gap (ι := ι) hh.ne' weight u
    have hgapZ :
        quadraticReducedObjective h m weight competitor -
            quadraticReducedObjective h m weight centerRaw =
          h * ∑ i, (competitor i - centerRaw i) ^ 2 := by
      simpa [centerRaw] using
        quadratic_unconstrained_gap (ι := ι) hh.ne' weight competitor
    have hsquares :
        (∑ i, (u i - centerRaw i) ^ 2) ≤
          ∑ i, (competitor i - centerRaw i) ^ 2 := by
      nlinarith
    have hnormU :
        ‖(WithLp.toLp 2 centerRaw : EuclideanSpace ℝ ι) -
            WithLp.toLp 2 u‖ ^ 2 =
          ∑ i, (u i - centerRaw i) ^ 2 := by
      rw [PiLp.norm_sq_eq_of_L2]
      apply Finset.sum_congr rfl
      intro i _
      simp [Real.norm_eq_abs, sq_abs]
      ring
    have hnormZ :
        ‖(WithLp.toLp 2 centerRaw : EuclideanSpace ℝ ι) - z.1‖ ^ 2 =
          ∑ i, (competitor i - centerRaw i) ^ 2 := by
      rw [PiLp.norm_sq_eq_of_L2]
      apply Finset.sum_congr rfl
      intro i _
      simp [competitor, Real.norm_eq_abs, sq_abs]
      ring
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simpa [centerRaw] using
      hnormU.trans_le (hsquares.trans_eq hnormZ.symm)
  · exact ciInf_le
      ⟨0, fun _ ⟨_, hmem⟩ ↦ hmem ▸ norm_nonneg _⟩ projectedPoint

/-- The Euclidean realization of the solid simplex is convex. -/
theorem solidSimplex_euclidean_convex
    {ι : Type*} [Fintype ι] :
    Convex ℝ {z : EuclideanSpace ℝ ι |
      SolidSimplex (fun i ↦ z i)} := by
  classical
  intro x hx y hy a b ha hb hab
  constructor
  · intro i
    change 0 ≤ a * x i + b * y i
    exact add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i))
  · change (∑ i, (a * x i + b * y i)) ≤ 1
    calc
      (∑ i, (a * x i + b * y i)) =
          a * (∑ i, x i) + b * (∑ i, y i) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ ≤ a * 1 + b * 1 :=
        add_le_add
          (mul_le_mul_of_nonneg_left hx.2 ha)
          (mul_le_mul_of_nonneg_left hy.2 hb)
      _ = 1 := by rw [mul_one, mul_one, hab]

/-- Actual quadratic simplex optimizers are nonexpansive under a change of
the positive grammar ratio.  The right side is the displacement of the two
unconstrained ratio-scaled weight vectors; the previous theorem identifies
each constrained optimizer with its metric projection. -/
theorem quadratic_ratio_minimizers_nonexpansive
    {ι : Type*} [Fintype ι] (weight u₁ u₂ : ι → ℝ)
    {rho₁ rho₂ : ℝ} (hrho₁ : 0 < rho₁) (hrho₂ : 0 < rho₂)
    (hu₁ : IsUniqueMinimizerOn (SolidSimplex : (ι → ℝ) → Prop)
      (quadraticReducedObjective rho₁ 1 weight) u₁)
    (hu₂ : IsUniqueMinimizerOn (SolidSimplex : (ι → ℝ) → Prop)
      (quadraticReducedObjective rho₂ 1 weight) u₂) :
    ‖(WithLp.toLp 2 u₁ : EuclideanSpace ℝ ι) - WithLp.toLp 2 u₂‖ ≤
      ‖(WithLp.toLp 2 (fun i ↦ weight i / (2 * rho₁)) :
          EuclideanSpace ℝ ι) -
        WithLp.toLp 2 (fun i ↦ weight i / (2 * rho₂))‖ := by
  let carrier : Set (EuclideanSpace ℝ ι) :=
    {z | SolidSimplex (fun i ↦ z i)}
  have hu₁mem : (WithLp.toLp 2 u₁ : EuclideanSpace ℝ ι) ∈ carrier := by
    change SolidSimplex u₁
    exact hu₁.1
  have hu₂mem : (WithLp.toLp 2 u₂ : EuclideanSpace ℝ ι) ∈ carrier := by
    change SolidSimplex u₂
    exact hu₂.1
  have hprojection₁ :
      ‖(WithLp.toLp 2 (fun i ↦ weight i / (2 * rho₁)) :
          EuclideanSpace ℝ ι) - WithLp.toLp 2 u₁‖ =
        ⨅ z : carrier,
          ‖(WithLp.toLp 2 (fun i ↦ weight i / (2 * rho₁)) :
            EuclideanSpace ℝ ι) - z‖ := by
    simpa only [one_mul] using
      quadratic_minimizer_is_metric_projection hrho₁ weight u₁ hu₁
  have hprojection₂ :
      ‖(WithLp.toLp 2 (fun i ↦ weight i / (2 * rho₂)) :
          EuclideanSpace ℝ ι) - WithLp.toLp 2 u₂‖ =
        ⨅ z : carrier,
          ‖(WithLp.toLp 2 (fun i ↦ weight i / (2 * rho₂)) :
            EuclideanSpace ℝ ι) - z‖ := by
    simpa only [one_mul] using
      quadratic_minimizer_is_metric_projection hrho₂ weight u₂ hu₂
  exact convex_metric_projection_nonexpansive
    solidSimplex_euclidean_convex hu₁mem hu₂mem hprojection₁ hprojection₂

/-- Exact squared-distance identity for two ratio-scaled finite weight
vectors. -/
theorem quadratic_unconstrained_ratio_distance
    {ι : Type*} [Fintype ι] (weight : ι → ℝ)
    {rho₁ rho₂ : ℝ} (hrho₁ : rho₁ ≠ 0) (hrho₂ : rho₂ ≠ 0) :
    (∑ i, (weight i / (2 * rho₁) -
        weight i / (2 * rho₂)) ^ 2) =
      (∑ i, (weight i) ^ 2) *
        (1 / rho₁ - 1 / rho₂) ^ 2 / 4 := by
  have hpoint (i : ι) :
      (weight i / (2 * rho₁) - weight i / (2 * rho₂)) ^ 2 =
        (weight i) ^ 2 *
          ((1 / rho₁ - 1 / rho₂) ^ 2 / 4) := by
    (field_simp [hrho₁, hrho₂]; ring)
  calc
    (∑ i, (weight i / (2 * rho₁) -
        weight i / (2 * rho₂)) ^ 2) =
        ∑ i, (weight i) ^ 2 *
          ((1 / rho₁ - 1 / rho₂) ^ 2 / 4) := by
      apply Finset.sum_congr rfl
      intro i _
      exact hpoint i
    _ = (∑ i, (weight i) ^ 2) *
        (1 / rho₁ - 1 / rho₂) ^ 2 / 4 := by
      calc
        ∑ i, (weight i) ^ 2 *
            ((1 / rho₁ - 1 / rho₂) ^ 2 / 4) =
            (∑ i, (weight i) ^ 2) *
              ((1 / rho₁ - 1 / rho₂) ^ 2 / 4) :=
          (Finset.sum_mul (Finset.univ) (fun i => (weight i) ^ 2)
            ((1 / rho₁ - 1 / rho₂) ^ 2 / 4)).symm
        _ = (∑ i, (weight i) ^ 2) *
            (1 / rho₁ - 1 / rho₂) ^ 2 / 4 :=
          (mul_div_assoc
            (∑ i, (weight i) ^ 2)
            ((1 / rho₁ - 1 / rho₂) ^ 2) (4 : ℝ)).symm

/-- The registered three-coordinate projection-bound calculation is exact
(indeed, equality holds before projection). -/
theorem chg_b3_projection_04 :
    let weight : Fin 3 → ℝ := ![3, 2, 1]
    let rho₁ : ℝ := 5
    let rho₂ : ℝ := 6
    (∑ i, (weight i / (2 * rho₁) -
        weight i / (2 * rho₂)) ^ 2) ≤
      (∑ i, (weight i) ^ 2) *
        (1 / rho₁ - 1 / rho₂) ^ 2 / 4 := by
  norm_num [Fin.sum_univ_succ]

/-- Integrated quadratic active-set theorem.  Below the triangular threshold,
the unconstrained decrease vector is the unique feasible optimizer and its
successive sums recover the unsaturated profile.  At the threshold, the
closed active set is the unique optimizer, has an exact first zero and stable
zero tail, and remains optimal under every finite horizon extension.  The
same theorem records the exact pre-projection ratio metric from which
nonexpansive projection bounds follow. -/
theorem chg_b3_complete_quadratic_active_set
    {ι : Type*} [Fintype ι] (weight : ι → ℝ)
    {rho₁ rho₂ : ℝ} (hrho₁ : rho₁ ≠ 0) (hrho₂ : rho₂ ≠ 0) :
    (∀ (h m : ℝ) (N : ℕ), QuadraticUnsaturatedCell h m N →
      IsUniqueMinimizerOn (SolidSimplex : (Fin N → ℝ) → Prop)
          (quadraticReducedObjective h m (quadraticPathWeight N))
          (quadraticUnsaturatedDecrease h m N) ∧
      (∀ i : Fin N,
        quadraticUnsaturatedProfile h m N i.1 -
            quadraticUnsaturatedProfile h m N (i.1 + 1) =
          quadraticUnsaturatedDecrease h m N i) ∧
      0 < quadraticUnsaturatedProfile h m N N) ∧
    (∀ (h m : ℝ) (K : ℕ), QuadraticPhaseCell h m K →
      IsUniqueMinimizerOn (SolidSimplex : (Fin K → ℝ) → Prop)
          (quadraticReducedObjective h m (quadraticPathWeight K))
          (quadraticSaturatedDecrease h m K) ∧
      (quadraticSaturatedProfile h m K K = 0 ∧
        (∀ i, i < K → 0 < quadraticSaturatedProfile h m K i) ∧
        (∀ i, K ≤ i → quadraticSaturatedProfile h m K i = 0)) ∧
      (QuadraticThresholdReached h m K ∧
        ∀ j, j < K → ¬ QuadraticThresholdReached h m j) ∧
      ∀ R, IsUniqueMinimizerOn
        (SolidSimplex : (Fin (K + R) → ℝ) → Prop)
        (quadraticReducedObjective h m (quadraticPathWeight (K + R)))
        (quadraticExtendedDecrease h m K R)) ∧
    (∑ i, (weight i / (2 * rho₁) -
        weight i / (2 * rho₂)) ^ 2) =
      (∑ i, (weight i) ^ 2) *
        (1 / rho₁ - 1 / rho₂) ^ 2 / 4 := by
  refine ⟨?_, ?_, quadratic_unconstrained_ratio_distance weight hrho₁ hrho₂⟩
  · intro h m N hcell
    refine ⟨quadraticUnsaturatedDecrease_unique_minimizer hcell,
      fun i => quadraticUnsaturatedProfile_step i, ?_⟩
    exact (quadraticUnsaturated_terminal_positive_iff hcell.1).2 hcell.2.2
  · intro h m K hphase
    exact ⟨quadraticSaturatedDecrease_unique_minimizer hphase,
      quadraticProfile_exact_first_zero hphase,
      quadraticPhaseCell_least_threshold hphase,
      fun R => quadraticExtension_stable_unique_minimizer hphase⟩

end PhonologicalCalculus.ContinuousHG
