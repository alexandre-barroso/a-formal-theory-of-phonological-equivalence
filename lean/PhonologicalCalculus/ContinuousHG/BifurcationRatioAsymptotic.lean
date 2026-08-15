import PhonologicalCalculus.ContinuousHG.BifurcationAsymptotic
import PhonologicalCalculus.ContinuousHG.ScalingLimitUniform

/-!
# Weight-ratio asymptotics at support birth

The phase parameter in `BifurcationAsymptotic` is internal to the exact
optimizer profile.  This module transports its asymptotics to the observable
grammar parameter `rho = h / m`.  The transport is proved as a genuine
change-of-variable theorem at the positive phase-boundary mass; it is not a
formal replacement of asymptotic variables.
-/

namespace PhonologicalCalculus.ContinuousHG

open Filter Set
open scoped Topology BigOperators

/-- Boundary mass of the old `k`-site support. -/
noncomputable def supportBirthBoundaryMass (q : ℝ) (k : ℕ) : ℝ :=
  shiftedPowerSum q 0 k

/-- Weight-ratio path corresponding to an entering phase.  When
`q = 1 / (p - 1)`, this is exactly the solution of
`(p * rho)^q = supportBirthMass q k t`. -/
noncomputable def supportBirthRatio
    (p q : ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  (supportBirthMass q k t) ^ (1 / q) / p

/-- Derivative of the ratio transport with respect to phase mass at the
boundary. -/
noncomputable def supportBirthRatioMassCoefficient
    (p q : ℝ) (k : ℕ) : ℝ :=
  (1 / q) * (supportBirthBoundaryMass q k) ^ (1 / q - 1) / p

theorem supportBirthMass_zero
    {q : ℝ} (hq : q ≠ 0) (k : ℕ) :
    supportBirthMass q k 0 = supportBirthBoundaryMass q k := by
  simp [supportBirthMass, supportBirthBoundaryMass, Real.zero_rpow hq,
    supportBirthOldSum_zero]

theorem supportBirthBoundaryMass_pos
    {q : ℝ} (hq : 0 < q) {k : ℕ} (hk : 0 < k) :
    0 < supportBirthBoundaryMass q k := by
  exact shiftedPowerSum_pos hq (by norm_num) hk

/-- On the entering side, the phase mass is strictly above its boundary
value.  This supplies the punctured-neighborhood premise needed for the
derivative transport. -/
theorem supportBirthMass_strictMono_from_zero
    {q t : ℝ} (hq : 0 < q) (ht : 0 < t) (k : ℕ) :
    supportBirthMass q k 0 < supportBirthMass q k t := by
  have hold : supportBirthOldSum q k 0 ≤ supportBirthOldSum q k t := by
    unfold supportBirthOldSum
    apply Finset.sum_le_sum
    intro r hr
    apply Real.rpow_le_rpow
    · positivity
    · linarith
    · exact hq.le
  have hnew : 0 < t ^ q := Real.rpow_pos_of_pos ht q
  simp only [supportBirthMass, Real.zero_rpow hq.ne']
  linarith

/-- The entering-phase mass converges to the old boundary mass. -/
theorem supportBirthMass_tendsto_boundary
    {q : ℝ} (hq : 0 < q) (k : ℕ) :
    Tendsto (supportBirthMass q k)
      (nhdsWithin 0 (Ioi 0))
      (nhds (supportBirthBoundaryMass q k)) := by
  have hcontinuous : ContinuousAt (supportBirthMass q k) 0 := by
    unfold supportBirthMass
    apply ContinuousAt.add
    · exact Real.continuousAt_rpow_const 0 q (Or.inr hq.le)
    · have hold : Continuous (supportBirthOldSum q k) := by
        unfold supportBirthOldSum
        apply continuous_finsetSum
        intro r _
        exact (Real.continuous_rpow_const hq.le).comp
          (continuous_const.add continuous_id)
      exact hold.continuousAt
  simpa [supportBirthMass_zero hq.ne'] using
    hcontinuous.tendsto.mono_left
      (show nhdsWithin (0 : ℝ) (Ioi 0) ≤ nhds 0 from inf_le_left)

/-- Exact first-order change of variables from phase mass to the weight ratio
`rho`. -/
theorem supportBirthRatio_excess_div_mass_excess_tendsto
    {p q : ℝ} (_hp : 0 < p) (hq : 0 < q)
    {k : ℕ} (hk : 0 < k) :
    Tendsto
      (fun t : ℝ =>
        (supportBirthRatio p q k t - supportBirthRatio p q k 0) /
          (supportBirthMass q k t - supportBirthMass q k 0))
      (nhdsWithin 0 (Ioi 0))
      (nhds (supportBirthRatioMassCoefficient p q k)) := by
  let A := supportBirthBoundaryMass q k
  let g : ℝ → ℝ := fun z => z ^ (1 / q) / p
  have hA : 0 < A := supportBirthBoundaryMass_pos hq hk
  have hg : HasDerivAt g
      ((1 / q) * A ^ (1 / q - 1) / p) A := by
    dsimp [g]
    exact (Real.hasDerivAt_rpow_const (p := 1 / q)
      (Or.inl hA.ne')).div_const p
  have hmass := supportBirthMass_tendsto_boundary hq k
  have hmassPunctured : Tendsto (supportBirthMass q k)
      (nhdsWithin 0 (Ioi 0)) (nhdsWithin A ({A}ᶜ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hmass, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hstrict := supportBirthMass_strictMono_from_zero hq ht k
    simpa [A, supportBirthMass_zero hq.ne'] using hstrict.ne'
  have hslope := hg.tendsto_slope.comp hmassPunctured
  have hslope' : Tendsto
      (fun t : ℝ =>
        (g (supportBirthMass q k t) - g A) /
          (supportBirthMass q k t - A))
      (nhdsWithin 0 (Ioi 0))
      (nhds ((1 / q) * A ^ (1 / q - 1) / p)) := by
    rw [slope_fun_def_field] at hslope
    change Tendsto
      (fun t : ℝ =>
        (g (supportBirthMass q k t) - g A) /
          (supportBirthMass q k t - A))
      (nhdsWithin 0 (Ioi 0))
      (nhds ((1 / q) * A ^ (1 / q - 1) / p)) at hslope
    exact hslope
  simpa [g, A, supportBirthRatio,
    supportBirthRatioMassCoefficient, supportBirthMass_zero hq.ne'] using hslope'

/-- The ratio path approaches its exact phase boundary. -/
theorem supportBirthRatio_tendsto_boundary
    {p q : ℝ} (_hp : 0 < p) (hq : 0 < q) (k : ℕ) :
    Tendsto (supportBirthRatio p q k)
      (nhdsWithin 0 (Ioi 0))
      (nhds ((supportBirthBoundaryMass q k) ^ (1 / q) / p)) := by
  have hmass := supportBirthMass_tendsto_boundary hq k
  have hpower := hmass.rpow_const (p := 1 / q)
    (Or.inr (by positivity : 0 ≤ 1 / q))
  change Tendsto
    (fun t : ℝ => (supportBirthMass q k t) ^ (1 / q) / p)
    (nhdsWithin 0 (Ioi 0))
    (nhds ((supportBirthBoundaryMass q k) ^ (1 / q) / p))
  exact hpower.div_const p

/-- The ratio transport coefficient is strictly positive. -/
theorem supportBirthRatioMassCoefficient_pos
    {p q : ℝ} (hp : 0 < p) (hq : 0 < q)
    {k : ℕ} (hk : 0 < k) :
    0 < supportBirthRatioMassCoefficient p q k := by
  unfold supportBirthRatioMassCoefficient
  have hA := supportBirthBoundaryMass_pos hq hk
  positivity

/-- The weight ratio is strictly above its boundary at every positive phase
parameter. -/
theorem supportBirthRatio_strictMono_from_zero
    {p q t : ℝ} (hp : 0 < p) (hq : 0 < q) (ht : 0 < t)
    {k : ℕ} (hk : 0 < k) :
    supportBirthRatio p q k 0 < supportBirthRatio p q k t := by
  have hmass := supportBirthMass_strictMono_from_zero hq ht k
  have hmassZero : 0 < supportBirthMass q k 0 := by
    rw [supportBirthMass_zero hq.ne']
    exact supportBirthBoundaryMass_pos hq hk
  have hpower :
      (supportBirthMass q k 0) ^ (1 / q) <
        (supportBirthMass q k t) ^ (1 / q) :=
    Real.rpow_lt_rpow hmassZero.le hmass (one_div_pos.mpr hq)
  unfold supportBirthRatio
  exact (div_lt_div_iff_of_pos_right hp).2 hpower

/-- The newborn coordinate is strictly active throughout the entering side. -/
theorem supportBirthCoordinate_pos
    {q t : ℝ} (hq : 0 < q) (ht : 0 < t)
    {k : ℕ} (hk : 0 < k) :
    0 < supportBirthCoordinate q k t := by
  unfold supportBirthCoordinate
  have hmass := supportBirthMass_strictMono_from_zero hq ht k
  have hden : 0 < supportBirthMass q k t := by
    rw [supportBirthMass_zero hq.ne'] at hmass
    have hboundary := supportBirthBoundaryMass_pos hq hk
    linarith
  exact div_pos (Real.rpow_pos_of_pos ht q) hden

/-- The newborn coordinate approaches zero from the active side. -/
theorem supportBirthCoordinate_tendsto_zero
    {q : ℝ} (hq : 0 < q) {k : ℕ} (hk : 0 < k) :
    Tendsto (supportBirthCoordinate q k)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  have hmass := supportBirthMass_tendsto_boundary hq k
  change Tendsto
    (fun t : ℝ => t ^ q / supportBirthMass q k t)
    (nhdsWithin 0 (Ioi 0)) (nhds 0)
  exact positivePower_ratio_tendsto_zero hq
    (supportBirthBoundaryMass_pos hq hk) hmass

/-- The old-support linear coefficient is positive whenever an old support
site exists. -/
theorem supportBirthLinearCoefficient_pos
    {q : ℝ} (hq : 0 < q) {k : ℕ} (hk : 0 < k) :
    0 < supportBirthLinearCoefficient q k := by
  unfold supportBirthLinearCoefficient
  have hsum : 0 < ∑ r ∈ Finset.range k,
      (((r + 1 : ℕ) : ℝ) ^ (q - 1)) := by
    apply Finset.sum_pos
    · intro r _
      exact Real.rpow_pos_of_pos (by positivity) _
    · simpa using (Nat.ne_of_gt hk)
  exact mul_pos hq hsum

/-- For `q>1`, ratio excess is linear in the phase parameter with the exact
transported old-support coefficient. -/
theorem supportBirthRatio_excess_div_t_tendsto_subquadratic
    {p q : ℝ} (hp : 0 < p) (hq : 1 < q)
    {k : ℕ} (hk : 0 < k) :
    Tendsto
      (fun t : ℝ =>
        (supportBirthRatio p q k t - supportBirthRatio p q k 0) / t)
      (nhdsWithin 0 (Ioi 0))
      (nhds (supportBirthRatioMassCoefficient p q k *
        supportBirthLinearCoefficient q k)) := by
  have houter := supportBirthRatio_excess_div_mass_excess_tendsto
    hp (lt_trans zero_lt_one hq) hk
  have hinner := supportBirthMass_excess_div_t_tendsto_subquadratic hq k
  have hproduct := houter.mul hinner
  refine hproduct.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hstrict := supportBirthMass_strictMono_from_zero
    (lt_trans zero_lt_one hq) ht k
  have hmassNe : supportBirthMass q k t - supportBirthMass q k 0 ≠ 0 := by
    linarith
  field_simp [hmassNe]

/-- At `q=1`, both the newborn term and the old support contribute to the
linear ratio displacement. -/
theorem supportBirthRatio_excess_div_t_tendsto_quadratic
    {p : ℝ} (hp : 0 < p) {k : ℕ} (hk : 0 < k) :
    Tendsto
      (fun t : ℝ =>
        (supportBirthRatio p 1 k t - supportBirthRatio p 1 k 0) / t)
      (nhdsWithin 0 (Ioi 0))
      (nhds (supportBirthRatioMassCoefficient p 1 k *
        (1 + supportBirthLinearCoefficient 1 k))) := by
  have houter := supportBirthRatio_excess_div_mass_excess_tendsto
    hp zero_lt_one hk
  have hinner := supportBirthMass_excess_div_t_tendsto_quadratic k
  have hproduct := houter.mul hinner
  refine hproduct.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hstrict := supportBirthMass_strictMono_from_zero zero_lt_one ht k
  have hmassNe : supportBirthMass 1 k t - supportBirthMass 1 k 0 ≠ 0 := by
    linarith
  field_simp [hmassNe]

/-- For `0<q<1`, ratio excess has the same `t^q` leading order as the
newborn phase-mass term. -/
theorem supportBirthRatio_excess_div_rpow_tendsto_superquadratic
    {p q : ℝ} (hp : 0 < p) (hqZero : 0 < q) (hqOne : q < 1)
    {k : ℕ} (hk : 0 < k) :
    Tendsto
      (fun t : ℝ =>
        (supportBirthRatio p q k t - supportBirthRatio p q k 0) / t ^ q)
      (nhdsWithin 0 (Ioi 0))
      (nhds (supportBirthRatioMassCoefficient p q k)) := by
  have houter := supportBirthRatio_excess_div_mass_excess_tendsto
    hp hqZero hk
  have hinner := supportBirthMass_excess_div_rpow_tendsto_superquadratic
    hqZero hqOne k
  have hproduct : Tendsto
      (fun t : ℝ =>
        ((supportBirthRatio p q k t - supportBirthRatio p q k 0) /
          (supportBirthMass q k t - supportBirthMass q k 0)) *
        ((supportBirthMass q k t - supportBirthMass q k 0) / t ^ q))
      (nhdsWithin 0 (Ioi 0))
      (nhds (supportBirthRatioMassCoefficient p q k)) := by
    simpa using houter.mul hinner
  refine hproduct.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hstrict := supportBirthMass_strictMono_from_zero hqZero ht k
  have hmassNe : supportBirthMass q k t - supportBirthMass q k 0 ≠ 0 := by
    linarith
  field_simp [hmassNe]

/-- Exact coefficient for flat support entry (`q>1`). -/
noncomputable def supportBirthSubquadraticCoordinateCoefficient
    (p q : ℝ) (k : ℕ) : ℝ :=
  (supportBirthBoundaryMass q k)⁻¹ /
    (supportBirthRatioMassCoefficient p q k *
      supportBirthLinearCoefficient q k) ^ q

/-- Exact coefficient for the quadratic kink (`q=1`). -/
noncomputable def supportBirthQuadraticCoordinateCoefficient
    (p : ℝ) (k : ℕ) : ℝ :=
  (supportBirthBoundaryMass 1 k)⁻¹ /
    (supportBirthRatioMassCoefficient p 1 k *
      (1 + supportBirthLinearCoefficient 1 k))

/-- Exact coefficient for cusp-dominated support entry (`0<q<1`). -/
noncomputable def supportBirthSuperquadraticCoordinateCoefficient
    (p q : ℝ) (k : ℕ) : ℝ :=
  (supportBirthBoundaryMass q k)⁻¹ /
    supportBirthRatioMassCoefficient p q k

/-- For `q>1`, the newborn coordinate is asymptotic to an exact positive
multiple of the `q`-th power of ratio excess. -/
theorem supportBirthCoordinate_div_ratioExcess_rpow_tendsto_subquadratic
    {p q : ℝ} (hp : 0 < p) (hq : 1 < q)
    {k : ℕ} (hk : 0 < k) :
    Tendsto
      (fun t : ℝ =>
        supportBirthCoordinate q k t /
          (supportBirthRatio p q k t - supportBirthRatio p q k 0) ^ q)
      (nhdsWithin 0 (Ioi 0))
      (nhds (supportBirthSubquadraticCoordinateCoefficient p q k)) := by
  let E := supportBirthRatioMassCoefficient p q k *
    supportBirthLinearCoefficient q k
  have hqZero : 0 < q := lt_trans zero_lt_one hq
  have hcoordinate := supportBirthCoordinate_div_rpow_tendsto hqZero hk
  have hratio := supportBirthRatio_excess_div_t_tendsto_subquadratic
    hp hq hk
  have hE : 0 < E := mul_pos
    (supportBirthRatioMassCoefficient_pos hp hqZero hk)
    (supportBirthLinearCoefficient_pos hqZero hk)
  have hratiopow : Tendsto
      (fun t : ℝ =>
        ((supportBirthRatio p q k t - supportBirthRatio p q k 0) / t) ^ q)
      (nhdsWithin 0 (Ioi 0)) (nhds (E ^ q)) := by
    simpa [E] using hratio.rpow_const (p := q) (Or.inl hE.ne')
  have hquotient := hcoordinate.div hratiopow
    (ne_of_gt (Real.rpow_pos_of_pos hE q))
  have hquotient' : Tendsto
      (fun t : ℝ =>
        (supportBirthCoordinate q k t / t ^ q) /
          (((supportBirthRatio p q k t - supportBirthRatio p q k 0) / t) ^ q))
      (nhdsWithin 0 (Ioi 0))
      (nhds ((supportBirthBoundaryMass q k)⁻¹ / E ^ q)) := by
    exact hquotient
  have htarget : Tendsto
      (fun t : ℝ =>
        supportBirthCoordinate q k t /
          (supportBirthRatio p q k t - supportBirthRatio p q k 0) ^ q)
      (nhdsWithin 0 (Ioi 0))
      (nhds ((supportBirthBoundaryMass q k)⁻¹ / E ^ q)) := by
    refine hquotient'.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have htPositive : 0 < t := ht
    have hepsPositive : 0 <
        supportBirthRatio p q k t - supportBirthRatio p q k 0 :=
      sub_pos.mpr (supportBirthRatio_strictMono_from_zero hp hqZero
        htPositive hk)
    rw [Real.div_rpow hepsPositive.le htPositive.le q]
    field_simp [ne_of_gt (Real.rpow_pos_of_pos htPositive q),
      ne_of_gt (Real.rpow_pos_of_pos hepsPositive q)]
  simpa [supportBirthSubquadraticCoordinateCoefficient, E] using htarget

/-- At `q=1`, the newborn coordinate has an exact positive linear
coefficient in ratio excess. -/
theorem supportBirthCoordinate_div_ratioExcess_tendsto_quadratic
    {p : ℝ} (hp : 0 < p) {k : ℕ} (hk : 0 < k) :
    Tendsto
      (fun t : ℝ =>
        supportBirthCoordinate 1 k t /
          (supportBirthRatio p 1 k t - supportBirthRatio p 1 k 0))
      (nhdsWithin 0 (Ioi 0))
      (nhds (supportBirthQuadraticCoordinateCoefficient p k)) := by
  let E := supportBirthRatioMassCoefficient p 1 k *
    (1 + supportBirthLinearCoefficient 1 k)
  have hcoordinateRaw := supportBirthCoordinate_div_rpow_tendsto
    (q := (1 : ℝ)) zero_lt_one hk
  have hcoordinate : Tendsto
      (fun t : ℝ => supportBirthCoordinate 1 k t / t)
      (nhdsWithin 0 (Ioi 0))
      (nhds ((supportBirthBoundaryMass 1 k)⁻¹)) := by
    simpa [Real.rpow_one, supportBirthBoundaryMass] using hcoordinateRaw
  have hratio := supportBirthRatio_excess_div_t_tendsto_quadratic hp hk
  have hE : 0 < E := mul_pos
    (supportBirthRatioMassCoefficient_pos hp zero_lt_one hk)
    (add_pos_of_pos_of_nonneg zero_lt_one
      (supportBirthLinearCoefficient_pos zero_lt_one hk).le)
  have hquotient := hcoordinate.div hratio hE.ne'
  have htarget : Tendsto
      (fun t : ℝ =>
        supportBirthCoordinate 1 k t /
          (supportBirthRatio p 1 k t - supportBirthRatio p 1 k 0))
      (nhdsWithin 0 (Ioi 0))
      (nhds ((supportBirthBoundaryMass 1 k)⁻¹ / E)) := by
    refine hquotient.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have htPositive : 0 < t := ht
    have hepsPositive : 0 <
        supportBirthRatio p 1 k t - supportBirthRatio p 1 k 0 :=
      sub_pos.mpr (supportBirthRatio_strictMono_from_zero hp zero_lt_one
        htPositive hk)
    change
      (supportBirthCoordinate 1 k t / t) /
          ((supportBirthRatio p 1 k t - supportBirthRatio p 1 k 0) / t) =
        supportBirthCoordinate 1 k t /
          (supportBirthRatio p 1 k t - supportBirthRatio p 1 k 0)
    field_simp [htPositive.ne', hepsPositive.ne']
  simpa [supportBirthQuadraticCoordinateCoefficient, E] using htarget

/-- For `0<q<1`, the newborn coordinate has an exact positive linear
coefficient in ratio excess even though both quantities have cusp order
`t^q`. -/
theorem supportBirthCoordinate_div_ratioExcess_tendsto_superquadratic
    {p q : ℝ} (hp : 0 < p) (hqZero : 0 < q) (hqOne : q < 1)
    {k : ℕ} (hk : 0 < k) :
    Tendsto
      (fun t : ℝ =>
        supportBirthCoordinate q k t /
          (supportBirthRatio p q k t - supportBirthRatio p q k 0))
      (nhdsWithin 0 (Ioi 0))
      (nhds (supportBirthSuperquadraticCoordinateCoefficient p q k)) := by
  have hcoordinate := supportBirthCoordinate_div_rpow_tendsto hqZero hk
  have hratio := supportBirthRatio_excess_div_rpow_tendsto_superquadratic
    hp hqZero hqOne hk
  have hC : 0 < supportBirthRatioMassCoefficient p q k :=
    supportBirthRatioMassCoefficient_pos hp hqZero hk
  have hquotient := hcoordinate.div hratio hC.ne'
  have htarget : Tendsto
      (fun t : ℝ =>
        supportBirthCoordinate q k t /
          (supportBirthRatio p q k t - supportBirthRatio p q k 0))
      (nhdsWithin 0 (Ioi 0))
      (nhds ((supportBirthBoundaryMass q k)⁻¹ /
        supportBirthRatioMassCoefficient p q k)) := by
    refine hquotient.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have htPositive : 0 < t := ht
    have htPower : 0 < t ^ q := Real.rpow_pos_of_pos htPositive q
    have hepsPositive : 0 <
        supportBirthRatio p q k t - supportBirthRatio p q k 0 :=
      sub_pos.mpr (supportBirthRatio_strictMono_from_zero hp hqZero
        htPositive hk)
    change
      (supportBirthCoordinate q k t / t ^ q) /
          ((supportBirthRatio p q k t - supportBirthRatio p q k 0) /
            t ^ q) =
        supportBirthCoordinate q k t /
          (supportBirthRatio p q k t - supportBirthRatio p q k 0)
    field_simp [htPower.ne', hepsPositive.ne']
  simpa [supportBirthSuperquadraticCoordinateCoefficient] using htarget

/-- All three ratio-scale onset coefficients are strictly positive. -/
theorem supportBirthCoordinateCoefficients_pos
    {p q : ℝ} (hp : 0 < p) (hq : 1 < q)
    {k : ℕ} (hk : 0 < k) :
    0 < supportBirthSubquadraticCoordinateCoefficient p q k ∧
      0 < supportBirthQuadraticCoordinateCoefficient p k ∧
      ∀ r : ℝ, 0 < r → r < 1 →
        0 < supportBirthSuperquadraticCoordinateCoefficient p r k := by
  have hqZero : 0 < q := lt_trans zero_lt_one hq
  constructor
  · unfold supportBirthSubquadraticCoordinateCoefficient
    have hA := supportBirthBoundaryMass_pos hqZero hk
    have hC := supportBirthRatioMassCoefficient_pos hp hqZero hk
    have hL := supportBirthLinearCoefficient_pos hqZero hk
    exact div_pos (inv_pos.mpr hA)
      (Real.rpow_pos_of_pos (mul_pos hC hL) q)
  constructor
  · unfold supportBirthQuadraticCoordinateCoefficient
    have hA := supportBirthBoundaryMass_pos zero_lt_one hk
    have hC := supportBirthRatioMassCoefficient_pos hp zero_lt_one hk
    have hL := supportBirthLinearCoefficient_pos zero_lt_one hk
    exact div_pos (inv_pos.mpr hA)
      (mul_pos hC (add_pos_of_pos_of_nonneg zero_lt_one hL.le))
  · intro r hrZero hrOne
    unfold supportBirthSuperquadraticCoordinateCoefficient
    exact div_pos (inv_pos.mpr (supportBirthBoundaryMass_pos hrZero hk))
      (supportBirthRatioMassCoefficient_pos hp hrZero hk)

theorem supportBirthLinearCoefficient_one (k : ℕ) :
    supportBirthLinearCoefficient 1 k = k := by
  unfold supportBirthLinearCoefficient
  simp

theorem supportBirthRatioMassCoefficient_two_one (k : ℕ) :
    supportBirthRatioMassCoefficient 2 1 k = 1 / 2 := by
  unfold supportBirthRatioMassCoefficient
  norm_num

/-- The abstract transport coefficient reduces to the printed quadratic
coefficient `2 / ((k+1) A_k)`. -/
theorem supportBirthQuadraticCoordinateCoefficient_closedForm
    {k : ℕ} (hk : 0 < k) :
    supportBirthQuadraticCoordinateCoefficient 2 k =
      2 / (((k + 1 : ℕ) : ℝ) * supportBirthBoundaryMass 1 k) := by
  unfold supportBirthQuadraticCoordinateCoefficient
  rw [supportBirthLinearCoefficient_one,
    supportBirthRatioMassCoefficient_two_one]
  have hA : supportBirthBoundaryMass 1 k ≠ 0 :=
    (supportBirthBoundaryMass_pos zero_lt_one hk).ne'
  field_simp [hA]
  norm_num
  ring

/-! ## Exact active-set and optimizer semantics -/

theorem generalPowerSum_eq_supportBirthBoundaryMass
    {p q : ℝ} (hq : q = powerShiftExponent p) (k : ℕ) :
    generalPowerSum p k = supportBirthBoundaryMass q k := by
  subst q
  unfold generalPowerSum supportBirthBoundaryMass shiftedPowerSum
  apply Finset.sum_congr rfl
  intro r _
  norm_num

theorem generalPowerSum_strictMono_step
    {p : ℝ} (_hp : 1 < p) (k : ℕ) :
    generalPowerSum p k < generalPowerSum p (k + 1) := by
  unfold generalPowerSum
  rw [Finset.sum_range_succ]
  have hterm : 0 < (((k + 1 : ℕ) : ℝ) ^ powerShiftExponent p) :=
    Real.rpow_pos_of_pos (by positivity) _
  linarith

/-- The ratio definition solves its phase-mass equation exactly. -/
theorem supportBirthRatio_power_eq_mass
    {p q t : ℝ} (hp : 0 < p) (hq : 0 < q) {k : ℕ} (hk : 0 < k)
    (ht : 0 ≤ t) :
    (p * supportBirthRatio p q k t) ^ q = supportBirthMass q k t := by
  have hmassZero : 0 < supportBirthMass q k 0 := by
    rw [supportBirthMass_zero hq.ne']
    exact supportBirthBoundaryMass_pos hq hk
  have hold : supportBirthOldSum q k 0 ≤ supportBirthOldSum q k t := by
    unfold supportBirthOldSum
    apply Finset.sum_le_sum
    intro r _
    apply Real.rpow_le_rpow
    · positivity
    · linarith
    · exact hq.le
  have hmass : 0 < supportBirthMass q k t := by
    simp only [supportBirthMass, Real.zero_rpow hq.ne'] at hmassZero ⊢
    have hnew : 0 ≤ t ^ q := Real.rpow_nonneg ht q
    linarith
  have hcancel :
      p * supportBirthRatio p q k t =
        (supportBirthMass q k t) ^ (1 / q) := by
    unfold supportBirthRatio
    field_simp [hp.ne']
  rw [hcancel, one_div]
  exact Real.rpow_inv_rpow hmass.le hq.ne'

/-- At the exact boundary, equality belongs to the old `k`-support cell. -/
theorem supportBirthBoundary_ratioPhaseCell
    {p q : ℝ} (hp : 1 < p) (hq : q = powerShiftExponent p)
    {k : ℕ} (hk : 0 < k) :
    GeneralPowerRatioPhaseCell p (supportBirthRatio p q k 0) k := by
  have hqPositive : 0 < q := by
    rw [hq]
    exact powerShiftExponent_positive hp
  have hpPositive : 0 < p := lt_trans zero_lt_one hp
  have hA : 0 < supportBirthBoundaryMass q k :=
    supportBirthBoundaryMass_pos hqPositive hk
  have hrho : 0 < supportBirthRatio p q k 0 := by
    unfold supportBirthRatio
    rw [supportBirthMass_zero hqPositive.ne']
    exact div_pos (Real.rpow_pos_of_pos hA (1 / q)) hpPositive
  apply (generalPowerRatioPhaseCell_iff_threshold).2
  refine ⟨hp, hrho, hk, ?_, ?_⟩
  · have hstep := generalPowerSum_strictMono_step hp (k - 1)
    have hkIdentity : k - 1 + 1 = k := by omega
    rw [hkIdentity] at hstep
    rw [← hq,
      supportBirthRatio_power_eq_mass hpPositive hqPositive hk (le_refl 0),
      supportBirthMass_zero hqPositive.ne',
      ← generalPowerSum_eq_supportBirthBoundaryMass hq k]
    exact hstep
  · rw [← hq,
      supportBirthRatio_power_eq_mass hpPositive hqPositive hk (le_refl 0),
      supportBirthMass_zero hqPositive.ne',
      ← generalPowerSum_eq_supportBirthBoundaryMass hq k]

/-- Every positive `t≤1` lies in the newly entered `(k+1)`-support cell. -/
theorem supportBirthEntering_ratioPhaseCell
    {p q t : ℝ} (hp : 1 < p) (hq : q = powerShiftExponent p)
    (htZero : 0 < t) (htOne : t ≤ 1) {k : ℕ} (hk : 0 < k) :
    GeneralPowerRatioPhaseCell p (supportBirthRatio p q k t) (k + 1) := by
  have hqPositive : 0 < q := by
    rw [hq]
    exact powerShiftExponent_positive hp
  have hpPositive : 0 < p := lt_trans zero_lt_one hp
  have hmassPositive : 0 < supportBirthMass q k t := by
    have hstrict := supportBirthMass_strictMono_from_zero hqPositive htZero k
    rw [supportBirthMass_zero hqPositive.ne'] at hstrict
    have hA := supportBirthBoundaryMass_pos hqPositive hk
    linarith
  have hrho : 0 < supportBirthRatio p q k t := by
    unfold supportBirthRatio
    exact div_pos (Real.rpow_pos_of_pos hmassPositive (1 / q)) hpPositive
  apply (generalPowerRatioPhaseCell_iff_threshold).2
  refine ⟨hp, hrho, by omega, ?_, ?_⟩
  · rw [show k + 1 - 1 = k by omega, ← hq,
      supportBirthRatio_power_eq_mass hpPositive hqPositive hk htZero.le,
      generalPowerSum_eq_supportBirthBoundaryMass hq,
      ← supportBirthMass_zero hqPositive.ne']
    exact supportBirthMass_strictMono_from_zero hqPositive htZero k
  · rw [← hq,
      supportBirthRatio_power_eq_mass hpPositive hqPositive hk htZero.le,
      supportBirthMass_eq_shiftedPowerSum]
    rw [hq]
    exact shiftedPowerSum_le_generalPowerSum hp (by linarith) (by linarith)
      (k + 1)

/-- The exact optimizer proof used to distinguish a support change from
a winner tie. -/
def SupportBirthOptimizerProof (rho p : ℝ) (K : ℕ) : Prop :=
  ∃ eta : ℝ,
    0 ≤ eta ∧ eta < 1 ∧ powerPathMass rho 1 p eta K = 1 ∧
    IsUniqueMinimizerOn (SolidSimplex : (Fin K → ℝ) → Prop)
      (powerReducedObjective rho 1 p (powerPathWeight K))
      (powerPathDecrease rho 1 p eta K) ∧
    ∀ i : ℕ,
      0 < powerProfileFromDecreases
        (powerPathDecrease rho 1 p eta K) i ↔ i < K

/-- Entering-phase proof tying the asymptotic coordinate to the actual
unique optimizer, rather than merely placing both in the same phase. -/
def SupportBirthEnteringCoordinateProof
    (p q : ℝ) (k : ℕ) (t : ℝ) : Prop :=
  ∃ eta : ℝ,
    eta = 1 - t ∧ 0 ≤ eta ∧ eta < 1 ∧
    powerPathMass (supportBirthRatio p q k t) 1 p eta (k + 1) = 1 ∧
    IsUniqueMinimizerOn (SolidSimplex : (Fin (k + 1) → ℝ) → Prop)
      (powerReducedObjective (supportBirthRatio p q k t) 1 p
        (powerPathWeight (k + 1)))
      (powerPathDecrease (supportBirthRatio p q k t) 1 p eta (k + 1)) ∧
    (∀ i : ℕ,
      0 < powerProfileFromDecreases
        (powerPathDecrease (supportBirthRatio p q k t) 1 p eta (k + 1)) i ↔
          i < k + 1) ∧
    powerProfileFromDecreases
        (powerPathDecrease (supportBirthRatio p q k t) 1 p eta (k + 1)) k =
      supportBirthCoordinate q k t

theorem supportBirthOptimizerProof_of_ratioPhaseCell
    {rho p : ℝ} {K : ℕ}
    (hcell : GeneralPowerRatioPhaseCell p rho K) :
    SupportBirthOptimizerProof rho p K := by
  have hfirst : GeneralPowerFirstZeroCell rho 1 p K := by
    apply (generalPowerFirstZeroCell_iff_ratioPhase hcell.2.1 one_pos).2
    simpa using hcell
  obtain ⟨eta, heta, hetaUpper, hmass, hunique, hsupport, _⟩ :=
    generalPower_all_horizon_finite_persistence hfirst
  exact ⟨eta, heta, hetaUpper, hmass, hunique, hsupport⟩

/-- The entering phase's explicit offset `eta=1-t` realizes the exact
newborn coordinate in the actual unique optimizer. -/
theorem supportBirthEntering_actualCoordinateProof
    {p q t : ℝ} (hp : 1 < p) (hq : q = powerShiftExponent p)
    (htZero : 0 < t) (htOne : t ≤ 1) {k : ℕ} (hk : 0 < k) :
    SupportBirthEnteringCoordinateProof p q k t := by
  have hqPositive : 0 < q := by
    rw [hq]
    exact powerShiftExponent_positive hp
  have hpPositive : 0 < p := lt_trans zero_lt_one hp
  have hcell := supportBirthEntering_ratioPhaseCell hp hq htZero htOne hk
  have hrho : 0 < supportBirthRatio p q k t := hcell.2.1
  have hfirst : GeneralPowerFirstZeroCell
      (supportBirthRatio p q k t) 1 p (k + 1) := by
    apply (generalPowerFirstZeroCell_iff_ratioPhase hrho one_pos).2
    simpa using hcell
  let eta : ℝ := 1 - t
  have hetaZero : 0 ≤ eta := by dsimp [eta]; linarith
  have hetaOne : eta < 1 := by dsimp [eta]; linarith
  have hphase :
      shiftedPowerSum (powerShiftExponent p) eta (k + 1) =
        (p * supportBirthRatio p q k t) ^ powerShiftExponent p := by
    rw [← hq]
    change shiftedPowerSum q (1 - t) (k + 1) =
      (p * supportBirthRatio p q k t) ^ q
    rw [← supportBirthMass_eq_shiftedPowerSum]
    exact (supportBirthRatio_power_eq_mass hpPositive hqPositive hk htZero.le).symm
  have hmass :
      powerPathMass (supportBirthRatio p q k t) 1 p eta (k + 1) = 1 :=
    (powerPathMass_one_iff_phaseEquation hrho one_pos hp hetaOne).2
      (by simpa using hphase)
  have hunique :
      IsUniqueMinimizerOn (SolidSimplex : (Fin (k + 1) → ℝ) → Prop)
        (powerReducedObjective (supportBirthRatio p q k t) 1 p
          (powerPathWeight (k + 1)))
        (powerPathDecrease (supportBirthRatio p q k t) 1 p eta (k + 1)) := by
    change IsUniqueMinimizerOn
      (SolidSimplex : (Fin (k + 1) → ℝ) → Prop)
      (powerReducedObjective (supportBirthRatio p q k t) 1 p
        (powerPathWeight (k + 1)))
      (powerKKTDecrease (supportBirthRatio p q k t) 1 p eta
        (powerPathWeight (k + 1)))
    exact powerKKTDecrease_unique_minimizer
      (powerPathWeight (k + 1)) hrho hp hetaZero hmass
  have hsupport : ∀ i : ℕ,
      0 < powerProfileFromDecreases
        (powerPathDecrease (supportBirthRatio p q k t) 1 p eta (k + 1)) i ↔
          i < k + 1 := by
    exact fun i => generalPower_exact_first_zero hfirst hetaZero hmass
  have hcoordinate :
      powerProfileFromDecreases
          (powerPathDecrease (supportBirthRatio p q k t) 1 p eta (k + 1)) k =
        supportBirthCoordinate q k t := by
    rw [powerProfileFromDecreases_eq_normalizedPhaseProfile
      hrho one_pos hp hetaOne hmass]
    rw [← hq]
    unfold normalizedPhaseProfile supportBirthCoordinate
    rw [show k + 1 - k = 1 by omega,
      supportBirthMass_eq_shiftedPowerSum]
    congr 1 <;> simp [shiftedPowerSum, eta]
  exact ⟨eta, rfl, hetaZero, hetaOne, hmass, hunique, hsupport, hcoordinate⟩

/-- Full active-set semantics of support birth: the boundary has a unique
`k`-support optimizer, every positive entering parameter has a unique
`k+1`-support optimizer, and the newly active coordinate is positive but
converges to zero.  No ranking change or winner tie is used. -/
theorem chg_b14_actualOptimizer_supportBirth_package
    {p q : ℝ} (hp : 1 < p) (hq : q = powerShiftExponent p)
    {k : ℕ} (hk : 0 < k) :
    SupportBirthOptimizerProof
        (supportBirthRatio p q k 0) p k ∧
    (∀ t : ℝ, 0 < t → t ≤ 1 →
      SupportBirthEnteringCoordinateProof p q k t ∧
        SupportBirthOptimizerProof
          (supportBirthRatio p q k t) p (k + 1) ∧
        0 < supportBirthCoordinate q k t) ∧
    Tendsto (supportBirthCoordinate q k)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  have hqPositive : 0 < q := by
    rw [hq]
    exact powerShiftExponent_positive hp
  refine ⟨supportBirthOptimizerProof_of_ratioPhaseCell
      (supportBirthBoundary_ratioPhaseCell hp hq hk), ?_,
    supportBirthCoordinate_tendsto_zero hqPositive hk⟩
  intro t htZero htOne
  exact ⟨supportBirthEntering_actualCoordinateProof
      hp hq htZero htOne hk,
    supportBirthOptimizerProof_of_ratioPhaseCell
      (supportBirthEntering_ratioPhaseCell hp hq htZero htOne hk),
    supportBirthCoordinate_pos hqPositive htZero hk⟩

theorem powerShiftExponent_gt_one_iff
    {p : ℝ} (hp : 1 < p) :
    1 < powerShiftExponent p ↔ p < 2 := by
  have hden : 0 < p - 1 := sub_pos.mpr hp
  unfold powerShiftExponent
  rw [one_lt_div hden]
  constructor <;> intro h <;> linarith

theorem powerShiftExponent_eq_one_iff
    {p : ℝ} (hp : 1 < p) :
    powerShiftExponent p = 1 ↔ p = 2 := by
  have hden : p - 1 ≠ 0 := (sub_pos.mpr hp).ne'
  unfold powerShiftExponent
  rw [div_eq_one_iff_eq hden]
  constructor <;> intro h <;> linarith

theorem powerShiftExponent_lt_one_iff
    {p : ℝ} (hp : 1 < p) :
    powerShiftExponent p < 1 ↔ 2 < p := by
  have hden : 0 < p - 1 := sub_pos.mpr hp
  unfold powerShiftExponent
  rw [div_lt_one hden]
  constructor <;> intro h <;> linarith

/-- Canonical CHG-B14 closure.  The exponent selected by the grammar fixes
the exact ratio-scale onset law, while one optimizer proof covers the
boundary and every entering phase. -/
theorem chg_b14_complete_ratio_onset_and_optimizer
    {p q : ℝ} (hp : 1 < p) (hq : q = powerShiftExponent p)
    {k : ℕ} (hk : 0 < k) :
    (p < 2 →
      Tendsto
        (fun t : ℝ =>
          supportBirthCoordinate q k t /
            (supportBirthRatio p q k t - supportBirthRatio p q k 0) ^ q)
        (nhdsWithin 0 (Ioi 0))
        (nhds (supportBirthSubquadraticCoordinateCoefficient p q k))) ∧
    (p = 2 →
      Tendsto
        (fun t : ℝ =>
          supportBirthCoordinate q k t /
            (supportBirthRatio p q k t - supportBirthRatio p q k 0))
        (nhdsWithin 0 (Ioi 0))
        (nhds (supportBirthQuadraticCoordinateCoefficient p k))) ∧
    (2 < p →
      Tendsto
        (fun t : ℝ =>
          supportBirthCoordinate q k t /
            (supportBirthRatio p q k t - supportBirthRatio p q k 0))
        (nhdsWithin 0 (Ioi 0))
        (nhds (supportBirthSuperquadraticCoordinateCoefficient p q k))) ∧
    SupportBirthOptimizerProof
        (supportBirthRatio p q k 0) p k ∧
    (∀ t : ℝ, 0 < t → t ≤ 1 →
      SupportBirthEnteringCoordinateProof p q k t ∧
        SupportBirthOptimizerProof
          (supportBirthRatio p q k t) p (k + 1) ∧
        0 < supportBirthCoordinate q k t) ∧
    Tendsto (supportBirthCoordinate q k)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  have hqPositive : 0 < q := by
    rw [hq]
    exact powerShiftExponent_positive hp
  have hsemantics := chg_b14_actualOptimizer_supportBirth_package hp hq hk
  refine ⟨?_, ?_, ?_, hsemantics.1, hsemantics.2.1, hsemantics.2.2⟩
  · intro hpTwo
    have hqOne : 1 < q := by
      rw [hq]
      exact (powerShiftExponent_gt_one_iff hp).2 hpTwo
    exact supportBirthCoordinate_div_ratioExcess_rpow_tendsto_subquadratic
      (lt_trans zero_lt_one hp) hqOne hk
  · intro hpTwo
    have hqEq : q = 1 := by
      rw [hq]
      exact (powerShiftExponent_eq_one_iff hp).2 hpTwo
    simpa [hqEq] using
      (supportBirthCoordinate_div_ratioExcess_tendsto_quadratic
        (lt_trans zero_lt_one hp) hk)
  · intro hpTwo
    have hqOne : q < 1 := by
      rw [hq]
      exact (powerShiftExponent_lt_one_iff hp).2 hpTwo
    exact supportBirthCoordinate_div_ratioExcess_tendsto_superquadratic
      (lt_trans zero_lt_one hp) hqPositive hqOne hk

end PhonologicalCalculus.ContinuousHG
