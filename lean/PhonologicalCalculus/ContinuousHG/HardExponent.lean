import PhonologicalCalculus.ContinuousHG.PhaseProfile
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-!
# Hard-exponent support and magnitude

This module formalizes the metric side of the hard-exponent theorem.  The
one-follower activity is rewritten exactly in exponential coordinates, its
strict positivity is classified, and its logarithmic scale is proved to tend
to zero.  Finite support anchors and the strict separation between positivity
and the complete phase-two condition are recorded separately.
-/

namespace PhonologicalCalculus.ContinuousHG

open Filter

/-- Logarithmic hard-exponent scale. -/
noncomputable def hardExponentScale (rho p : ℝ) : ℝ :=
  Real.log (p * rho) / (p - 1)

/-- Exact one-follower activity in the hard-exponent family. -/
noncomputable def hardExponentFollower (rho p : ℝ) : ℝ :=
  1 - (p * rho) ^ (-1 / (p - 1))

/-- Complete phase-two inequality. -/
def HardExponentPhaseTwo (rho p : ℝ) : Prop :=
  1 < p * rho ∧
    p * rho ≤ (1 + 2 ^ (1 / (p - 1) : ℝ)) ^ (p - 1)

/-- The real identity underlying `CHG-B16.ONEFOLLOWER.02`. -/
theorem hardExponentFollower_exp_identity
    {rho p : ℝ} (hrho : 0 < rho) (hp : 1 < p) :
    hardExponentFollower rho p =
      1 - Real.exp (-hardExponentScale rho p) := by
  have hbase : 0 < p * rho := mul_pos (lt_trans zero_lt_one hp) hrho
  unfold hardExponentFollower hardExponentScale
  rw [Real.rpow_def_of_pos hbase]
  congr 2
  field_simp [ne_of_gt (sub_pos.mpr hp)]

/-- Finite-exponent positivity is equivalent to the strict lower phase
boundary; it does not encode the upper phase-two inequality. -/
theorem hardExponentFollower_pos_iff
    {rho p : ℝ} (hrho : 0 < rho) (hp : 1 < p) :
    0 < hardExponentFollower rho p ↔ 1 < p * rho := by
  rw [hardExponentFollower_exp_identity hrho hp]
  have hden : 0 < p - 1 := sub_pos.mpr hp
  have hbase : 0 < p * rho := mul_pos (lt_trans zero_lt_one hp) hrho
  constructor
  · intro hpositive
    have hexp : Real.exp (-hardExponentScale rho p) < 1 := by linarith
    have hnegative : -hardExponentScale rho p < 0 :=
      Real.exp_lt_one_iff.mp hexp
    have hlog : 0 < Real.log (p * rho) := by
      unfold hardExponentScale at hnegative
      have : 0 < Real.log (p * rho) / (p - 1) := by linarith
      have hproduct := mul_pos this hden
      have hrecover : Real.log (p * rho) / (p - 1) * (p - 1) =
          Real.log (p * rho) := by
        field_simp [ne_of_gt hden]
      rwa [hrecover] at hproduct
    exact (Real.log_pos_iff hbase.le).mp hlog
  · intro hstrict
    have hlog : 0 < Real.log (p * rho) := Real.log_pos hstrict
    have hscale : 0 < hardExponentScale rho p := by
      exact div_pos hlog hden
    have hexp : Real.exp (-hardExponentScale rho p) < 1 :=
      Real.exp_lt_one_iff.mpr (neg_neg_of_pos hscale)
    linarith

private theorem tendsto_id_atTop_real :
    Tendsto (fun p : ℝ => p) atTop atTop := by
  refine Filter.tendsto_atTop.2 ?_
  intro b
  exact Filter.eventually_ge_atTop b

private theorem tendsto_sub_one_atTop_real :
    Tendsto (fun p : ℝ => p - 1) atTop atTop := by
  refine Filter.tendsto_atTop.2 ?_
  intro b
  filter_upwards [Filter.eventually_ge_atTop (b + 1)] with p hp
  linarith

/-- `CHG-B16.LAMBDA.01`: logarithmic growth is negligible relative to the
hard exponent. -/
theorem hardExponentScale_tendsto_zero {rho : ℝ} (hrho : 0 < rho) :
    Tendsto (hardExponentScale rho) atTop (nhds 0) := by
  have hlogDiv : Tendsto (fun p : ℝ => Real.log p / p)
      atTop (nhds 0) := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hconstDiv : Tendsto (fun p : ℝ => Real.log rho / p)
      atTop (nhds 0) := tendsto_const_nhds.div_atTop tendsto_id_atTop_real
  have hbaseDiv : Tendsto (fun p : ℝ => Real.log (p * rho) / p)
      atTop (nhds 0) := by
    have hsum := hlogDiv.add hconstDiv
    have hsum0 : Tendsto
        (fun p : ℝ => Real.log p / p + Real.log rho / p)
        atTop (nhds 0) := by simpa using hsum
    refine hsum0.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with p hp
    rw [Real.log_mul (ne_of_gt hp) (ne_of_gt hrho)]
    ring
  have hinvSub : Tendsto (fun p : ℝ => (p - 1)⁻¹)
      atTop (nhds 0) := tendsto_inv_atTop_zero.comp tendsto_sub_one_atTop_real
  have hratio : Tendsto (fun p : ℝ => p / (p - 1))
      atTop (nhds 1) := by
    have hconstOne : Tendsto (fun _ : ℝ => (1 : ℝ))
        atTop (nhds 1) := tendsto_const_nhds
    have hone := hconstOne.add hinvSub
    have hone' : Tendsto (fun p : ℝ => 1 + (p - 1)⁻¹)
        atTop (nhds 1) := by simpa using hone
    refine hone'.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with p hp
    field_simp [ne_of_gt (sub_pos.mpr hp)]
    ring
  have hproduct := hbaseDiv.mul hratio
  unfold hardExponentScale
  have hproduct0 : Tendsto
      (fun p : ℝ => Real.log (p * rho) / p * (p / (p - 1)))
      atTop (nhds 0) := by simpa using hproduct
  refine hproduct0.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with p hp
  field_simp [ne_of_gt (lt_trans zero_lt_one hp),
    ne_of_gt (sub_pos.mpr hp)]

/-- The one-follower magnitude tends to zero although its finite-p support may
remain positive. -/
theorem hardExponentFollower_tendsto_zero {rho : ℝ} (hrho : 0 < rho) :
    Tendsto (hardExponentFollower rho) atTop (nhds 0) := by
  have hscale := hardExponentScale_tendsto_zero hrho
  have hexp : Tendsto (fun p : ℝ => Real.exp (-hardExponentScale rho p))
      atTop (nhds 1) := by
    change Tendsto (Real.exp ∘ fun p : ℝ => -hardExponentScale rho p)
      atTop (nhds 1)
    simpa using Real.continuous_exp.continuousAt.tendsto.comp hscale.neg
  have hconstOne : Tendsto (fun _ : ℝ => (1 : ℝ))
      atTop (nhds 1) := tendsto_const_nhds
  have hdifference : Tendsto
      (fun p : ℝ => 1 - Real.exp (-hardExponentScale rho p))
      atTop (nhds 0) := by simpa using hconstOne.sub hexp
  refine hdifference.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with p hp
  symm
  exact hardExponentFollower_exp_identity hrho hp

/-- Strict positivity alone does not imply the complete phase-two condition. -/
theorem chg_b16_positivity_not_full_phase :
    0 < hardExponentFollower 5 2 ∧ ¬ HardExponentPhaseTwo 5 2 := by
  constructor
  · exact (hardExponentFollower_pos_iff (by norm_num) (by norm_num)).2
      (by norm_num)
  · norm_num [HardExponentPhaseTwo]

/-- Integer sufficient condition used by the three registered large-exponent
support anchors. -/
def HardSupportAnchor (p : ℕ) : Prop :=
  5 * p > 1 ∧ 2 ^ (p - 1) > 5 * p

/-- `CHG-B16.SUPPORT.04`: the three registered exact support anchors. -/
theorem chg_b16_support_04 :
    HardSupportAnchor 10 ∧ HardSupportAnchor 20 ∧
      HardSupportAnchor 50 := by
  norm_num [HardSupportAnchor]

/-- `CHG-B16.ONEFOLLOWER.02` and `CHG-B16.POSITIVITY.03` in one exact
declaration. -/
theorem chg_b16_oneFollower_positivity_02_03
    {rho p : ℝ} (hrho : 0 < rho) (hp : 1 < p) :
    hardExponentFollower rho p = 1 - Real.exp (-hardExponentScale rho p) ∧
      (0 < hardExponentFollower rho p ↔ 1 < p * rho) := by
  exact ⟨hardExponentFollower_exp_identity hrho hp,
    hardExponentFollower_pos_iff hrho hp⟩

/-- `CHG-B16.NONCOMMUTE.05`: an exact finite positive anchor accompanies the
zero metric limit. -/
theorem chg_b16_noncommute_05 :
    0 < hardExponentFollower 1 2 ∧
      Tendsto (hardExponentFollower 1) atTop (nhds 0) := by
  exact ⟨(hardExponentFollower_pos_iff (by norm_num) (by norm_num)).2
    (by norm_num), hardExponentFollower_tendsto_zero (by norm_num)⟩

/-- Exact analytic and registered finite components of `CHG-B16`. -/
theorem chg_b16_registered_components :
    (∀ rho, 0 < rho → Tendsto (hardExponentScale rho) atTop (nhds 0)) ∧
    (∀ rho p, 0 < rho → 1 < p →
      hardExponentFollower rho p = 1 - Real.exp (-hardExponentScale rho p) ∧
      (0 < hardExponentFollower rho p ↔ 1 < p * rho)) ∧
    (0 < hardExponentFollower 5 2 ∧ ¬ HardExponentPhaseTwo 5 2) ∧
    (HardSupportAnchor 10 ∧ HardSupportAnchor 20 ∧
      HardSupportAnchor 50) ∧
    (0 < hardExponentFollower 1 2 ∧
      Tendsto (hardExponentFollower 1) atTop (nhds 0)) := by
  exact ⟨fun rho hrho => hardExponentScale_tendsto_zero hrho,
    fun rho p hrho hp => chg_b16_oneFollower_positivity_02_03 hrho hp,
    chg_b16_positivity_not_full_phase, chg_b16_support_04,
    chg_b16_noncommute_05⟩

end PhonologicalCalculus.ContinuousHG
