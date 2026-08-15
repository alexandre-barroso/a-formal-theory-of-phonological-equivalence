import PhonologicalCalculus.Support.BellmanContinuation
import PhonologicalCalculus.Support.MatchedPower
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Topology.Order.IntermediateValue

/-!
# Infinite matched-power continuation

This module treats the real-exponent matched-power family directly.  It proves
existence and uniqueness of the decay ratio, the sharp one-edge Bellman
inequality, convergence of the geometric candidate, and global optimality on
the declared infinite admissible class.
-/

namespace PhonologicalCalculus.Support

open Filter Finset Set
open scoped Topology

/-! ## Strict Bellman telescoping -/

/-- The sum of the local Bellman gaps is the terminally corrected prefix
cost minus the initial potential. -/
theorem bellman_gap_sum_identity
    (cost potential : ℕ → ℝ) :
    ∀ horizon,
      ∑ index ∈ range horizon,
          (cost index + potential (index + 1) - potential index) =
        (∑ index ∈ range horizon, cost index) +
          potential horizon - potential 0 := by
  intro horizon
  induction horizon with
  | zero => simp
  | succ horizon inductionHypothesis =>
      rw [sum_range_succ, sum_range_succ, inductionHypothesis]
      ring

/-- A single strict local Bellman inequality creates a fixed positive global
gap after passage to the infinite limit. -/
theorem bellman_limit_strict_of_local_strict
    (cost potential : ℕ → ℝ) (total : ℝ) (strictIndex : ℕ)
    (localBound : ∀ index, potential index ≤ cost index + potential (index + 1))
    (localStrict : potential strictIndex <
      cost strictIndex + potential (strictIndex + 1))
    (costConvergence :
      Tendsto (fun horizon => ∑ index ∈ range horizon, cost index)
        atTop (nhds total))
    (residualVanishing : Tendsto potential atTop (nhds 0)) :
    potential 0 < total := by
  let gap : ℕ → ℝ := fun index =>
    cost index + potential (index + 1) - potential index
  have gapNonnegative : ∀ index, 0 ≤ gap index := by
    intro index
    dsimp [gap]
    linarith [localBound index]
  have selectedGapPositive : 0 < gap strictIndex := by
    dsimp [gap]
    linarith
  have eventuallySelectedGapBound :
      ∀ᶠ horizon in atTop,
        potential 0 + gap strictIndex ≤
          (∑ index ∈ range horizon, cost index) + potential horizon := by
    filter_upwards [eventually_gt_atTop strictIndex] with horizon indexBeforeHorizon
    have strictIndexMem : strictIndex ∈ range horizon :=
      mem_range.mpr indexBeforeHorizon
    have gapLeSum : gap strictIndex ≤ ∑ index ∈ range horizon, gap index :=
      single_le_sum (fun index _ => gapNonnegative index) strictIndexMem
    rw [bellman_gap_sum_identity cost potential horizon] at gapLeSum
    linarith
  have combinedConvergence := costConvergence.add residualVanishing
  have limitGap : potential 0 + gap strictIndex ≤ total + 0 :=
    ge_of_tendsto combinedConvergence eventuallySelectedGapBound
  linarith

/-! ## The scalar decay equation -/

/-- Residual of the real-exponent matched-power decay equation. -/
noncomputable def matchedDecayResidual
    (h m p lambda : ℝ) : ℝ :=
  h * (1 - lambda) ^ (p - 1) * (1 - lambda ^ (p - 1)) -
    m * lambda ^ (p - 1)

/-- Equation defining the matched-power decay ratio. -/
def MatchedPowerDecayEquation
    (h m p lambda : ℝ) : Prop :=
  m * lambda ^ (p - 1) =
    h * (1 - lambda) ^ (p - 1) * (1 - lambda ^ (p - 1))

/-- The residual vanishes exactly when the decay equation holds. -/
theorem matchedDecayResidual_eq_zero_iff
    (h m p lambda : ℝ) :
    matchedDecayResidual h m p lambda = 0 ↔
      MatchedPowerDecayEquation h m p lambda := by
  unfold matchedDecayResidual MatchedPowerDecayEquation
  constructor
  · intro residualZero
    exact (sub_eq_zero.mp residualZero).symm
  · intro decay
    exact sub_eq_zero.mpr decay.symm

/-- The matched-power residual is continuous for every exponent `p > 1`. -/
theorem continuous_matchedDecayResidual
    (h m p : ℝ) (pGreaterOne : 1 < p) :
    Continuous (matchedDecayResidual h m p) := by
  have exponentNonnegative : 0 ≤ p - 1 := le_of_lt (sub_pos.mpr pGreaterOne)
  unfold matchedDecayResidual
  fun_prop

/-- The residual has opposite strict signs at the endpoints of the unit
interval. -/
theorem matchedDecayResidual_endpoint_signs
    (h m p : ℝ) (hPositive : 0 < h) (mPositive : 0 < m)
    (pGreaterOne : 1 < p) :
    0 < matchedDecayResidual h m p 0 ∧
      matchedDecayResidual h m p 1 < 0 := by
  have exponentPositive : 0 < p - 1 := sub_pos.mpr pGreaterOne
  simp [matchedDecayResidual, Real.zero_rpow exponentPositive.ne', hPositive,
    mPositive]

/-- There is a decay ratio strictly between zero and one. -/
theorem exists_matchedPowerDecayRatio
    (h m p : ℝ) (hPositive : 0 < h) (mPositive : 0 < m)
    (pGreaterOne : 1 < p) :
    ∃ lambda : ℝ, 0 < lambda ∧ lambda < 1 ∧
      MatchedPowerDecayEquation h m p lambda := by
  let residual := matchedDecayResidual h m p
  have continuousResidual : ContinuousOn residual (Icc (0 : ℝ) 1) :=
    (continuous_matchedDecayResidual h m p pGreaterOne).continuousOn
  have endpointSigns := matchedDecayResidual_endpoint_signs h m p
    hPositive mPositive pGreaterOne
  have zeroBetween : (0 : ℝ) ∈ Icc (residual 1) (residual 0) :=
    ⟨le_of_lt endpointSigns.2, le_of_lt endpointSigns.1⟩
  obtain ⟨lambda, lambdaMem, residualZero⟩ :=
    intermediate_value_Icc' (show (0 : ℝ) ≤ 1 by norm_num)
      continuousResidual zeroBetween
  have lambdaPositive : 0 < lambda := by
    rcases lambdaMem.1.eq_or_lt with lambdaZero | lambdaPositive
    · subst lambda
      have endpointPositive : 0 < residual 0 := endpointSigns.1
      rw [residualZero] at endpointPositive
      exact (lt_irrefl 0 endpointPositive).elim
    · exact lambdaPositive
  have lambdaBelowOne : lambda < 1 := by
    rcases lambdaMem.2.eq_or_lt with lambdaOne | lambdaBelowOne
    · subst lambda
      have endpointNegative : residual 1 < 0 := endpointSigns.2
      rw [residualZero] at endpointNegative
      exact (lt_irrefl 0 endpointNegative).elim
    · exact lambdaBelowOne
  exact ⟨lambda, lambdaPositive, lambdaBelowOne,
    (matchedDecayResidual_eq_zero_iff h m p lambda).mp residualZero⟩

/-- Two distinct points of the open unit interval cannot both solve the
matched-power decay equation. -/
theorem matchedPowerDecayRatio_not_both_of_lt
    (h m p lambda mu : ℝ)
    (hPositive : 0 < h) (mPositive : 0 < m)
    (pGreaterOne : 1 < p)
    (lambdaPositive : 0 < lambda) (lambdaBelowOne : lambda < 1)
    (muPositive : 0 < mu) (muBelowOne : mu < 1)
    (lambdaBelowMu : lambda < mu)
    (lambdaDecay : MatchedPowerDecayEquation h m p lambda)
    (muDecay : MatchedPowerDecayEquation h m p mu) : False := by
  have exponentPositive : 0 < p - 1 := sub_pos.mpr pGreaterOne
  have lambdaPow_lt_muPow :
      lambda ^ (p - 1) < mu ^ (p - 1) :=
    Real.rpow_lt_rpow (le_of_lt lambdaPositive) lambdaBelowMu exponentPositive
  have lambdaPow_lt_one : lambda ^ (p - 1) < 1 := by
    simpa using Real.rpow_lt_rpow (le_of_lt lambdaPositive) lambdaBelowOne
      exponentPositive
  have muPow_lt_one : mu ^ (p - 1) < 1 := by
    simpa using Real.rpow_lt_rpow (le_of_lt muPositive) muBelowOne
      exponentPositive
  have edgeMu_lt_edgeLambda :
      (1 - mu) ^ (p - 1) < (1 - lambda) ^ (p - 1) := by
    apply Real.rpow_lt_rpow
    · exact sub_nonneg.mpr (le_of_lt muBelowOne)
    · linarith
    · exact exponentPositive
  have edgeMuPositive : 0 < (1 - mu) ^ (p - 1) :=
    Real.rpow_pos_of_pos (sub_pos.mpr muBelowOne) _
  have edgeLambdaPositive : 0 < (1 - lambda) ^ (p - 1) :=
    Real.rpow_pos_of_pos (sub_pos.mpr lambdaBelowOne) _
  have leftFactorStrict :
      (1 - mu) ^ (p - 1) * (1 - mu ^ (p - 1)) <
        (1 - lambda) ^ (p - 1) * (1 - lambda ^ (p - 1)) := by
    calc
      (1 - mu) ^ (p - 1) * (1 - mu ^ (p - 1)) <
          (1 - lambda) ^ (p - 1) * (1 - mu ^ (p - 1)) :=
        mul_lt_mul_of_pos_right edgeMu_lt_edgeLambda (sub_pos.mpr muPow_lt_one)
      _ < (1 - lambda) ^ (p - 1) * (1 - lambda ^ (p - 1)) :=
        mul_lt_mul_of_pos_left (by linarith) edgeLambdaPositive
  have weightedLeftStrict :
      h * ((1 - mu) ^ (p - 1) * (1 - mu ^ (p - 1))) <
        h * ((1 - lambda) ^ (p - 1) *
          (1 - lambda ^ (p - 1))) :=
    mul_lt_mul_of_pos_left leftFactorStrict hPositive
  have weightedRightStrict :
      m * lambda ^ (p - 1) < m * mu ^ (p - 1) :=
    mul_lt_mul_of_pos_left lambdaPow_lt_muPow mPositive
  unfold MatchedPowerDecayEquation at lambdaDecay muDecay
  nlinarith

/-- The open-unit decay ratio is unique. -/
theorem matchedPowerDecayRatio_unique
    (h m p lambda mu : ℝ)
    (hPositive : 0 < h) (mPositive : 0 < m)
    (pGreaterOne : 1 < p)
    (lambdaPositive : 0 < lambda) (lambdaBelowOne : lambda < 1)
    (muPositive : 0 < mu) (muBelowOne : mu < 1)
    (lambdaDecay : MatchedPowerDecayEquation h m p lambda)
    (muDecay : MatchedPowerDecayEquation h m p mu) :
    lambda = mu := by
  rcases lt_trichotomy lambda mu with lambdaBelowMu | lambdaEqualMu | muBelowLambda
  · exact (matchedPowerDecayRatio_not_both_of_lt h m p lambda mu
      hPositive mPositive pGreaterOne lambdaPositive lambdaBelowOne
      muPositive muBelowOne lambdaBelowMu lambdaDecay muDecay).elim
  · exact lambdaEqualMu
  · exact (matchedPowerDecayRatio_not_both_of_lt h m p mu lambda
      hPositive mPositive pGreaterOne muPositive muBelowOne
      lambdaPositive lambdaBelowOne muBelowLambda muDecay lambdaDecay).elim

/-- Positive weights and exponent determine exactly one open-unit decay
ratio. -/
theorem existsUnique_matchedPowerDecayRatio
    (h m p : ℝ) (hPositive : 0 < h) (mPositive : 0 < m)
    (pGreaterOne : 1 < p) :
    ∃! lambda : ℝ,
      0 < lambda ∧ lambda < 1 ∧
        MatchedPowerDecayEquation h m p lambda := by
  obtain ⟨lambda, lambdaPositive, lambdaBelowOne, lambdaDecay⟩ :=
    exists_matchedPowerDecayRatio h m p hPositive mPositive pGreaterOne
  refine ⟨lambda, ⟨lambdaPositive, lambdaBelowOne, lambdaDecay⟩, ?_⟩
  intro mu muProperties
  exact matchedPowerDecayRatio_unique h m p mu lambda
    hPositive mPositive pGreaterOne
    muProperties.1 muProperties.2.1 lambdaPositive lambdaBelowOne
    muProperties.2.2 lambdaDecay

/-! ## Weighted convexity proof -/

/-- Two-point Jensen inequality for the real power on the nonnegative ray. -/
theorem weighted_rpow_le
    (p weight u v : ℝ) (pGreaterOne : 1 < p)
    (weightPositive : 0 < weight) (weightBelowOne : weight < 1)
    (uNonnegative : 0 ≤ u) (vNonnegative : 0 ≤ v) :
    ((1 - weight) * u + weight * v) ^ p ≤
      (1 - weight) * u ^ p + weight * v ^ p := by
  have convexPower := convexOn_rpow (le_of_lt pGreaterOne)
  have oneMinusPositive : 0 < 1 - weight := sub_pos.mpr weightBelowOne
  have weightsSum : (1 - weight) + weight = 1 := by ring
  simpa [smul_eq_mul] using
    convexPower.2 uNonnegative vNonnegative
      (le_of_lt oneMinusPositive) (le_of_lt weightPositive) weightsSum

/-- Strict two-point Jensen inequality when the normalized endpoints differ. -/
theorem weighted_rpow_lt
    (p weight u v : ℝ) (pGreaterOne : 1 < p)
    (weightPositive : 0 < weight) (weightBelowOne : weight < 1)
    (uNonnegative : 0 ≤ u) (vNonnegative : 0 ≤ v)
    (endpointsDiffer : u ≠ v) :
    ((1 - weight) * u + weight * v) ^ p <
      (1 - weight) * u ^ p + weight * v ^ p := by
  have strictConvexPower := strictConvexOn_rpow pGreaterOne
  have oneMinusPositive : 0 < 1 - weight := sub_pos.mpr weightBelowOne
  have weightsSum : (1 - weight) + weight = 1 := by ring
  simpa [smul_eq_mul] using
    strictConvexPower.2 uNonnegative vNonnegative endpointsDiffer
      oneMinusPositive weightPositive weightsSum

/-- Normalizing a nonnegative power by a positive scale removes one factor
from the exponent. -/
theorem scale_mul_div_rpow
    (p scale value : ℝ) (scalePositive : 0 < scale)
    (valueNonnegative : 0 ≤ value) :
    scale * (value / scale) ^ p =
      value ^ p / scale ^ (p - 1) := by
  rw [Real.div_rpow valueNonnegative (le_of_lt scalePositive)]
  have powerSplit : scale ^ p = scale ^ (p - 1) * scale := by
    calc
      scale ^ p = scale ^ ((p - 1) + 1) := by ring_nf
      _ = scale ^ (p - 1) * scale ^ (1 : ℝ) :=
        Real.rpow_add scalePositive (p - 1) 1
      _ = scale ^ (p - 1) * scale := by rw [Real.rpow_one]
  rw [powerSplit]
  have scaleNonzero : scale ≠ 0 := ne_of_gt scalePositive
  have powerNonzero : scale ^ (p - 1) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos scalePositive _)
  field_simp [scaleNonzero, powerNonzero]

/-- The matched decay equation determines the combined site-plus-continuation
coefficient. -/
theorem matchedDecay_combinedCoefficient
    (h m p lambda : ℝ)
    (lambdaPositive : 0 < lambda)
    (decay : MatchedPowerDecayEquation h m p lambda) :
    (m + h * (1 - lambda) ^ (p - 1)) * lambda ^ (p - 1) =
      h * (1 - lambda) ^ (p - 1) := by
  unfold MatchedPowerDecayEquation at decay
  have sitePowerPositive : 0 < lambda ^ (p - 1) :=
    Real.rpow_pos_of_pos lambdaPositive _
  nlinarith

/-- The positive-part predecessor plus a nonnegative successor always covers
the predecessor. -/
theorem le_posPart_sub_add
    (a b : ℝ) (_bNonnegative : 0 ≤ b) :
    a ≤ max (a - b) 0 + b := by
  by_cases differenceNonnegative : 0 ≤ a - b
  · rw [max_eq_left differenceNonnegative]
    ring_nf
    exact le_rfl
  · have differenceNonpositive : a - b ≤ 0 := le_of_not_ge differenceNonnegative
    rw [max_eq_right differenceNonpositive]
    linarith

/-! ## Sharp scalar Bellman inequality -/

/-- The continuation coefficient of the real-exponent matched-power family. -/
noncomputable def matchedPowerContinuationCoefficient
    (h p lambda : ℝ) : ℝ :=
  h * (1 - lambda) ^ (p - 1)

/-- The one-edge matched-power cost, with a directional positive-part edge. -/
noncomputable def matchedPowerEdgeCost
    (h m p a b : ℝ) : ℝ :=
  h * (max (a - b) 0) ^ p + m * b ^ p

/-- The Jensen upper expression is exactly the edge cost plus the continued
tail value. -/
theorem matchedPower_jensen_expression
    (h m p lambda a b : ℝ)
    (_pGreaterOne : 1 < p)
    (lambdaPositive : 0 < lambda) (lambdaBelowOne : lambda < 1)
    (_aNonnegative : 0 ≤ a) (bNonnegative : 0 ≤ b)
    (decay : MatchedPowerDecayEquation h m p lambda) :
    matchedPowerContinuationCoefficient h p lambda *
        ((1 - lambda) *
            (max (a - b) 0 / (1 - lambda)) ^ p +
          lambda * (b / lambda) ^ p) =
      matchedPowerEdgeCost h m p a b +
        matchedPowerContinuationCoefficient h p lambda * b ^ p := by
  have oneMinusPositive : 0 < 1 - lambda := sub_pos.mpr lambdaBelowOne
  have positivePartNonnegative : 0 ≤ max (a - b) 0 := le_max_right _ _
  have leftScale := scale_mul_div_rpow p (1 - lambda)
    (max (a - b) 0) oneMinusPositive positivePartNonnegative
  have rightScale := scale_mul_div_rpow p lambda b
    lambdaPositive bNonnegative
  have combinedCoefficient := matchedDecay_combinedCoefficient h m p lambda
    lambdaPositive decay
  unfold matchedPowerContinuationCoefficient matchedPowerEdgeCost
  rw [leftScale, rightScale]
  have edgePowerPositive : 0 < (1 - lambda) ^ (p - 1) :=
    Real.rpow_pos_of_pos oneMinusPositive _
  have sitePowerPositive : 0 < lambda ^ (p - 1) :=
    Real.rpow_pos_of_pos lambdaPositive _
  let edgePower := (1 - lambda) ^ (p - 1)
  let sitePower := lambda ^ (p - 1)
  let coefficient := h * edgePower
  have edgePowerNonzero : edgePower ≠ 0 := by
    dsimp [edgePower]
    exact ne_of_gt edgePowerPositive
  have sitePowerNonzero : sitePower ≠ 0 := by
    dsimp [sitePower]
    exact ne_of_gt sitePowerPositive
  have leftIdentity :
      coefficient * (max (a - b) 0 ^ p / edgePower) =
        h * max (a - b) 0 ^ p := by
    dsimp [coefficient]
    field_simp [edgePowerNonzero]
  have coefficientQuotient : coefficient / sitePower = m + coefficient := by
    apply (div_eq_iff sitePowerNonzero).2
    dsimp [coefficient, sitePower, edgePower]
    exact combinedCoefficient.symm
  have rightIdentity :
      coefficient * (b ^ p / sitePower) =
        (m + coefficient) * b ^ p := by
    calc
      coefficient * (b ^ p / sitePower) =
          (coefficient / sitePower) * b ^ p := by ring
      _ = (m + coefficient) * b ^ p := by rw [coefficientQuotient]
  change coefficient *
      (max (a - b) 0 ^ p / edgePower + b ^ p / sitePower) =
    h * max (a - b) 0 ^ p + m * b ^ p + coefficient * b ^ p
  rw [mul_add, leftIdentity, rightIdentity]
  ring

/-- Sharp local Bellman inequality for arbitrary real exponent `p > 1`. -/
theorem matchedPower_bellman_lower_bound
    (h m p lambda a b : ℝ)
    (hPositive : 0 < h) (_mPositive : 0 < m)
    (pGreaterOne : 1 < p)
    (lambdaPositive : 0 < lambda) (lambdaBelowOne : lambda < 1)
    (aNonnegative : 0 ≤ a) (bNonnegative : 0 ≤ b)
    (decay : MatchedPowerDecayEquation h m p lambda) :
    matchedPowerContinuationCoefficient h p lambda * a ^ p ≤
      matchedPowerEdgeCost h m p a b +
        matchedPowerContinuationCoefficient h p lambda * b ^ p := by
  let positiveDrop := max (a - b) 0
  let leftNormalized := positiveDrop / (1 - lambda)
  let rightNormalized := b / lambda
  have positiveDropNonnegative : 0 ≤ positiveDrop := le_max_right _ _
  have leftNormalizedNonnegative : 0 ≤ leftNormalized :=
    div_nonneg positiveDropNonnegative (sub_nonneg.mpr (le_of_lt lambdaBelowOne))
  have rightNormalizedNonnegative : 0 ≤ rightNormalized :=
    div_nonneg bNonnegative (le_of_lt lambdaPositive)
  have jensen := weighted_rpow_le p lambda leftNormalized rightNormalized
    pGreaterOne lambdaPositive lambdaBelowOne
    leftNormalizedNonnegative rightNormalizedNonnegative
  have normalizedCombination :
      (1 - lambda) * leftNormalized + lambda * rightNormalized =
        positiveDrop + b := by
    dsimp [leftNormalized, rightNormalized]
    field_simp [ne_of_gt (sub_pos.mpr lambdaBelowOne), ne_of_gt lambdaPositive]
  rw [normalizedCombination] at jensen
  have predecessorCovered : a ≤ positiveDrop + b := by
    exact le_posPart_sub_add a b bNonnegative
  have sumNonnegative : 0 ≤ positiveDrop + b :=
    add_nonneg positiveDropNonnegative bNonnegative
  have powerMonotone : a ^ p ≤ (positiveDrop + b) ^ p :=
    Real.rpow_le_rpow aNonnegative predecessorCovered
      (le_trans (by norm_num) (le_of_lt pGreaterOne))
  have coefficientPositive :
      0 < matchedPowerContinuationCoefficient h p lambda := by
    exact mul_pos hPositive
      (Real.rpow_pos_of_pos (sub_pos.mpr lambdaBelowOne) _)
  have scaledChain :
      matchedPowerContinuationCoefficient h p lambda * a ^ p ≤
        matchedPowerContinuationCoefficient h p lambda *
          ((1 - lambda) * leftNormalized ^ p +
            lambda * rightNormalized ^ p) := by
    exact (mul_le_mul_of_nonneg_left powerMonotone (le_of_lt coefficientPositive)).trans
      (mul_le_mul_of_nonneg_left jensen (le_of_lt coefficientPositive))
  rw [matchedPower_jensen_expression h m p lambda a b pGreaterOne
    lambdaPositive lambdaBelowOne aNonnegative bNonnegative decay] at scaledChain
  exact scaledChain

/-- Equality in the sharp Bellman inequality holds exactly at the geometric
successor. -/
theorem matchedPower_bellman_equality_iff
    (h m p lambda a b : ℝ)
    (hPositive : 0 < h) (_mPositive : 0 < m)
    (pGreaterOne : 1 < p)
    (lambdaPositive : 0 < lambda) (lambdaBelowOne : lambda < 1)
    (aNonnegative : 0 ≤ a) (bNonnegative : 0 ≤ b)
    (decay : MatchedPowerDecayEquation h m p lambda) :
    matchedPowerEdgeCost h m p a b +
        matchedPowerContinuationCoefficient h p lambda * b ^ p =
        matchedPowerContinuationCoefficient h p lambda * a ^ p ↔
      b = lambda * a := by
  let positiveDrop := max (a - b) 0
  let leftNormalized := positiveDrop / (1 - lambda)
  let rightNormalized := b / lambda
  have positiveDropNonnegative : 0 ≤ positiveDrop := le_max_right _ _
  have leftNormalizedNonnegative : 0 ≤ leftNormalized :=
    div_nonneg positiveDropNonnegative (sub_nonneg.mpr (le_of_lt lambdaBelowOne))
  have rightNormalizedNonnegative : 0 ≤ rightNormalized :=
    div_nonneg bNonnegative (le_of_lt lambdaPositive)
  have normalizedCombination :
      (1 - lambda) * leftNormalized + lambda * rightNormalized =
        positiveDrop + b := by
    dsimp [leftNormalized, rightNormalized]
    field_simp [ne_of_gt (sub_pos.mpr lambdaBelowOne), ne_of_gt lambdaPositive]
  have predecessorCovered : a ≤ positiveDrop + b :=
    le_posPart_sub_add a b bNonnegative
  have coefficientPositive :
      0 < matchedPowerContinuationCoefficient h p lambda := by
    exact mul_pos hPositive
      (Real.rpow_pos_of_pos (sub_pos.mpr lambdaBelowOne) _)
  constructor
  · intro totalEquality
    have normalizedEqual : leftNormalized = rightNormalized := by
      by_contra normalizedDiffer
      have strictJensen := weighted_rpow_lt p lambda
        leftNormalized rightNormalized pGreaterOne lambdaPositive lambdaBelowOne
        leftNormalizedNonnegative rightNormalizedNonnegative normalizedDiffer
      rw [normalizedCombination] at strictJensen
      have powerMonotone : a ^ p ≤ (positiveDrop + b) ^ p :=
        Real.rpow_le_rpow aNonnegative predecessorCovered
          (le_trans (by norm_num) (le_of_lt pGreaterOne))
      have strictScaled :
          matchedPowerContinuationCoefficient h p lambda * a ^ p <
            matchedPowerContinuationCoefficient h p lambda *
              ((1 - lambda) * leftNormalized ^ p +
                lambda * rightNormalized ^ p) :=
        (mul_le_mul_of_nonneg_left powerMonotone
          (le_of_lt coefficientPositive)).trans_lt
          (mul_lt_mul_of_pos_left strictJensen coefficientPositive)
      rw [matchedPower_jensen_expression h m p lambda a b pGreaterOne
        lambdaPositive lambdaBelowOne aNonnegative bNonnegative decay] at strictScaled
      exact (not_lt_of_ge (le_of_eq totalEquality) strictScaled)
    have crossIdentity : lambda * positiveDrop = (1 - lambda) * b := by
      dsimp [leftNormalized, rightNormalized] at normalizedEqual
      field_simp [ne_of_gt (sub_pos.mpr lambdaBelowOne),
        ne_of_gt lambdaPositive] at normalizedEqual
      nlinarith
    by_cases differenceNonnegative : 0 ≤ a - b
    · have positiveDropIdentity : positiveDrop = a - b := by
        dsimp [positiveDrop]
        exact max_eq_left differenceNonnegative
      rw [positiveDropIdentity] at crossIdentity
      nlinarith
    · have differenceNonpositive : a - b ≤ 0 := le_of_not_ge differenceNonnegative
      have positiveDropZero : positiveDrop = 0 := by
        dsimp [positiveDrop]
        exact max_eq_right differenceNonpositive
      rw [positiveDropZero] at crossIdentity
      have bZero : b = 0 := by nlinarith
      have aZero : a = 0 := by nlinarith
      rw [aZero, bZero]
      ring
  · intro geometricSuccessor
    subst b
    have differenceNonnegative : 0 ≤ a - lambda * a := by
      nlinarith
    have positiveDropIdentity :
        max (a - lambda * a) 0 = (1 - lambda) * a := by
      rw [max_eq_left differenceNonnegative]
      ring
    have leftNormalizedIdentity :
        max (a - lambda * a) 0 / (1 - lambda) = a := by
      rw [positiveDropIdentity]
      field_simp [ne_of_gt (sub_pos.mpr lambdaBelowOne)]
    have rightNormalizedIdentity : lambda * a / lambda = a := by
      field_simp [ne_of_gt lambdaPositive]
    have jensenExpressionIdentity :
        (1 - lambda) *
            (max (a - lambda * a) 0 / (1 - lambda)) ^ p +
          lambda * (lambda * a / lambda) ^ p = a ^ p := by
      rw [leftNormalizedIdentity, rightNormalizedIdentity]
      ring
    have expressionIdentity := matchedPower_jensen_expression h m p lambda
      a (lambda * a) pGreaterOne lambdaPositive lambdaBelowOne aNonnegative
      (mul_nonneg (le_of_lt lambdaPositive) aNonnegative) decay
    rw [jensenExpressionIdentity] at expressionIdentity
    exact expressionIdentity.symm

/-! ## Infinite geometric profile and exact global value -/

/-- Geometric profile generated by the matched-power decay ratio. -/
noncomputable def matchedPowerGeometricProfile
    (lambda : ℝ) (index : ℕ) : ℝ :=
  lambda ^ index

/-- Edge-and-site cost along the geometric profile. -/
noncomputable def matchedPowerGeometricCost
    (h m p lambda : ℝ) (index : ℕ) : ℝ :=
  matchedPowerEdgeCost h m p
    (matchedPowerGeometricProfile lambda index)
    (matchedPowerGeometricProfile lambda (index + 1))

/-- Bellman continuation potential along the geometric profile. -/
noncomputable def matchedPowerGeometricPotential
    (h p lambda : ℝ) (index : ℕ) : ℝ :=
  matchedPowerContinuationCoefficient h p lambda *
    (matchedPowerGeometricProfile lambda index) ^ p

/-- Every geometric edge realizes equality in the sharp Bellman bound. -/
theorem matchedPower_geometric_local_identity
    (h m p lambda : ℝ)
    (hPositive : 0 < h) (mPositive : 0 < m)
    (pGreaterOne : 1 < p)
    (lambdaPositive : 0 < lambda) (lambdaBelowOne : lambda < 1)
    (decay : MatchedPowerDecayEquation h m p lambda)
    (index : ℕ) :
    matchedPowerGeometricPotential h p lambda index =
      matchedPowerGeometricCost h m p lambda index +
        matchedPowerGeometricPotential h p lambda (index + 1) := by
  have currentNonnegative :
      0 ≤ matchedPowerGeometricProfile lambda index :=
    pow_nonneg (le_of_lt lambdaPositive) _
  have nextNonnegative :
      0 ≤ matchedPowerGeometricProfile lambda (index + 1) :=
    pow_nonneg (le_of_lt lambdaPositive) _
  have successorIdentity :
      matchedPowerGeometricProfile lambda (index + 1) =
        lambda * matchedPowerGeometricProfile lambda index := by
    simp [matchedPowerGeometricProfile, pow_succ, mul_comm]
  have equality := (matchedPower_bellman_equality_iff h m p lambda
    (matchedPowerGeometricProfile lambda index)
    (matchedPowerGeometricProfile lambda (index + 1))
    hPositive mPositive pGreaterOne lambdaPositive lambdaBelowOne
    currentNonnegative nextNonnegative decay).2 successorIdentity
  simpa [matchedPowerGeometricPotential, matchedPowerGeometricCost] using
    equality.symm

/-- The geometric continuation potential tends to zero. -/
theorem matchedPower_geometric_potential_vanishes
    (h p lambda : ℝ) (pGreaterOne : 1 < p)
    (lambdaNonnegative : 0 ≤ lambda) (lambdaBelowOne : lambda < 1) :
    Tendsto (matchedPowerGeometricPotential h p lambda) atTop (nhds 0) := by
  have powersVanish :
      Tendsto (matchedPowerGeometricProfile lambda) atTop (nhds 0) := by
    change Tendsto (fun index : ℕ => lambda ^ index) atTop (nhds 0)
    exact tendsto_pow_atTop_nhds_zero_of_lt_one lambdaNonnegative lambdaBelowOne
  have pNonnegative : 0 ≤ p := le_trans (by norm_num) (le_of_lt pGreaterOne)
  have poweredVanish := powersVanish.rpow_const (Or.inr pNonnegative)
  have pNonzero : p ≠ 0 := ne_of_gt (lt_trans (by norm_num) pGreaterOne)
  have scaledVanish := poweredVanish.const_mul
    (matchedPowerContinuationCoefficient h p lambda)
  change Tendsto
    (fun index => matchedPowerContinuationCoefficient h p lambda *
      matchedPowerGeometricProfile lambda index ^ p) atTop (nhds 0)
  simpa [Real.zero_rpow pNonzero] using scaledVanish

/-- The geometric partial costs converge to the exact continuation
coefficient. -/
theorem matchedPower_geometric_cost_converges
    (h m p lambda : ℝ)
    (hPositive : 0 < h) (mPositive : 0 < m)
    (pGreaterOne : 1 < p)
    (lambdaPositive : 0 < lambda) (lambdaBelowOne : lambda < 1)
    (decay : MatchedPowerDecayEquation h m p lambda) :
    Tendsto
      (fun horizon =>
        ∑ index ∈ range horizon,
          matchedPowerGeometricCost h m p lambda index)
      atTop (nhds (matchedPowerContinuationCoefficient h p lambda)) := by
  have localIdentity := matchedPower_geometric_local_identity h m p lambda
    hPositive mPositive pGreaterOne lambdaPositive lambdaBelowOne decay
  have residualVanishing := matchedPower_geometric_potential_vanishes h p lambda
    pGreaterOne (le_of_lt lambdaPositive) lambdaBelowOne
  simpa [matchedPowerGeometricPotential, matchedPowerGeometricProfile] using
    bellman_partial_costs_converge
      (matchedPowerGeometricCost h m p lambda)
      (matchedPowerGeometricPotential h p lambda)
      localIdentity residualVanishing

/-- The geometric profile belongs to the declared real `ell^p` domain. -/
theorem matchedPower_geometric_site_summable
    (p lambda : ℝ) (pGreaterOne : 1 < p)
    (lambdaNonnegative : 0 ≤ lambda) (lambdaBelowOne : lambda < 1) :
    Summable (fun index : ℕ =>
      (matchedPowerGeometricProfile lambda index) ^ p) := by
  have pPositive : 0 < p := lt_trans (by norm_num) pGreaterOne
  have ratioNonnegative : 0 ≤ lambda ^ p :=
    Real.rpow_nonneg lambdaNonnegative _
  have ratioBelowOne : lambda ^ p < 1 := by
    simpa using Real.rpow_lt_rpow lambdaNonnegative lambdaBelowOne pPositive
  have geometricSummable :=
    summable_geometric_of_lt_one ratioNonnegative ratioBelowOne
  have pointwiseIdentity :
      (fun index : ℕ =>
        matchedPowerGeometricProfile lambda index ^ p) =
      fun index : ℕ => (lambda ^ p) ^ index := by
    funext index
    exact (Real.rpow_pow_comm lambdaNonnegative p index).symm
  rw [pointwiseIdentity]
  exact geometricSummable

/-- The nonnegative geometric edge-cost series has the exact sum given by the
continuation coefficient. -/
theorem matchedPower_geometric_cost_hasSum
    (h m p lambda : ℝ)
    (hPositive : 0 < h) (mPositive : 0 < m)
    (pGreaterOne : 1 < p)
    (lambdaPositive : 0 < lambda) (lambdaBelowOne : lambda < 1)
    (decay : MatchedPowerDecayEquation h m p lambda) :
    HasSum (matchedPowerGeometricCost h m p lambda)
      (matchedPowerContinuationCoefficient h p lambda) := by
  have costNonnegative :
      ∀ index, 0 ≤ matchedPowerGeometricCost h m p lambda index := by
    intro index
    unfold matchedPowerGeometricCost matchedPowerEdgeCost
    exact add_nonneg
      (mul_nonneg (le_of_lt hPositive) (Real.rpow_nonneg (le_max_right _ _) _))
      (mul_nonneg (le_of_lt mPositive)
        (Real.rpow_nonneg (pow_nonneg (le_of_lt lambdaPositive) _) _))
  exact (hasSum_iff_tendsto_nat_of_nonneg costNonnegative
    (matchedPowerContinuationCoefficient h p lambda)).2
      (matchedPower_geometric_cost_converges h m p lambda hPositive
        mPositive pGreaterOne lambdaPositive lambdaBelowOne decay)

/-- Cost of an arbitrary infinite profile. -/
noncomputable def matchedPowerProfileCost
    (h m p : ℝ) (profile : ℕ → ℝ) (index : ℕ) : ℝ :=
  matchedPowerEdgeCost h m p (profile index) (profile (index + 1))

/-- Continuation potential of an arbitrary infinite profile. -/
noncomputable def matchedPowerProfilePotential
    (h p lambda : ℝ) (profile : ℕ → ℝ) (index : ℕ) : ℝ :=
  matchedPowerContinuationCoefficient h p lambda * (profile index) ^ p

/-- Every admissible infinite profile has cost at least the geometric
continuation value. -/
theorem matchedPower_global_lower_bound
    (h m p lambda : ℝ) (profile : ℕ → ℝ)
    (hPositive : 0 < h) (mPositive : 0 < m)
    (pGreaterOne : 1 < p)
    (lambdaPositive : 0 < lambda) (lambdaBelowOne : lambda < 1)
    (decay : MatchedPowerDecayEquation h m p lambda)
    (profileInitial : profile 0 = 1)
    (profileNonnegative : ∀ index, 0 ≤ profile index)
    (costSummable : Summable (matchedPowerProfileCost h m p profile))
    (siteSummable : Summable (fun index => (profile index) ^ p)) :
    matchedPowerContinuationCoefficient h p lambda ≤
      ∑' index, matchedPowerProfileCost h m p profile index := by
  have localBound : ∀ index,
      matchedPowerProfilePotential h p lambda profile index ≤
        matchedPowerProfileCost h m p profile index +
          matchedPowerProfilePotential h p lambda profile (index + 1) := by
    intro index
    exact matchedPower_bellman_lower_bound h m p lambda
      (profile index) (profile (index + 1)) hPositive mPositive pGreaterOne
      lambdaPositive lambdaBelowOne (profileNonnegative index)
      (profileNonnegative (index + 1)) decay
  have costConvergence := costSummable.hasSum.tendsto_sum_nat
  have residualVanishing :
      Tendsto (matchedPowerProfilePotential h p lambda profile)
        atTop (nhds 0) := by
    have siteVanishing := siteSummable.tendsto_atTop_zero
    change Tendsto
      (fun index => matchedPowerContinuationCoefficient h p lambda *
        profile index ^ p) atTop (nhds 0)
    simpa using siteVanishing.const_mul
      (matchedPowerContinuationCoefficient h p lambda)
  have lowerBound := bellman_limit_lower_bound
    (matchedPowerProfileCost h m p profile)
    (matchedPowerProfilePotential h p lambda profile)
    (∑' index, matchedPowerProfileCost h m p profile index)
    localBound costConvergence residualVanishing
  simpa [matchedPowerProfilePotential, profileInitial] using lowerBound

/-- Equality in the global lower bound forces the geometric recurrence at
every edge. -/
theorem matchedPower_global_equality_forces_recurrence
    (h m p lambda : ℝ) (profile : ℕ → ℝ)
    (hPositive : 0 < h) (mPositive : 0 < m)
    (pGreaterOne : 1 < p)
    (lambdaPositive : 0 < lambda) (lambdaBelowOne : lambda < 1)
    (decay : MatchedPowerDecayEquation h m p lambda)
    (profileInitial : profile 0 = 1)
    (profileNonnegative : ∀ index, 0 ≤ profile index)
    (costSummable : Summable (matchedPowerProfileCost h m p profile))
    (siteSummable : Summable (fun index => (profile index) ^ p))
    (costEquality :
      ∑' index, matchedPowerProfileCost h m p profile index =
        matchedPowerContinuationCoefficient h p lambda) :
    ∀ index, profile (index + 1) = lambda * profile index := by
  intro index
  have localBound : ∀ position,
      matchedPowerProfilePotential h p lambda profile position ≤
        matchedPowerProfileCost h m p profile position +
          matchedPowerProfilePotential h p lambda profile (position + 1) := by
    intro position
    exact matchedPower_bellman_lower_bound h m p lambda
      (profile position) (profile (position + 1)) hPositive mPositive pGreaterOne
      lambdaPositive lambdaBelowOne (profileNonnegative position)
      (profileNonnegative (position + 1)) decay
  by_contra recurrenceFails
  have localStrict :
      matchedPowerProfilePotential h p lambda profile index <
        matchedPowerProfileCost h m p profile index +
          matchedPowerProfilePotential h p lambda profile (index + 1) := by
    have equalityCharacterization := matchedPower_bellman_equality_iff
      h m p lambda (profile index) (profile (index + 1)) hPositive mPositive
      pGreaterOne lambdaPositive lambdaBelowOne (profileNonnegative index)
      (profileNonnegative (index + 1)) decay
    have notReverseEquality :
        matchedPowerProfileCost h m p profile index +
            matchedPowerProfilePotential h p lambda profile (index + 1) ≠
          matchedPowerProfilePotential h p lambda profile index := by
      simpa [matchedPowerProfileCost, matchedPowerProfilePotential] using
        (not_congr equalityCharacterization).mpr recurrenceFails
    exact lt_of_le_of_ne (localBound index) notReverseEquality.symm
  have costConvergence := costSummable.hasSum.tendsto_sum_nat
  have residualVanishing :
      Tendsto (matchedPowerProfilePotential h p lambda profile)
        atTop (nhds 0) := by
    have siteVanishing := siteSummable.tendsto_atTop_zero
    change Tendsto
      (fun position => matchedPowerContinuationCoefficient h p lambda *
        profile position ^ p) atTop (nhds 0)
    simpa using siteVanishing.const_mul
      (matchedPowerContinuationCoefficient h p lambda)
  have strictGlobal := bellman_limit_strict_of_local_strict
    (matchedPowerProfileCost h m p profile)
    (matchedPowerProfilePotential h p lambda profile)
    (∑' position, matchedPowerProfileCost h m p profile position)
    index localBound localStrict costConvergence residualVanishing
  have initialPotential :
      matchedPowerProfilePotential h p lambda profile 0 =
        matchedPowerContinuationCoefficient h p lambda := by
    simp [matchedPowerProfilePotential, profileInitial]
  rw [initialPotential, costEquality] at strictGlobal
  exact (lt_irrefl _ strictGlobal)

/-- The geometric profile is the unique admissible global minimizer. -/
theorem matchedPower_unique_global_minimizer
    (h m p lambda : ℝ) (profile : ℕ → ℝ)
    (hPositive : 0 < h) (mPositive : 0 < m)
    (pGreaterOne : 1 < p)
    (lambdaPositive : 0 < lambda) (lambdaBelowOne : lambda < 1)
    (decay : MatchedPowerDecayEquation h m p lambda)
    (profileInitial : profile 0 = 1)
    (profileNonnegative : ∀ index, 0 ≤ profile index)
    (costSummable : Summable (matchedPowerProfileCost h m p profile))
    (siteSummable : Summable (fun index => (profile index) ^ p))
    (costEquality :
      ∑' index, matchedPowerProfileCost h m p profile index =
        matchedPowerContinuationCoefficient h p lambda) :
    ∀ index, profile index = matchedPowerGeometricProfile lambda index := by
  have recurrence := matchedPower_global_equality_forces_recurrence
    h m p lambda profile hPositive mPositive pGreaterOne lambdaPositive
    lambdaBelowOne decay profileInitial profileNonnegative costSummable
    siteSummable costEquality
  intro index
  induction index with
  | zero => simpa [matchedPowerGeometricProfile] using profileInitial
  | succ index inductionHypothesis =>
      rw [recurrence index, inductionHypothesis]
      simp [matchedPowerGeometricProfile, pow_succ, mul_comm]

/-- Full real-exponent SUP-E3 package: one decay ratio, one admissible
geometric winner, exact value, global lower bound, and equality uniqueness. -/
theorem sup_e3_general_real_exponent
    (h m p : ℝ) (hPositive : 0 < h) (mPositive : 0 < m)
    (pGreaterOne : 1 < p) :
    ∃! lambda : ℝ,
      0 < lambda ∧ lambda < 1 ∧
      MatchedPowerDecayEquation h m p lambda ∧
      HasSum (matchedPowerGeometricCost h m p lambda)
        (matchedPowerContinuationCoefficient h p lambda) ∧
      Summable (fun index : ℕ =>
        matchedPowerGeometricProfile lambda index ^ p) := by
  obtain ⟨lambda, lambdaPositive, lambdaBelowOne, lambdaDecay⟩ :=
    exists_matchedPowerDecayRatio h m p hPositive mPositive pGreaterOne
  refine ⟨lambda,
    ⟨lambdaPositive, lambdaBelowOne, lambdaDecay,
      matchedPower_geometric_cost_hasSum h m p lambda hPositive mPositive
        pGreaterOne lambdaPositive lambdaBelowOne lambdaDecay,
      matchedPower_geometric_site_summable p lambda pGreaterOne
        (le_of_lt lambdaPositive) lambdaBelowOne⟩, ?_⟩
  intro mu muProperties
  exact matchedPowerDecayRatio_unique h m p mu lambda hPositive mPositive
    pGreaterOne muProperties.1 muProperties.2.1 lambdaPositive lambdaBelowOne
    muProperties.2.2.1 lambdaDecay

/-! ## Exact finite continuation and projective prefixes -/

/-- Finite matched-power objective with the exact monomial continuation. -/
noncomputable def matchedPowerFiniteContinuationCost
    (h m p lambda : ℝ) (profile : ℕ → ℝ) (horizon : ℕ) : ℝ :=
  (∑ index ∈ range horizon,
      matchedPowerProfileCost h m p profile index) +
    matchedPowerProfilePotential h p lambda profile horizon

/-- Exact continuation gives a lower bound independent of the finite horizon. -/
theorem matchedPower_finite_continuation_lower_bound
    (h m p lambda : ℝ) (profile : ℕ → ℝ) (horizon : ℕ)
    (hPositive : 0 < h) (mPositive : 0 < m)
    (pGreaterOne : 1 < p)
    (lambdaPositive : 0 < lambda) (lambdaBelowOne : lambda < 1)
    (decay : MatchedPowerDecayEquation h m p lambda)
    (profileInitial : profile 0 = 1)
    (profileNonnegative : ∀ index, 0 ≤ profile index) :
    matchedPowerContinuationCoefficient h p lambda ≤
      matchedPowerFiniteContinuationCost h m p lambda profile horizon := by
  have localBound : ∀ index,
      matchedPowerProfilePotential h p lambda profile index ≤
        matchedPowerProfileCost h m p profile index +
          matchedPowerProfilePotential h p lambda profile (index + 1) := by
    intro index
    exact matchedPower_bellman_lower_bound h m p lambda
      (profile index) (profile (index + 1)) hPositive mPositive pGreaterOne
      lambdaPositive lambdaBelowOne (profileNonnegative index)
      (profileNonnegative (index + 1)) decay
  have prefixBound := bellman_prefix_lower_bound
    (matchedPowerProfileCost h m p profile)
    (matchedPowerProfilePotential h p lambda profile)
    localBound horizon
  simpa [matchedPowerFiniteContinuationCost, matchedPowerProfilePotential,
    profileInitial] using prefixBound

/-- The geometric prefix attains the exact finite continuation value at every
horizon. -/
theorem matchedPower_geometric_finite_continuation_identity
    (h m p lambda : ℝ) (horizon : ℕ)
    (hPositive : 0 < h) (mPositive : 0 < m)
    (pGreaterOne : 1 < p)
    (lambdaPositive : 0 < lambda) (lambdaBelowOne : lambda < 1)
    (decay : MatchedPowerDecayEquation h m p lambda) :
    matchedPowerFiniteContinuationCost h m p lambda
        (matchedPowerGeometricProfile lambda) horizon =
      matchedPowerContinuationCoefficient h p lambda := by
  have localIdentity := matchedPower_geometric_local_identity h m p lambda
    hPositive mPositive pGreaterOne lambdaPositive lambdaBelowOne decay
  have prefixIdentity := bellman_prefix_identity
    (matchedPowerGeometricCost h m p lambda)
    (matchedPowerGeometricPotential h p lambda)
    localIdentity horizon
  simpa [matchedPowerFiniteContinuationCost, matchedPowerProfileCost,
    matchedPowerProfilePotential, matchedPowerGeometricCost,
    matchedPowerGeometricPotential, matchedPowerGeometricProfile] using
      prefixIdentity.symm

/-- Equality in the continued finite objective forces every retained edge to
follow the geometric recurrence. -/
theorem matchedPower_finite_equality_forces_recurrence
    (h m p lambda : ℝ) (profile : ℕ → ℝ) (horizon : ℕ)
    (hPositive : 0 < h) (mPositive : 0 < m)
    (pGreaterOne : 1 < p)
    (lambdaPositive : 0 < lambda) (lambdaBelowOne : lambda < 1)
    (decay : MatchedPowerDecayEquation h m p lambda)
    (profileInitial : profile 0 = 1)
    (profileNonnegative : ∀ index, 0 ≤ profile index)
    (costEquality :
      matchedPowerFiniteContinuationCost h m p lambda profile horizon =
        matchedPowerContinuationCoefficient h p lambda) :
    ∀ index, index < horizon →
      profile (index + 1) = lambda * profile index := by
  intro index indexBeforeHorizon
  let cost := matchedPowerProfileCost h m p profile
  let potential := matchedPowerProfilePotential h p lambda profile
  let gap : ℕ → ℝ := fun position =>
    cost position + potential (position + 1) - potential position
  have localBound : ∀ position,
      potential position ≤ cost position + potential (position + 1) := by
    intro position
    exact matchedPower_bellman_lower_bound h m p lambda
      (profile position) (profile (position + 1)) hPositive mPositive pGreaterOne
      lambdaPositive lambdaBelowOne (profileNonnegative position)
      (profileNonnegative (position + 1)) decay
  have gapNonnegative : ∀ position, 0 ≤ gap position := by
    intro position
    dsimp [gap]
    linarith [localBound position]
  have gapSumZero : ∑ position ∈ range horizon, gap position = 0 := by
    rw [bellman_gap_sum_identity cost potential horizon]
    dsimp [cost, potential]
    rw [← matchedPowerFiniteContinuationCost]
    simp [costEquality, matchedPowerProfilePotential, profileInitial]
  have selectedGapLe : gap index ≤ ∑ position ∈ range horizon, gap position :=
    single_le_sum (fun position _ => gapNonnegative position)
      (mem_range.mpr indexBeforeHorizon)
  rw [gapSumZero] at selectedGapLe
  have selectedGapZero : gap index = 0 :=
    le_antisymm selectedGapLe (gapNonnegative index)
  have localEquality :
      matchedPowerProfileCost h m p profile index +
          matchedPowerProfilePotential h p lambda profile (index + 1) =
        matchedPowerProfilePotential h p lambda profile index := by
    dsimp [gap, cost, potential] at selectedGapZero
    linarith
  exact (matchedPower_bellman_equality_iff h m p lambda
    (profile index) (profile (index + 1)) hPositive mPositive pGreaterOne
    lambdaPositive lambdaBelowOne (profileNonnegative index)
    (profileNonnegative (index + 1)) decay).mp
      (by simpa [matchedPowerProfileCost, matchedPowerProfilePotential] using
        localEquality)

/-- Exact equality identifies the entire retained profile with the geometric
prefix. -/
theorem matchedPower_finite_equality_profile
    (h m p lambda : ℝ) (profile : ℕ → ℝ) (horizon : ℕ)
    (hPositive : 0 < h) (mPositive : 0 < m)
    (pGreaterOne : 1 < p)
    (lambdaPositive : 0 < lambda) (lambdaBelowOne : lambda < 1)
    (decay : MatchedPowerDecayEquation h m p lambda)
    (profileInitial : profile 0 = 1)
    (profileNonnegative : ∀ index, 0 ≤ profile index)
    (costEquality :
      matchedPowerFiniteContinuationCost h m p lambda profile horizon =
        matchedPowerContinuationCoefficient h p lambda) :
    ∀ index, index ≤ horizon →
      profile index = matchedPowerGeometricProfile lambda index := by
  have recurrence := matchedPower_finite_equality_forces_recurrence
    h m p lambda profile horizon hPositive mPositive pGreaterOne
    lambdaPositive lambdaBelowOne decay profileInitial profileNonnegative
    costEquality
  intro index indexWithinHorizon
  induction index with
  | zero => simpa [matchedPowerGeometricProfile] using profileInitial
  | succ index inductionHypothesis =>
      have indexBeforeHorizon : index < horizon := by omega
      rw [recurrence index indexBeforeHorizon,
        inductionHypothesis (Nat.le_of_succ_le indexWithinHorizon)]
      simp [matchedPowerGeometricProfile, pow_succ, mul_comm]

/-- The real-exponent continuation coefficient is uniquely fixed by terminal
stationarity within the declared monomial class. -/
theorem matchedPower_continuationCoefficient_unique
    (h m p lambda : ℝ)
    (lambdaPositive : 0 < lambda)
    (decay : MatchedPowerDecayEquation h m p lambda) :
    ∃! coefficient : ℝ,
      coefficient = matchedPowerContinuationCoefficient h p lambda ∧
      coefficient =
        matchedPowerContinuationCoefficient h p lambda /
            lambda ^ (p - 1) - m := by
  have abstractDecay : SatisfiesMatchedDecay h m
      ((1 - lambda) ^ (p - 1)) (lambda ^ (p - 1)) := by
    unfold SatisfiesMatchedDecay MatchedPowerDecayEquation at *
    exact decay
  simpa [matchedPowerContinuationCoefficient] using
    sup_e4_coefficient_01_unique h m ((1 - lambda) ^ (p - 1))
      (lambda ^ (p - 1))
      (ne_of_gt (Real.rpow_pos_of_pos lambdaPositive _)) abstractDecay

/-- Full real-exponent SUP-E4 package: exact finite-prefix continuation,
prefix identification, and monomial-coefficient uniqueness. -/
theorem sup_e4_general_real_exponent
    (h m p lambda : ℝ)
    (hPositive : 0 < h) (mPositive : 0 < m)
    (pGreaterOne : 1 < p)
    (lambdaPositive : 0 < lambda) (lambdaBelowOne : lambda < 1)
    (decay : MatchedPowerDecayEquation h m p lambda) :
    (∀ horizon,
      matchedPowerFiniteContinuationCost h m p lambda
          (matchedPowerGeometricProfile lambda) horizon =
        matchedPowerContinuationCoefficient h p lambda) ∧
      (∃! coefficient : ℝ,
        coefficient = matchedPowerContinuationCoefficient h p lambda ∧
        coefficient =
          matchedPowerContinuationCoefficient h p lambda /
              lambda ^ (p - 1) - m) := by
  constructor
  · intro horizon
    exact matchedPower_geometric_finite_continuation_identity h m p lambda
      horizon hPositive mPositive pGreaterOne lambdaPositive lambdaBelowOne decay
  · exact matchedPower_continuationCoefficient_unique h m p lambda
      lambdaPositive decay

end PhonologicalCalculus.Support
