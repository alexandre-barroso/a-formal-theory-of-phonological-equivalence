import PhonologicalCalculus.Selection.SphericalMeasure
import PhonologicalCalculus.Selection.TwoShellReversal
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.AtTopBot.Ring
import Mathlib.Tactic

/-!
# Source-facing exact application corollaries

This module contains the exact mathematical layer used by four source-facing
applications.  Source transcription, page anchoring, and bibliographic
identity are maintained in the corresponding JSON records.  Lean proves only
the mathematical consequences of the transcribed equations; it does not
interpret source prose.

The Goldrick--Daland declarations re-export the exact source-premise check and
the four machine-closed branches of `SEL-F2`.  The Walker declarations derive
the exact two-candidate response boundary and its order-only counterwitness.
The Pater declarations prove the complete finite-support common-scaling limit,
two fixed-support counterwitnesses, and the finite exponential error envelope.
The Cabrera declarations prove consumer-relative deletion of the `MPARSE`
parameter, the exact binary curvature factorization and boundary, and the
minimum algebraic recovery bridge.
-/

namespace PhonologicalCalculus.Application

open Filter
open MeasureTheory
open scoped Topology

noncomputable section

-- The source-facing two-shell statements use the same Borel structure on the
-- registered five-dimensional space as their defining module.  These local
-- instances make that structure explicit at the application boundary.
local instance sourceFacingEuclideanFiveMeasurableSpace :
    MeasurableSpace Selection.EuclideanFive :=
  borel Selection.EuclideanFive

local instance sourceFacingEuclideanFiveBorelSpace :
    BorelSpace Selection.EuclideanFive :=
  ⟨rfl⟩

local instance sourceFacingEuclideanUnitSphereNonempty :
    Nonempty Selection.EuclideanUnitSphere :=
  ⟨Selection.euclideanShellDirection⟩

/-! ## Goldrick--Daland selected-output binding -/

theorem goldrickDaland_sel_f2_source_matchedPremises :
    Selection.bilinear Selection.firstInput
        Selection.counterexampleFaithfulness Selection.firstOutput = 20 ∧
      Selection.bilinear Selection.secondInput
        Selection.counterexampleFaithfulness Selection.jointOutput = 20 ∧
      Selection.bilinear Selection.firstInput
        Selection.counterexampleFaithfulness Selection.jointOutput = 3 ∧
      Selection.bilinear Selection.secondInput
        Selection.counterexampleFaithfulness Selection.firstOutput = 3 ∧
      Selection.bilinear Selection.firstOutput
        Selection.counterexampleMarkedness Selection.firstOutput = 0 ∧
      Selection.bilinear Selection.jointOutput
        Selection.counterexampleMarkedness Selection.jointOutput = -2 ∧
      (19 : ℤ) > 15 ∧
      (1 : ℤ) ^ 2 + 2 ^ 2 = 5 ∧
      ((-1 : ℤ) ^ 2 + (-2 : ℤ) ^ 2 = 5) :=
  Selection.matchedPairPremises

theorem goldrickDaland_sel_f2_source_contrastPreservation :
    Selection.firstInput ≠ Selection.secondInput ∧
      Selection.firstOutput ≠ Selection.jointOutput := by
  decide

theorem goldrickDaland_sel_f2_source_scores :
    Selection.scoreRow Selection.firstInput = [0, 20, -17, 1] ∧
      Selection.scoreRow Selection.secondInput = [0, 3, 17, 18] ∧
      (20 : ℤ) > 0 ∧ 20 > -17 ∧ 20 > 1 ∧
      (18 : ℤ) > 0 ∧ 18 > 3 ∧ 18 > 17 :=
  Selection.sel_f2_scores_01

theorem goldrickDaland_sel_f2_source_euclidean :
    Selection.firstSelectedClosure Selection.euclideanFirstProjection ∧
      Selection.euclideanSquared Selection.euclideanFirstProjection = 361 / 5 ∧
      (∀ point, Selection.firstSelectedClosure point →
        361 / 5 ≤ Selection.euclideanSquared point) ∧
      Selection.secondSelectedClosure Selection.euclideanSecondProjection ∧
      Selection.euclideanSquared Selection.euclideanSecondProjection = 1010 / 9 ∧
      (∀ point, Selection.secondSelectedClosure point →
        1010 / 9 ≤ Selection.euclideanSquared point) ∧
      1010 / 9 - 361 / 5 = 1801 / 45 ∧
      (0 : ℝ) < 16 / 9 ∧ (0 : ℝ) < 55 / 9 :=
  Selection.sel_f2_euclidean_02

theorem goldrickDaland_sel_f2_source_frobenius :
    Selection.firstSelectedClosure Selection.frobeniusFirstProjection ∧
      Selection.frobeniusSquared Selection.frobeniusFirstProjection = 361 / 3 ∧
      (∀ point, Selection.firstSelectedClosure point →
        361 / 3 ≤ Selection.frobeniusSquared point) ∧
      Selection.secondSelectedClosure Selection.frobeniusSecondProjection ∧
      Selection.frobeniusSquared Selection.frobeniusSecondProjection = 618 / 5 ∧
      (∀ point, Selection.secondSelectedClosure point →
        618 / 5 ≤ Selection.frobeniusSquared point) ∧
      618 / 5 - 361 / 3 = 49 / 15 :=
  Selection.sel_f2_frobenius_03

theorem goldrickDaland_sel_f2_source_commonLaw :
    ((Selection.euclideanSphericalLaw :
          MeasureTheory.Measure Selection.EuclideanUnitSphere)
        (Selection.euclideanSecondDirectionEvent
          Selection.euclideanShellRadius) = 0 ∧
      0 < (Selection.euclideanSphericalLaw :
          MeasureTheory.Measure Selection.EuclideanUnitSphere)
        (Selection.euclideanFirstDirectionEvent
          Selection.euclideanShellRadius)) ∧
    ((Selection.frobeniusSphericalLaw :
          MeasureTheory.Measure Selection.EuclideanUnitSphere)
        (Selection.frobeniusSecondDirectionEvent
          Selection.frobeniusShellRadius) = 0 ∧
      0 < (Selection.frobeniusSphericalLaw :
          MeasureTheory.Measure Selection.EuclideanUnitSphere)
        (Selection.frobeniusFirstDirectionEvent
          Selection.frobeniusShellRadius)) :=
  Selection.sel_f2_commonlaw_04

/-- Exact source-facing strengthening of the intermediate-shell witness: in
both registered metrics there is one common two-atom radial law under which
both named selected-output errors have positive probability and
`P(w maps to y) < P(x maps to z)`. -/
theorem goldrickDaland_sel_f2_source_twoShellPositiveReversal :
    (∃ law : Selection.TwoShellSphericalLaw Selection.EuclideanUnitSphere,
      law.angularLaw = Selection.euclideanSphericalLaw ∧
      0 < law.eventProbability Selection.euclideanFirstDirectionEvent ∧
      0 < law.eventProbability Selection.euclideanSecondDirectionEvent ∧
      law.eventProbability Selection.euclideanSecondDirectionEvent <
        law.eventProbability Selection.euclideanFirstDirectionEvent) ∧
    (∃ law : Selection.TwoShellSphericalLaw Selection.EuclideanUnitSphere,
      law.angularLaw = Selection.frobeniusSphericalLaw ∧
      0 < law.eventProbability Selection.frobeniusFirstDirectionEvent ∧
      0 < law.eventProbability Selection.frobeniusSecondDirectionEvent ∧
      law.eventProbability Selection.frobeniusSecondDirectionEvent <
        law.eventProbability Selection.frobeniusFirstDirectionEvent) :=
  Selection.sel_f2_common_twoShell_positive_reversal

/-- Exact mixing step for a two-shell selected-output reversal.  The near
shell contributes positive mass `nearFirst` only to the first event
`x maps to z`; the far shell contributes nonnegative mass `farFirst` to that
event and positive mass `farSecond` to the second event `w maps to y`.  The
declared far-shell weight makes both mixture events positive and proves
`P(w maps to y) < P(x maps to z)`. -/
theorem goldrickDaland_twoShellMixture_reversal
    {nearFirst farFirst farSecond : ℝ}
    (hnear : 0 < nearFirst) (hfarFirst : 0 ≤ farFirst)
    (hfarSecond : 0 < farSecond) :
    let farWeight := nearFirst / (2 * (nearFirst + farSecond))
    0 < farWeight ∧ farWeight < 1 ∧
      0 < farWeight * farSecond ∧
      farWeight * farSecond <
        (1 - farWeight) * nearFirst + farWeight * farFirst := by
  dsimp only
  have hsum : 0 < nearFirst + farSecond := add_pos hnear hfarSecond
  have hdenominator : 0 < 2 * (nearFirst + farSecond) := by positivity
  have hweight : 0 < nearFirst / (2 * (nearFirst + farSecond)) :=
    div_pos hnear hdenominator
  have hweightOne : nearFirst / (2 * (nearFirst + farSecond)) < 1 := by
    apply (div_lt_one hdenominator).2
    linarith
  have hidentity :
      (1 - nearFirst / (2 * (nearFirst + farSecond))) * nearFirst +
          (nearFirst / (2 * (nearFirst + farSecond))) * farFirst -
          (nearFirst / (2 * (nearFirst + farSecond))) * farSecond =
        nearFirst / 2 +
          (nearFirst / (2 * (nearFirst + farSecond))) * farFirst := by
    field_simp [hsum.ne']
    ring
  have hfarTerm :
      0 ≤ (nearFirst / (2 * (nearFirst + farSecond))) * farFirst :=
    mul_nonneg hweight.le hfarFirst
  refine ⟨hweight, hweightOne, mul_pos hweight hfarSecond, ?_⟩
  linarith

/-! ## Walker's two-candidate Korean place-activity fragment -/

/-- Penalty assigned to the assimilation candidate when the target activity
is `x`. -/
def walkerAssimilationCost (x : ℝ) : ℝ := 1 + 20 * x

/-- Penalty assigned to the faithful candidate when the trigger activity is
`y`. -/
def walkerFaithfulCost (y : ℝ) : ℝ := 2 + 20 * y

theorem walker_assimilation_iff (x y : ℝ) :
    walkerAssimilationCost x < walkerFaithfulCost y ↔
      -(1 : ℝ) / 20 < y - x := by
  unfold walkerAssimilationCost walkerFaithfulCost
  constructor <;> intro h <;> linarith

theorem walker_tie_iff (x y : ℝ) :
    walkerAssimilationCost x = walkerFaithfulCost y ↔
      y - x = -(1 : ℝ) / 20 := by
  unfold walkerAssimilationCost walkerFaithfulCost
  constructor <;> intro h <;> linarith

theorem walker_faithful_iff (x y : ℝ) :
    walkerFaithfulCost y < walkerAssimilationCost x ↔
      y - x < -(1 : ℝ) / 20 := by
  unfold walkerAssimilationCost walkerFaithfulCost
  constructor <;> intro h <;> linarith

/-- Every activity pair in the open strip `-1/20 < y-x < 0` is an exact
counterwitness to an order-only response rule: the trigger is weaker, but the
printed weighted evaluator selects assimilation. -/
theorem walker_order_only_open_strip_counterwitness
    {x y : ℝ} (hlower : -(1 : ℝ) / 20 < y - x)
    (hupper : y - x < 0) :
    y < x ∧ walkerAssimilationCost x < walkerFaithfulCost y := by
  constructor
  · linarith
  · exact (walker_assimilation_iff x y).2 hlower

/-- Exact rational instance of the open-strip counterwitness. -/
theorem walker_registered_counterwitness :
    (39 : ℝ) / 50 < 4 / 5 ∧
      walkerAssimilationCost (4 / 5) = 17 ∧
      walkerFaithfulCost (39 / 50) = 88 / 5 ∧
      walkerAssimilationCost (4 / 5) <
        walkerFaithfulCost (39 / 50) := by
  norm_num [walkerAssimilationCost, walkerFaithfulCost]

/-- The six directional outcomes induced by three ordered place activities.
The first three clauses are the assimilation directions and the final three
are the faithful directions. -/
def walkerSixDirectionsPreserved (coronal labial dorsal : ℝ) : Prop :=
  walkerAssimilationCost coronal < walkerFaithfulCost labial ∧
  walkerAssimilationCost coronal < walkerFaithfulCost dorsal ∧
  walkerAssimilationCost labial < walkerFaithfulCost dorsal ∧
  walkerFaithfulCost coronal < walkerAssimilationCost labial ∧
  walkerFaithfulCost coronal < walkerAssimilationCost dorsal ∧
  walkerFaithfulCost labial < walkerAssimilationCost dorsal

/-- For an ordered three-place scale, preserving all six unique directions is
equivalent to both adjacent gaps being strictly greater than `1/20`. -/
theorem walker_six_directions_iff_adjacent_gaps
    {coronal labial dorsal : ℝ}
    (horder : coronal < labial ∧ labial < dorsal) :
    walkerSixDirectionsPreserved coronal labial dorsal ↔
      (1 : ℝ) / 20 < labial - coronal ∧
        (1 : ℝ) / 20 < dorsal - labial := by
  rcases horder with ⟨hcl, hld⟩
  unfold walkerSixDirectionsPreserved walkerAssimilationCost walkerFaithfulCost
  constructor
  · rintro ⟨_, _, _, hfc, _, hfl⟩
    constructor <;> linarith
  · rintro ⟨hgapCL, hgapLD⟩
    constructor
    · linarith
    constructor
    · linarith
    constructor
    · linarith
    constructor
    · linarith
    constructor <;> linarith

theorem walker_six_directions_iff_minimum_gap
    {coronal labial dorsal : ℝ}
    (horder : coronal < labial ∧ labial < dorsal) :
    walkerSixDirectionsPreserved coronal labial dorsal ↔
      (1 : ℝ) / 20 < min (labial - coronal) (dorsal - labial) := by
  rw [walker_six_directions_iff_adjacent_gaps horder, lt_min_iff]

/-! ## Pater--Staubs--Jesney--Smith fixed-support scaling -/

section PaterFiniteSupport

variable {Candidate : Type*} [Fintype Candidate]

/-- Probability of a target overt fibre under common scaling of every hidden
candidate Harmony.  Candidate support, base mass, and the overt-fibre map are
held fixed. -/
def paterCommonScalingProbability
    (target : Candidate → Prop) (baseMass score : Candidate → ℝ)
    (time : ℝ) : ℝ := by
  classical
  exact
    (∑ candidate ∈ Finset.univ.filter target,
        baseMass candidate * Real.exp (time * score candidate)) /
      (∑ candidate, baseMass candidate * Real.exp (time * score candidate))

/-- Numerically stable gauge obtained by subtracting a declared global
maximum from every hidden-candidate Harmony. -/
def paterShiftedScalingProbability
    (target : Candidate → Prop) (baseMass score : Candidate → ℝ)
    (maximum time : ℝ) : ℝ := by
  classical
  exact
    (∑ candidate ∈ Finset.univ.filter target,
        baseMass candidate *
          Real.exp (time * (score candidate - maximum))) /
      (∑ candidate,
        baseMass candidate *
          Real.exp (time * (score candidate - maximum)))

/-- Total base mass carried by all globally best hidden candidates. -/
def paterGlobalBestMass
    (baseMass score : Candidate → ℝ) (maximum : ℝ) : ℝ := by
  classical
  exact ∑ candidate ∈ Finset.univ.filter (fun c ↦ score c = maximum),
    baseMass candidate

/-- Base mass carried by globally best hidden candidates in the target overt
fibre. -/
def paterTargetBestMass
    (target : Candidate → Prop) (baseMass score : Candidate → ℝ)
    (maximum : ℝ) : ℝ := by
  classical
  exact ∑ candidate ∈ Finset.univ.filter
    (fun c ↦ target c ∧ score c = maximum), baseMass candidate

omit [Fintype Candidate] in
theorem pater_shifted_candidate_tendsto
    (baseMass score : Candidate → ℝ) (maximum : ℝ)
    (hupper : ∀ candidate, score candidate ≤ maximum)
    (candidate : Candidate) :
    Tendsto
        (fun time ↦ baseMass candidate *
          Real.exp (time * (score candidate - maximum)))
        atTop
        (nhds (if score candidate = maximum then baseMass candidate else 0)) := by
  by_cases hbest : score candidate = maximum
  · simp [hbest]
  · have hstrict : score candidate - maximum < 0 :=
      sub_neg.mpr (lt_of_le_of_ne (hupper candidate) hbest)
    have hexponential :
        Tendsto
          (fun time : ℝ ↦ Real.exp ((score candidate - maximum) * time))
          atTop (nhds 0) :=
      Real.tendsto_exp_atBot.comp
        (tendsto_id.const_mul_atTop_of_neg hstrict)
    have hconstant :
        Tendsto (fun _ : ℝ ↦ baseMass candidate) atTop
          (nhds (baseMass candidate)) := tendsto_const_nhds
    have hproduct := hconstant.mul hexponential
    simpa [hbest, mul_comm] using hproduct

open Classical in
theorem pater_shifted_target_mass_tendsto
    (target : Candidate → Prop) (baseMass score : Candidate → ℝ)
    (maximum : ℝ) (hupper : ∀ candidate, score candidate ≤ maximum) :
    Tendsto
        (fun time ↦
          ∑ candidate ∈ Finset.univ.filter target,
            baseMass candidate *
              Real.exp (time * (score candidate - maximum)))
        atTop
        (nhds (paterTargetBestMass target baseMass score maximum)) := by
  classical
  have hsum := tendsto_finsetSum (Finset.univ.filter target)
    (fun candidate _ ↦
      pater_shifted_candidate_tendsto baseMass score maximum hupper candidate)
  have hlimit :
      (∑ candidate ∈ Finset.univ.filter target,
          if score candidate = maximum then baseMass candidate else 0) =
        paterTargetBestMass target baseMass score maximum := by
    unfold paterTargetBestMass
    conv_rhs =>
      rw [← Finset.filter_filter]
      rw [Finset.sum_filter]
  rw [← hlimit]
  exact hsum

theorem pater_shifted_global_mass_tendsto
    (baseMass score : Candidate → ℝ) (maximum : ℝ)
    (hupper : ∀ candidate, score candidate ≤ maximum) :
    Tendsto
        (fun time ↦
          ∑ candidate,
            baseMass candidate *
              Real.exp (time * (score candidate - maximum)))
        atTop
        (nhds (paterGlobalBestMass baseMass score maximum)) := by
  classical
  have hsum := tendsto_finsetSum Finset.univ
    (fun candidate _ ↦
      pater_shifted_candidate_tendsto baseMass score maximum hupper candidate)
  have hlimit :
      (∑ candidate,
          if score candidate = maximum then baseMass candidate else 0) =
        paterGlobalBestMass baseMass score maximum := by
    unfold paterGlobalBestMass
    conv_rhs => rw [Finset.sum_filter]
  rw [← hlimit]
  exact hsum

theorem pater_global_best_mass_pos
    (baseMass score : Candidate → ℝ) (maximum : ℝ)
    (hbase : ∀ candidate, 0 < baseMass candidate)
    (hattained : ∃ candidate, score candidate = maximum) :
    0 < paterGlobalBestMass baseMass score maximum := by
  classical
  obtain ⟨candidate, hbest⟩ := hattained
  unfold paterGlobalBestMass
  apply Finset.sum_pos'
  · intro index hindex
    exact (hbase index).le
  · exact ⟨candidate, by simp [hbest], hbase candidate⟩

/-- A common score shift is an evaluator gauge: it leaves the normalized
overt-fibre law unchanged at every finite scale. -/
theorem pater_common_scaling_eq_shifted
    (target : Candidate → Prop) (baseMass score : Candidate → ℝ)
    (maximum time : ℝ) :
    paterCommonScalingProbability target baseMass score time =
      paterShiftedScalingProbability target baseMass score maximum time := by
  classical
  have htarget :
      (∑ candidate ∈ Finset.univ.filter target,
          baseMass candidate * Real.exp (time * score candidate)) =
        Real.exp (time * maximum) *
          (∑ candidate ∈ Finset.univ.filter target,
            baseMass candidate *
              Real.exp (time * (score candidate - maximum))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro candidate _
    calc
      baseMass candidate * Real.exp (time * score candidate) =
          baseMass candidate *
            (Real.exp (time * maximum) *
              Real.exp (time * (score candidate - maximum))) := by
                rw [← Real.exp_add]
                congr 2
                ring
      _ = Real.exp (time * maximum) *
          (baseMass candidate *
            Real.exp (time * (score candidate - maximum))) := by ring
  have hglobal :
      (∑ candidate,
          baseMass candidate * Real.exp (time * score candidate)) =
        Real.exp (time * maximum) *
          (∑ candidate,
            baseMass candidate *
              Real.exp (time * (score candidate - maximum))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro candidate _
    calc
      baseMass candidate * Real.exp (time * score candidate) =
          baseMass candidate *
            (Real.exp (time * maximum) *
              Real.exp (time * (score candidate - maximum))) := by
                rw [← Real.exp_add]
                congr 2
                ring
      _ = Real.exp (time * maximum) *
          (baseMass candidate *
            Real.exp (time * (score candidate - maximum))) := by ring
  unfold paterCommonScalingProbability paterShiftedScalingProbability
  rw [htarget, hglobal]
  exact mul_div_mul_left _ _ (Real.exp_ne_zero _)

/-- Exact finite-support max-fibre limit.  The limiting probability is the
target's base mass on the global-best hidden set divided by the total base
mass on that set. -/
theorem pater_common_scaling_tendsto_best_mass_ratio
    (target : Candidate → Prop) (baseMass score : Candidate → ℝ)
    (maximum : ℝ)
    (hbase : ∀ candidate, 0 < baseMass candidate)
    (hupper : ∀ candidate, score candidate ≤ maximum)
    (hattained : ∃ candidate, score candidate = maximum) :
    Tendsto
      (paterCommonScalingProbability target baseMass score)
      atTop
      (nhds
        (paterTargetBestMass target baseMass score maximum /
          paterGlobalBestMass baseMass score maximum)) := by
  have hbestMass : 0 < paterGlobalBestMass baseMass score maximum :=
    pater_global_best_mass_pos baseMass score maximum hbase hattained
  have hshifted : Tendsto
      (paterShiftedScalingProbability target baseMass score maximum)
      atTop
      (nhds
        (paterTargetBestMass target baseMass score maximum /
          paterGlobalBestMass baseMass score maximum)) := by
    exact (pater_shifted_target_mass_tendsto
      target baseMass score maximum hupper).div
        (pater_shifted_global_mass_tendsto
          baseMass score maximum hupper)
        hbestMass.ne'
  have hequality :
      paterCommonScalingProbability target baseMass score =
        paterShiftedScalingProbability target baseMass score maximum := by
    funext time
    exact pater_common_scaling_eq_shifted
      target baseMass score maximum time
  rw [hequality]
  exact hshifted

/-- The limiting probability is one exactly when every globally best hidden
candidate belongs to the target overt fibre. -/
theorem pater_best_mass_ratio_eq_one_iff
    (target : Candidate → Prop) (baseMass score : Candidate → ℝ)
    (maximum : ℝ)
    (hbase : ∀ candidate, 0 < baseMass candidate)
    (hattained : ∃ candidate, score candidate = maximum) :
    paterTargetBestMass target baseMass score maximum /
        paterGlobalBestMass baseMass score maximum = 1 ↔
      ∀ candidate, score candidate = maximum → target candidate := by
  classical
  have hbestMass : 0 < paterGlobalBestMass baseMass score maximum :=
    pater_global_best_mass_pos baseMass score maximum hbase hattained
  constructor
  · intro hratio candidate hbest
    by_contra hnontarget
    have hsubset :
        Finset.univ.filter
            (fun c ↦ target c ∧ score c = maximum) ⊆
          Finset.univ.filter (fun c ↦ score c = maximum) := by
      intro c hc
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ c, (Finset.mem_filter.mp hc).2.2⟩
    have hcandidateBest :
        candidate ∈ Finset.univ.filter (fun c ↦ score c = maximum) := by
      simp [hbest]
    have hcandidateNotTarget :
        candidate ∉ Finset.univ.filter
          (fun c ↦ target c ∧ score c = maximum) := by
      simp [hnontarget]
    have hstrict :
        paterTargetBestMass target baseMass score maximum <
          paterGlobalBestMass baseMass score maximum := by
      unfold paterTargetBestMass paterGlobalBestMass
      exact Finset.sum_lt_sum_of_subset hsubset hcandidateBest
        hcandidateNotTarget (hbase candidate)
        (fun c _ _ ↦ (hbase c).le)
    have hequal :
        paterTargetBestMass target baseMass score maximum =
          paterGlobalBestMass baseMass score maximum :=
      (div_eq_one_iff_eq hbestMass.ne').1 hratio
    exact (ne_of_lt hstrict) hequal
  · intro hall
    have hsets :
        Finset.univ.filter
            (fun c ↦ target c ∧ score c = maximum) =
          Finset.univ.filter (fun c ↦ score c = maximum) := by
      ext candidate
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact fun h ↦ h.2
      · exact fun h ↦ ⟨hall candidate h, h⟩
    unfold paterTargetBestMass paterGlobalBestMass
    rw [hsets]
    exact div_self hbestMass.ne'

/-- Complete promoted scaling criterion: under fixed finite positive support,
common scaling sends the target overt probability to one exactly when every
global hidden maximizer lies in the target fibre. -/
theorem pater_common_scaling_tendsto_one_iff
    (target : Candidate → Prop) (baseMass score : Candidate → ℝ)
    (maximum : ℝ)
    (hbase : ∀ candidate, 0 < baseMass candidate)
    (hupper : ∀ candidate, score candidate ≤ maximum)
    (hattained : ∃ candidate, score candidate = maximum) :
    Tendsto
        (paterCommonScalingProbability target baseMass score)
        atTop (nhds 1) ↔
      ∀ candidate, score candidate = maximum → target candidate := by
  have hlimit := pater_common_scaling_tendsto_best_mass_ratio
    target baseMass score maximum hbase hupper hattained
  have hcriterion := pater_best_mass_ratio_eq_one_iff
    target baseMass score maximum hbase hattained
  constructor
  · intro hone
    apply hcriterion.1
    exact tendsto_nhds_unique hlimit hone
  · intro hall
    have hequal := hcriterion.2 hall
    simpa [hequal] using hlimit

end PaterFiniteSupport

/-- Four hidden parses split symmetrically across two overt fibres. -/
def paterSymmetricFourParseProbability (time weight : ℝ) : ℝ :=
  (1 + Real.exp (-time * weight)) /
    (2 + 2 * Real.exp (-time * weight))

theorem pater_symmetric_four_parse_probability_eq_half
    (time weight : ℝ) :
    paterSymmetricFourParseProbability time weight = 1 / 2 := by
  have hpositive : 0 < Real.exp (-time * weight) := Real.exp_pos _
  have hdenominator : 2 + 2 * Real.exp (-time * weight) ≠ 0 := by
    positivity
  unfold paterSymmetricFourParseProbability
  field_simp [hdenominator]

/-- Three correct hidden parses at Harmony zero against one wrong hidden parse
at Harmony one. -/
def paterMultiplicityReversalProbability (time : ℝ) : ℝ :=
  3 / (3 + Real.exp time)

/-- An exact positive-scale starting grammar satisfies the source's strict
overt-fibre success comparison even though further common scaling follows the
same response curve toward zero. -/
theorem pater_multiplicity_reversal_at_log_two :
    paterMultiplicityReversalProbability (Real.log 2) = 3 / 5 ∧
      (1 : ℝ) / 2 < paterMultiplicityReversalProbability (Real.log 2) := by
  rw [paterMultiplicityReversalProbability,
    Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  norm_num

theorem pater_multiplicity_reversal_at_log_three :
    paterMultiplicityReversalProbability (Real.log 3) = 1 / 2 := by
  rw [paterMultiplicityReversalProbability, Real.exp_log (by norm_num : (0 : ℝ) < 3)]
  norm_num

theorem pater_multiplicity_reversal_above_half_iff (time : ℝ) :
    1 / 2 < paterMultiplicityReversalProbability time ↔
      time < Real.log 3 := by
  have hden : 0 < 3 + Real.exp time := by positivity
  unfold paterMultiplicityReversalProbability
  constructor
  · intro h
    have hcross := (lt_div_iff₀ hden).1 h
    apply (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)).2
    linarith
  · intro h
    apply (lt_div_iff₀ hden).2
    have hexponential :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)).1 h
    linarith

theorem pater_multiplicity_reversal_tendsto_zero :
    Tendsto paterMultiplicityReversalProbability atTop (nhds 0) := by
  have hdenominator : Tendsto (fun time : ℝ ↦ 3 + Real.exp time) atTop atTop :=
    tendsto_const_nhds.add_atTop Real.tendsto_exp_atTop
  change Tendsto (fun time : ℝ ↦ 3 / (3 + Real.exp time)) atTop (nhds 0)
  exact hdenominator.const_div_atTop (3 : ℝ)

/-- Algebraic finite-support envelope behind the explicit exponential bound:
the wrong-to-target probability ratio is bounded by its unnormalized ratio.
-/
theorem pater_finite_exponential_error_envelope
    {targetMass wrongMass time gap : ℝ}
    (htarget : 0 < targetMass) (hwrong : 0 ≤ wrongMass) :
    wrongMass * Real.exp (-time * gap) /
        (targetMass + wrongMass * Real.exp (-time * gap)) ≤
      (wrongMass / targetMass) * Real.exp (-time * gap) := by
  have hexp : 0 < Real.exp (-time * gap) := Real.exp_pos _
  have hterm : 0 ≤ wrongMass * Real.exp (-time * gap) :=
    mul_nonneg hwrong hexp.le
  have hden : 0 < targetMass + wrongMass * Real.exp (-time * gap) :=
    add_pos_of_pos_of_nonneg htarget hterm
  have hrhs :
      (wrongMass / targetMass) * Real.exp (-time * gap) =
        (wrongMass * Real.exp (-time * gap)) / targetMass := by
    field_simp [htarget.ne']
  rw [hrhs]
  apply (div_le_div_iff₀ hden htarget).2
  exact mul_le_mul_of_nonneg_left
    (le_add_of_nonneg_right hterm) hterm

/-! ## Cabrera's two normalization consumers -/

/-- One-shot lexical probability on violation counts `0,...,K`.  The
`mparse` argument is retained explicitly to state its exact deletion by this
consumer. -/
def cabreraOneShotProbability (K n : ℕ) (markedness _mparse : ℝ) : ℝ :=
  Real.exp (-markedness * n) /
    ∑ j ∈ Finset.range (K + 1), Real.exp (-markedness * j)

theorem cabrera_one_shot_deletes_mparse
    (K n : ℕ) (markedness leftMparse rightMparse : ℝ) :
    cabreraOneShotProbability K n markedness leftMparse =
      cabreraOneShotProbability K n markedness rightMparse := rfl

theorem cabrera_one_shot_derivative_mparse_zero
    (K n : ℕ) (markedness mparse : ℝ) :
    HasDerivAt
      (fun p ↦ cabreraOneShotProbability K n markedness p) 0 mparse := by
  simpa only [cabreraOneShotProbability] using
    hasDerivAt_const mparse
      (Real.exp (-markedness * n) /
        ∑ j ∈ Finset.range (K + 1), Real.exp (-markedness * j))

theorem cabrera_one_shot_normalizer_pos (K : ℕ) (markedness : ℝ) :
    0 < ∑ j ∈ Finset.range (K + 1),
      Real.exp (-markedness * j) := by
  apply Finset.sum_pos
  · intro j hj
    exact Real.exp_pos _
  · simp

/-- The algebraic adjacent-ratio identity for the one-shot probability
formula.  The following theorem adds the source-support premise needed to use
the identity as a licensed finite-candidate comparison. -/
theorem cabrera_one_shot_adjacent_ratio
    (K n : ℕ) (markedness mparse : ℝ) :
    cabreraOneShotProbability K (n + 1) markedness mparse /
        cabreraOneShotProbability K n markedness mparse =
      Real.exp (-markedness) := by
  have hnormalizer :
      (∑ j ∈ Finset.range (K + 1),
        Real.exp (-markedness * j)) ≠ 0 :=
    (cabrera_one_shot_normalizer_pos K markedness).ne'
  have hnumerator : Real.exp (-markedness * n) ≠ 0 := Real.exp_ne_zero _
  unfold cabreraOneShotProbability
  field_simp [hnormalizer, hnumerator]
  rw [← Real.exp_add]
  congr 1
  push_cast
  ring

/-- Source-licensed adjacent ratio: the support premise is used to prove
that the successor count is inside `0,...,K`, while the ratio itself follows
from the exact one-shot law. -/
theorem cabrera_one_shot_supported_adjacent_ratio
    {K n : ℕ} (markedness mparse : ℝ) (hmember : n < K) :
    n + 1 ≤ K ∧
      cabreraOneShotProbability K (n + 1) markedness mparse /
          cabreraOneShotProbability K n markedness mparse =
        Real.exp (-markedness) := by
  exact ⟨Nat.succ_le_iff.mpr hmember,
    cabrera_one_shot_adjacent_ratio K n markedness mparse⟩

theorem cabrera_one_shot_markedness_recovery
    (K n : ℕ) (markedness mparse : ℝ) :
    -Real.log
        (cabreraOneShotProbability K (n + 1) markedness mparse /
          cabreraOneShotProbability K n markedness mparse) = markedness := by
  rw [cabrera_one_shot_adjacent_ratio, Real.log_exp]
  ring

/-- Structural-output probability in one structural-versus-null binary
competition. -/
def cabreraBinaryResponse (n : ℕ) (markedness mparse : ℝ) : ℝ :=
  1 / (1 + Real.exp (markedness * n - mparse))

/-- Exact algebraic factorization of the second difference of a logistic
geometric sequence. -/
theorem cabrera_geometric_logistic_second_difference
    {activity ratio : ℝ} (hactivity : 0 < activity)
    (hratio : 0 < ratio) :
    1 / (1 + ratio ^ 2 * activity) -
          2 / (1 + ratio * activity) + 1 / (1 + activity) =
      activity * (ratio - 1) ^ 2 * (ratio * activity - 1) /
        ((1 + activity) * (1 + ratio * activity) *
          (1 + ratio ^ 2 * activity)) := by
  have h₀ : 1 + activity ≠ 0 := by positivity
  have h₁ : 1 + ratio * activity ≠ 0 := by positivity
  have h₂ : 1 + ratio ^ 2 * activity ≠ 0 := by positivity
  field_simp [h₀, h₁, h₂]
  ring

theorem cabrera_binary_response_succ
    (n : ℕ) (markedness mparse : ℝ) :
    cabreraBinaryResponse (n + 1) markedness mparse =
      1 / (1 + Real.exp markedness *
        Real.exp (markedness * n - mparse)) := by
  unfold cabreraBinaryResponse
  congr 2
  rw [← Real.exp_add]
  congr 1
  push_cast
  ring

theorem cabrera_binary_response_add_two
    (n : ℕ) (markedness mparse : ℝ) :
    cabreraBinaryResponse (n + 2) markedness mparse =
      1 / (1 + (Real.exp markedness) ^ 2 *
        Real.exp (markedness * n - mparse)) := by
  unfold cabreraBinaryResponse
  congr 2
  rw [pow_two, ← Real.exp_add, ← Real.exp_add]
  congr 1
  push_cast
  ring

/-- Exact curvature factorization for the binary response. -/
theorem cabrera_binary_second_difference_factorization
    (n : ℕ) (markedness mparse : ℝ) :
    cabreraBinaryResponse (n + 2) markedness mparse -
          2 * cabreraBinaryResponse (n + 1) markedness mparse +
          cabreraBinaryResponse n markedness mparse =
      let activity := Real.exp (markedness * n - mparse)
      let ratio := Real.exp markedness
      activity * (ratio - 1) ^ 2 * (ratio * activity - 1) /
        ((1 + activity) * (1 + ratio * activity) *
          (1 + ratio ^ 2 * activity)) := by
  rw [cabrera_binary_response_add_two, cabrera_binary_response_succ]
  unfold cabreraBinaryResponse
  dsimp only
  simpa only [div_eq_mul_inv, one_mul] using
    (cabrera_geometric_logistic_second_difference
      (Real.exp_pos (markedness * n - mparse)) (Real.exp_pos markedness))

theorem cabrera_binary_curvature_positive
    (n : ℕ) {markedness mparse : ℝ}
    (hmarkedness : 0 < markedness)
    (hboundary : mparse < markedness * (n + 1)) :
    0 < cabreraBinaryResponse (n + 2) markedness mparse -
          2 * cabreraBinaryResponse (n + 1) markedness mparse +
          cabreraBinaryResponse n markedness mparse := by
  rw [cabrera_binary_second_difference_factorization]
  dsimp only
  have hactivity : 0 < Real.exp (markedness * n - mparse) := Real.exp_pos _
  have hratio : 1 < Real.exp markedness := (Real.one_lt_exp_iff).2 hmarkedness
  have hlast : 1 < Real.exp markedness *
      Real.exp (markedness * n - mparse) := by
    rw [← Real.exp_add, Real.one_lt_exp_iff]
    linarith
  positivity

theorem cabrera_binary_curvature_zero
    (n : ℕ) {markedness mparse : ℝ}
    (hboundary : mparse = markedness * (n + 1)) :
    cabreraBinaryResponse (n + 2) markedness mparse -
          2 * cabreraBinaryResponse (n + 1) markedness mparse +
          cabreraBinaryResponse n markedness mparse = 0 := by
  rw [cabrera_binary_second_difference_factorization]
  dsimp only
  have hlast : Real.exp markedness *
      Real.exp (markedness * n - mparse) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 2
    linarith
  rw [hlast]
  norm_num

theorem cabrera_binary_curvature_negative
    (n : ℕ) {markedness mparse : ℝ}
    (hmarkedness : 0 < markedness)
    (hboundary : markedness * (n + 1) < mparse) :
    cabreraBinaryResponse (n + 2) markedness mparse -
          2 * cabreraBinaryResponse (n + 1) markedness mparse +
          cabreraBinaryResponse n markedness mparse < 0 := by
  rw [cabrera_binary_second_difference_factorization]
  dsimp only
  have hactivity : 0 < Real.exp (markedness * n - mparse) := Real.exp_pos _
  have hratio : 1 < Real.exp markedness := (Real.one_lt_exp_iff).2 hmarkedness
  have hlast : Real.exp markedness *
      Real.exp (markedness * n - mparse) < 1 := by
    rw [← Real.exp_add, Real.exp_lt_one_iff]
    linarith
  have hprefix : 0 <
      Real.exp (markedness * n - mparse) *
        (Real.exp markedness - 1) ^ 2 := by positivity
  have hdenominator : 0 <
      (1 + Real.exp (markedness * n - mparse)) *
        (1 + Real.exp markedness * Real.exp (markedness * n - mparse)) *
        (1 + (Real.exp markedness) ^ 2 *
          Real.exp (markedness * n - mparse)) := by positivity
  exact div_neg_of_neg_of_pos
    (mul_neg_of_pos_of_neg hprefix (sub_neg.mpr hlast))
    hdenominator

/-- The exact odds recover the affine binary score. -/
theorem cabrera_binary_odds
    (n : ℕ) (markedness mparse : ℝ) :
    cabreraBinaryResponse n markedness mparse /
        (1 - cabreraBinaryResponse n markedness mparse) =
      Real.exp (mparse - markedness * n) := by
  unfold cabreraBinaryResponse
  have hpositive : 0 < Real.exp (markedness * n - mparse) := Real.exp_pos _
  have hden : 1 + Real.exp (markedness * n - mparse) ≠ 0 := by positivity
  field_simp [hden, hpositive.ne']
  ring_nf
  rw [← Real.exp_add]
  rw [show markedness * (n : ℝ) - mparse +
      (-(markedness * (n : ℝ)) + mparse) = 0 by ring]
  exact Real.exp_zero.symm

theorem cabrera_binary_logit
    (n : ℕ) (markedness mparse : ℝ) :
    Real.log
        (cabreraBinaryResponse n markedness mparse /
          (1 - cabreraBinaryResponse n markedness mparse)) =
      mparse - markedness * n := by
  rw [cabrera_binary_odds, Real.log_exp]

theorem cabrera_mparse_recovery
    (n : ℕ) (markedness mparse : ℝ) :
    markedness * n +
        Real.log
          (cabreraBinaryResponse n markedness mparse /
            (1 - cabreraBinaryResponse n markedness mparse)) =
      mparse := by
  rw [cabrera_binary_logit]
  ring

end

end PhonologicalCalculus.Application
