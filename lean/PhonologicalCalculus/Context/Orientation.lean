import PhonologicalCalculus.Context.TwoTrigger
import PhonologicalCalculus.ContinuousHG.Core
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Directional and absolute-edge one-trigger evaluation

Running-minimum normalization removes every upward excursion.  This module
shows that it weakly lowers both the directional and the absolute-edge path
objectives and lowers either objective strictly when markedness has positive
weight and the profile changes.  Since the objectives agree on a normalized
profile, their complete sets of one-trigger minimizers coincide.

The final section checks the registered finite order reversal and the exact
opposite-trigger support probes.
-/

namespace PhonologicalCalculus.Context

open PhonologicalCalculus.ContinuousHG

/-- Absolute change across one edge. -/
def absoluteDrop (previous next : ℝ) : ℝ :=
  |previous - next|

def absoluteDropsFrom (previous : ℝ) : List ℝ → List ℝ
  | [] => []
  | x :: xs => absoluteDrop previous x :: absoluteDropsFrom x xs

def absoluteDrops (profile : List ℝ) : List ℝ :=
  absoluteDropsFrom 1 profile

/-- Absolute-edge harmony plus positive linear markedness. -/
def absolutePathHarmony (penalty : ℝ → ℝ) (h m : ℝ)
    (profile : List ℝ) : ℝ :=
  h * ((absoluteDrops profile).map penalty).sum + m * profile.sum

theorem directionalDrop_le_absoluteDrop (previous next : ℝ) :
    directionalDrop previous next ≤ absoluteDrop previous next := by
  unfold directionalDrop absoluteDrop
  exact max_le (le_abs_self _) (abs_nonneg _)

theorem absoluteDropsFrom_nonnegative (previous : ℝ) (profile : List ℝ) :
    ∀ drop ∈ absoluteDropsFrom previous profile, 0 ≤ drop := by
  induction profile generalizing previous with
  | nil => simp [absoluteDropsFrom]
  | cons x xs ih =>
      intro drop hdrop
      simp only [absoluteDropsFrom, List.mem_cons] at hdrop
      rcases hdrop with rfl | hdrop
      · exact abs_nonneg _
      · exact ih x drop hdrop

theorem absoluteDropsFrom_runningMinimumFrom_eq_directional
    (previous : ℝ) (profile : List ℝ) :
    absoluteDropsFrom previous (runningMinimumFrom previous profile) =
      directionalDropsFrom previous (runningMinimumFrom previous profile) := by
  induction profile generalizing previous with
  | nil => rfl
  | cons x xs ih =>
      simp only [runningMinimumFrom, absoluteDropsFrom, directionalDropsFrom]
      have hsub : 0 ≤ previous - min previous x :=
        sub_nonneg.mpr (min_le_left _ _)
      rw [ih (min previous x)]
      simp [absoluteDrop, directionalDrop, abs_of_nonneg hsub, hsub]

theorem runningMinimumFrom_drops_le_absolute {running previous : ℝ}
    (hrun : running ≤ previous) (profile : List ℝ) :
    List.Forall₂ (· ≤ ·)
      (directionalDropsFrom running (runningMinimumFrom running profile))
      (absoluteDropsFrom previous profile) := by
  induction profile generalizing running previous with
  | nil => exact .nil
  | cons x xs ih =>
      simp only [runningMinimumFrom, directionalDropsFrom, absoluteDropsFrom]
      exact .cons
        ((directionalDrop_running_min_le hrun).trans
          (directionalDrop_le_absoluteDrop previous x))
        (ih (min_le_right running x))

private theorem penalty_sum_le_of_forall₂
    (penalty : ℝ → ℝ)
    (hmono : ∀ ⦃a b : ℝ⦄, 0 ≤ a → a ≤ b → penalty a ≤ penalty b)
    {xs ys : List ℝ} (hxy : List.Forall₂ (· ≤ ·) xs ys)
    (hx : ∀ x ∈ xs, 0 ≤ x) :
    (xs.map penalty).sum ≤ (ys.map penalty).sum := by
  induction hxy with
  | nil => simp
  | @cons x y xs ys hhead htail ih =>
      simp only [List.mem_cons, forall_eq_or_imp] at hx
      simp only [List.map_cons, List.sum_cons]
      exact add_le_add (hmono hx.1 hhead) (ih hx.2)

theorem runningMinimum_absolute_penalty_le
    (penalty : ℝ → ℝ)
    (hmono : ∀ ⦃a b : ℝ⦄, 0 ≤ a → a ≤ b → penalty a ≤ penalty b)
    (profile : List ℝ) :
    ((absoluteDrops (runningMinimum profile)).map penalty).sum ≤
      ((absoluteDrops profile).map penalty).sum := by
  have hdrops := runningMinimumFrom_drops_le_absolute
    (le_refl (1 : ℝ)) profile
  have heq :
      absoluteDrops (runningMinimum profile) =
        directionalDrops (runningMinimum profile) := by
    exact absoluteDropsFrom_runningMinimumFrom_eq_directional 1 profile
  rw [heq]
  apply penalty_sum_le_of_forall₂ penalty hmono hdrops
  intro drop hdrop
  exact directionalDropsFrom_nonnegative 1 (runningMinimumFrom 1 profile)
    drop hdrop

theorem absolutePathHarmony_runningMinimum_le
    (penalty : ℝ → ℝ)
    (hmono : ∀ ⦃a b : ℝ⦄, 0 ≤ a → a ≤ b → penalty a ≤ penalty b)
    {h m : ℝ} (hh : 0 ≤ h) (hm : 0 ≤ m) (profile : List ℝ) :
    absolutePathHarmony penalty h m (runningMinimum profile) ≤
      absolutePathHarmony penalty h m profile := by
  exact add_le_add
    (mul_le_mul_of_nonneg_left
      (runningMinimum_absolute_penalty_le penalty hmono profile) hh)
    (mul_le_mul_of_nonneg_left (runningMinimum_sum_le profile) hm)

theorem absolutePathHarmony_runningMinimum_lt_of_changed
    (penalty : ℝ → ℝ)
    (hmono : ∀ ⦃a b : ℝ⦄, 0 ≤ a → a ≤ b → penalty a ≤ penalty b)
    {h m : ℝ} (hh : 0 ≤ h) (hm : 0 < m) (profile : List ℝ)
    (hchanged : runningMinimum profile ≠ profile) :
    absolutePathHarmony penalty h m (runningMinimum profile) <
      absolutePathHarmony penalty h m profile := by
  exact add_lt_add_of_le_of_lt
    (mul_le_mul_of_nonneg_left
      (runningMinimum_absolute_penalty_le penalty hmono profile) hh)
    (mul_lt_mul_of_pos_left
      (runningMinimum_sum_strict_of_changed profile hchanged) hm)

theorem absoluteDrops_runningMinimum_eq_directionalDrops
    (profile : List ℝ) :
    absoluteDrops (runningMinimum profile) =
      directionalDrops (runningMinimum profile) := by
  exact absoluteDropsFrom_runningMinimumFrom_eq_directional 1 profile

theorem absolutePathHarmony_runningMinimum_eq_pathHarmony
    (penalty : ℝ → ℝ) (h m : ℝ) (profile : List ℝ) :
    absolutePathHarmony penalty h m (runningMinimum profile) =
      pathHarmony penalty h m (runningMinimum profile) := by
  simp [absolutePathHarmony, pathHarmony,
    absoluteDrops_runningMinimum_eq_directionalDrops]

/-- A complete one-trigger winner predicate over the declared finite-profile
candidate domain. -/
def IsGlobalWinner (energy : List ℝ → ℝ) (profile : List ℝ) : Prop :=
  ∀ candidate, energy profile ≤ energy candidate

/-- Directional and absolute-edge objectives have exactly the same complete
set of one-trigger winners whenever the edge penalty is monotone on
nonnegative changes and markedness has positive weight. -/
theorem oneTrigger_globalWinner_iff
    (penalty : ℝ → ℝ)
    (hmono : ∀ ⦃a b : ℝ⦄, 0 ≤ a → a ≤ b → penalty a ≤ penalty b)
    {h m : ℝ} (hh : 0 ≤ h) (hm : 0 < m) (profile : List ℝ) :
    IsGlobalWinner (pathHarmony penalty h m) profile ↔
      IsGlobalWinner (absolutePathHarmony penalty h m) profile := by
  constructor
  · intro hwin candidate
    have hfixed : runningMinimum profile = profile := by
      by_contra hchanged
      have hstrict := pathHarmony_runningMinimum_lt_of_changed penalty hmono
        hh hm profile hchanged
      exact (not_lt_of_ge (hwin (runningMinimum profile))) hstrict
    calc
      absolutePathHarmony penalty h m profile =
          pathHarmony penalty h m profile := by
            rw [← hfixed]
            exact absolutePathHarmony_runningMinimum_eq_pathHarmony
              penalty h m profile
      _ ≤ pathHarmony penalty h m (runningMinimum candidate) :=
        hwin (runningMinimum candidate)
      _ = absolutePathHarmony penalty h m (runningMinimum candidate) :=
        (absolutePathHarmony_runningMinimum_eq_pathHarmony
          penalty h m candidate).symm
      _ ≤ absolutePathHarmony penalty h m candidate :=
        absolutePathHarmony_runningMinimum_le penalty hmono hh hm.le candidate
  · intro hwin candidate
    have hfixed : runningMinimum profile = profile := by
      by_contra hchanged
      have hstrict := absolutePathHarmony_runningMinimum_lt_of_changed
        penalty hmono hh hm profile hchanged
      exact (not_lt_of_ge (hwin (runningMinimum profile))) hstrict
    calc
      pathHarmony penalty h m profile =
          absolutePathHarmony penalty h m profile := by
            rw [← hfixed]
            exact (absolutePathHarmony_runningMinimum_eq_pathHarmony
              penalty h m profile).symm
      _ ≤ absolutePathHarmony penalty h m (runningMinimum candidate) :=
        hwin (runningMinimum candidate)
      _ = pathHarmony penalty h m (runningMinimum candidate) :=
        absolutePathHarmony_runningMinimum_eq_pathHarmony penalty h m candidate
      _ ≤ pathHarmony penalty h m candidate :=
        pathHarmony_runningMinimum_le penalty hmono hh hm.le candidate

/-- Positive real-power edge penalty. -/
noncomputable def powerPenalty (p drop : ℝ) : ℝ :=
  Real.rpow drop p

theorem powerPenalty_monotone_on_nonnegative {p a b : ℝ}
    (hp : 0 < p) (ha : 0 ≤ a) (hab : a ≤ b) :
    powerPenalty p a ≤ powerPenalty p b := by
  exact Real.rpow_le_rpow ha hab hp.le

/-- The all-horizon, all-candidate one-trigger winner equivalence for every
registered exponent `p > 1`. -/
theorem oneTrigger_power_globalWinner_iff {p h m : ℝ}
    (hp : 1 < p) (hh : 0 ≤ h) (hm : 0 < m) (profile : List ℝ) :
    IsGlobalWinner (pathHarmony (powerPenalty p) h m) profile ↔
      IsGlobalWinner (absolutePathHarmony (powerPenalty p) h m) profile :=
  oneTrigger_globalWinner_iff (powerPenalty p)
    (fun {_a _b} ha hab =>
      powerPenalty_monotone_on_nonnegative (lt_trans zero_lt_one hp) ha hab)
    hh hm profile

/-- The two registered candidates for the complete-order witness. -/
noncomputable def orderCandidateA : List ℝ := [0, 1 / 2]
noncomputable def orderCandidateB : List ℝ := [1, 0]

/-- `CTX-C2.ORDER.01`: directional and absolute evaluation rank the two
registered candidates in opposite orders. -/
theorem ctx_c2_order_01 :
    [(pathHarmony quadraticPenalty 3 1 orderCandidateA,
        pathHarmony quadraticPenalty 3 1 orderCandidateB),
      (absolutePathHarmony quadraticPenalty 3 1 orderCandidateA,
        absolutePathHarmony quadraticPenalty 3 1 orderCandidateB)] =
        [(7 / 2, 4), (17 / 4, 4)] ∧
      pathHarmony quadraticPenalty 3 1 orderCandidateA <
        pathHarmony quadraticPenalty 3 1 orderCandidateB ∧
      absolutePathHarmony quadraticPenalty 3 1 orderCandidateB <
        absolutePathHarmony quadraticPenalty 3 1 orderCandidateA := by
  norm_num [orderCandidateA, orderCandidateB, pathHarmony,
    absolutePathHarmony, absoluteDrops, absoluteDropsFrom, absoluteDrop,
    directionalDrops, directionalDropsFrom, directionalDrop, quadraticPenalty]

/-- Exact profiles in the registered shortest-separator fixture. -/
noncomputable def forwardSeparatorProfile : List ℝ := [1 / 6, 0]
noncomputable def absoluteSeparatorProfile : List ℝ := [1 / 3, 1 / 3]

/-- `CTX-C2.SHORTEST.02`: the forward profile reaches zero while the
absolute-edge profile remains positive at the registered `K = 2` probe. -/
theorem ctx_c2_shortest_02 :
    [forwardSeparatorProfile, absoluteSeparatorProfile] =
        [[1 / 6, 0], [1 / 3, 1 / 3]] ∧
      0 ∈ forwardSeparatorProfile ∧
      (∀ x ∈ absoluteSeparatorProfile, 0 < x) := by
  norm_num [forwardSeparatorProfile, absoluteSeparatorProfile]

/-- The maximum positive opposite-trigger gap of the three support classes. -/
inductive EdgeSupportClass where
  | forward
  | absoluteLowPhase
  | absoluteHighPhase
  deriving DecidableEq

def maximumPositiveGap (K : ℕ) : EdgeSupportClass → ℕ
  | .forward => K
  | .absoluteLowPhase => 2 * K - 1
  | .absoluteHighPhase => 2 * K

def positiveAtGap (K L : ℕ) (kind : EdgeSupportClass) : Bool :=
  decide (L ≤ maximumPositiveGap K kind)

def twoProbeCode (K : ℕ) (kind : EdgeSupportClass) : Bool × Bool :=
  (positiveAtGap K (K + 1) kind, positiveAtGap K (2 * K) kind)

theorem no_shorter_binary_separator {K L : ℕ} (hK : 2 ≤ K)
    (hL : L < K + 1) :
    positiveAtGap K L .forward = true ∧
      positiveAtGap K L .absoluteLowPhase = true ∧
      positiveAtGap K L .absoluteHighPhase = true := by
  simp [positiveAtGap, maximumPositiveGap]
  omega

theorem opposite_trigger_separates_at_K_add_one {K : ℕ} (hK : 2 ≤ K) :
    positiveAtGap K (K + 1) .forward = false ∧
      positiveAtGap K (K + 1) .absoluteLowPhase = true ∧
      positiveAtGap K (K + 1) .absoluteHighPhase = true := by
  simp [positiveAtGap, maximumPositiveGap]
  omega

/-- The two probes at `K+1` and `2K` give the three exact diagnostic codes. -/
theorem three_support_codes {K : ℕ} (hK : 2 ≤ K) :
    twoProbeCode K .forward = (false, false) ∧
      twoProbeCode K .absoluteLowPhase = (true, false) ∧
      twoProbeCode K .absoluteHighPhase = (true, true) := by
  simp [twoProbeCode, positiveAtGap, maximumPositiveGap]
  omega

end PhonologicalCalculus.Context
