import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Finite directional profiles and monotone normalization

This module gives an exact finite-list model of the normal-form reduction used
for directional continuous Harmonic Grammar.  A profile lists the follower
activities; the trigger value is supplied separately.  The running-minimum
map removes every upward excursion.  Its directional drops cannot increase,
and its coordinate sum cannot increase.  These facts yield a general energy
comparison for every penalty that is monotone on nonnegative drops.

The second part identifies nonincreasing nonnegative profiles with a solid
simplex of nonnegative decreases.  The correspondence does not assume a
terminal zero.
-/

namespace PhonologicalCalculus.ContinuousHG

/-- Running minima of a finite profile, beginning from a declared preceding
activity. -/
def runningMinimumFrom (previous : ℝ) : List ℝ → List ℝ
  | [] => []
  | x :: xs =>
      let y := min previous x
      y :: runningMinimumFrom y xs

/-- Running-minimum normalization for a profile whose trigger has activity
one. -/
def runningMinimum (profile : List ℝ) : List ℝ :=
  runningMinimumFrom 1 profile

/-- The positive directional drop from one site to the next. -/
def directionalDrop (previous next : ℝ) : ℝ :=
  max (previous - next) 0

/-- Directional drops along a finite profile. -/
def directionalDropsFrom (previous : ℝ) : List ℝ → List ℝ
  | [] => []
  | x :: xs => directionalDrop previous x :: directionalDropsFrom x xs

/-- Directional drops when the trigger activity is one. -/
def directionalDrops (profile : List ℝ) : List ℝ :=
  directionalDropsFrom 1 profile

/-- Directional harmony plus positive linear markedness. -/
def pathHarmony (penalty : ℝ → ℝ) (h m : ℝ)
    (profile : List ℝ) : ℝ :=
  h * ((directionalDrops profile).map penalty).sum + m * profile.sum

theorem directionalDrop_nonnegative (previous next : ℝ) :
    0 ≤ directionalDrop previous next := by
  exact le_max_right _ _

theorem directionalDrop_running_min_le {running previous next : ℝ}
    (hrun : running ≤ previous) :
    directionalDrop running (min running next) ≤
      directionalDrop previous next := by
  rcases le_total running next with hle | hle
  · simp [directionalDrop, min_eq_left hle]
  · have hsub : running - next ≤ previous - next :=
      sub_le_sub_right hrun next
    simpa [directionalDrop, min_eq_right hle] using
      max_le_max hsub (le_refl (0 : ℝ))

theorem runningMinimumFrom_coordinatewise_le (previous : ℝ)
    (profile : List ℝ) :
    List.Forall₂ (· ≤ ·) (runningMinimumFrom previous profile) profile := by
  induction profile generalizing previous with
  | nil => exact .nil
  | cons x xs ih =>
      simp only [runningMinimumFrom]
      exact .cons (min_le_right previous x) (ih (min previous x))

theorem runningMinimumFrom_drops_le {running previous : ℝ}
    (hrun : running ≤ previous) (profile : List ℝ) :
    List.Forall₂ (· ≤ ·)
      (directionalDropsFrom running (runningMinimumFrom running profile))
      (directionalDropsFrom previous profile) := by
  induction profile generalizing running previous with
  | nil => exact .nil
  | cons x xs ih =>
      simp only [runningMinimumFrom, directionalDropsFrom]
      exact .cons (directionalDrop_running_min_le hrun)
        (ih (min_le_right running x))

theorem directionalDropsFrom_nonnegative (previous : ℝ)
    (profile : List ℝ) :
    ∀ drop ∈ directionalDropsFrom previous profile, 0 ≤ drop := by
  induction profile generalizing previous with
  | nil => simp [directionalDropsFrom]
  | cons x xs ih =>
      intro drop hdrop
      simp only [directionalDropsFrom, List.mem_cons] at hdrop
      rcases hdrop with rfl | hdrop
      · exact directionalDrop_nonnegative _ _
      · exact ih x drop hdrop

private theorem sum_le_of_forall₂ {xs ys : List ℝ}
    (hxy : List.Forall₂ (· ≤ ·) xs ys) : xs.sum ≤ ys.sum := by
  induction hxy with
  | nil => simp
  | cons hhead _ ih =>
      simpa using add_le_add hhead ih

private theorem sum_lt_of_forall₂_of_ne {xs ys : List ℝ}
    (hxy : List.Forall₂ (· ≤ ·) xs ys) (hne : xs ≠ ys) :
    xs.sum < ys.sum := by
  induction hxy with
  | nil => exact False.elim (hne rfl)
  | @cons x y xs ys hhead htail ih =>
      simp only [List.sum_cons]
      by_cases hxyHead : x = y
      · subst y
        have htailNe : xs ≠ ys := by
          intro h
          exact hne (congrArg (List.cons x) h)
        simpa [add_comm] using add_lt_add_left (ih htailNe) x
      · have hheadStrict : x < y := lt_of_le_of_ne hhead hxyHead
        have htailSum : xs.sum ≤ ys.sum := sum_le_of_forall₂ htail
        exact add_lt_add_of_lt_of_le hheadStrict htailSum

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

theorem runningMinimum_directional_penalty_le
    (penalty : ℝ → ℝ)
    (hmono : ∀ ⦃a b : ℝ⦄, 0 ≤ a → a ≤ b → penalty a ≤ penalty b)
    (profile : List ℝ) :
    ((directionalDrops (runningMinimum profile)).map penalty).sum ≤
      ((directionalDrops profile).map penalty).sum := by
  apply penalty_sum_le_of_forall₂ penalty hmono
    (runningMinimumFrom_drops_le (le_refl (1 : ℝ)) profile)
  intro drop hdrop
  exact directionalDropsFrom_nonnegative 1 (runningMinimumFrom 1 profile)
    drop hdrop

theorem runningMinimum_sum_le (profile : List ℝ) :
    (runningMinimum profile).sum ≤ profile.sum := by
  exact sum_le_of_forall₂ (runningMinimumFrom_coordinatewise_le 1 profile)

theorem runningMinimum_sum_strict_of_changed (profile : List ℝ)
    (hchanged : runningMinimum profile ≠ profile) :
    (runningMinimum profile).sum < profile.sum := by
  exact sum_lt_of_forall₂_of_ne
    (runningMinimumFrom_coordinatewise_le 1 profile) hchanged

/-- Running-minimum normalization weakly lowers every directional path
objective whose penalty is monotone on nonnegative drops and whose two weights
are nonnegative. -/
theorem pathHarmony_runningMinimum_le
    (penalty : ℝ → ℝ)
    (hmono : ∀ ⦃a b : ℝ⦄, 0 ≤ a → a ≤ b → penalty a ≤ penalty b)
    {h m : ℝ} (hh : 0 ≤ h) (hm : 0 ≤ m) (profile : List ℝ) :
    pathHarmony penalty h m (runningMinimum profile) ≤
      pathHarmony penalty h m profile := by
  have hpenalty := runningMinimum_directional_penalty_le penalty hmono profile
  have hmarked := runningMinimum_sum_le profile
  exact add_le_add (mul_le_mul_of_nonneg_left hpenalty hh)
    (mul_le_mul_of_nonneg_left hmarked hm)

/-- If normalization changes at least one coordinate and markedness has
strictly positive weight, the path objective strictly decreases. -/
theorem pathHarmony_runningMinimum_lt_of_changed
    (penalty : ℝ → ℝ)
    (hmono : ∀ ⦃a b : ℝ⦄, 0 ≤ a → a ≤ b → penalty a ≤ penalty b)
    {h m : ℝ} (hh : 0 ≤ h) (hm : 0 < m) (profile : List ℝ)
    (hchanged : runningMinimum profile ≠ profile) :
    pathHarmony penalty h m (runningMinimum profile) <
      pathHarmony penalty h m profile := by
  have hpenalty := runningMinimum_directional_penalty_le penalty hmono profile
  have hmarked := runningMinimum_sum_strict_of_changed profile hchanged
  exact add_lt_add_of_le_of_lt (mul_le_mul_of_nonneg_left hpenalty hh)
    (mul_lt_mul_of_pos_left hmarked hm)

/-- Quadratic penalty used by the `p = 2` directional-HG specialization. -/
def quadraticPenalty (drop : ℝ) : ℝ := drop ^ 2

theorem quadraticPenalty_monotone_on_nonnegative
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    quadraticPenalty a ≤ quadraticPenalty b := by
  unfold quadraticPenalty
  nlinarith

/-- Exact running-minimum reduction for the quadratic directional path
objective. -/
theorem quadraticPathHarmony_runningMinimum_le
    {h m : ℝ} (hh : 0 ≤ h) (hm : 0 ≤ m) (profile : List ℝ) :
    pathHarmony quadraticPenalty h m (runningMinimum profile) ≤
      pathHarmony quadraticPenalty h m profile :=
  pathHarmony_runningMinimum_le quadraticPenalty
    (fun {_a _b : ℝ} ha hab =>
      quadraticPenalty_monotone_on_nonnegative ha hab) hh hm profile

/-- Quadratic running-minimum reduction is strict whenever normalization
changes a coordinate and markedness has positive weight. -/
theorem quadraticPathHarmony_runningMinimum_lt_of_changed
    {h m : ℝ} (hh : 0 ≤ h) (hm : 0 < m) (profile : List ℝ)
    (hchanged : runningMinimum profile ≠ profile) :
    pathHarmony quadraticPenalty h m (runningMinimum profile) <
      pathHarmony quadraticPenalty h m profile :=
  pathHarmony_runningMinimum_lt_of_changed quadraticPenalty
    (fun {_a _b : ℝ} ha hab =>
      quadraticPenalty_monotone_on_nonnegative ha hab) hh hm profile hchanged

/-- Consecutive decreases of a profile beginning from `previous`. -/
def decreasesFrom (previous : ℝ) : List ℝ → List ℝ
  | [] => []
  | x :: xs => (previous - x) :: decreasesFrom x xs

/-- Reconstruct a profile from consecutive decreases. -/
def profileFromDecreases (previous : ℝ) : List ℝ → List ℝ
  | [] => []
  | d :: ds =>
      let x := previous - d
      x :: profileFromDecreases x ds

theorem profileFromDecreases_decreasesFrom (previous : ℝ)
    (profile : List ℝ) :
    profileFromDecreases previous (decreasesFrom previous profile) = profile := by
  induction profile generalizing previous with
  | nil => rfl
  | cons x xs ih =>
      simp [decreasesFrom, profileFromDecreases, ih]

theorem decreasesFrom_profileFromDecreases (previous : ℝ)
    (decreases : List ℝ) :
    decreasesFrom previous (profileFromDecreases previous decreases) =
      decreases := by
  induction decreases generalizing previous with
  | nil => rfl
  | cons d ds ih =>
      simp [decreasesFrom, profileFromDecreases, ih]

/-- Nonincreasing and nonnegative profile coordinates relative to a preceding
activity. -/
def AdmissibleProfileFrom : ℝ → List ℝ → Prop
  | previous, [] => 0 ≤ previous
  | previous, x :: xs => 0 ≤ x ∧ x ≤ previous ∧ AdmissibleProfileFrom x xs

/-- Solid simplex of nonnegative decreases whose total does not exceed the
preceding activity. -/
def SolidSimplexFrom (budget : ℝ) (decreases : List ℝ) : Prop :=
  (∀ d ∈ decreases, 0 ≤ d) ∧ decreases.sum ≤ budget

theorem admissibleProfile_iff_decreases_solidSimplex (previous : ℝ)
    (profile : List ℝ) :
    AdmissibleProfileFrom previous profile ↔
      SolidSimplexFrom previous (decreasesFrom previous profile) := by
  induction profile generalizing previous with
  | nil => simp [AdmissibleProfileFrom, SolidSimplexFrom, decreasesFrom]
  | cons x xs ih =>
      constructor
      · rintro ⟨hx0, hxprev, htail⟩
        have htailSimplex := (ih x).1 htail
        constructor
        · intro d hd
          simp only [decreasesFrom, List.mem_cons] at hd
          rcases hd with rfl | hd
          · linarith
          · exact htailSimplex.1 d hd
        · simp only [decreasesFrom, List.sum_cons]
          linarith [htailSimplex.2]
      · rintro ⟨hnonneg, hsum⟩
        have hfirst : 0 ≤ previous - x := by
          exact hnonneg _ (by simp [decreasesFrom])
        have htailNonnegative : ∀ d ∈ decreasesFrom x xs, 0 ≤ d := by
          intro d hd
          exact hnonneg d (by simp [decreasesFrom, hd])
        have htailSum : (decreasesFrom x xs).sum ≤ x := by
          simp only [decreasesFrom, List.sum_cons] at hsum
          linarith
        have hx0 : 0 ≤ x := by
          have htailSumNonnegative : 0 ≤ (decreasesFrom x xs).sum := by
            exact List.sum_nonneg htailNonnegative
          linarith
        exact ⟨hx0, by linarith, (ih x).2 ⟨htailNonnegative, htailSum⟩⟩

/-- The decrease/profile maps are inverse bijections between the declared
monotone-profile carrier and its solid-simplex carrier. -/
theorem solidSimplex_profile_equivalence (previous : ℝ) :
    (∀ profile,
      AdmissibleProfileFrom previous profile →
        SolidSimplexFrom previous (decreasesFrom previous profile)) ∧
    (∀ decreases,
      SolidSimplexFrom previous decreases →
        AdmissibleProfileFrom previous
          (profileFromDecreases previous decreases)) ∧
    (∀ profile,
      profileFromDecreases previous (decreasesFrom previous profile) = profile) ∧
    (∀ decreases,
      decreasesFrom previous (profileFromDecreases previous decreases) =
        decreases) := by
  constructor
  · intro profile hprofile
    exact (admissibleProfile_iff_decreases_solidSimplex previous profile).1 hprofile
  constructor
  · intro decreases hdecreases
    have hcorrespondence :=
      (admissibleProfile_iff_decreases_solidSimplex previous
        (profileFromDecreases previous decreases)).2
    rw [decreasesFrom_profileFromDecreases] at hcorrespondence
    exact hcorrespondence hdecreases
  exact ⟨profileFromDecreases_decreasesFrom previous,
    decreasesFrom_profileFromDecreases previous⟩

end PhonologicalCalculus.ContinuousHG
