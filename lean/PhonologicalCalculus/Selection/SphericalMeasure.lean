import PhonologicalCalculus.Selection.MatchedPair
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Tactic

/-!
# Spherical probability laws for selected-output regions

Finite-dimensional Lebesgue measure induces a finite surface measure on the
Euclidean unit sphere.  Normalizing this measure gives the common spherical
direction law used by the selected-output results.  The general lemmas below
turn nonempty relatively open directional events into strictly positive
probability and show that an empty event has probability zero.

The final constructions specialize this standard measure to the registered
five-coordinate Euclidean and Frobenius perturbation metrics.  In each metric,
one shell lies strictly after the first selected region begins and strictly
before the second selected region begins.  Consequently the same spherical
shell law assigns positive probability to the first selected output and zero
probability to the second.
-/

namespace PhonologicalCalculus.Selection

open MeasureTheory Metric Set
open scoped NNReal ENNReal

noncomputable section

/-! ## A normalized full-support measure on a Euclidean unit sphere -/

section GenericSphere

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

/-- The finite surface measure induced on the unit sphere by an additive Haar
measure on the ambient finite-dimensional real normed space. -/
def haarSphereFiniteMeasure (ambient : Measure E) [ambient.IsAddHaarMeasure] :
    FiniteMeasure (sphere (0 : E) 1) :=
  ⟨ambient.toSphere, inferInstance⟩

/-- The normalized spherical direction law induced by an additive Haar
measure. -/
def haarSphereProbability (ambient : Measure E) [ambient.IsAddHaarMeasure]
    [Nontrivial E] [Nonempty (sphere (0 : E) 1)] :
    ProbabilityMeasure (sphere (0 : E) 1) :=
  (haarSphereFiniteMeasure ambient).normalize

theorem haarSphereFiniteMeasure_ne_zero
    (ambient : Measure E) [ambient.IsAddHaarMeasure] [Nontrivial E] :
    haarSphereFiniteMeasure ambient ≠ 0 := by
  intro hzero
  have hmeasure : ambient.toSphere = 0 := by
    exact congrArg FiniteMeasure.toMeasure hzero
  exact ambient.toSphere_ne_zero hmeasure

/-- Every nonempty relatively open set of directions has positive probability
under the normalized Haar-induced spherical law. -/
theorem haarSphereProbability_open_pos
    (ambient : Measure E) [ambient.IsAddHaarMeasure] [Nontrivial E]
    [Nonempty (sphere (0 : E) 1)]
    {U : Set (sphere (0 : E) 1)} (hUopen : IsOpen U) (hUne : U.Nonempty) :
    0 < (haarSphereProbability ambient : Measure (sphere (0 : E) 1)) U := by
  have hraw : 0 < ambient.toSphere U :=
    hUopen.measure_pos ambient.toSphere hUne
  change 0 < ((haarSphereFiniteMeasure ambient).normalize :
    Measure (sphere (0 : E) 1)) U
  rw [(haarSphereFiniteMeasure ambient).toMeasure_normalize_eq_of_nonzero
    (haarSphereFiniteMeasure_ne_zero ambient)]
  rw [Measure.smul_apply]
  have hmass : (haarSphereFiniteMeasure ambient).mass ≠ 0 :=
    (haarSphereFiniteMeasure ambient).mass_nonzero_iff.mpr
      (haarSphereFiniteMeasure_ne_zero ambient)
  let massInv : ℝ≥0 := (haarSphereFiniteMeasure ambient).mass⁻¹
  have hcoef : 0 < (massInv : ℝ≥0∞) :=
    ENNReal.coe_pos.mpr (inv_pos.mpr (bot_lt_iff_ne_bot.mpr hmass))
  exact ENNReal.mul_pos hcoef.ne' hraw.ne'

theorem haarSphereProbability_empty
    (ambient : Measure E) [ambient.IsAddHaarMeasure] [Nontrivial E]
    [Nonempty (sphere (0 : E) 1)] :
    (haarSphereProbability ambient : Measure (sphere (0 : E) 1)) ∅ = 0 := by
  simp

/-- A nonempty relatively open part of the pairwise-only region forces a
strict probability gap.  This is the measure-theoretic converse step used
after the finite-dimensional halfspace geometry has produced an open sector.
-/
theorem haarSphereProbability_strict_of_open_gap
    (ambient : Measure E) [ambient.IsAddHaarMeasure] [Nontrivial E]
    [Nonempty (sphere (0 : E) 1)]
    {selected pairwise gap : Set (sphere (0 : E) 1)}
    (hselected : selected ⊆ pairwise)
    (hselectedMeasurable : MeasurableSet selected)
    (hgapOpen : IsOpen gap) (hgapNonempty : gap.Nonempty)
    (hgap : gap ⊆ pairwise \ selected) :
    (haarSphereProbability ambient : Measure (sphere (0 : E) 1)) selected <
      (haarSphereProbability ambient : Measure (sphere (0 : E) 1)) pairwise := by
  let probability : Measure (sphere (0 : E) 1) :=
    haarSphereProbability ambient
  have hgapPos : 0 < probability (pairwise \ selected) :=
    (haarSphereProbability_open_pos ambient hgapOpen hgapNonempty).trans_le
      (measure_mono hgap)
  have hdecomposition :
      probability pairwise =
        probability (pairwise \ selected) + probability selected := by
    rw [← measure_union Set.disjoint_sdiff_left hselectedMeasurable,
      Set.sdiff_union_of_subset hselected]
  have hfinite : probability selected ≠ ∞ := measure_ne_top probability selected
  have hstrict : probability selected <
      probability (pairwise \ selected) + probability selected := by
    have := (ENNReal.add_lt_add_iff_right hfinite).2 hgapPos
    simpa using this
  exact hstrict.trans_eq hdecomposition.symm

end GenericSphere

/-! ## Converse geometry for homogeneous comparison halfspaces -/

theorem coordinateDot_comm {ι : Type*} [Fintype ι]
    (x y : ι → ℝ) : coordinateDot x y = coordinateDot y x := by
  unfold coordinateDot
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem coordinateDot_sub_left {ι : Type*} [Fintype ι]
    (x y z : ι → ℝ) :
    coordinateDot (fun i => x i - y i) z =
      coordinateDot x z - coordinateDot y z := by
  unfold coordinateDot
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem coordinateDot_sub_right {ι : Type*} [Fintype ι]
    (x y z : ι → ℝ) :
    coordinateDot x (fun i => y i - z i) =
      coordinateDot x y - coordinateDot x z := by
  rw [coordinateDot_comm, coordinateDot_sub_left,
    coordinateDot_comm x y, coordinateDot_comm x z]

theorem coordinateDot_add_right {ι : Type*} [Fintype ι]
    (x y z : ι → ℝ) :
    coordinateDot x (fun i => y i + z i) =
      coordinateDot x y + coordinateDot x z := by
  unfold coordinateDot
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem coordinateDot_scale_left {ι : Type*} [Fintype ι]
    (x y : ι → ℝ) (scale : ℝ) :
    coordinateDot (fun i => scale * x i) y =
      scale * coordinateDot x y := by
  rw [coordinateDot_comm, coordinateDot_scale_right, coordinateDot_comm]

theorem coordinateDot_self_pos {ι : Type*} [Fintype ι]
    {x : ι → ℝ} (hx : x ≠ 0) : 0 < coordinateDot x x := by
  unfold coordinateDot
  apply Finset.sum_pos'
  · intro i hi
    exact mul_self_nonneg (x i)
  · have hexists : ∃ i, x i ≠ 0 := by
      by_contra hnone
      apply hx
      funext i
      by_contra hi
      exact hnone ⟨i, hi⟩
    obtain ⟨i, hi⟩ := hexists
    exact ⟨i, Finset.mem_univ i, mul_self_pos.mpr hi⟩

/-- Inclusion between two strict homogeneous comparison halfspaces forces the
second normal to be a positive scalar multiple of the first. -/
theorem positiveRay_of_pairwiseEvent_subset
    {ι : Type*} [Fintype ι]
    {target normal : ι → ℝ} (htarget : target ≠ 0)
    (hinclusion : pairwiseEvent target ⊆ pairwiseEvent normal) :
    ∃ scale : ℝ, 0 < scale ∧
      normal = fun i => scale * target i := by
  let denominator := coordinateDot target target
  let numerator := coordinateDot target normal
  have hdenominator : 0 < denominator := coordinateDot_self_pos htarget
  have htargetEvent : target ∈ pairwiseEvent target := hdenominator
  have hnumerator : 0 < numerator := hinclusion htargetEvent
  let scale := numerator / denominator
  have hscale : 0 < scale := div_pos hnumerator hdenominator
  let residual : ι → ℝ := fun i => normal i - scale * target i
  have horthogonal : coordinateDot target residual = 0 := by
    rw [coordinateDot_sub_right, coordinateDot_scale_right]
    change numerator - scale * denominator = 0
    dsimp only [scale]
    field_simp [hdenominator.ne']
    ring
  have hresidualZero : residual = 0 := by
    by_contra hresidual
    have hresidualNorm : 0 < coordinateDot residual residual :=
      coordinateDot_self_pos hresidual
    let coefficient := (numerator + 1) / coordinateDot residual residual
    let witness : ι → ℝ := fun i => target i - coefficient * residual i
    have hresidualTarget : coordinateDot residual target = 0 := by
      rw [coordinateDot_comm]
      exact horthogonal
    have hwitnessTarget : coordinateDot witness target = denominator := by
      rw [coordinateDot_sub_left, coordinateDot_scale_left,
        hresidualTarget, mul_zero, sub_zero]
    have hwitnessEvent : witness ∈ pairwiseEvent target := by
      change 0 < coordinateDot witness target
      rw [hwitnessTarget]
      exact hdenominator
    have hwitnessNormal : 0 < coordinateDot witness normal :=
      hinclusion hwitnessEvent
    have hnormalDecomposition :
        normal = fun i => scale * target i + residual i := by
      funext i
      dsimp only [residual]
      ring
    have hresidualNormal :
        coordinateDot residual normal = coordinateDot residual residual := by
      rw [hnormalDecomposition, coordinateDot_add_right,
        coordinateDot_scale_right, hresidualTarget, mul_zero, zero_add]
    have hwitnessValue : coordinateDot witness normal = -1 := by
      rw [coordinateDot_sub_left, coordinateDot_scale_left,
        hresidualNormal]
      dsimp only [witness, coefficient]
      dsimp only [numerator]
      field_simp [hresidualNorm.ne']
      ring
    rw [hwitnessValue] at hwitnessNormal
    linarith
  refine ⟨scale, hscale, ?_⟩
  funext i
  have hi := congrFun hresidualZero i
  dsimp only [residual] at hi
  simpa using sub_eq_zero.mp hi

/-- For a complete finite comparison list containing a nonzero target normal,
event identity is equivalent to the positive-ray condition. -/
theorem selectedEvent_eq_pairwise_iff_positiveRays
    {ι : Type*} [Fintype ι]
    {target : ι → ℝ} {normals : List (ι → ℝ)}
    (htargetMember : target ∈ normals) (htargetNonzero : target ≠ 0) :
    selectedEvent normals = pairwiseEvent target ↔
      PositiveRayFamily target normals := by
  constructor
  · intro hevents normal hnormal
    apply positiveRay_of_pairwiseEvent_subset htargetNonzero
    intro parameter hpairwise
    have hselected : parameter ∈ selectedEvent normals := by
      rw [hevents]
      exact hpairwise
    exact hselected normal hnormal
  · exact selectedEvent_eq_pairwise_of_positiveRays htargetMember

/-- Positive-ray equality is distribution-independent: because the two
registered events are literally the same set, every measure on the parameter
space assigns them the same value.  This is the exact universal-probability
sufficiency licensed by the event theorem; no converse from equality under one
particular measure is asserted. -/
theorem measure_selectedEvent_eq_pairwise_of_positiveRays
    {ι : Type*} [Fintype ι] [MeasurableSpace (ι → ℝ)]
    (measure : Measure (ι → ℝ))
    {target : ι → ℝ} {normals : List (ι → ℝ)}
    (htargetMember : target ∈ normals)
    (hrays : PositiveRayFamily target normals) :
    measure (selectedEvent normals) = measure (pairwiseEvent target) := by
  rw [selectedEvent_eq_pairwise_of_positiveRays htargetMember hrays]

/-! ## Five-coordinate Euclidean shell -/

abbrev EuclideanFive := EuclideanSpace ℝ (Fin 5)
abbrev EuclideanUnitSphere := sphere (0 : EuclideanFive) 1

local instance euclideanFiveMeasurableSpace : MeasurableSpace EuclideanFive :=
  borel EuclideanFive

local instance euclideanFiveBorelSpace : BorelSpace EuclideanFive := ⟨rfl⟩

def disruptionOfEuclidean (point : EuclideanFive) : Disruption :=
  ⟨point 0, point 1, point 2, point 3, point 4⟩

def euclideanOfDisruption (point : Disruption) : EuclideanFive :=
  WithLp.toLp 2 ![point.a, point.b, point.c, point.d, point.e]

@[simp]
theorem disruptionOfEuclidean_euclideanOfDisruption (point : Disruption) :
    disruptionOfEuclidean (euclideanOfDisruption point) = point := by
  cases point
  rfl

theorem euclideanSquared_disruptionOfEuclidean (point : EuclideanFive) :
    euclideanSquared (disruptionOfEuclidean point) = ‖point‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [euclideanSquared, disruptionOfEuclidean, Fin.sum_univ_succ]
  ring

def euclideanFirstDirectionEvent (radius : ℝ) : Set EuclideanUnitSphere :=
  {direction | firstSelectedStrict
    (disruptionOfEuclidean (radius • (direction : EuclideanFive)))}

def euclideanSecondDirectionEvent (radius : ℝ) : Set EuclideanUnitSphere :=
  {direction | secondSelectedStrict
    (disruptionOfEuclidean (radius • (direction : EuclideanFive)))}

theorem euclideanFirstDirectionEvent_isOpen (radius : ℝ) :
    IsOpen (euclideanFirstDirectionEvent radius) := by
  unfold euclideanFirstDirectionEvent firstSelectedStrict disruptionOfEuclidean
  change IsOpen ({direction : EuclideanUnitSphere |
      0 < 1 + (radius • (direction : EuclideanFive)) 0 +
        (radius • (direction : EuclideanFive)) 1 +
        2 * (radius • (direction : EuclideanFive)) 4} ∩
    ({direction : EuclideanUnitSphere |
      19 < (radius • (direction : EuclideanFive)) 1 +
        2 * (radius • (direction : EuclideanFive)) 4} ∩
    {direction : EuclideanUnitSphere |
      0 < 18 + (radius • (direction : EuclideanFive)) 0 +
        2 * (radius • (direction : EuclideanFive)) 4}))
  refine (isOpen_lt continuous_const ?_).inter
    ((isOpen_lt continuous_const ?_).inter
      (isOpen_lt continuous_const ?_)) <;> fun_prop

noncomputable def euclideanShellRadius : ℝ := Real.sqrt 80

theorem euclideanShellRadius_pos : 0 < euclideanShellRadius := by
  norm_num [euclideanShellRadius]

theorem euclideanShellRadius_sq : euclideanShellRadius ^ 2 = 80 := by
  norm_num [euclideanShellRadius]

theorem euclideanOfDisruption_shell_norm :
    ‖euclideanOfDisruption euclideanShellPoint‖ = euclideanShellRadius := by
  apply (sq_eq_sq₀ (norm_nonneg _) (euclideanShellRadius_pos.le)).mp
  rw [← euclideanSquared_disruptionOfEuclidean]
  simp only [disruptionOfEuclidean_euclideanOfDisruption]
  rw [euclideanShellRadius_sq]
  exact euclidean_common_shell_geometry.1

def euclideanShellDirection : EuclideanUnitSphere :=
  ⟨euclideanShellRadius⁻¹ • euclideanOfDisruption euclideanShellPoint, by
    simp only [mem_sphere, dist_zero_right, norm_smul,
      euclideanOfDisruption_shell_norm]
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr euclideanShellRadius_pos)]
    exact inv_mul_cancel₀ euclideanShellRadius_pos.ne'⟩

theorem euclideanShellDirection_mem_first :
    euclideanShellDirection ∈
      euclideanFirstDirectionEvent euclideanShellRadius := by
  change firstSelectedStrict (disruptionOfEuclidean
    (euclideanShellRadius • (euclideanShellRadius⁻¹ •
      euclideanOfDisruption euclideanShellPoint)))
  simpa [smul_smul, mul_inv_cancel₀ euclideanShellRadius_pos.ne'] using
    euclidean_common_shell_geometry.2.1

theorem euclideanSecondDirectionEvent_eq_empty :
    euclideanSecondDirectionEvent euclideanShellRadius = ∅ := by
  ext direction
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hsecond
  have hclosure := secondSelectedStrict_toClosure hsecond
  have hbelow := euclidean_common_shell_geometry.2.2.1 _ hclosure
  have hnorm : ‖(euclideanShellRadius •
      (direction : EuclideanFive))‖ ^ 2 = 80 := by
    rw [norm_smul, Real.norm_of_nonneg euclideanShellRadius_pos.le,
      mul_pow, euclideanShellRadius_sq]
    have hsphere := direction.property
    simp only [mem_sphere, dist_zero_right] at hsphere
    rw [hsphere]
    norm_num
  rw [euclideanSquared_disruptionOfEuclidean] at hbelow
  linarith

local instance euclideanUnitSphereNonempty : Nonempty EuclideanUnitSphere :=
  ⟨euclideanShellDirection⟩

noncomputable def euclideanSphericalLaw : ProbabilityMeasure EuclideanUnitSphere :=
  haarSphereProbability (volume : Measure EuclideanFive)

/-- `SEL-F2.COMMONLAW.04`, Euclidean branch: the normalized standard
spherical direction law on squared radius `80` assigns positive probability
to the first selected-output event and zero probability to the second. -/
theorem sel_f2_commonlaw_euclidean :
    (euclideanSphericalLaw : Measure EuclideanUnitSphere)
        (euclideanSecondDirectionEvent euclideanShellRadius) = 0 ∧
      0 < (euclideanSphericalLaw : Measure EuclideanUnitSphere)
        (euclideanFirstDirectionEvent euclideanShellRadius) := by
  constructor
  · rw [euclideanSecondDirectionEvent_eq_empty]
    simp
  · exact haarSphereProbability_open_pos (volume : Measure EuclideanFive)
      (euclideanFirstDirectionEvent_isOpen euclideanShellRadius)
      ⟨euclideanShellDirection, euclideanShellDirection_mem_first⟩

/-! ## Five-coordinate Frobenius shell -/

def disruptionOfFrobenius (point : EuclideanFive) : Disruption :=
  ⟨point 0, point 1, point 2, point 3, point 4 / Real.sqrt 2⟩

def frobeniusOfDisruption (point : Disruption) : EuclideanFive :=
  WithLp.toLp 2 ![point.a, point.b, point.c, point.d,
    Real.sqrt 2 * point.e]

theorem sqrtTwo_pos : 0 < Real.sqrt 2 := by positivity

@[simp]
theorem disruptionOfFrobenius_frobeniusOfDisruption (point : Disruption) :
    disruptionOfFrobenius (frobeniusOfDisruption point) = point := by
  cases point
  simp [disruptionOfFrobenius, frobeniusOfDisruption,
    Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2)]

theorem frobeniusSquared_disruptionOfFrobenius (point : EuclideanFive) :
    frobeniusSquared (disruptionOfFrobenius point) = ‖point‖ ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  have hsqrt : (Real.sqrt 2) ^ 2 = 2 := by norm_num
  simp [frobeniusSquared, disruptionOfFrobenius, Fin.sum_univ_succ,
    div_pow, hsqrt]
  field_simp [Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2)]
  ring

def frobeniusFirstDirectionEvent (radius : ℝ) : Set EuclideanUnitSphere :=
  {direction | firstSelectedStrict
    (disruptionOfFrobenius (radius • (direction : EuclideanFive)))}

def frobeniusSecondDirectionEvent (radius : ℝ) : Set EuclideanUnitSphere :=
  {direction | secondSelectedStrict
    (disruptionOfFrobenius (radius • (direction : EuclideanFive)))}

theorem frobeniusFirstDirectionEvent_isOpen (radius : ℝ) :
    IsOpen (frobeniusFirstDirectionEvent radius) := by
  unfold frobeniusFirstDirectionEvent firstSelectedStrict disruptionOfFrobenius
  change IsOpen ({direction : EuclideanUnitSphere |
      0 < 1 + (radius • (direction : EuclideanFive)) 0 +
        (radius • (direction : EuclideanFive)) 1 +
        2 * ((radius • (direction : EuclideanFive)) 4 / Real.sqrt 2)} ∩
    ({direction : EuclideanUnitSphere |
      19 < (radius • (direction : EuclideanFive)) 1 +
        2 * ((radius • (direction : EuclideanFive)) 4 / Real.sqrt 2)} ∩
    {direction : EuclideanUnitSphere |
      0 < 18 + (radius • (direction : EuclideanFive)) 0 +
        2 * ((radius • (direction : EuclideanFive)) 4 / Real.sqrt 2)}))
  refine (isOpen_lt continuous_const ?_).inter
    ((isOpen_lt continuous_const ?_).inter
      (isOpen_lt continuous_const ?_)) <;> fun_prop

noncomputable def frobeniusShellRadius : ℝ := Real.sqrt 122

theorem frobeniusShellRadius_pos : 0 < frobeniusShellRadius := by
  norm_num [frobeniusShellRadius]

theorem frobeniusShellRadius_sq : frobeniusShellRadius ^ 2 = 122 := by
  norm_num [frobeniusShellRadius]

theorem frobeniusOfDisruption_shell_norm :
    ‖frobeniusOfDisruption frobeniusShellPoint‖ = frobeniusShellRadius := by
  apply (sq_eq_sq₀ (norm_nonneg _) (frobeniusShellRadius_pos.le)).mp
  rw [← frobeniusSquared_disruptionOfFrobenius]
  simp only [disruptionOfFrobenius_frobeniusOfDisruption]
  rw [frobeniusShellRadius_sq]
  exact frobenius_common_shell_geometry.1

def frobeniusShellDirection : EuclideanUnitSphere :=
  ⟨frobeniusShellRadius⁻¹ • frobeniusOfDisruption frobeniusShellPoint, by
    simp only [mem_sphere, dist_zero_right, norm_smul,
      frobeniusOfDisruption_shell_norm]
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr frobeniusShellRadius_pos)]
    exact inv_mul_cancel₀ frobeniusShellRadius_pos.ne'⟩

theorem frobeniusShellDirection_mem_first :
    frobeniusShellDirection ∈
      frobeniusFirstDirectionEvent frobeniusShellRadius := by
  change firstSelectedStrict (disruptionOfFrobenius
    (frobeniusShellRadius • (frobeniusShellRadius⁻¹ •
      frobeniusOfDisruption frobeniusShellPoint)))
  simpa [smul_smul, mul_inv_cancel₀ frobeniusShellRadius_pos.ne'] using
    frobenius_common_shell_geometry.2.1

theorem frobeniusSecondDirectionEvent_eq_empty :
    frobeniusSecondDirectionEvent frobeniusShellRadius = ∅ := by
  ext direction
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hsecond
  have hclosure := secondSelectedStrict_toClosure hsecond
  have hbelow := frobenius_common_shell_geometry.2.2.1 _ hclosure
  have hnorm : ‖(frobeniusShellRadius •
      (direction : EuclideanFive))‖ ^ 2 = 122 := by
    rw [norm_smul, Real.norm_of_nonneg frobeniusShellRadius_pos.le,
      mul_pow, frobeniusShellRadius_sq]
    have hsphere := direction.property
    simp only [mem_sphere, dist_zero_right] at hsphere
    rw [hsphere]
    norm_num
  rw [frobeniusSquared_disruptionOfFrobenius] at hbelow
  linarith

noncomputable def frobeniusSphericalLaw : ProbabilityMeasure EuclideanUnitSphere :=
  haarSphereProbability (volume : Measure EuclideanFive)

/-- `SEL-F2.COMMONLAW.04`, Frobenius branch: after the exact coordinate
isometry, the same normalized spherical direction law on squared radius `122`
assigns positive probability to the first event and zero to the second. -/
theorem sel_f2_commonlaw_frobenius :
    (frobeniusSphericalLaw : Measure EuclideanUnitSphere)
        (frobeniusSecondDirectionEvent frobeniusShellRadius) = 0 ∧
      0 < (frobeniusSphericalLaw : Measure EuclideanUnitSphere)
        (frobeniusFirstDirectionEvent frobeniusShellRadius) := by
  constructor
  · rw [frobeniusSecondDirectionEvent_eq_empty]
    simp
  · exact haarSphereProbability_open_pos (volume : Measure EuclideanFive)
      (frobeniusFirstDirectionEvent_isOpen frobeniusShellRadius)
      ⟨frobeniusShellDirection, frobeniusShellDirection_mem_first⟩

/-- The two declared metric branches of `SEL-F2.COMMONLAW.04`. -/
theorem sel_f2_commonlaw_04 :
    ((euclideanSphericalLaw : Measure EuclideanUnitSphere)
        (euclideanSecondDirectionEvent euclideanShellRadius) = 0 ∧
      0 < (euclideanSphericalLaw : Measure EuclideanUnitSphere)
        (euclideanFirstDirectionEvent euclideanShellRadius)) ∧
    ((frobeniusSphericalLaw : Measure EuclideanUnitSphere)
        (frobeniusSecondDirectionEvent frobeniusShellRadius) = 0 ∧
      0 < (frobeniusSphericalLaw : Measure EuclideanUnitSphere)
        (frobeniusFirstDirectionEvent frobeniusShellRadius)) :=
  ⟨sel_f2_commonlaw_euclidean, sel_f2_commonlaw_frobenius⟩

end

end PhonologicalCalculus.Selection
