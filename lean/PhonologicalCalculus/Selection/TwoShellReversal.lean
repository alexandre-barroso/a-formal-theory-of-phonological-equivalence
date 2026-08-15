import PhonologicalCalculus.Selection.SphericalMeasure
import Mathlib.Tactic

/-!
# A common two-shell law with two positive selected-output errors

The intermediate shells in `SphericalMeasure` make the first selected-output
event positive while the second event is empty.  This module supplies a second,
larger shell on which both strict events contain an open patch.  A sufficiently
small positive mixture of the larger shell into the intermediate shell is then
one common radial law for the two compared inputs: both named errors have
positive probability, while the first remains strictly more probable.

The construction is exact in both registered coordinate metrics.  Its radial
law has two atoms; no continuity or density premise is required.  The angular
law on every shell is the same normalized Haar-induced spherical law.
-/

namespace PhonologicalCalculus.Selection

open MeasureTheory Metric Set
open scoped NNReal ENNReal

noncomputable section

-- `SphericalMeasure` intentionally keeps these Borel instances local.  This
-- module constructs new measures on the same sphere, so it reinstates the
-- identical ambient measurable structure explicitly.
local instance twoShellEuclideanFiveMeasurableSpace :
    MeasurableSpace EuclideanFive :=
  borel EuclideanFive

local instance twoShellEuclideanFiveBorelSpace :
    BorelSpace EuclideanFive :=
  ⟨rfl⟩

local instance twoShellEuclideanUnitSphereNonempty :
    Nonempty EuclideanUnitSphere :=
  ⟨euclideanShellDirection⟩

/-! ## A typed two-shell radial law -/

/-- A two-atom radial law together with one common angular probability law.
`farWeight` is the mass of the far shell and `1 - farWeight` is the mass of
the near shell. -/
structure TwoShellSphericalLaw (Omega : Type*) [MeasurableSpace Omega] where
  angularLaw : ProbabilityMeasure Omega
  nearRadius : Real
  farRadius : Real
  nearRadius_pos : 0 < nearRadius
  farRadius_pos : 0 < farRadius
  nearRadius_lt_farRadius : nearRadius < farRadius
  farWeight : Real
  farWeight_pos : 0 < farWeight
  farWeight_lt_one : farWeight < 1

/-- The real probability of a radius-indexed angular event under a two-shell
law.  This is the conditional-probability formula for the two-atom radial
mixture. -/
def TwoShellSphericalLaw.eventProbability
    {Omega : Type*} [MeasurableSpace Omega]
    (law : TwoShellSphericalLaw Omega) (event : Real → Set Omega) : Real :=
  (1 - law.farWeight) * (law.angularLaw : Measure Omega).real
      (event law.nearRadius) +
    law.farWeight * (law.angularLaw : Measure Omega).real
      (event law.farRadius)

theorem TwoShellSphericalLaw.eventProbability_nonneg
    {Omega : Type*} [MeasurableSpace Omega]
    (law : TwoShellSphericalLaw Omega) (event : Real → Set Omega) :
    0 ≤ law.eventProbability event := by
  unfold TwoShellSphericalLaw.eventProbability
  exact add_nonneg
    (mul_nonneg (sub_nonneg.mpr law.farWeight_lt_one.le) measureReal_nonneg)
    (mul_nonneg law.farWeight_pos.le measureReal_nonneg)

theorem TwoShellSphericalLaw.eventProbability_le_one
    {Omega : Type*} [MeasurableSpace Omega]
    (law : TwoShellSphericalLaw Omega) (event : Real → Set Omega) :
    law.eventProbability event ≤ 1 := by
  unfold TwoShellSphericalLaw.eventProbability
  have hnear : (law.angularLaw : Measure Omega).real
      (event law.nearRadius) ≤ 1 := measureReal_le_one
  have hfar : (law.angularLaw : Measure Omega).real
      (event law.farRadius) ≤ 1 := measureReal_le_one
  have hnearWeight : 0 ≤ 1 - law.farWeight :=
    sub_nonneg.mpr law.farWeight_lt_one.le
  have hfarWeight : 0 ≤ law.farWeight := law.farWeight_pos.le
  calc
    (1 - law.farWeight) * (law.angularLaw : Measure Omega).real
          (event law.nearRadius) +
        law.farWeight * (law.angularLaw : Measure Omega).real
          (event law.farRadius)
        ≤ (1 - law.farWeight) * 1 + law.farWeight * 1 :=
      add_le_add
        (mul_le_mul_of_nonneg_left hnear hnearWeight)
        (mul_le_mul_of_nonneg_left hfar hfarWeight)
    _ = 1 := by ring

/-! ## The elementary exact mixture lemma -/

/-- If the near shell has first-event mass `a > 0` and zero second-event
mass, while the far shell has positive masses `b` and `c`, then the exact
choice `epsilon = a / (2 * (a + c))` keeps the first event larger and makes
both mixture masses positive. -/
theorem exists_positive_twoShell_reversal
    {a b c : Real} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    ∃ epsilon : Real,
      0 < epsilon ∧ epsilon < 1 ∧
      0 < (1 - epsilon) * a + epsilon * b ∧
      0 < epsilon * c ∧
      epsilon * c < (1 - epsilon) * a + epsilon * b := by
  let epsilon : Real := a / (2 * (a + c))
  have hac : 0 < a + c := by linarith
  have hden : 0 < 2 * (a + c) := by positivity
  have hepsilonPos : 0 < epsilon := by
    exact div_pos ha hden
  have hepsilonLt : epsilon < 1 := by
    exact (div_lt_one hden).2 (by linarith)
  have hhalf : epsilon * (a + c) = a / 2 := by
    dsimp [epsilon]
    field_simp [ne_of_gt hac]
  have heb : 0 < epsilon * b := mul_pos hepsilonPos hb
  have hec : 0 < epsilon * c := mul_pos hepsilonPos hc
  have hnear : 0 < (1 - epsilon) * a :=
    mul_pos (sub_pos.mpr hepsilonLt) ha
  refine ⟨epsilon, hepsilonPos, hepsilonLt, ?_, hec, ?_⟩
  · linarith
  · nlinarith [hhalf]

/-! ## Euclidean far shell -/

def euclideanFarFirstPoint : Disruption :=
  { a := 0, b := 5, c := 12, d := 0, e := 8 }

def euclideanFarSecondPoint : Disruption :=
  { a := 10, b := 0, c := 6, d := -9, e := -4 }

noncomputable def euclideanFarRadius : Real := Real.sqrt 233

theorem euclideanFarRadius_pos : 0 < euclideanFarRadius := by
  norm_num [euclideanFarRadius]

theorem euclideanFarRadius_sq : euclideanFarRadius ^ 2 = 233 := by
  norm_num [euclideanFarRadius]

theorem euclideanFarFirst_geometry :
    euclideanSquared euclideanFarFirstPoint = 233 ∧
      firstSelectedStrict euclideanFarFirstPoint := by
  constructor <;> norm_num [euclideanSquared, euclideanFarFirstPoint,
    firstSelectedStrict]

theorem euclideanFarSecond_geometry :
    euclideanSquared euclideanFarSecondPoint = 233 ∧
      secondSelectedStrict euclideanFarSecondPoint := by
  constructor <;> norm_num [euclideanSquared, euclideanFarSecondPoint,
    secondSelectedStrict]

theorem euclideanFarFirst_norm :
    ‖euclideanOfDisruption euclideanFarFirstPoint‖ = euclideanFarRadius := by
  apply (sq_eq_sq₀ (norm_nonneg _) euclideanFarRadius_pos.le).mp
  rw [← euclideanSquared_disruptionOfEuclidean]
  simp only [disruptionOfEuclidean_euclideanOfDisruption]
  rw [euclideanFarRadius_sq]
  exact euclideanFarFirst_geometry.1

theorem euclideanFarSecond_norm :
    ‖euclideanOfDisruption euclideanFarSecondPoint‖ = euclideanFarRadius := by
  apply (sq_eq_sq₀ (norm_nonneg _) euclideanFarRadius_pos.le).mp
  rw [← euclideanSquared_disruptionOfEuclidean]
  simp only [disruptionOfEuclidean_euclideanOfDisruption]
  rw [euclideanFarRadius_sq]
  exact euclideanFarSecond_geometry.1

def euclideanFarFirstDirection : EuclideanUnitSphere :=
  ⟨euclideanFarRadius⁻¹ • euclideanOfDisruption euclideanFarFirstPoint, by
    simp only [mem_sphere, dist_zero_right, norm_smul, euclideanFarFirst_norm]
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr euclideanFarRadius_pos)]
    exact inv_mul_cancel₀ euclideanFarRadius_pos.ne'⟩

def euclideanFarSecondDirection : EuclideanUnitSphere :=
  ⟨euclideanFarRadius⁻¹ • euclideanOfDisruption euclideanFarSecondPoint, by
    simp only [mem_sphere, dist_zero_right, norm_smul, euclideanFarSecond_norm]
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr euclideanFarRadius_pos)]
    exact inv_mul_cancel₀ euclideanFarRadius_pos.ne'⟩

theorem euclideanFarFirstDirection_mem :
    euclideanFarFirstDirection ∈
      euclideanFirstDirectionEvent euclideanFarRadius := by
  change firstSelectedStrict (disruptionOfEuclidean
    (euclideanFarRadius • (euclideanFarRadius⁻¹ •
      euclideanOfDisruption euclideanFarFirstPoint)))
  simpa [smul_smul, mul_inv_cancel₀ euclideanFarRadius_pos.ne'] using
    euclideanFarFirst_geometry.2

theorem euclideanFarSecondDirection_mem :
    euclideanFarSecondDirection ∈
      euclideanSecondDirectionEvent euclideanFarRadius := by
  change secondSelectedStrict (disruptionOfEuclidean
    (euclideanFarRadius • (euclideanFarRadius⁻¹ •
      euclideanOfDisruption euclideanFarSecondPoint)))
  simpa [smul_smul, mul_inv_cancel₀ euclideanFarRadius_pos.ne'] using
    euclideanFarSecond_geometry.2

theorem euclideanSecondDirectionEvent_isOpen (radius : Real) :
    IsOpen (euclideanSecondDirectionEvent radius) := by
  unfold euclideanSecondDirectionEvent secondSelectedStrict disruptionOfEuclidean
  change IsOpen ({direction : EuclideanUnitSphere |
      -3 < (radius • (direction : EuclideanFive)) 2} ∩
    ({direction : EuclideanUnitSphere |
      14 < (radius • (direction : EuclideanFive)) 2 -
        (radius • (direction : EuclideanFive)) 3} ∩
    {direction : EuclideanUnitSphere |
      15 < -(radius • (direction : EuclideanFive)) 3 -
        2 * (radius • (direction : EuclideanFive)) 4}))
  refine (isOpen_lt continuous_const ?_).inter
    ((isOpen_lt continuous_const ?_).inter
      (isOpen_lt continuous_const ?_)) <;> fun_prop

theorem euclideanFarEvents_positive :
    0 < (euclideanSphericalLaw : Measure EuclideanUnitSphere)
        (euclideanFirstDirectionEvent euclideanFarRadius) ∧
      0 < (euclideanSphericalLaw : Measure EuclideanUnitSphere)
        (euclideanSecondDirectionEvent euclideanFarRadius) := by
  constructor
  · exact haarSphereProbability_open_pos (volume : Measure EuclideanFive)
      (euclideanFirstDirectionEvent_isOpen euclideanFarRadius)
      ⟨euclideanFarFirstDirection, euclideanFarFirstDirection_mem⟩
  · exact haarSphereProbability_open_pos (volume : Measure EuclideanFive)
      (euclideanSecondDirectionEvent_isOpen euclideanFarRadius)
      ⟨euclideanFarSecondDirection, euclideanFarSecondDirection_mem⟩

/-! ## Frobenius far shell -/

def frobeniusFarFirstPoint : Disruption :=
  { a := 0, b := 5, c := 0, d := 0, e := 8 }

def frobeniusFarSecondPoint : Disruption :=
  { a := 2, b := 0, c := 6, d := -9, e := -4 }

noncomputable def frobeniusFarRadius : Real := Real.sqrt 153

theorem frobeniusFarRadius_pos : 0 < frobeniusFarRadius := by
  norm_num [frobeniusFarRadius]

theorem frobeniusFarRadius_sq : frobeniusFarRadius ^ 2 = 153 := by
  norm_num [frobeniusFarRadius]

theorem frobeniusFarFirst_geometry :
    frobeniusSquared frobeniusFarFirstPoint = 153 ∧
      firstSelectedStrict frobeniusFarFirstPoint := by
  constructor <;> norm_num [frobeniusSquared, frobeniusFarFirstPoint,
    firstSelectedStrict]

theorem frobeniusFarSecond_geometry :
    frobeniusSquared frobeniusFarSecondPoint = 153 ∧
      secondSelectedStrict frobeniusFarSecondPoint := by
  constructor <;> norm_num [frobeniusSquared, frobeniusFarSecondPoint,
    secondSelectedStrict]

theorem frobeniusFarFirst_norm :
    ‖frobeniusOfDisruption frobeniusFarFirstPoint‖ = frobeniusFarRadius := by
  apply (sq_eq_sq₀ (norm_nonneg _) frobeniusFarRadius_pos.le).mp
  rw [← frobeniusSquared_disruptionOfFrobenius]
  simp only [disruptionOfFrobenius_frobeniusOfDisruption]
  rw [frobeniusFarRadius_sq]
  exact frobeniusFarFirst_geometry.1

theorem frobeniusFarSecond_norm :
    ‖frobeniusOfDisruption frobeniusFarSecondPoint‖ = frobeniusFarRadius := by
  apply (sq_eq_sq₀ (norm_nonneg _) frobeniusFarRadius_pos.le).mp
  rw [← frobeniusSquared_disruptionOfFrobenius]
  simp only [disruptionOfFrobenius_frobeniusOfDisruption]
  rw [frobeniusFarRadius_sq]
  exact frobeniusFarSecond_geometry.1

def frobeniusFarFirstDirection : EuclideanUnitSphere :=
  ⟨frobeniusFarRadius⁻¹ • frobeniusOfDisruption frobeniusFarFirstPoint, by
    simp only [mem_sphere, dist_zero_right, norm_smul, frobeniusFarFirst_norm]
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr frobeniusFarRadius_pos)]
    exact inv_mul_cancel₀ frobeniusFarRadius_pos.ne'⟩

def frobeniusFarSecondDirection : EuclideanUnitSphere :=
  ⟨frobeniusFarRadius⁻¹ • frobeniusOfDisruption frobeniusFarSecondPoint, by
    simp only [mem_sphere, dist_zero_right, norm_smul, frobeniusFarSecond_norm]
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr frobeniusFarRadius_pos)]
    exact inv_mul_cancel₀ frobeniusFarRadius_pos.ne'⟩

theorem frobeniusFarFirstDirection_mem :
    frobeniusFarFirstDirection ∈
      frobeniusFirstDirectionEvent frobeniusFarRadius := by
  change firstSelectedStrict (disruptionOfFrobenius
    (frobeniusFarRadius • (frobeniusFarRadius⁻¹ •
      frobeniusOfDisruption frobeniusFarFirstPoint)))
  simpa [smul_smul, mul_inv_cancel₀ frobeniusFarRadius_pos.ne'] using
    frobeniusFarFirst_geometry.2

theorem frobeniusFarSecondDirection_mem :
    frobeniusFarSecondDirection ∈
      frobeniusSecondDirectionEvent frobeniusFarRadius := by
  change secondSelectedStrict (disruptionOfFrobenius
    (frobeniusFarRadius • (frobeniusFarRadius⁻¹ •
      frobeniusOfDisruption frobeniusFarSecondPoint)))
  simpa [smul_smul, mul_inv_cancel₀ frobeniusFarRadius_pos.ne'] using
    frobeniusFarSecond_geometry.2

theorem frobeniusSecondDirectionEvent_isOpen (radius : Real) :
    IsOpen (frobeniusSecondDirectionEvent radius) := by
  unfold frobeniusSecondDirectionEvent secondSelectedStrict
    disruptionOfFrobenius
  change IsOpen ({direction : EuclideanUnitSphere |
      -3 < (radius • (direction : EuclideanFive)) 2} ∩
    ({direction : EuclideanUnitSphere |
      14 < (radius • (direction : EuclideanFive)) 2 -
        (radius • (direction : EuclideanFive)) 3} ∩
    {direction : EuclideanUnitSphere |
      15 < -(radius • (direction : EuclideanFive)) 3 -
        2 * ((radius • (direction : EuclideanFive)) 4 / Real.sqrt 2)}))
  refine (isOpen_lt continuous_const ?_).inter
    ((isOpen_lt continuous_const ?_).inter
      (isOpen_lt continuous_const ?_)) <;> fun_prop

theorem frobeniusFarEvents_positive :
    0 < (frobeniusSphericalLaw : Measure EuclideanUnitSphere)
        (frobeniusFirstDirectionEvent frobeniusFarRadius) ∧
      0 < (frobeniusSphericalLaw : Measure EuclideanUnitSphere)
        (frobeniusSecondDirectionEvent frobeniusFarRadius) := by
  constructor
  · exact haarSphereProbability_open_pos (volume : Measure EuclideanFive)
      (frobeniusFirstDirectionEvent_isOpen frobeniusFarRadius)
      ⟨frobeniusFarFirstDirection, frobeniusFarFirstDirection_mem⟩
  · exact haarSphereProbability_open_pos (volume : Measure EuclideanFive)
      (frobeniusSecondDirectionEvent_isOpen frobeniusFarRadius)
      ⟨frobeniusFarSecondDirection, frobeniusFarSecondDirection_mem⟩

/-! ## Final common-law reversal in both registered metrics -/

theorem sel_f2_common_twoShell_positive_reversal_euclidean :
    ∃ law : TwoShellSphericalLaw EuclideanUnitSphere,
      law.angularLaw = euclideanSphericalLaw ∧
      law.nearRadius = euclideanShellRadius ∧
      law.farRadius = euclideanFarRadius ∧
      0 < law.eventProbability euclideanFirstDirectionEvent ∧
      0 < law.eventProbability euclideanSecondDirectionEvent ∧
      law.eventProbability euclideanSecondDirectionEvent <
        law.eventProbability euclideanFirstDirectionEvent := by
  let mu : Measure EuclideanUnitSphere := euclideanSphericalLaw
  let a : Real := mu.real (euclideanFirstDirectionEvent euclideanShellRadius)
  let b : Real := mu.real (euclideanFirstDirectionEvent euclideanFarRadius)
  let c : Real := mu.real (euclideanSecondDirectionEvent euclideanFarRadius)
  have ha : 0 < a := by
    exact ENNReal.toReal_pos sel_f2_commonlaw_euclidean.2.ne'
      (measure_ne_top mu _)
  have hb : 0 < b := by
    exact ENNReal.toReal_pos euclideanFarEvents_positive.1.ne'
      (measure_ne_top mu _)
  have hc : 0 < c := by
    exact ENNReal.toReal_pos euclideanFarEvents_positive.2.ne'
      (measure_ne_top mu _)
  obtain ⟨epsilon, hepsilonPos, hepsilonLt, hfirst, hsecond, horder⟩ :=
    exists_positive_twoShell_reversal ha hb hc
  let law : TwoShellSphericalLaw EuclideanUnitSphere :=
    { angularLaw := euclideanSphericalLaw
      nearRadius := euclideanShellRadius
      farRadius := euclideanFarRadius
      nearRadius_pos := euclideanShellRadius_pos
      farRadius_pos := euclideanFarRadius_pos
      nearRadius_lt_farRadius := by
        exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      farWeight := epsilon
      farWeight_pos := hepsilonPos
      farWeight_lt_one := hepsilonLt }
  refine ⟨law, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simpa [TwoShellSphericalLaw.eventProbability, law, mu, a, b] using hfirst
  · have hnearZero : mu.real
        (euclideanSecondDirectionEvent euclideanShellRadius) = 0 := by
      exact (measureReal_eq_zero_iff (measure_ne_top mu _)).2
        sel_f2_commonlaw_euclidean.1
    simpa [TwoShellSphericalLaw.eventProbability, law, mu, c, hnearZero] using
      hsecond
  · have hnearZero : mu.real
        (euclideanSecondDirectionEvent euclideanShellRadius) = 0 := by
      exact (measureReal_eq_zero_iff (measure_ne_top mu _)).2
        sel_f2_commonlaw_euclidean.1
    simpa [TwoShellSphericalLaw.eventProbability, law, mu, a, b, c,
      hnearZero] using horder

theorem sel_f2_common_twoShell_positive_reversal_frobenius :
    ∃ law : TwoShellSphericalLaw EuclideanUnitSphere,
      law.angularLaw = frobeniusSphericalLaw ∧
      law.nearRadius = frobeniusShellRadius ∧
      law.farRadius = frobeniusFarRadius ∧
      0 < law.eventProbability frobeniusFirstDirectionEvent ∧
      0 < law.eventProbability frobeniusSecondDirectionEvent ∧
      law.eventProbability frobeniusSecondDirectionEvent <
        law.eventProbability frobeniusFirstDirectionEvent := by
  let mu : Measure EuclideanUnitSphere := frobeniusSphericalLaw
  let a : Real := mu.real (frobeniusFirstDirectionEvent frobeniusShellRadius)
  let b : Real := mu.real (frobeniusFirstDirectionEvent frobeniusFarRadius)
  let c : Real := mu.real (frobeniusSecondDirectionEvent frobeniusFarRadius)
  have ha : 0 < a := by
    exact ENNReal.toReal_pos sel_f2_commonlaw_frobenius.2.ne'
      (measure_ne_top mu _)
  have hb : 0 < b := by
    exact ENNReal.toReal_pos frobeniusFarEvents_positive.1.ne'
      (measure_ne_top mu _)
  have hc : 0 < c := by
    exact ENNReal.toReal_pos frobeniusFarEvents_positive.2.ne'
      (measure_ne_top mu _)
  obtain ⟨epsilon, hepsilonPos, hepsilonLt, hfirst, hsecond, horder⟩ :=
    exists_positive_twoShell_reversal ha hb hc
  let law : TwoShellSphericalLaw EuclideanUnitSphere :=
    { angularLaw := frobeniusSphericalLaw
      nearRadius := frobeniusShellRadius
      farRadius := frobeniusFarRadius
      nearRadius_pos := frobeniusShellRadius_pos
      farRadius_pos := frobeniusFarRadius_pos
      nearRadius_lt_farRadius := by
        exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      farWeight := epsilon
      farWeight_pos := hepsilonPos
      farWeight_lt_one := hepsilonLt }
  refine ⟨law, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simpa [TwoShellSphericalLaw.eventProbability, law, mu, a, b] using hfirst
  · have hnearZero : mu.real
        (frobeniusSecondDirectionEvent frobeniusShellRadius) = 0 := by
      exact (measureReal_eq_zero_iff (measure_ne_top mu _)).2
        sel_f2_commonlaw_frobenius.1
    simpa [TwoShellSphericalLaw.eventProbability, law, mu, c, hnearZero] using
      hsecond
  · have hnearZero : mu.real
        (frobeniusSecondDirectionEvent frobeniusShellRadius) = 0 := by
      exact (measureReal_eq_zero_iff (measure_ne_top mu _)).2
        sel_f2_commonlaw_frobenius.1
    simpa [TwoShellSphericalLaw.eventProbability, law, mu, a, b, c,
      hnearZero] using horder

/-- The source-facing common-law result: in both registered metrics there is
one two-atom radial law, with one common angular law across the compared
inputs, under which both named selected-output errors are positive and their
probability order is the strict reverse of the printed corollary. -/
theorem sel_f2_common_twoShell_positive_reversal :
    (∃ law : TwoShellSphericalLaw EuclideanUnitSphere,
      law.angularLaw = euclideanSphericalLaw ∧
      0 < law.eventProbability euclideanFirstDirectionEvent ∧
      0 < law.eventProbability euclideanSecondDirectionEvent ∧
      law.eventProbability euclideanSecondDirectionEvent <
        law.eventProbability euclideanFirstDirectionEvent) ∧
    (∃ law : TwoShellSphericalLaw EuclideanUnitSphere,
      law.angularLaw = frobeniusSphericalLaw ∧
      0 < law.eventProbability frobeniusFirstDirectionEvent ∧
      0 < law.eventProbability frobeniusSecondDirectionEvent ∧
      law.eventProbability frobeniusSecondDirectionEvent <
        law.eventProbability frobeniusFirstDirectionEvent) := by
  constructor
  · obtain ⟨law, hangular, hnear, hfar, hfirst, hsecond, horder⟩ :=
      sel_f2_common_twoShell_positive_reversal_euclidean
    exact ⟨law, hangular, hfirst, hsecond, horder⟩
  · obtain ⟨law, hangular, hnear, hfar, hfirst, hsecond, horder⟩ :=
      sel_f2_common_twoShell_positive_reversal_frobenius
    exact ⟨law, hangular, hfirst, hsecond, horder⟩

end

end PhonologicalCalculus.Selection
