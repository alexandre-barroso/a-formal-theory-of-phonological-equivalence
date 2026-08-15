import PhonologicalCalculus.Selection.Regions
import Mathlib.Tactic

/-!
# Complete-binary selected-output counterexample

This module checks the complete score rows of the binary Harmonic Grammar,
defines its two five-coordinate selected-output regions, and proves the exact
Euclidean and Frobenius onset distances by global quadratic lower bounds.
It also supplies explicit rational shell points, relative open neighborhoods,
and proofs that the later region is empty on each chosen shell.

The conversion from a nonempty relative open patch to positive normalized
spherical surface measure is not asserted here.
-/

namespace PhonologicalCalculus.Selection

/-! ## Complete binary score calculation -/

structure BinaryVector where
  first : ℤ
  second : ℤ
  deriving DecidableEq, Repr

structure BinaryMatrix where
  firstFirst : ℤ
  firstSecond : ℤ
  secondFirst : ℤ
  secondSecond : ℤ
  deriving DecidableEq, Repr

def bilinear (left : BinaryVector) (matrix : BinaryMatrix)
    (right : BinaryVector) : ℤ :=
  left.first * matrix.firstFirst * right.first +
    left.first * matrix.firstSecond * right.second +
    left.second * matrix.secondFirst * right.first +
    left.second * matrix.secondSecond * right.second

def binaryHarmony (input output : BinaryVector)
    (faithfulness markedness : BinaryMatrix) : ℤ :=
  bilinear input faithfulness output + bilinear output markedness output

def firstInput : BinaryVector := ⟨1, 0⟩
def secondInput : BinaryVector := ⟨0, 1⟩

def zeroOutput : BinaryVector := ⟨0, 0⟩
def firstOutput : BinaryVector := ⟨1, 0⟩
def secondOutput : BinaryVector := ⟨0, 1⟩
def jointOutput : BinaryVector := ⟨1, 1⟩

def counterexampleFaithfulness : BinaryMatrix :=
  ⟨20, -17, 3, 17⟩

def counterexampleMarkedness : BinaryMatrix :=
  ⟨0, -1, -1, 0⟩

def completeOutputs : List BinaryVector :=
  [zeroOutput, firstOutput, secondOutput, jointOutput]

def scoreRow (input : BinaryVector) : List ℤ :=
  completeOutputs.map
    (fun output => binaryHarmony input output
      counterexampleFaithfulness counterexampleMarkedness)

/-- `SEL-F2.SCORES.01`: direct multiplication gives the two complete intact
score rows, with unique winners `firstOutput` and `jointOutput`. -/
theorem sel_f2_scores_01 :
    scoreRow firstInput = [0, 20, -17, 1] ∧
      scoreRow secondInput = [0, 3, 17, 18] ∧
      (20 : ℤ) > 0 ∧ 20 > -17 ∧ 20 > 1 ∧
      (18 : ℤ) > 0 ∧ 18 > 3 ∧ 18 > 17 := by
  decide

/-- The printed equifaithfulness and markedness comparisons, together with
the equal independent-coordinate pairwise normal lengths. -/
theorem matchedPairPremises :
    bilinear firstInput counterexampleFaithfulness firstOutput = 20 ∧
      bilinear secondInput counterexampleFaithfulness jointOutput = 20 ∧
      bilinear firstInput counterexampleFaithfulness jointOutput = 3 ∧
      bilinear secondInput counterexampleFaithfulness firstOutput = 3 ∧
      bilinear firstOutput counterexampleMarkedness firstOutput = 0 ∧
      bilinear jointOutput counterexampleMarkedness jointOutput = -2 ∧
      (19 : ℤ) > 15 ∧
      (1 : ℤ) ^ 2 + 2 ^ 2 = 5 ∧
      ((-1 : ℤ) ^ 2 + (-2 : ℤ) ^ 2 = 5) := by
  decide

/-! ## Five-coordinate selected-output regions -/

structure Disruption where
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ
  e : ℝ

def euclideanSquared (point : Disruption) : ℝ :=
  point.a ^ 2 + point.b ^ 2 + point.c ^ 2 + point.d ^ 2 + point.e ^ 2

/-- Frobenius metric on the symmetric perturbation subspace: the independent
off-diagonal coordinate is counted twice. -/
def frobeniusSquared (point : Disruption) : ℝ :=
  point.a ^ 2 + point.b ^ 2 + point.c ^ 2 + point.d ^ 2 + 2 * point.e ^ 2

def firstSelectedClosure (point : Disruption) : Prop :=
  0 ≤ 1 + point.a + point.b + 2 * point.e ∧
    19 ≤ point.b + 2 * point.e ∧
    0 ≤ 18 + point.a + 2 * point.e

def firstSelectedStrict (point : Disruption) : Prop :=
  0 < 1 + point.a + point.b + 2 * point.e ∧
    19 < point.b + 2 * point.e ∧
    0 < 18 + point.a + 2 * point.e

def secondSelectedClosure (point : Disruption) : Prop :=
  -3 ≤ point.c ∧
    14 ≤ point.c - point.d ∧
    15 ≤ -point.d - 2 * point.e

def secondSelectedStrict (point : Disruption) : Prop :=
  -3 < point.c ∧
    14 < point.c - point.d ∧
    15 < -point.d - 2 * point.e

theorem firstSelectedStrict_toClosure {point : Disruption}
    (h : firstSelectedStrict point) : firstSelectedClosure point := by
  rcases h with ⟨h₁, h₂, h₃⟩
  exact ⟨h₁.le, h₂.le, h₃.le⟩

theorem secondSelectedStrict_toClosure {point : Disruption}
    (h : secondSelectedStrict point) : secondSelectedClosure point := by
  rcases h with ⟨h₁, h₂, h₃⟩
  exact ⟨h₁.le, h₂.le, h₃.le⟩

/-! ## Euclidean projections -/

noncomputable def euclideanFirstProjection : Disruption :=
  ⟨0, 19 / 5, 0, 0, 38 / 5⟩

noncomputable def euclideanSecondProjection : Disruption :=
  ⟨0, 0, 55 / 9, -71 / 9, -32 / 9⟩

theorem euclidean_first_lower_bound {point : Disruption}
    (hregion : firstSelectedClosure point) :
    361 / 5 ≤ euclideanSquared point := by
  rcases hregion with ⟨h₁, hmain, h₃⟩
  have ha := sq_nonneg point.a
  have hc := sq_nonneg point.c
  have hd := sq_nonneg point.d
  have horth := sq_nonneg (2 * point.b - point.e)
  have hsum : 0 ≤ point.b + 2 * point.e + 19 := by linarith
  have hthreshold :
      0 ≤ (point.b + 2 * point.e - 19) *
        (point.b + 2 * point.e + 19) :=
    mul_nonneg (sub_nonneg.mpr hmain) hsum
  unfold euclideanSquared
  nlinarith

theorem euclidean_second_lower_bound {point : Disruption}
    (hregion : secondSelectedClosure point) :
    1010 / 9 ≤ euclideanSquared point := by
  rcases hregion with ⟨hfirst, hone, htwo⟩
  have ha := sq_nonneg point.a
  have hb := sq_nonneg point.b
  have hc := sq_nonneg (point.c - 55 / 9)
  have hd := sq_nonneg (point.d + 71 / 9)
  have he := sq_nonneg (point.e + 32 / 9)
  have hdot :
      1010 / 9 ≤
        (55 / 9) * point.c - (71 / 9) * point.d - (32 / 9) * point.e := by
    nlinarith
  unfold euclideanSquared
  nlinarith

/-- `SEL-F2.EUCLIDEAN.02`: exact feasible projections, global lower bounds,
positive active multipliers, and the reversed onset gap. -/
theorem sel_f2_euclidean_02 :
    firstSelectedClosure euclideanFirstProjection ∧
      euclideanSquared euclideanFirstProjection = 361 / 5 ∧
      (∀ point, firstSelectedClosure point →
        361 / 5 ≤ euclideanSquared point) ∧
      secondSelectedClosure euclideanSecondProjection ∧
      euclideanSquared euclideanSecondProjection = 1010 / 9 ∧
      (∀ point, secondSelectedClosure point →
        1010 / 9 ≤ euclideanSquared point) ∧
      1010 / 9 - 361 / 5 = 1801 / 45 ∧
      (0 : ℝ) < 16 / 9 ∧ (0 : ℝ) < 55 / 9 := by
  refine ⟨?_, ?_, (fun point h => euclidean_first_lower_bound h), ?_, ?_,
    (fun point h => euclidean_second_lower_bound h), ?_, ?_, ?_⟩ <;>
    norm_num [firstSelectedClosure, secondSelectedClosure,
      euclideanSquared, euclideanFirstProjection, euclideanSecondProjection]

/-! ## Frobenius projections -/

noncomputable def frobeniusFirstProjection : Disruption :=
  ⟨0, 19 / 3, 0, 0, 19 / 3⟩

noncomputable def frobeniusSecondProjection : Disruption :=
  ⟨0, 0, 27 / 5, -43 / 5, -16 / 5⟩

theorem frobenius_first_lower_bound {point : Disruption}
    (hregion : firstSelectedClosure point) :
    361 / 3 ≤ frobeniusSquared point := by
  rcases hregion with ⟨h₁, hmain, h₃⟩
  have ha := sq_nonneg point.a
  have hc := sq_nonneg point.c
  have hd := sq_nonneg point.d
  have horth := sq_nonneg (point.b - point.e)
  have hsum : 0 ≤ point.b + 2 * point.e + 19 := by linarith
  have hthreshold :
      0 ≤ (point.b + 2 * point.e - 19) *
        (point.b + 2 * point.e + 19) :=
    mul_nonneg (sub_nonneg.mpr hmain) hsum
  unfold frobeniusSquared
  nlinarith

theorem frobenius_second_lower_bound {point : Disruption}
    (hregion : secondSelectedClosure point) :
    618 / 5 ≤ frobeniusSquared point := by
  rcases hregion with ⟨hfirst, hone, htwo⟩
  have ha := sq_nonneg point.a
  have hb := sq_nonneg point.b
  have hc := sq_nonneg (point.c - 27 / 5)
  have hd := sq_nonneg (point.d + 43 / 5)
  have he := sq_nonneg (point.e + 16 / 5)
  have hdot :
      618 / 5 ≤
        (27 / 5) * point.c - (43 / 5) * point.d - (32 / 5) * point.e := by
    nlinarith
  unfold frobeniusSquared
  nlinarith

/-- `SEL-F2.FROBENIUS.03`: the induced metric has exact onset squares
`361/3` and `618/5`, with positive reversed gap `49/15`. -/
theorem sel_f2_frobenius_03 :
    firstSelectedClosure frobeniusFirstProjection ∧
      frobeniusSquared frobeniusFirstProjection = 361 / 3 ∧
      (∀ point, firstSelectedClosure point →
        361 / 3 ≤ frobeniusSquared point) ∧
      secondSelectedClosure frobeniusSecondProjection ∧
      frobeniusSquared frobeniusSecondProjection = 618 / 5 ∧
      (∀ point, secondSelectedClosure point →
        618 / 5 ≤ frobeniusSquared point) ∧
      618 / 5 - 361 / 3 = 49 / 15 := by
  refine ⟨?_, ?_, (fun point h => frobenius_first_lower_bound h), ?_, ?_,
    (fun point h => frobenius_second_lower_bound h), ?_⟩ <;>
    norm_num [firstSelectedClosure, secondSelectedClosure,
      frobeniusSquared, frobeniusFirstProjection, frobeniusSecondProjection]

/-! ## Explicit separating shells and relative open patches -/

def coordinateClose (radius : ℝ) (x y : Disruption) : Prop :=
  |x.a - y.a| < radius ∧ |x.b - y.b| < radius ∧
    |x.c - y.c| < radius ∧ |x.d - y.d| < radius ∧
    |x.e - y.e| < radius

noncomputable def euclideanShellPoint : Disruption :=
  ⟨0, 4, 0, 0, 8⟩

theorem euclideanShellPatch_stable {point : Disruption}
    (hclose : coordinateClose (1 / 4) point euclideanShellPoint) :
    firstSelectedStrict point := by
  rcases hclose with ⟨ha, hb, hc, hd, he⟩
  rcases abs_lt.mp ha with ⟨haL, haU⟩
  rcases abs_lt.mp hb with ⟨hbL, hbU⟩
  rcases abs_lt.mp he with ⟨heL, heU⟩
  norm_num [euclideanShellPoint] at haL haU hbL hbU heL heU
  exact ⟨by linarith, by linarith, by linarith⟩

/-- Exact Euclidean shell geometry underlying the common-law construction:
the earlier region contains a proved relative open patch on radius square
`80`, while the later closed region is disjoint from that shell. -/
theorem euclidean_common_shell_geometry :
    euclideanSquared euclideanShellPoint = 80 ∧
      firstSelectedStrict euclideanShellPoint ∧
      (∀ point, secondSelectedClosure point →
        80 < euclideanSquared point) ∧
      (0 : ℝ) < 1 / 4 ∧
      (∀ point, coordinateClose (1 / 4) point euclideanShellPoint →
        firstSelectedStrict point) := by
  refine ⟨?_, ?_, ?_, by norm_num,
    (fun point h => euclideanShellPatch_stable h)⟩
  · norm_num [euclideanSquared, euclideanShellPoint]
  · norm_num [firstSelectedStrict, euclideanShellPoint]
  · intro point hregion
    have hlower := euclidean_second_lower_bound hregion
    linarith

noncomputable def frobeniusShellPoint : Disruption :=
  ⟨9 / 10, 127 / 20, 2 / 5, 1 / 4, 127 / 20⟩

theorem frobeniusShellPatch_stable {point : Disruption}
    (hclose : coordinateClose (1 / 100) point frobeniusShellPoint) :
    firstSelectedStrict point := by
  rcases hclose with ⟨ha, hb, hc, hd, he⟩
  rcases abs_lt.mp ha with ⟨haL, haU⟩
  rcases abs_lt.mp hb with ⟨hbL, hbU⟩
  rcases abs_lt.mp he with ⟨heL, heU⟩
  norm_num [frobeniusShellPoint] at haL haU hbL hbU heL heU
  exact ⟨by linarith, by linarith, by linarith⟩

/-- Exact Frobenius shell geometry: a rational strict point and relative open
patch occur at radius square `122`, below the later onset square `618/5`. -/
theorem frobenius_common_shell_geometry :
    frobeniusSquared frobeniusShellPoint = 122 ∧
      firstSelectedStrict frobeniusShellPoint ∧
      (∀ point, secondSelectedClosure point →
        122 < frobeniusSquared point) ∧
      (0 : ℝ) < 1 / 100 ∧
      (∀ point, coordinateClose (1 / 100) point frobeniusShellPoint →
        firstSelectedStrict point) := by
  refine ⟨?_, ?_, ?_, by norm_num,
    (fun point h => frobeniusShellPatch_stable h)⟩
  · norm_num [frobeniusSquared, frobeniusShellPoint]
  · norm_num [firstSelectedStrict, frobeniusShellPoint]
  · intro point hregion
    have hlower := frobenius_second_lower_bound hregion
    linarith

end PhonologicalCalculus.Selection
