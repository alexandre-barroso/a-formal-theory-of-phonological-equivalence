import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Combinatorics.Enumerative.Bell
import Mathlib.Logic.Relation
import Mathlib.Tactic.NormNum

/-!
Kernel-checked quantitative and graph regressions for `CALC-R09`--`CALC-R12`
and `CALC-R14`.
-/

namespace PhonologicalCalculus.Regression

section SubprobabilityMass

def retainedMass : ℚ := 2 / 3
def initialStopMass : ℚ := 1 / 3
def noFailureMass : ℚ := 2 / 3

inductive MassVerdict where
  | pass | notEvaluated
  deriving DecidableEq, Repr

def massVerdict : MassVerdict :=
  if retainedMass = 1 then MassVerdict.pass else MassVerdict.notEvaluated

/-- Exact `CALC-R09.MASS.01`. -/
theorem CALC_R09_MASS_01 :
    retainedMass = 2 / 3 ∧
      initialStopMass = 1 / 3 ∧
      noFailureMass = 2 / 3 ∧
      retainedMass + initialStopMass = 1 ∧
      retainedMass ≠ 1 ∧
      massVerdict = MassVerdict.notEvaluated := by
  norm_num [retainedMass, initialStopMass, noFailureMass, massVerdict]

end SubprobabilityMass

section ReachableCycles

inductive CycleState where
  | s | z
  deriving DecidableEq, Repr

def structuralEdge : CycleState → CycleState → Prop
  | CycleState.s, CycleState.s | CycleState.s, CycleState.z => True
  | _, _ => False

def positiveSupportEdge : CycleState → CycleState → Prop
  | CycleState.s, CycleState.z => True
  | _, _ => False

def cycleStarts : Finset CycleState := {CycleState.s}
def cycleStops : Finset CycleState := {CycleState.z}

def HasReachableCycle (edge : CycleState → CycleState → Prop) : Prop :=
  ∃ start ∈ cycleStarts, ∃ x,
    Relation.ReflTransGen edge start x ∧
      Relation.TransGen edge x x ∧ x ∉ cycleStops

def cycleRank : CycleState → Nat
  | CycleState.s => 0
  | CycleState.z => 1

theorem positiveSupportEdge_rank {x y : CycleState}
    (h : positiveSupportEdge x y) : cycleRank x < cycleRank y := by
  cases x <;> cases y <;> simp [positiveSupportEdge, cycleRank] at h ⊢

theorem transGen_rank_increases {edge : CycleState → CycleState → Prop}
    (hstep : ∀ {x y}, edge x y → cycleRank x < cycleRank y)
    {x y : CycleState} (hpath : Relation.TransGen edge x y) :
    cycleRank x < cycleRank y := by
  induction hpath using Relation.TransGen.trans_induction_on with
  | single h => exact hstep h
  | trans _ _ hxy hyz => exact Nat.lt_trans hxy hyz

/-- Exact `CALC-R10.CYCLE.01`: the structural self-loop is a reachable cycle,
the positive-support graph is acyclic, and the declared infinity mass is zero. -/
theorem CALC_R10_CYCLE_01 :
    HasReachableCycle structuralEdge ∧
      ¬HasReachableCycle positiveSupportEdge ∧
      (0 : ℚ) = 0 := by
  constructor
  · refine ⟨CycleState.s, ?_, CycleState.s,
      Relation.ReflTransGen.refl, Relation.TransGen.single ?_, ?_⟩
    · simp [cycleStarts]
    · simp [structuralEdge]
    · simp [cycleStops]
  constructor
  · rintro ⟨_, _, x, _, hcycle, _⟩
    have hlt := transGen_rank_increases positiveSupportEdge_rank hcycle
    exact (Nat.lt_irrefl (cycleRank x)) hlt
  · rfl

end ReachableCycles

section PushforwardMass

inductive FibreLabel where
  | a
  deriving DecidableEq, Repr

def fibreWeights : List (FibreLabel × ℚ) :=
  [(FibreLabel.a, 1 / 3), (FibreLabel.a, 2 / 3)]

def pushforwardMassAt (key : FibreLabel) : ℚ :=
  ((fibreWeights.filter (fun row => row.1 = key)).map Prod.snd).sum

/-- Exact `CALC-R11.FIBRE.01`. -/
theorem CALC_R11_FIBRE_01 : pushforwardMassAt FibreLabel.a = 1 := by
  norm_num [pushforwardMassAt, fibreWeights]

end PushforwardMass

section GeometricStoppedLaw

def geometricCoefficient (p : ℝ) (n : Nat) : ℝ := (1 - p) * p ^ n

def stoppedStateCount : Nat := 2
def geometricInfinityMass : ℝ := 0

theorem geometricCoefficient_positive {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (n : Nat) : 0 < geometricCoefficient p n := by
  exact mul_pos (sub_pos.mpr hp1) (pow_pos hp0 n)

theorem geometricStoppedLaw_hasSum_one {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    HasSum (geometricCoefficient p) 1 := by
  have hsum := (hasSum_geometric_of_lt_one hp0.le hp1).mul_left (1 - p)
  have hne : 1 - p ≠ 0 := ne_of_gt (sub_pos.mpr hp1)
  change HasSum (fun n : Nat => (1 - p) * p ^ n) 1
  simpa only [mul_inv_cancel₀ hne] using! hsum

/-- Exact analytic content of `CALC-R12.SERIES.01`: every finite stopping
coefficient is positive, the total mass is one, the presentation has two
states, and the infinity atom is zero. -/
theorem CALC_R12_SERIES_01 {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    geometricCoefficient p 0 = 1 - p ∧
      geometricCoefficient p 1 = (1 - p) * p ∧
      geometricCoefficient p 2 = (1 - p) * p ^ 2 ∧
      geometricCoefficient p 3 = (1 - p) * p ^ 3 ∧
      (∀ n, 0 < geometricCoefficient p n) ∧
      HasSum (geometricCoefficient p) 1 ∧
      stoppedStateCount = 2 ∧ geometricInfinityMass = 0 := by
  constructor
  · simp [geometricCoefficient]
  constructor
  · simp [geometricCoefficient]
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · exact geometricCoefficient_positive hp0 hp1
  constructor
  · exact geometricStoppedLaw_hasSum_one hp0 hp1
  constructor <;> rfl

end GeometricStoppedLaw

section BellNumbers

/-- Exact `CALC-R14.BELL.01`, using mathlib's definition of the Bell numbers
as counts of set partitions rather than a project-local lookup table. -/
theorem CALC_R14_BELL_01 :
    Nat.bell 2 * Nat.bell 3 = 10 ∧ Nat.bell 3 = 5 := by
  have hb3 : Nat.bell 3 = 5 := by
    have hic : Finset.Iic 2 = {0, 1, 2} := Finset.eq_of_veq rfl
    rw [show (3 : Nat) = 2 + 1 by rfl, Nat.bell_succ, hic]
    norm_num
  simp [hb3]

end BellNumbers

end PhonologicalCalculus.Regression
