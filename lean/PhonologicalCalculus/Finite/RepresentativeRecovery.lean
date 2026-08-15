import PhonologicalCalculus.Finite.OrbitRecovery
import Mathlib.Tactic

/-!
# Representative recovery under complete action policies

Raw representative recovery is stronger than recovery of semantic orbits.  A
recovery map must be injective on raw representatives, its target image must
remain stable under every requested action, and the inverse must commute with
the corresponding source action.  This module proves the exact finite
proof-witness equivalence.
-/

namespace PhonologicalCalculus

/-- Every requested target action maps the raw image back into that image. -/
def TargetImageStable {A X Y : Type*} (weakening : X → Y)
    (targetAction : A → Y → Y) : Prop :=
  ∀ action y, y ∈ Set.range weakening →
    targetAction action y ∈ Set.range weakening

/-- The weakening commutes with every declared source/target action pair. -/
def ActionLiftCoherent {A X Y : Type*} (weakening : X → Y)
    (sourceAction : A → X → X) (targetAction : A → Y → Y) : Prop :=
  ∀ action x,
    weakening (sourceAction action x) =
      targetAction action (weakening x)

/-- A representative-recovery proof witness consists of a stable target image,
a raw inverse, and commutation of that inverse with every requested action. -/
def RepresentativeRecoveryExists {A X Y : Type*} (weakening : X → Y)
    (sourceAction : A → X → X) (targetAction : A → Y → Y) : Prop :=
  ∃ stable : TargetImageStable weakening targetAction,
    ∃ inverse : Set.range weakening → X,
      (∀ x, inverse ⟨weakening x, ⟨x, rfl⟩⟩ = x) ∧
      (∀ action y,
        inverse
          ⟨targetAction action y.1,
            stable action y.1 y.property⟩ =
          sourceAction action (inverse y))

/-- A left inverse on the range also satisfies the range-side inverse
equation. -/
theorem range_rightInverse_of_leftInverse {X Y : Type*} (weakening : X → Y)
    (inverse : Set.range weakening → X)
    (leftInverse :
      ∀ x, inverse ⟨weakening x, ⟨x, rfl⟩⟩ = x) :
    ∀ y, weakening (inverse y) = y.1 := by
  rintro ⟨y, ⟨x, rfl⟩⟩
  exact congrArg weakening (leftInverse x)

/-- Representative recovery exists exactly under raw injectivity, target-image
stability, and coherent action lifting. -/
theorem representativeRecovery_iff
    {A X Y : Type*} (weakening : X → Y)
    (sourceAction : A → X → X) (targetAction : A → Y → Y) :
    RepresentativeRecoveryExists weakening sourceAction targetAction ↔
      Function.Injective weakening ∧
      TargetImageStable weakening targetAction ∧
      ActionLiftCoherent weakening sourceAction targetAction := by
  constructor
  · rintro ⟨stable, inverse, leftInverse, inverseCoherent⟩
    have hInjective : Function.Injective weakening := by
      intro x y hxy
      calc
        x = inverse ⟨weakening x, ⟨x, rfl⟩⟩ := (leftInverse x).symm
        _ = inverse ⟨weakening y, ⟨y, rfl⟩⟩ := by congr
        _ = y := leftInverse y
    refine ⟨hInjective, stable, ?_⟩
    intro action x
    let sourcePoint : Set.range weakening :=
      ⟨weakening x, ⟨x, rfl⟩⟩
    let targetPoint : Set.range weakening :=
      ⟨targetAction action (weakening x),
        stable action (weakening x) ⟨x, rfl⟩⟩
    have hInverse := inverseCoherent action sourcePoint
    have hTarget : weakening (inverse targetPoint) = targetPoint.1 :=
      range_rightInverse_of_leftInverse weakening inverse leftInverse targetPoint
    have hSource : inverse sourcePoint = x := leftInverse x
    calc
      weakening (sourceAction action x) =
          weakening (sourceAction action (inverse sourcePoint)) := by
            rw [hSource]
      _ = weakening (inverse targetPoint) := by
            rw [hInverse]
      _ = targetAction action (weakening x) := hTarget
  · rintro ⟨hInjective, stable, coherent⟩
    let inverse : Set.range weakening → X :=
      fun y => Classical.choose y.property
    have leftInverse :
        ∀ x, inverse ⟨weakening x, ⟨x, rfl⟩⟩ = x := by
      intro x
      apply hInjective
      exact Classical.choose_spec
        (show weakening x ∈ Set.range weakening from ⟨x, rfl⟩)
    have rightInverse : ∀ y, weakening (inverse y) = y.1 :=
      range_rightInverse_of_leftInverse weakening inverse leftInverse
    refine ⟨stable, inverse, leftInverse, ?_⟩
    intro action y
    apply hInjective
    calc
      weakening
          (inverse
            ⟨targetAction action y.1,
              stable action y.1 y.property⟩) =
          targetAction action y.1 := rightInverse _
      _ = targetAction action (weakening (inverse y)) := by
            rw [rightInverse]
      _ = weakening (sourceAction action (inverse y)) :=
            (coherent action (inverse y)).symm

/-- The target-image test is logically prior to restricting the target policy:
an outbound action supplies an explicit failure witness. -/
theorem representativeRecovery_requires_target_stability
    {A X Y : Type*} {weakening : X → Y}
    {sourceAction : A → X → X} {targetAction : A → Y → Y}
    (recovery :
      RepresentativeRecoveryExists weakening sourceAction targetAction) :
    TargetImageStable weakening targetAction :=
  (representativeRecovery_iff weakening sourceAction targetAction).1 recovery |>.2.1

def identityBoolAction (_ : Bool) (value : Bool) : Bool := value

/-- Exact stable coherent inverse fixture. -/
theorem fin_a2_proof_01 :
    RepresentativeRecoveryExists id identityBoolAction identityBoolAction := by
  apply (representativeRecovery_iff id identityBoolAction identityBoolAction).2
  refine ⟨Function.injective_id, ?_, ?_⟩
  · intro action y hy
    exact hy
  · intro action x
    rfl

def outboundWeakening : Bool → Fin 4
  | false => 0
  | true => 1

def outboundTargetSwap (_ : Unit) (value : Fin 4) : Fin 4 :=
  ⟨(value.1 + 2) % 4, Nat.mod_lt _ (by norm_num)⟩

/-- Exact outbound target action: the image point zero is sent to point two,
which is outside the two-point raw image. -/
theorem fin_a2_outbound_02 :
    outboundTargetSwap () (outboundWeakening false) = 2 ∧
      ¬TargetImageStable outboundWeakening outboundTargetSwap := by
  constructor
  · rfl
  · intro stable
    obtain ⟨source, hSource⟩ :=
      stable () (outboundWeakening false) ⟨false, rfl⟩
    cases source <;> norm_num [outboundTargetSwap, outboundWeakening] at hSource

/-- Identity and composition coherence for a complete Boolean action policy. -/
theorem fin_a2_coherence_03 :
    ActionLiftCoherent id identityBoolAction identityBoolAction ∧
      (∀ value, identityBoolAction false value = value) ∧
      (∀ first second value,
        identityBoolAction first (identityBoolAction second value) =
          identityBoolAction second value) := by
  simp [ActionLiftCoherent, identityBoolAction]

/-- Integrated representative-recovery theorem. -/
theorem fin_a2_representativeRecovery
    {A X Y : Type*} (weakening : X → Y)
    (sourceAction : A → X → X) (targetAction : A → Y → Y) :
    RepresentativeRecoveryExists weakening sourceAction targetAction ↔
      Function.Injective weakening ∧
      TargetImageStable weakening targetAction ∧
      ActionLiftCoherent weakening sourceAction targetAction :=
  representativeRecovery_iff weakening sourceAction targetAction

end PhonologicalCalculus
