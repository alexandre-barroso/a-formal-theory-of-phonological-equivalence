                 
import PhonologicalCalculus.Finite.OrbitRecovery
import Mathlib.Tactic

namespace PhonologicalCalculus

def TargetImageStable {A X Y : Type*} (weakening : X → Y)
    (targetAction : A → Y → Y) : Prop :=
  ∀ action y, y ∈ Set.range weakening →
    targetAction action y ∈ Set.range weakening

def ActionLiftCoherent {A X Y : Type*} (weakening : X → Y)
    (sourceAction : A → X → X) (targetAction : A → Y → Y) : Prop :=
  ∀ action x,
    weakening (sourceAction action x) =
      targetAction action (weakening x)

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

theorem range_rightInverse_of_leftInverse {X Y : Type*} (weakening : X → Y)
    (inverse : Set.range weakening → X)
    (leftInverse :
      ∀ x, inverse ⟨weakening x, ⟨x, rfl⟩⟩ = x) :
    ∀ y, weakening (inverse y) = y.1 := by
  rintro ⟨y, ⟨x, rfl⟩⟩
  exact congrArg weakening (leftInverse x)

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

theorem representativeRecovery_requires_target_stability
    {A X Y : Type*} {weakening : X → Y}
    {sourceAction : A → X → X} {targetAction : A → Y → Y}
    (recovery :
      RepresentativeRecoveryExists weakening sourceAction targetAction) :
    TargetImageStable weakening targetAction :=
  (representativeRecovery_iff weakening sourceAction targetAction).1 recovery |>.2.1

def identityBoolAction (_ : Bool) (value : Bool) : Bool := value

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

theorem fin_a2_outbound_02 :
    outboundTargetSwap () (outboundWeakening false) = 2 ∧
      ¬TargetImageStable outboundWeakening outboundTargetSwap := by
  constructor
  · rfl
  · intro stable
    obtain ⟨source, hSource⟩ :=
      stable () (outboundWeakening false) ⟨false, rfl⟩
    cases source <;> norm_num [outboundTargetSwap, outboundWeakening] at hSource

theorem fin_a2_coherence_03 :
    ActionLiftCoherent id identityBoolAction identityBoolAction ∧
      (∀ value, identityBoolAction false value = value) ∧
      (∀ first second value,
        identityBoolAction first (identityBoolAction second value) =
          identityBoolAction second value) := by
  simp [ActionLiftCoherent, identityBoolAction]

theorem fin_a2_representativeRecovery
    {A X Y : Type*} (weakening : X → Y)
    (sourceAction : A → X → X) (targetAction : A → Y → Y) :
    RepresentativeRecoveryExists weakening sourceAction targetAction ↔
      Function.Injective weakening ∧
      TargetImageStable weakening targetAction ∧
      ActionLiftCoherent weakening sourceAction targetAction :=
  representativeRecovery_iff weakening sourceAction targetAction

end PhonologicalCalculus
