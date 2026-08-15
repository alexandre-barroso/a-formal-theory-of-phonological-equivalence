import PhonologicalCalculus.Foundation.Finite

/-!
# Finite semantic-orbit recovery

For a finite induced map, collision freedom, injectivity, and invertibility on
the reachable image are equivalent.  The proofs are representation-neutral:
the elements may be semantic orbits, provided that the action-respecting
quotient map has already been shown well defined.
-/

namespace PhonologicalCalculus

/-- An inverse on the reachable image with both inverse equations written
explicitly. -/
def HasTwoSidedInverseOnRange {X Y : Type*} (f : X → Y) : Prop :=
  ∃ inverse : Set.range f → X,
    (∀ x, inverse ⟨f x, ⟨x, rfl⟩⟩ = x) ∧
    (∀ y, (⟨f (inverse y), ⟨inverse y, rfl⟩⟩ : Set.range f) = y)

/-- A left inverse on the range automatically satisfies the range-side
inverse equation. -/
theorem hasTwoSidedInverseOnRange_iff_injective {X Y : Type*} (f : X → Y) :
    HasTwoSidedInverseOnRange f ↔ Function.Injective f := by
  constructor
  · rintro ⟨inverse, hLeft, _⟩ x y hxy
    calc
      x = inverse ⟨f x, ⟨x, rfl⟩⟩ := (hLeft x).symm
      _ = inverse ⟨f y, ⟨y, rfl⟩⟩ := by congr
      _ = y := hLeft y
  · intro hInjective
    let inverse : Set.range f → X := fun y => Classical.choose y.property
    have hLeft : ∀ x, inverse ⟨f x, ⟨x, rfl⟩⟩ = x := by
      intro x
      apply hInjective
      exact Classical.choose_spec
        (show f x ∈ Set.range f from ⟨x, rfl⟩)
    refine ⟨inverse, hLeft, ?_⟩
    rintro ⟨y, ⟨x, rfl⟩⟩
    apply Subtype.ext
    simp only
    exact congrArg f (hLeft x)

/-- An inverse on the reachable image is unique once its source-side equation
is fixed. -/
theorem inverseOnRange_unique {X Y : Type*} (f : X → Y)
    (first second : Set.range f → X)
    (hFirst : ∀ x, first ⟨f x, ⟨x, rfl⟩⟩ = x)
    (hSecond : ∀ x, second ⟨f x, ⟨x, rfl⟩⟩ = x) :
    first = second := by
  funext y
  obtain ⟨x, hx⟩ := y.property
  have hy : y = ⟨f x, ⟨x, rfl⟩⟩ := by
    apply Subtype.ext
    exact hx.symm
  rw [hy, hFirst, hSecond]

/-- The complete four-way recovery equivalence for a finite induced map. -/
theorem finiteOrbitRecovery_equivalences
    {X Y : Type*} [Fintype X] [DecidableEq X] [DecidableEq Y]
    (orbitMap : X → Y) :
    (CollisionSet orbitMap = ∅ ↔ Function.Injective orbitMap) ∧
    (Function.Injective orbitMap ↔ HasInverseOnRange orbitMap) ∧
    (HasInverseOnRange orbitMap ↔ HasTwoSidedInverseOnRange orbitMap) := by
  refine ⟨collisionSet_empty_iff_injective orbitMap,
    (hasInverseOnRange_iff_injective orbitMap).symm, ?_⟩
  rw [hasInverseOnRange_iff_injective,
    hasTwoSidedInverseOnRange_iff_injective]

/-- The empty source has an empty reachable image; any recovery statement on
that image is therefore vacuous. -/
theorem range_empty_of_isEmpty {X Y : Type*} [IsEmpty X] (f : X → Y) :
    Set.range f = ∅ := by
  ext y
  constructor
  · rintro ⟨x, _⟩
    exact isEmptyElim x
  · simp

/-- Equivariance is the proof that a declared action commutes with the
induced weakening. -/
def Equivariant {A X Y : Type*} (sourceAction : A → X → X)
    (targetAction : A → Y → Y) (f : X → Y) : Prop :=
  ∀ action x, f (sourceAction action x) = targetAction action (f x)

theorem equivariant_identity {A X : Type*} (action : A → X → X) :
    Equivariant action action id := by
  intro a x
  rfl

/-- A weakening is admissible on semantic orbits when it preserves the
source and target orbit equivalence relations. -/
def OrbitMapRespects {X Y : Type*} (source : Setoid X) (target : Setoid Y)
    (weakening : X → Y) : Prop :=
  ∀ ⦃x y⦄, source.r x y → target.r (weakening x) (weakening y)

/-- The induced semantic-orbit map obtained from an orbit-respecting
weakening.  Its construction is proof-carrying: a map that does not preserve
the declared relations cannot be supplied to this definition. -/
def inducedOrbitMap {X Y : Type*} (source : Setoid X) (target : Setoid Y)
    (weakening : X → Y) (respects : OrbitMapRespects source target weakening) :
    Quotient source → Quotient target :=
  Quotient.map weakening respects

/-- The induced map sends each source orbit to the target orbit of the
weakened representative. -/
theorem inducedOrbitMap_mk {X Y : Type*} (source : Setoid X)
    (target : Setoid Y) (weakening : X → Y)
    (respects : OrbitMapRespects source target weakening) (x : X) :
    inducedOrbitMap source target weakening respects (Quotient.mk source x) =
      Quotient.mk target (weakening x) := by
  rfl

abbrev OrbitFixture := Bool

def orbitIdentity : OrbitFixture → OrbitFixture := id

def orbitCollision (_ : OrbitFixture) : Bool := false

/-- Exact positive recovery fixture: all four recovery predicates hold. -/
theorem fin_a1_inverse_01 :
    CollisionSet orbitIdentity = ∅ ∧
      Function.Injective orbitIdentity ∧
      HasInverseOnRange orbitIdentity ∧
      HasTwoSidedInverseOnRange orbitIdentity := by
  have hInjective : Function.Injective orbitIdentity := by
    intro x y h
    exact h
  exact ⟨(collisionSet_empty_iff_injective orbitIdentity).2 hInjective,
    hInjective, (hasInverseOnRange_iff_injective orbitIdentity).2 hInjective,
    (hasTwoSidedInverseOnRange_iff_injective orbitIdentity).2 hInjective⟩

/-- Exact empty-image boundary. -/
theorem fin_a1_empty_02 :
    Set.range (fun x : Empty => x) = ∅ := by
  exact range_empty_of_isEmpty _

/-- Exact action/equivariance fixture for the identity-induced orbit map. -/
theorem fin_a1_equivariance_03 :
    Equivariant (fun _ : Bool => orbitIdentity)
      (fun _ : Bool => orbitIdentity) orbitIdentity := by
  exact equivariant_identity _

/-- Exact negative fixture: two source orbits collide, so injectivity and both
forms of recovery fail together. -/
theorem fin_a1_negative_04 :
    CollisionSet orbitCollision ≠ ∅ ∧
      ¬Function.Injective orbitCollision ∧
      ¬HasInverseOnRange orbitCollision ∧
    ¬HasTwoSidedInverseOnRange orbitCollision := by
  have hNotInjective : ¬Function.Injective orbitCollision := by
    intro hInjective
    have hFalse := hInjective
      (show orbitCollision false = orbitCollision true from rfl)
    cases hFalse
  refine ⟨?_, hNotInjective, ?_, ?_⟩
  · intro hEmpty
    exact hNotInjective
      ((collisionSet_empty_iff_injective orbitCollision).1 hEmpty)
  · exact fun hInverse => hNotInjective
      ((hasInverseOnRange_iff_injective orbitCollision).1 hInverse)
  · exact fun hInverse => hNotInjective
      ((hasTwoSidedInverseOnRange_iff_injective orbitCollision).1 hInverse)

/-- Registered semantic-orbit recovery theorem, including the nonempty-image
boundary needed for a positive recovery claim. -/
theorem fin_a1_semanticOrbitRecovery
    {X Y : Type*} [Fintype X] [DecidableEq X] [DecidableEq Y]
    [Nonempty X] (orbitMap : X → Y) :
    (CollisionSet orbitMap = ∅ ↔ HasTwoSidedInverseOnRange orbitMap) ∧
      (Set.range orbitMap).Nonempty := by
  constructor
  · rw [collisionSet_empty_iff_injective,
      hasTwoSidedInverseOnRange_iff_injective]
  · exact nonempty_range_of_nonempty orbitMap

/-- Integrated quotient-level recovery theorem.  Relation preservation first
constructs the induced orbit map; collision freedom is then equivalent to a
unique two-sided inverse on its reachable image, while source nonemptiness
keeps the positive recovery claim nonvacuous. -/
theorem fin_a1_semanticOrbitRecovery_from_weakening
    {X Y : Type*} (source : Setoid X) (target : Setoid Y)
    (weakening : X → Y) (respects : OrbitMapRespects source target weakening)
    [Fintype (Quotient source)] [DecidableEq (Quotient source)]
    [DecidableEq (Quotient target)] [Nonempty X] :
    let orbitMap := inducedOrbitMap source target weakening respects
    (CollisionSet orbitMap = ∅ ↔ HasTwoSidedInverseOnRange orbitMap) ∧
      (Set.range orbitMap).Nonempty := by
  let orbitMap := inducedOrbitMap source target weakening respects
  have quotientNonempty : Nonempty (Quotient source) :=
    ⟨Quotient.mk source (Classical.choice (inferInstance : Nonempty X))⟩
  letI : Nonempty (Quotient source) := quotientNonempty
  exact fin_a1_semanticOrbitRecovery orbitMap

end PhonologicalCalculus
