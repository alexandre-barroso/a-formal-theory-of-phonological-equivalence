import PhonologicalCalculus.Finite.InformationLattice
import Mathlib.Tactic

         

namespace PhonologicalCalculus

universe uSort uCarrier uOperation uObservation

structure FinitarySortedSignature (SortIndex : Type uSort) where
  Operation : Type uOperation
  arity : Operation → Nat
  inputSort : (operation : Operation) → Fin (arity operation) → SortIndex
  outputSort : Operation → SortIndex

abbrev SortedArguments {SortIndex : Type uSort}
    (Carrier : SortIndex → Type uCarrier)
    (signature : FinitarySortedSignature SortIndex)
    (operation : signature.Operation) :=
  (position : Fin (signature.arity operation)) →
    Carrier (signature.inputSort operation position)

abbrev FinitarySortedOperations {SortIndex : Type uSort}
    (Carrier : SortIndex → Type uCarrier)
    (signature : FinitarySortedSignature SortIndex) :=
  (operation : signature.Operation) →
    SortedArguments Carrier signature operation →
      Option (Carrier (signature.outputSort operation))

abbrev SortedRelation {SortIndex : Type uSort}
    (Carrier : SortIndex → Type uCarrier) :=
  (sort : SortIndex) → Carrier sort → Carrier sort → Prop

def SortedRelationRefines {SortIndex : Type uSort}
    {Carrier : SortIndex → Type uCarrier}
    (finer coarser : SortedRelation Carrier) : Prop :=
  ∀ sort x y, finer sort x y → coarser sort x y

def SortedRelationIntersection {Index : Type*}
    {SortIndex : Type uSort} {Carrier : SortIndex → Type uCarrier}
    (relations : Index → SortedRelation Carrier) : SortedRelation Carrier :=
  fun sort x y => ∀ index, relations index sort x y

def SortedKernelIntersection {SortIndex : Type uSort}
    {Carrier : SortIndex → Type uCarrier}
    (first second : SortedRelation Carrier) : SortedRelation Carrier :=
  fun sort x y => first sort x y ∧ second sort x y

def ManySortedStrongCongruence {SortIndex : Type uSort}
    {Carrier : SortIndex → Type uCarrier}
    (signature : FinitarySortedSignature SortIndex)
    (operations : FinitarySortedOperations Carrier signature)
    (relation : SortedRelation Carrier) : Prop :=
  (∀ sort, Equivalence (relation sort)) ∧
    ∀ operation first second,
      (∀ position, relation (signature.inputSort operation position)
        (first position) (second position)) →
      Option.isSome (operations operation first) =
          Option.isSome (operations operation second) ∧
        ∀ firstResult secondResult,
          operations operation first = some firstResult →
          operations operation second = some secondResult →
          relation (signature.outputSort operation)
            firstResult secondResult

theorem equality_manySortedStrongCongruence
    {SortIndex : Type uSort} {Carrier : SortIndex → Type uCarrier}
    (signature : FinitarySortedSignature SortIndex)
    (operations : FinitarySortedOperations Carrier signature) :
    ManySortedStrongCongruence signature operations
      (fun _ x y => x = y) := by
  constructor
  · intro sort
    exact eq_equivalence
  · intro operation first second hArguments
    have hTuple : first = second := funext hArguments
    subst second
    refine ⟨rfl, ?_⟩
    intro firstResult secondResult hFirst hSecond
    rw [hFirst] at hSecond
    exact Option.some.inj hSecond

theorem manySortedStrongCongruence_intersection
    {Index : Type*} [Nonempty Index]
    {SortIndex : Type uSort} {Carrier : SortIndex → Type uCarrier}
    (signature : FinitarySortedSignature SortIndex)
    (operations : FinitarySortedOperations Carrier signature)
    (relations : Index → SortedRelation Carrier)
    (hStrong : ∀ index,
      ManySortedStrongCongruence signature operations (relations index)) :
    ManySortedStrongCongruence signature operations
      (SortedRelationIntersection relations) := by
  constructor
  · intro sort
    constructor
    · intro x index
      exact (hStrong index).1 sort |>.1 x
    · intro x y hxy index
      exact (hStrong index).1 sort |>.2 (hxy index)
    · intro x y z hxy hyz index
      exact (hStrong index).1 sort |>.3 (hxy index) (hyz index)
  · intro operation first second hArguments
    let witness : Index := Classical.choice inferInstance
    have hWitness := (hStrong witness).2 operation first second
      (fun position => hArguments position witness)
    refine ⟨hWitness.1, ?_⟩
    intro firstResult secondResult hFirst hSecond index
    exact (hStrong index).2 operation first second
      (fun position => hArguments position index) |>.2
        firstResult secondResult hFirst hSecond

theorem manySortedStrongCongruence_binaryIntersection
    {SortIndex : Type uSort} {Carrier : SortIndex → Type uCarrier}
    (signature : FinitarySortedSignature SortIndex)
    (operations : FinitarySortedOperations Carrier signature)
    (first second : SortedRelation Carrier)
    (hFirst : ManySortedStrongCongruence signature operations first)
    (hSecond : ManySortedStrongCongruence signature operations second) :
    ManySortedStrongCongruence signature operations
      (SortedKernelIntersection first second) := by
  constructor
  · intro sort
    constructor
    · intro x
      exact ⟨(hFirst.1 sort).1 x, (hSecond.1 sort).1 x⟩
    · intro x y hxy
      exact ⟨(hFirst.1 sort).2 hxy.1, (hSecond.1 sort).2 hxy.2⟩
    · intro x y z hxy hyz
      exact ⟨(hFirst.1 sort).3 hxy.1 hyz.1,
        (hSecond.1 sort).3 hxy.2 hyz.2⟩
  · intro operation firstArguments secondArguments hArguments
    have hFirstCompatibility := hFirst.2 operation firstArguments secondArguments
      (fun position => (hArguments position).1)
    have hSecondCompatibility := hSecond.2 operation firstArguments secondArguments
      (fun position => (hArguments position).2)
    refine ⟨hFirstCompatibility.1, ?_⟩
    intro firstResult secondResult hFirstResult hSecondResult
    exact ⟨hFirstCompatibility.2 firstResult secondResult
        hFirstResult hSecondResult,
      hSecondCompatibility.2 firstResult secondResult
        hFirstResult hSecondResult⟩

def IsGreatestSortedContextualRelation
    {SortIndex : Type uSort} {Carrier : SortIndex → Type uCarrier}
    (signature : FinitarySortedSignature SortIndex)
    (operations : FinitarySortedOperations Carrier signature)
    (kernel relation : SortedRelation Carrier) : Prop :=
  ManySortedStrongCongruence signature operations relation ∧
    SortedRelationRefines relation kernel ∧
    ∀ other,
      ManySortedStrongCongruence signature operations other →
      SortedRelationRefines other kernel →
      SortedRelationRefines other relation

theorem greatestSortedContextualRelation_intersection_iff
    {SortIndex : Type uSort} {Carrier : SortIndex → Type uCarrier}
    (signature : FinitarySortedSignature SortIndex)
    (operations : FinitarySortedOperations Carrier signature)
    (firstKernel secondKernel : SortedRelation Carrier)
    (firstRelation secondRelation jointRelation : SortedRelation Carrier)
    (hFirst : IsGreatestSortedContextualRelation signature operations
      firstKernel firstRelation)
    (hSecond : IsGreatestSortedContextualRelation signature operations
      secondKernel secondRelation)
    (hJoint : IsGreatestSortedContextualRelation signature operations
      (SortedKernelIntersection firstKernel secondKernel) jointRelation) :
    ∀ sort x y,
      jointRelation sort x y ↔
        firstRelation sort x y ∧ secondRelation sort x y := by
  have hJointBelowFirst : SortedRelationRefines jointRelation firstKernel :=
    fun sort x y hxy => (hJoint.2.1 sort x y hxy).1
  have hJointBelowSecond : SortedRelationRefines jointRelation secondKernel :=
    fun sort x y hxy => (hJoint.2.1 sort x y hxy).2
  have hJointToFirst : SortedRelationRefines jointRelation firstRelation :=
    hFirst.2.2 jointRelation hJoint.1 hJointBelowFirst
  have hJointToSecond : SortedRelationRefines jointRelation secondRelation :=
    hSecond.2.2 jointRelation hJoint.1 hJointBelowSecond
  let intersectionRelation : SortedRelation Carrier :=
    SortedKernelIntersection firstRelation secondRelation
  have hIntersectionStrong : ManySortedStrongCongruence signature operations
      intersectionRelation := by
    exact manySortedStrongCongruence_binaryIntersection signature operations
      firstRelation secondRelation hFirst.1 hSecond.1
  have hIntersectionBelow : SortedRelationRefines intersectionRelation
      (SortedKernelIntersection firstKernel secondKernel) := by
    intro sort x y hxy
    exact ⟨hFirst.2.1 sort x y hxy.1, hSecond.2.1 sort x y hxy.2⟩
  have hIntersectionToJoint : SortedRelationRefines intersectionRelation
      jointRelation :=
    hJoint.2.2 intersectionRelation hIntersectionStrong hIntersectionBelow
  intro sort x y
  constructor
  · intro hxy
    exact ⟨hJointToFirst sort x y hxy, hJointToSecond sort x y hxy⟩
  · intro hxy
    exact hIntersectionToJoint sort x y hxy

def SortedObservationKernel
    {SortIndex : Type uSort} {Carrier : SortIndex → Type uCarrier}
    (Observation : SortIndex → Type uObservation)
    (observe : (sort : SortIndex) → Carrier sort → Observation sort) :
    SortedRelation Carrier :=
  fun sort x y => observe sort x = observe sort y

theorem sortedObservationKernel_reflexive
    {SortIndex : Type uSort} {Carrier : SortIndex → Type uCarrier}
    (Observation : SortIndex → Type uObservation)
    (observe : (sort : SortIndex) → Carrier sort → Observation sort) :
    ∀ sort x, SortedObservationKernel Observation observe sort x x := by
  intro sort x
  rfl

theorem different_definedness_refutes_manySortedStrongness
    {SortIndex : Type uSort} {Carrier : SortIndex → Type uCarrier}
    (signature : FinitarySortedSignature SortIndex)
    (operations : FinitarySortedOperations Carrier signature)
    (relation : SortedRelation Carrier)
    (operation : signature.Operation)
    (first second : SortedArguments Carrier signature operation)
    (hRelated : ∀ position,
      relation (signature.inputSort operation position)
        (first position) (second position))
    (hDifferent : Option.isSome (operations operation first) ≠
      Option.isSome (operations operation second)) :
    ¬ManySortedStrongCongruence signature operations relation := by
  intro hStrong
  exact hDifferent (hStrong.2 operation first second hRelated).1

         
theorem fin_a6_arbitraryFinitaryManySortedContextual
    {SortIndex : Type uSort} {Carrier : SortIndex → Type uCarrier}
    (signature : FinitarySortedSignature SortIndex)
    (operations : FinitarySortedOperations Carrier signature)
    (firstKernel secondKernel : SortedRelation Carrier)
    (firstRelation secondRelation jointRelation : SortedRelation Carrier)
    (hFirst : IsGreatestSortedContextualRelation signature operations
      firstKernel firstRelation)
    (hSecond : IsGreatestSortedContextualRelation signature operations
      secondKernel secondRelation)
    (hJoint : IsGreatestSortedContextualRelation signature operations
      (SortedKernelIntersection firstKernel secondKernel) jointRelation) :
    (∀ sort x y,
      jointRelation sort x y ↔
        firstRelation sort x y ∧ secondRelation sort x y) ∧
      (∀ relation operation first second,
        (∀ position,
          relation (signature.inputSort operation position)
            (first position) (second position)) →
        Option.isSome (operations operation first) ≠
          Option.isSome (operations operation second) →
        ¬ManySortedStrongCongruence signature operations relation) := by
  exact ⟨greatestSortedContextualRelation_intersection_iff
      signature operations firstKernel secondKernel
      firstRelation secondRelation jointRelation hFirst hSecond hJoint,
    fun relation operation first second =>
      different_definedness_refutes_manySortedStrongness
        signature operations relation operation first second⟩

end PhonologicalCalculus
