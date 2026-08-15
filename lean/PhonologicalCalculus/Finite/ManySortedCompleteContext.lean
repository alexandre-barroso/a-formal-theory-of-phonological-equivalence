import PhonologicalCalculus.Finite.ManySortedContext
import Mathlib.Tactic

/-!
# Constructed complete contexts for arbitrary-finitary many-sorted algebras

The conditional FIN-A6 intersection law requires an actual greatest strong
congruence. This module constructs it from every finite one-hole context of a
fixed partial signature. Contexts may place the hole in any argument of any
operation and may carry fixed parameters in all remaining arguments.
-/

namespace PhonologicalCalculus

universe uSort uCarrier uOperation uObservation

/-- Replace one coordinate of a dependent argument tuple. -/
noncomputable def replaceSortedArgument
    {SortIndex : Type uSort} {Carrier : SortIndex → Type uCarrier}
    (signature : FinitarySortedSignature SortIndex)
    {operation : signature.Operation}
    (arguments : SortedArguments Carrier signature operation)
    (position : Fin (signature.arity operation))
    (value : Carrier (signature.inputSort operation position)) :
    SortedArguments Carrier signature operation :=
  Function.update arguments position value

/-- Replace every coordinate in a finite set by the corresponding coordinate
of a second dependent tuple. -/
noncomputable def replaceSortedArgumentsOn
    {SortIndex : Type uSort} {Carrier : SortIndex → Type uCarrier}
    (signature : FinitarySortedSignature SortIndex)
    {operation : signature.Operation}
    (positions : Finset (Fin (signature.arity operation)))
    (first second : SortedArguments Carrier signature operation) :
    SortedArguments Carrier signature operation :=
  fun position => if position ∈ positions then second position else first position

/-- A finite one-hole context. The prior context delivers the selected input
sort of the next operation; all other arguments are fixed parameters. -/
inductive FinitarySortedContext
    {SortIndex : Type uSort} (Carrier : SortIndex → Type uCarrier)
    (signature : FinitarySortedSignature.{uSort, uOperation} SortIndex) :
    SortIndex → SortIndex → Type (max uCarrier uOperation) where
  | hole (sort : SortIndex) : FinitarySortedContext Carrier signature sort sort
  | extend {source : SortIndex}
      (operation : signature.Operation)
      (position : Fin (signature.arity operation))
      (prior : FinitarySortedContext Carrier signature source
        (signature.inputSort operation position))
      (fixed : SortedArguments Carrier signature operation) :
      FinitarySortedContext Carrier signature source
        (signature.outputSort operation)

/-- Evaluate a finite one-hole context in the declared partial algebra. -/
noncomputable def evaluateFinitarySortedContext
    {SortIndex : Type uSort} {Carrier : SortIndex → Type uCarrier}
    (signature : FinitarySortedSignature SortIndex)
    (operations : FinitarySortedOperations Carrier signature) :
    {source target : SortIndex} →
      FinitarySortedContext Carrier signature source target →
      Carrier source → Option (Carrier target)
  | _, _, .hole _, value => some value
  | _, _, .extend operation position prior fixed, value =>
      (evaluateFinitarySortedContext signature operations prior value).bind
        fun intermediate =>
          operations operation
            (replaceSortedArgument signature fixed position intermediate)

/-- Composition of finite one-hole contexts. -/
noncomputable def composeFinitarySortedContext
    {SortIndex : Type uSort} {Carrier : SortIndex → Type uCarrier}
    {signature : FinitarySortedSignature SortIndex}
    {source middle target : SortIndex}
    (first : FinitarySortedContext Carrier signature source middle)
    (second : FinitarySortedContext Carrier signature middle target) :
    FinitarySortedContext Carrier signature source target :=
  match second with
  | .hole _ => first
  | .extend operation position prior fixed =>
      .extend operation position
        (composeFinitarySortedContext first prior) fixed

theorem evaluate_composeFinitarySortedContext
    {SortIndex : Type uSort} {Carrier : SortIndex → Type uCarrier}
    (signature : FinitarySortedSignature SortIndex)
    (operations : FinitarySortedOperations Carrier signature)
    {source middle target : SortIndex}
    (first : FinitarySortedContext Carrier signature source middle)
    (second : FinitarySortedContext Carrier signature middle target)
    (value : Carrier source) :
    evaluateFinitarySortedContext signature operations
        (composeFinitarySortedContext first second) value =
      (evaluateFinitarySortedContext signature operations first value).bind
        (evaluateFinitarySortedContext signature operations second) := by
  induction second with
  | hole => simp [composeFinitarySortedContext,
      evaluateFinitarySortedContext]
  | extend operation position prior fixed inductionHypothesis =>
      simp [composeFinitarySortedContext, evaluateFinitarySortedContext,
        inductionHypothesis, Option.bind_assoc]

/-- Complete contextual indistinguishability under every admitted finite
one-hole context and the registered heterogeneous observation family. -/
def CompleteManySortedContextRelation
    {SortIndex : Type uSort} {Carrier : SortIndex → Type uCarrier}
    (signature : FinitarySortedSignature SortIndex)
    (operations : FinitarySortedOperations Carrier signature)
    (Observation : SortIndex → Type uObservation)
    (observe : (sort : SortIndex) → Carrier sort → Observation sort) :
    SortedRelation Carrier :=
  fun source first second =>
    ∀ target (context : FinitarySortedContext Carrier signature source target),
      Option.map (observe target)
          (evaluateFinitarySortedContext signature operations context first) =
        Option.map (observe target)
          (evaluateFinitarySortedContext signature operations context second)

theorem completeManySortedContextRelation_equivalence
    {SortIndex : Type uSort} {Carrier : SortIndex → Type uCarrier}
    (signature : FinitarySortedSignature SortIndex)
    (operations : FinitarySortedOperations Carrier signature)
    (Observation : SortIndex → Type uObservation)
    (observe : (sort : SortIndex) → Carrier sort → Observation sort) :
    ∀ sort,
      Equivalence (CompleteManySortedContextRelation
        signature operations Observation observe sort) := by
  intro sort
  unfold CompleteManySortedContextRelation
  constructor
  · intro value target context
    rfl
  · intro first second hEqual target context
    exact (hEqual target context).symm
  · intro first second third hFirst hSecond target context
    exact (hFirst target context).trans (hSecond target context)

/-- Two partial results agree in definedness and, when defined, return
related values. -/
def PartialResultRelated {X : Type*} (relation : X → X → Prop)
    (first second : Option X) : Prop :=
  Option.isSome first = Option.isSome second ∧
    ∀ firstResult secondResult,
      first = some firstResult → second = some secondResult →
      relation firstResult secondResult

theorem partialResultRelated_reflexive
    {X : Type*} (relation : X → X → Prop)
    (hReflexive : ∀ value, relation value value) (result : Option X) :
    PartialResultRelated relation result result := by
  constructor
  · rfl
  · intro firstResult secondResult hFirst hSecond
    rw [hFirst] at hSecond
    have hEqual : firstResult = secondResult := Option.some.inj hSecond
    rw [hEqual]
    exact hReflexive secondResult

theorem partialResultRelated_transitive
    {X : Type*} (relation : X → X → Prop)
    (hTransitive : ∀ ⦃first middle last⦄,
      relation first middle → relation middle last → relation first last)
    {first middle last : Option X}
    (hFirst : PartialResultRelated relation first middle)
    (hSecond : PartialResultRelated relation middle last) :
    PartialResultRelated relation first last := by
  constructor
  · exact hFirst.1.trans hSecond.1
  · intro firstResult lastResult hFirstResult hLastResult
    cases hMiddle : middle with
    | none =>
        have hContradiction := hFirst.1
        simp [hFirstResult, hMiddle] at hContradiction
    | some middleResult =>
        exact hTransitive
          (hFirst.2 firstResult middleResult hFirstResult hMiddle)
          (hSecond.2 middleResult lastResult hMiddle hLastResult)

/-- A complete-context relation is compatible with replacing one operation
argument while every other argument is fixed. -/
theorem completeManySortedContext_singleArgument
    {SortIndex : Type uSort} {Carrier : SortIndex → Type uCarrier}
    (signature : FinitarySortedSignature SortIndex)
    (operations : FinitarySortedOperations Carrier signature)
    (Observation : SortIndex → Type uObservation)
    (observe : (sort : SortIndex) → Carrier sort → Observation sort)
    (operation : signature.Operation)
    (position : Fin (signature.arity operation))
    (fixed : SortedArguments Carrier signature operation)
    (first second : Carrier (signature.inputSort operation position))
    (hRelated : CompleteManySortedContextRelation
      signature operations Observation observe
      (signature.inputSort operation position) first second) :
    PartialResultRelated
      (CompleteManySortedContextRelation signature operations
        Observation observe (signature.outputSort operation))
      (operations operation
        (replaceSortedArgument signature fixed position first))
      (operations operation
        (replaceSortedArgument signature fixed position second)) := by
  let operationContext : FinitarySortedContext Carrier signature
      (signature.inputSort operation position)
      (signature.outputSort operation) :=
    .extend operation position (.hole _) fixed
  have hDirect := hRelated (signature.outputSort operation) operationContext
  have hDefined : Option.isSome
      (operations operation
        (replaceSortedArgument signature fixed position first)) =
      Option.isSome
      (operations operation
        (replaceSortedArgument signature fixed position second)) := by
    cases hFirst : operations operation
        (replaceSortedArgument signature fixed position first) <;>
      cases hSecond : operations operation
        (replaceSortedArgument signature fixed position second) <;>
      simp [operationContext, evaluateFinitarySortedContext,
        hFirst, hSecond] at hDirect ⊢
  refine ⟨hDefined, ?_⟩
  intro firstResult secondResult hFirstResult hSecondResult target tail
  have hComposed := hRelated target
    (composeFinitarySortedContext operationContext tail)
  rw [evaluate_composeFinitarySortedContext,
    evaluate_composeFinitarySortedContext] at hComposed
  simpa [operationContext, evaluateFinitarySortedContext,
    hFirstResult, hSecondResult] using hComposed

/-- Pointwise-related argument tuples produce related partial results. -/
theorem completeManySortedContext_operationCompatible
    {SortIndex : Type uSort} {Carrier : SortIndex → Type uCarrier}
    (signature : FinitarySortedSignature SortIndex)
    (operations : FinitarySortedOperations Carrier signature)
    (Observation : SortIndex → Type uObservation)
    (observe : (sort : SortIndex) → Carrier sort → Observation sort)
    (operation : signature.Operation)
    (first second : SortedArguments Carrier signature operation)
    (hArguments : ∀ position,
      CompleteManySortedContextRelation signature operations
        Observation observe (signature.inputSort operation position)
        (first position) (second position)) :
    PartialResultRelated
      (CompleteManySortedContextRelation signature operations
        Observation observe (signature.outputSort operation))
      (operations operation first) (operations operation second) := by
  classical
  let relation := CompleteManySortedContextRelation
    signature operations Observation observe
  have hEquivalence := completeManySortedContextRelation_equivalence
    signature operations Observation observe
  have hChain : ∀ positions : Finset (Fin (signature.arity operation)),
      PartialResultRelated (relation (signature.outputSort operation))
        (operations operation first)
        (operations operation
          (replaceSortedArgumentsOn signature positions first second)) := by
    intro positions
    induction positions using Finset.induction_on with
    | empty =>
        have hEmpty :
            replaceSortedArgumentsOn signature ∅ first second = first := by
          funext position
          simp [replaceSortedArgumentsOn]
        rw [hEmpty]
        exact partialResultRelated_reflexive
          (relation (signature.outputSort operation))
          (by simpa [relation] using
            (hEquivalence (signature.outputSort operation)).1)
          (operations operation first)
    | @insert position positions hNotMember inductionHypothesis =>
        let prior := replaceSortedArgumentsOn signature positions first second
        have hPosition : relation (signature.inputSort operation position)
            (prior position) (second position) := by
          simpa [prior, replaceSortedArgumentsOn, hNotMember] using
            hArguments position
        have hSingle := completeManySortedContext_singleArgument
          signature operations Observation observe operation position
          prior (prior position) (second position) hPosition
        have hPriorSelf :
            replaceSortedArgument signature prior position (prior position) =
              prior := by
          funext coordinate
          by_cases hCoordinate : coordinate = position
          · subst coordinate
            simp [replaceSortedArgument]
          · simp [replaceSortedArgument, hCoordinate]
        have hUpdated :
            replaceSortedArgument signature prior position (second position) =
              replaceSortedArgumentsOn signature (insert position positions)
                first second := by
          funext coordinate
          by_cases hCoordinate : coordinate = position
          · subst coordinate
            simp [replaceSortedArgument, replaceSortedArgumentsOn]
          · simp [replaceSortedArgument, replaceSortedArgumentsOn,
              prior, hCoordinate]
        rw [hPriorSelf, hUpdated] at hSingle
        exact partialResultRelated_transitive
          (relation (signature.outputSort operation))
          (fun {_ _ _} hFirstRelation hSecondRelation =>
            (hEquivalence (signature.outputSort operation)).3
              hFirstRelation hSecondRelation)
          inductionHypothesis hSingle
  have hAll := hChain Finset.univ
  have hUniv :
      replaceSortedArgumentsOn signature Finset.univ first second = second := by
    funext position
    simp [replaceSortedArgumentsOn]
  simpa [relation, hUniv] using hAll

/-- The constructed complete-context relation is a strong congruence for the
full arbitrary-finitary many-sorted partial signature. -/
theorem completeManySortedContextRelation_strong
    {SortIndex : Type uSort} {Carrier : SortIndex → Type uCarrier}
    (signature : FinitarySortedSignature SortIndex)
    (operations : FinitarySortedOperations Carrier signature)
    (Observation : SortIndex → Type uObservation)
    (observe : (sort : SortIndex) → Carrier sort → Observation sort) :
    ManySortedStrongCongruence signature operations
      (CompleteManySortedContextRelation
        signature operations Observation observe) := by
  constructor
  · exact completeManySortedContextRelation_equivalence
      signature operations Observation observe
  · intro operation first second hArguments
    exact completeManySortedContext_operationCompatible
      signature operations Observation observe operation first second hArguments

/-- Complete contextual indistinguishability refines the direct observation
kernel by taking the empty context. -/
theorem completeManySortedContextRelation_belowObservation
    {SortIndex : Type uSort} {Carrier : SortIndex → Type uCarrier}
    (signature : FinitarySortedSignature SortIndex)
    (operations : FinitarySortedOperations Carrier signature)
    (Observation : SortIndex → Type uObservation)
    (observe : (sort : SortIndex) → Carrier sort → Observation sort) :
    SortedRelationRefines
      (CompleteManySortedContextRelation
        signature operations Observation observe)
      (SortedObservationKernel Observation observe) := by
  intro sort first second hRelated
  unfold SortedObservationKernel
  simpa [evaluateFinitarySortedContext] using hRelated sort (.hole sort)

/-- Every strong congruence below the direct observation kernel is preserved
by every finite one-hole context. -/
theorem strongCongruence_contextResultRelated
    {SortIndex : Type uSort} {Carrier : SortIndex → Type uCarrier}
    (signature : FinitarySortedSignature SortIndex)
    (operations : FinitarySortedOperations Carrier signature)
    (relation : SortedRelation Carrier)
    (hStrong : ManySortedStrongCongruence signature operations relation)
    {source target : SortIndex}
    (context : FinitarySortedContext Carrier signature source target)
    (first second : Carrier source) (hRelated : relation source first second) :
    PartialResultRelated (relation target)
      (evaluateFinitarySortedContext signature operations context first)
      (evaluateFinitarySortedContext signature operations context second) := by
  induction context with
  | hole =>
      constructor
      · simp [evaluateFinitarySortedContext]
      · intro firstResult secondResult hFirst hSecond
        simp only [evaluateFinitarySortedContext] at hFirst hSecond
        have hFirstEq : firstResult = first := by
          exact (Option.some.inj hFirst.symm)
        have hSecondEq : secondResult = second := by
          exact (Option.some.inj hSecond.symm)
        simpa [hFirstEq, hSecondEq] using hRelated
  | extend operation position prior fixed inductionHypothesis =>
      have hPrior := inductionHypothesis
      cases hFirst : evaluateFinitarySortedContext
          signature operations prior first with
      | none =>
          cases hSecond : evaluateFinitarySortedContext
              signature operations prior second with
          | none => simp [evaluateFinitarySortedContext, hFirst, hSecond,
              PartialResultRelated]
          | some secondResult =>
              have : False := by
                have := hPrior.1
                simp [hFirst, hSecond] at this
              contradiction
      | some firstResult =>
          cases hSecond : evaluateFinitarySortedContext
              signature operations prior second with
          | none =>
              have : False := by
                have := hPrior.1
                simp [hFirst, hSecond] at this
              contradiction
          | some secondResult =>
              have hIntermediate : relation
                  (signature.inputSort operation position)
                  firstResult secondResult :=
                hPrior.2 firstResult secondResult hFirst hSecond
              have hArguments : ∀ coordinate,
                  relation (signature.inputSort operation coordinate)
                    ((replaceSortedArgument signature fixed position
                      firstResult) coordinate)
                    ((replaceSortedArgument signature fixed position
                      secondResult) coordinate) := by
                intro coordinate
                by_cases hCoordinate : coordinate = position
                · subst coordinate
                  simpa [replaceSortedArgument] using
                    hIntermediate
                · simp [replaceSortedArgument,
                    hCoordinate,
                    (hStrong.1 (signature.inputSort operation coordinate)).1]
              simpa [evaluateFinitarySortedContext, PartialResultRelated,
                hFirst, hSecond] using
                hStrong.2 operation _ _ hArguments

/-- The constructed relation is the greatest strong congruence below the
registered heterogeneous observation kernel. -/
theorem completeManySortedContextRelation_isGreatest
    {SortIndex : Type uSort} {Carrier : SortIndex → Type uCarrier}
    (signature : FinitarySortedSignature SortIndex)
    (operations : FinitarySortedOperations Carrier signature)
    (Observation : SortIndex → Type uObservation)
    (observe : (sort : SortIndex) → Carrier sort → Observation sort) :
    IsGreatestSortedContextualRelation signature operations
      (SortedObservationKernel Observation observe)
      (CompleteManySortedContextRelation
        signature operations Observation observe) := by
  refine ⟨completeManySortedContextRelation_strong
      signature operations Observation observe,
    completeManySortedContextRelation_belowObservation
      signature operations Observation observe, ?_⟩
  intro relation hStrong hBelow sort first second hRelated
  simp only [CompleteManySortedContextRelation]
  intro target context
  have hContext := strongCongruence_contextResultRelated
    signature operations relation hStrong context first second hRelated
  cases hFirst : evaluateFinitarySortedContext
      signature operations context first with
  | none =>
      cases hSecond : evaluateFinitarySortedContext
          signature operations context second with
      | none => rfl
      | some secondResult =>
          have : False := by
            have := hContext.1
            simp [hFirst, hSecond] at this
          contradiction
  | some firstResult =>
      cases hSecond : evaluateFinitarySortedContext
          signature operations context second with
      | none =>
          have : False := by
            have := hContext.1
            simp [hFirst, hSecond] at this
          contradiction
      | some secondResult =>
          have hResults := hContext.2 firstResult secondResult hFirst hSecond
          have hObserved := hBelow target firstResult secondResult hResults
          simpa [hFirst, hSecond, SortedObservationKernel] using hObserved

/-- Exact constructed FIN-A6 many-sorted contextual package. -/
theorem fin_a6_constructedArbitraryFinitaryManySortedContextual
    {SortIndex : Type uSort} {Carrier : SortIndex → Type uCarrier}
    (signature : FinitarySortedSignature SortIndex)
    (operations : FinitarySortedOperations Carrier signature)
    (FirstObservation SecondObservation : SortIndex → Type uObservation)
    (firstObserve : (sort : SortIndex) → Carrier sort → FirstObservation sort)
    (secondObserve : (sort : SortIndex) → Carrier sort → SecondObservation sort) :
    IsGreatestSortedContextualRelation signature operations
      (SortedObservationKernel FirstObservation firstObserve)
      (CompleteManySortedContextRelation signature operations
        FirstObservation firstObserve) ∧
    IsGreatestSortedContextualRelation signature operations
      (SortedObservationKernel SecondObservation secondObserve)
      (CompleteManySortedContextRelation signature operations
        SecondObservation secondObserve) ∧
    (∀ sort first second,
      CompleteManySortedContextRelation signature operations
          (fun sort => FirstObservation sort × SecondObservation sort)
          (fun sort value =>
            (firstObserve sort value, secondObserve sort value))
          sort first second ↔
        CompleteManySortedContextRelation signature operations
            FirstObservation firstObserve sort first second ∧
          CompleteManySortedContextRelation signature operations
            SecondObservation secondObserve sort first second) := by
  have hFirst := completeManySortedContextRelation_isGreatest
    signature operations FirstObservation firstObserve
  have hSecond := completeManySortedContextRelation_isGreatest
    signature operations SecondObservation secondObserve
  have hJoint := completeManySortedContextRelation_isGreatest
    signature operations
    (fun sort => FirstObservation sort × SecondObservation sort)
    (fun sort value => (firstObserve sort value, secondObserve sort value))
  have hJointKernel :
      SortedObservationKernel
          (fun sort => FirstObservation sort × SecondObservation sort)
          (fun sort value =>
            (firstObserve sort value, secondObserve sort value)) =
        SortedKernelIntersection
          (SortedObservationKernel FirstObservation firstObserve)
          (SortedObservationKernel SecondObservation secondObserve) := by
    funext sort first second
    apply propext
    constructor
    · intro hEqual
      exact ⟨congrArg Prod.fst hEqual, congrArg Prod.snd hEqual⟩
    · intro hEqual
      exact Prod.ext hEqual.1 hEqual.2
  rw [hJointKernel] at hJoint
  refine ⟨hFirst, hSecond, ?_⟩
  exact greatestSortedContextualRelation_intersection_iff
    signature operations
    (SortedObservationKernel FirstObservation firstObserve)
    (SortedObservationKernel SecondObservation secondObserve)
    (CompleteManySortedContextRelation signature operations
      FirstObservation firstObserve)
    (CompleteManySortedContextRelation signature operations
      SecondObservation secondObserve)
    (CompleteManySortedContextRelation signature operations
      (fun sort => FirstObservation sort × SecondObservation sort)
      (fun sort value =>
        (firstObserve sort value, secondObserve sort value)))
    hFirst hSecond hJoint

section FiniteManySortedRefinement

/-- A tagged point in a heterogeneous carrier records its carrier sort. -/
abbrev SortedCarrierPoint {SortIndex : Type uSort}
    (Carrier : SortIndex → Type uCarrier) :=
  Σ sort, Carrier sort

/-- Lift a heterogeneous sorted relation to a homogeneous relation on tagged
carrier points. Values at different sorts are never related. -/
def LiftSortedRelation
    {SortIndex : Type uSort} {Carrier : SortIndex → Type uCarrier}
    (relation : SortedRelation Carrier) :
    SortedCarrierPoint Carrier → SortedCarrierPoint Carrier → Prop
  | ⟨firstSort, first⟩, ⟨secondSort, second⟩ =>
      ∃ hSort : firstSort = secondSort,
        relation secondSort (hSort ▸ first) second

/-- The finite graph of a heterogeneous sorted relation. -/
noncomputable def finiteSortedRelationGraph
    {SortIndex : Type uSort} {Carrier : SortIndex → Type uCarrier}
    [Fintype SortIndex] [∀ sort, Fintype (Carrier sort)]
    (relation : SortedRelation Carrier) :
    FiniteRelation (SortedCarrierPoint Carrier) :=
  finiteRelationGraph (LiftSortedRelation relation)

theorem mem_finiteSortedRelationGraph_iff
    {SortIndex : Type uSort} {Carrier : SortIndex → Type uCarrier}
    [Fintype SortIndex] [∀ sort, Fintype (Carrier sort)]
    (relation : SortedRelation Carrier)
    (sort : SortIndex) (first second : Carrier sort) :
    (⟨sort, first⟩, ⟨sort, second⟩) ∈
        finiteSortedRelationGraph relation ↔
      relation sort first second := by
  classical
  rw [finiteSortedRelationGraph, mem_finiteRelationGraph_iff]
  constructor
  · rintro ⟨hSort, hRelated⟩
    cases hSort
    exact hRelated
  · intro hRelated
    exact ⟨rfl, hRelated⟩

theorem finiteSortedRelationGraph_subset_iff
    {SortIndex : Type uSort} {Carrier : SortIndex → Type uCarrier}
    [Fintype SortIndex] [∀ sort, Fintype (Carrier sort)]
    (first second : SortedRelation Carrier) :
    finiteSortedRelationGraph first ⊆ finiteSortedRelationGraph second ↔
      SortedRelationRefines first second := by
  classical
  constructor
  · intro hSubset sort x y hFirst
    exact (mem_finiteSortedRelationGraph_iff second sort x y).1
      (hSubset ((mem_finiteSortedRelationGraph_iff first sort x y).2 hFirst))
  · intro hPointwise atom hAtom
    rcases atom with ⟨⟨firstSort, x⟩, ⟨secondSort, y⟩⟩
    rw [finiteSortedRelationGraph,
      mem_finiteRelationGraph_iff] at hAtom ⊢
    rcases hAtom with ⟨hSort, hRelated⟩
    subst secondSort
    exact ⟨rfl, hPointwise firstSort x y hRelated⟩

/-- On finite sorts and finite carriers, every contracting complete splitter
that preserves complete contextual indistinguishability and admits no larger
stable graph reaches the constructed greatest contextual relation in finitely
many steps. The bound is the number of directly observation-equivalent sorted
pairs in the initial graph. -/
theorem fin_a6_finiteManySortedContextualRefinement_metaproof
    {SortIndex : Type uSort} {Carrier : SortIndex → Type uCarrier}
    [Fintype SortIndex] [DecidableEq SortIndex]
    [∀ sort, Fintype (Carrier sort)]
    [∀ sort, DecidableEq (Carrier sort)]
    (signature : FinitarySortedSignature SortIndex)
    (operations : FinitarySortedOperations Carrier signature)
    (Observation : SortIndex → Type uObservation)
    (observe : (sort : SortIndex) → Carrier sort → Observation sort)
    (step : FiniteRelation (SortedCarrierPoint Carrier) →
      FiniteRelation (SortedCarrierPoint Carrier))
    (hContracting : ∀ relation, step relation ⊆ relation)
    (hTargetPreserved : ∀ relation,
      finiteSortedRelationGraph
          (CompleteManySortedContextRelation signature operations
            Observation observe) ⊆ relation →
        finiteSortedRelationGraph
          (CompleteManySortedContextRelation signature operations
            Observation observe) ⊆ step relation)
    (hTerminalSound : ∀ relation, step relation = relation →
      relation ⊆ finiteSortedRelationGraph
        (CompleteManySortedContextRelation signature operations
          Observation observe)) :
    ∃ n ≤ (finiteSortedRelationGraph
        (SortedObservationKernel Observation observe)).card,
      refinementIterate step n
          (finiteSortedRelationGraph
            (SortedObservationKernel Observation observe)) =
        finiteSortedRelationGraph
          (CompleteManySortedContextRelation signature operations
            Observation observe) ∧
      refinementIterate step (n + 1)
          (finiteSortedRelationGraph
            (SortedObservationKernel Observation observe)) =
        refinementIterate step n
          (finiteSortedRelationGraph
            (SortedObservationKernel Observation observe)) := by
  apply finiteRefinement_reaches_target step
    (finiteSortedRelationGraph
      (SortedObservationKernel Observation observe))
    (finiteSortedRelationGraph
      (CompleteManySortedContextRelation signature operations
        Observation observe))
    hContracting
  · exact (finiteSortedRelationGraph_subset_iff _ _).2
      (completeManySortedContextRelation_belowObservation
        signature operations Observation observe)
  · exact hTargetPreserved
  · exact hTerminalSound

end FiniteManySortedRefinement

end PhonologicalCalculus
