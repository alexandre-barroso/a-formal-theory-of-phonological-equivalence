import PhonologicalCalculus.Finite.CarrierAlgebra
import Mathlib.Tactic

/-!
# Finite consumer-battery closure and contextual refinement

The direct component is derived from the kernels of a fixed finite consumerUniverse of
consumers.  Redundancy is fibre constancy, so its closure laws and the closed
battery meet and join are proved rather than assumed.  The contextual
component records partial-operation definedness explicitly and proves the
nonempty-intersection law for a fixed signature.
-/

namespace PhonologicalCalculus

section DirectClosure

variable {Consumer X : Type*} {Answer : Consumer → Type*}

def BatteryAnswer (answers : (consumer : Consumer) → X → Answer consumer)
    (battery : Finset Consumer) (x : X) :
    (consumer : {consumer : Consumer // consumer ∈ battery}) →
      Answer consumer.1 :=
  fun consumer => answers consumer.1 x

def ConsumerRedundant
    (answers : (consumer : Consumer) → X → Answer consumer)
    (battery : Finset Consumer) (consumer : Consumer) : Prop :=
  KernelRefines (BatteryAnswer answers battery) (answers consumer)

noncomputable def RedundancyClosure
    (consumerUniverse : Finset Consumer)
    (answers : (consumer : Consumer) → X → Answer consumer)
    (battery : Finset Consumer) : Finset Consumer := by
  classical
  exact consumerUniverse.filter (ConsumerRedundant answers battery)

theorem mem_redundancyClosure_iff
    (consumerUniverse : Finset Consumer)
    (answers : (consumer : Consumer) → X → Answer consumer)
    (battery : Finset Consumer) (consumer : Consumer) :
    consumer ∈ RedundancyClosure consumerUniverse answers battery ↔
      consumer ∈ consumerUniverse ∧ ConsumerRedundant answers battery consumer := by
  classical
  simp [RedundancyClosure]

theorem redundancyClosure_extensive
    (consumerUniverse : Finset Consumer)
    (answers : (consumer : Consumer) → X → Answer consumer)
    (battery : Finset Consumer) (hBattery : battery ⊆ consumerUniverse) :
    battery ⊆ RedundancyClosure consumerUniverse answers battery := by
  intro consumer hconsumer
  apply (mem_redundancyClosure_iff consumerUniverse answers battery consumer).2
  refine ⟨hBattery hconsumer, ?_⟩
  intro x y hxy
  exact congrFun hxy ⟨consumer, hconsumer⟩

theorem batteryAnswer_mono_kernel
    (answers : (consumer : Consumer) → X → Answer consumer)
    {smaller larger : Finset Consumer} (hSubset : smaller ⊆ larger) :
    KernelRefines (BatteryAnswer answers larger)
      (BatteryAnswer answers smaller) := by
  intro x y hxy
  funext consumer
  exact congrFun hxy ⟨consumer.1, hSubset consumer.2⟩

theorem redundancyClosure_monotone
    (consumerUniverse : Finset Consumer)
    (answers : (consumer : Consumer) → X → Answer consumer)
    {smaller larger : Finset Consumer} (hSubset : smaller ⊆ larger) :
    RedundancyClosure consumerUniverse answers smaller ⊆
      RedundancyClosure consumerUniverse answers larger := by
  intro consumer hconsumer
  have hMember :=
    (mem_redundancyClosure_iff consumerUniverse answers smaller consumer).1 hconsumer
  apply (mem_redundancyClosure_iff consumerUniverse answers larger consumer).2
  refine ⟨hMember.1, ?_⟩
  exact kernelRefines_trans
    (batteryAnswer_mono_kernel answers hSubset) hMember.2

theorem redundancyClosure_idempotent
    (consumerUniverse : Finset Consumer)
    (answers : (consumer : Consumer) → X → Answer consumer)
    (battery : Finset Consumer) (hBattery : battery ⊆ consumerUniverse) :
    RedundancyClosure consumerUniverse answers
        (RedundancyClosure consumerUniverse answers battery) =
      RedundancyClosure consumerUniverse answers battery := by
  apply Finset.Subset.antisymm
  · intro consumer hconsumer
    have hOuter :=
      (mem_redundancyClosure_iff consumerUniverse answers
        (RedundancyClosure consumerUniverse answers battery) consumer).1 hconsumer
    apply (mem_redundancyClosure_iff consumerUniverse answers battery consumer).2
    refine ⟨hOuter.1, ?_⟩
    intro x y hBatteryEqual
    apply hOuter.2
    funext redundantConsumer
    have hRedundant :=
      (mem_redundancyClosure_iff consumerUniverse answers battery
        redundantConsumer.1).1 redundantConsumer.2
    exact hRedundant.2 hBatteryEqual
  · exact redundancyClosure_monotone consumerUniverse answers
      (redundancyClosure_extensive consumerUniverse answers battery hBattery)

def ClosedBattery (consumerUniverse : Finset Consumer)
    (answers : (consumer : Consumer) → X → Answer consumer)
    (battery : Finset Consumer) : Prop :=
  battery ⊆ consumerUniverse ∧ RedundancyClosure consumerUniverse answers battery = battery

theorem redundancyClosure_closed
    (consumerUniverse : Finset Consumer)
    (answers : (consumer : Consumer) → X → Answer consumer)
    (battery : Finset Consumer) (hBattery : battery ⊆ consumerUniverse) :
    ClosedBattery consumerUniverse answers
      (RedundancyClosure consumerUniverse answers battery) := by
  constructor
  · intro consumer hconsumer
    exact (mem_redundancyClosure_iff consumerUniverse answers battery consumer).1
      hconsumer |>.1
  · exact redundancyClosure_idempotent consumerUniverse answers battery hBattery

theorem closedBattery_intersection
    [DecidableEq Consumer]
    (consumerUniverse : Finset Consumer)
    (answers : (consumer : Consumer) → X → Answer consumer)
    {first second : Finset Consumer}
    (hFirst : ClosedBattery consumerUniverse answers first)
    (hSecond : ClosedBattery consumerUniverse answers second) :
    ClosedBattery consumerUniverse answers (first ∩ second) := by
  constructor
  · intro consumer hconsumer
    exact hFirst.1 (Finset.mem_inter.1 hconsumer).1
  · apply Finset.Subset.antisymm
    · intro consumer hconsumer
      have hToFirst := redundancyClosure_monotone consumerUniverse answers
        (Finset.inter_subset_left : first ∩ second ⊆ first) hconsumer
      have hToSecond := redundancyClosure_monotone consumerUniverse answers
        (Finset.inter_subset_right : first ∩ second ⊆ second) hconsumer
      rw [hFirst.2] at hToFirst
      rw [hSecond.2] at hToSecond
      exact Finset.mem_inter.2 ⟨hToFirst, hToSecond⟩
    · exact redundancyClosure_extensive consumerUniverse answers _
        (fun _ h => hFirst.1 (Finset.mem_inter.1 h).1)

theorem closedBattery_join
    [DecidableEq Consumer]
    (consumerUniverse : Finset Consumer)
    (answers : (consumer : Consumer) → X → Answer consumer)
    {first second : Finset Consumer}
    (hFirst : ClosedBattery consumerUniverse answers first)
    (hSecond : ClosedBattery consumerUniverse answers second) :
    ClosedBattery consumerUniverse answers
      (RedundancyClosure consumerUniverse answers (first ∪ second)) := by
  apply redundancyClosure_closed
  intro consumer hconsumer
  rcases Finset.mem_union.1 hconsumer with h | h
  · exact hFirst.1 h
  · exact hSecond.1 h

/-- Integrated direct information-lattice theorem: redundancy closure is
extensive, monotone, and idempotent, and closed batteries possess intersection
and closure-of-union operations. -/
theorem fin_a6_directInformationLattice
    [DecidableEq Consumer]
    (consumerUniverse : Finset Consumer)
    (answers : (consumer : Consumer) → X → Answer consumer)
    (battery : Finset Consumer) (hBattery : battery ⊆ consumerUniverse) :
    battery ⊆ RedundancyClosure consumerUniverse answers battery ∧
    (∀ smaller larger, smaller ⊆ larger →
      RedundancyClosure consumerUniverse answers smaller ⊆
        RedundancyClosure consumerUniverse answers larger) ∧
    RedundancyClosure consumerUniverse answers
        (RedundancyClosure consumerUniverse answers battery) =
      RedundancyClosure consumerUniverse answers battery ∧
    (∀ first second,
      ClosedBattery consumerUniverse answers first →
      ClosedBattery consumerUniverse answers second →
        ClosedBattery consumerUniverse answers (first ∩ second) ∧
        ClosedBattery consumerUniverse answers
          (RedundancyClosure consumerUniverse answers (first ∪ second))) := by
  exact ⟨redundancyClosure_extensive consumerUniverse answers battery hBattery,
    fun _ _ => redundancyClosure_monotone consumerUniverse answers,
    redundancyClosure_idempotent consumerUniverse answers battery hBattery,
    fun _ _ hFirst hSecond =>
      ⟨closedBattery_intersection consumerUniverse answers hFirst hSecond,
        closedBattery_join consumerUniverse answers hFirst hSecond⟩⟩

/-- Exact two-bit fixture: the two coordinate carriers are incomparable, and
their product kernel is raw equality. -/
theorem fin_a6_lattice_01 :
    ¬KernelRefines (fun value : Bool × Bool => value.1) (fun value => value.2) ∧
    ¬KernelRefines (fun value : Bool × Bool => value.2) (fun value => value.1) ∧
    (∀ x y : Bool × Bool,
      (x.1, x.2) = (y.1, y.2) ↔ x = y) := by
  constructor
  · intro hrefines
    have := hrefines
      (show (false, false).1 = (false, true).1 from rfl)
    contradiction
  constructor
  · intro hrefines
    have := hrefines
      (show (false, false).2 = (true, false).2 from rfl)
    contradiction
  · intro x y
    simp

/-! ### The arbitrary finite closed-battery lattice -/

/-- A registered battery contains only consumers from the prospectively fixed
consumer universe. -/
def RegisteredBattery (consumerUniverse : Finset Consumer) :=
  {battery : Finset Consumer // battery ⊆ consumerUniverse}

/-- Equality of a joint battery answer is exactly the intersection of the
kernels of every registered consumer in that battery. -/
theorem batteryAnswer_eq_iff_all_consumers
    (answers : (consumer : Consumer) → X → Answer consumer)
    (battery : Finset Consumer)
    (x y : X) :
    BatteryAnswer answers battery x = BatteryAnswer answers battery y ↔
      ∀ consumer, consumer ∈ battery →
        answers consumer x = answers consumer y := by
  constructor
  · intro hEqual consumer hConsumer
    exact congrFun hEqual ⟨consumer, hConsumer⟩
  · intro hPointwise
    funext consumer
    exact hPointwise consumer.1 consumer.2

instance registeredBatteryPartialOrder
    [DecidableEq Consumer]
    (consumerUniverse : Finset Consumer) :
    PartialOrder (RegisteredBattery consumerUniverse) :=
  PartialOrder.lift Subtype.val Subtype.val_injective

/-- Encode a registered battery as a finite set over the finite subtype carried
by the registered universe.  The ambient consumer type need not be finite. -/
noncomputable def registeredBatteryCode
    [DecidableEq Consumer] (consumerUniverse : Finset Consumer) :
    RegisteredBattery consumerUniverse →
      Finset {consumer // consumer ∈ consumerUniverse} := by
  classical
  intro battery
  exact battery.1.attach.map
    ⟨fun consumer => ⟨consumer.1, battery.2 consumer.2⟩, by
      intro first second hEqual
      apply Subtype.ext
      exact congrArg
        (fun consumer : {c // c ∈ consumerUniverse} => (consumer : Consumer))
        hEqual⟩

theorem registeredBatteryCode_injective
    [DecidableEq Consumer] (consumerUniverse : Finset Consumer) :
    Function.Injective (registeredBatteryCode consumerUniverse) := by
  classical
  intro first second hCode
  apply Subtype.ext
  ext consumer
  constructor
  · intro hFirst
    have hMember :
        (⟨consumer, first.2 hFirst⟩ : {c // c ∈ consumerUniverse}) ∈
          registeredBatteryCode consumerUniverse first := by
      simp [registeredBatteryCode, hFirst]
    rw [hCode] at hMember
    simpa [registeredBatteryCode] using hMember
  · intro hSecond
    have hMember :
        (⟨consumer, second.2 hSecond⟩ : {c // c ∈ consumerUniverse}) ∈
          registeredBatteryCode consumerUniverse second := by
      simp [registeredBatteryCode, hSecond]
    rw [← hCode] at hMember
    simpa [registeredBatteryCode] using hMember

noncomputable instance registeredBatteryFinite
    [DecidableEq Consumer]
    (consumerUniverse : Finset Consumer) :
    Finite (RegisteredBattery consumerUniverse) :=
  Finite.of_injective (registeredBatteryCode consumerUniverse)
    (registeredBatteryCode_injective consumerUniverse)

/-- The kernel-induced redundancy operation, bundled as an order-theoretic
closure operator on all registered batteries. -/
noncomputable def redundancyClosureOperator
    [DecidableEq Consumer]
    (consumerUniverse : Finset Consumer)
    (answers : (consumer : Consumer) → X → Answer consumer) :
    ClosureOperator (RegisteredBattery consumerUniverse) := by
  classical
  let close : RegisteredBattery consumerUniverse →
      RegisteredBattery consumerUniverse := fun battery =>
    ⟨RedundancyClosure consumerUniverse answers battery.1, by
      intro consumer hconsumer
      exact (mem_redundancyClosure_iff consumerUniverse answers _ consumer).1
        hconsumer |>.1⟩
  apply ClosureOperator.mk' close
  · intro first second hSubset
    change RedundancyClosure consumerUniverse answers first.1 ⊆
      RedundancyClosure consumerUniverse answers second.1
    exact redundancyClosure_monotone consumerUniverse answers hSubset
  · intro battery
    change battery.1 ⊆ RedundancyClosure consumerUniverse answers battery.1
    exact redundancyClosure_extensive consumerUniverse answers battery.1 battery.2
  · intro battery
    change RedundancyClosure consumerUniverse answers
      (RedundancyClosure consumerUniverse answers battery.1) ⊆
        RedundancyClosure consumerUniverse answers battery.1
    rw [redundancyClosure_idempotent consumerUniverse answers battery.1 battery.2]

/-- The closed points of the registered redundancy closure. -/
abbrev RedundancyClosedBattery
    [DecidableEq Consumer]
    (consumerUniverse : Finset Consumer)
    (answers : (consumer : Consumer) → X → Answer consumer) :=
  (redundancyClosureOperator consumerUniverse answers).Closeds

noncomputable instance redundancyClosedBatteryInf
    [DecidableEq Consumer]
    (consumerUniverse : Finset Consumer)
    (answers : (consumer : Consumer) → X → Answer consumer) :
    Min (RedundancyClosedBattery consumerUniverse answers) where
  min first second := by
    refine ⟨⟨first.1.1 ∩ second.1.1, ?_⟩, ?_⟩
    · intro consumer hconsumer
      exact first.1.2 (Finset.mem_inter.1 hconsumer).1
    · apply (redundancyClosureOperator consumerUniverse answers).isClosed_iff.2
      apply Subtype.ext
      exact (closedBattery_intersection consumerUniverse answers
        ⟨first.1.2, congrArg Subtype.val
          ((redundancyClosureOperator consumerUniverse answers).isClosed_iff.1
            first.2)⟩
        ⟨second.1.2, congrArg Subtype.val
          ((redundancyClosureOperator consumerUniverse answers).isClosed_iff.1
            second.2)⟩).2

noncomputable instance redundancyClosedBatteryMax
    [DecidableEq Consumer]
    (consumerUniverse : Finset Consumer)
    (answers : (consumer : Consumer) → X → Answer consumer) :
    Max (RedundancyClosedBattery consumerUniverse answers) where
  max first second :=
    (redundancyClosureOperator consumerUniverse answers).toCloseds
      ⟨first.1.1 ∪ second.1.1, by
        intro consumer hconsumer
        rcases Finset.mem_union.1 hconsumer with hconsumer | hconsumer
        · exact first.1.2 hconsumer
        · exact second.1.2 hconsumer⟩

noncomputable instance redundancyClosedBatteryLattice
    [DecidableEq Consumer]
    (consumerUniverse : Finset Consumer)
    (answers : (consumer : Consumer) → X → Answer consumer) :
    Lattice (RedundancyClosedBattery consumerUniverse answers) where
  sup := max
  le_sup_left first second := by
    change first.1.1 ⊆
      RedundancyClosure consumerUniverse answers (first.1.1 ∪ second.1.1)
    intro consumer hconsumer
    exact (redundancyClosureOperator consumerUniverse answers).le_closure
      ⟨first.1.1 ∪ second.1.1, by
        intro c hc
        rcases Finset.mem_union.1 hc with hc | hc
        · exact first.1.2 hc
        · exact second.1.2 hc⟩
      (Finset.mem_union_left second.1.1 hconsumer)
  le_sup_right first second := by
    change second.1.1 ⊆
      RedundancyClosure consumerUniverse answers (first.1.1 ∪ second.1.1)
    intro consumer hconsumer
    exact (redundancyClosureOperator consumerUniverse answers).le_closure
      ⟨first.1.1 ∪ second.1.1, by
        intro c hc
        rcases Finset.mem_union.1 hc with hc | hc
        · exact first.1.2 hc
        · exact second.1.2 hc⟩
      (Finset.mem_union_right first.1.1 hconsumer)
  sup_le first second third hFirst hSecond := by
    change RedundancyClosure consumerUniverse answers (first.1.1 ∪ second.1.1) ⊆
      third.1.1
    have hClosedThird :
        RedundancyClosure consumerUniverse answers third.1.1 = third.1.1 :=
      congrArg Subtype.val
        ((redundancyClosureOperator consumerUniverse answers).isClosed_iff.1 third.2)
    rw [← hClosedThird]
    apply redundancyClosure_monotone consumerUniverse answers
    intro consumer hconsumer
    rcases Finset.mem_union.1 hconsumer with hconsumer | hconsumer
    · exact hFirst hconsumer
    · exact hSecond hconsumer
  inf := min
  inf_le_left first second := by
    change first.1.1 ∩ second.1.1 ⊆ first.1.1
    exact Finset.inter_subset_left
  inf_le_right first second := by
    change first.1.1 ∩ second.1.1 ⊆ second.1.1
    exact Finset.inter_subset_right
  le_inf first second third hSecond hThird := by
    change first.1.1 ⊆ second.1.1 ∩ third.1.1
    intro consumer hconsumer
    exact Finset.mem_inter.2 ⟨hSecond hconsumer, hThird hconsumer⟩

instance redundancyClosedBatteryFinite
    [DecidableEq Consumer]
    (consumerUniverse : Finset Consumer)
    (answers : (consumer : Consumer) → X → Answer consumer) :
    Finite (RedundancyClosedBattery consumerUniverse answers) :=
  Finite.of_injective Subtype.val Subtype.val_injective

noncomputable instance redundancyClosedBatteryFintype
    [DecidableEq Consumer]
    (consumerUniverse : Finset Consumer)
    (answers : (consumer : Consumer) → X → Answer consumer) :
    Fintype (RedundancyClosedBattery consumerUniverse answers) :=
  Fintype.ofFinite _

@[simp]
theorem redundancyClosedBattery_inf_carrier
    [DecidableEq Consumer]
    (consumerUniverse : Finset Consumer)
    (answers : (consumer : Consumer) → X → Answer consumer)
    (first second : RedundancyClosedBattery consumerUniverse answers) :
    (first ⊓ second).1.1 = first.1.1 ∩ second.1.1 :=
  rfl

@[simp]
theorem redundancyClosedBattery_sup_carrier
    [DecidableEq Consumer]
    (consumerUniverse : Finset Consumer)
    (answers : (consumer : Consumer) → X → Answer consumer)
    (first second : RedundancyClosedBattery consumerUniverse answers) :
    (first ⊔ second).1.1 =
      RedundancyClosure consumerUniverse answers (first.1.1 ∪ second.1.1) :=
  rfl

/-- Arbitrary finite registered consumer batteries form a genuine finite
lattice: meet is intersection and join is redundancy closure of union. -/
theorem fin_a6_arbitraryFiniteInformationLattice
    [DecidableEq Consumer]
    (consumerUniverse : Finset Consumer)
    (answers : (consumer : Consumer) → X → Answer consumer) :
    Nonempty (Fintype (RedundancyClosedBattery consumerUniverse answers)) ∧
      (∀ first second : RedundancyClosedBattery consumerUniverse answers,
        (first ⊓ second).1.1 = first.1.1 ∩ second.1.1 ∧
        (first ⊔ second).1.1 =
          RedundancyClosure consumerUniverse answers
            (first.1.1 ∪ second.1.1)) := by
  refine ⟨⟨inferInstance⟩, ?_⟩
  intro first second
  exact ⟨rfl, rfl⟩

end DirectClosure

section ContextualRelations

variable {Operation X : Type*}

def StrongPartialCongruence (operations : Operation → X → Option X)
    (relation : X → X → Prop) : Prop :=
  Equivalence relation ∧
    ∀ operation x y, relation x y →
      (Option.isSome (operations operation x) =
        Option.isSome (operations operation y)) ∧
      ∀ xResult yResult,
        operations operation x = some xResult →
        operations operation y = some yResult →
        relation xResult yResult

def RelationIntersection {Index X : Type*}
    (relations : Index → X → X → Prop) : X → X → Prop :=
  fun x y => ∀ index, relations index x y

/-- A nonempty intersection of strong congruences for one fixed complete
partial signature is again strong. -/
theorem strongPartialCongruence_intersection
    {Index : Type*} [Nonempty Index]
    (operations : Operation → X → Option X)
    (relations : Index → X → X → Prop)
    (hStrong : ∀ index,
      StrongPartialCongruence operations (relations index)) :
    StrongPartialCongruence operations (RelationIntersection relations) := by
  constructor
  · constructor
    · intro x index
      exact (hStrong index).1.1 x
    · intro x y hxy index
      exact (hStrong index).1.2 (hxy index)
    · intro x y z hxy hyz index
      exact (hStrong index).1.3 (hxy index) (hyz index)
  · intro operation x y hxy
    let witness : Index := Classical.choice inferInstance
    have hDefined := (hStrong witness).2 operation x y (hxy witness) |>.1
    refine ⟨hDefined, ?_⟩
    intro xResult yResult hx hy index
    exact (hStrong index).2 operation x y (hxy index) |>.2
      xResult yResult hx hy

/-- Relating two arguments on which a registered partial operation has
different definedness is an exact obstruction to strong congruence. -/
theorem different_definedness_refutes_strongness
    (operations : Operation → X → Option X) (relation : X → X → Prop)
    (operation : Operation) (x y : X) (hRelated : relation x y)
    (hDifferent : Option.isSome (operations operation x) ≠
      Option.isSome (operations operation y)) :
    ¬StrongPartialCongruence operations relation := by
  intro hStrong
  exact hDifferent (hStrong.2 operation x y hRelated).1

/-- Integrated fixed-signature contextual theorem. -/
theorem fin_a6_contextualIntersectionAndDefinedness
    {Index : Type*} [Nonempty Index]
    (operations : Operation → X → Option X)
    (relations : Index → X → X → Prop)
    (hStrong : ∀ index,
      StrongPartialCongruence operations (relations index)) :
    StrongPartialCongruence operations (RelationIntersection relations) ∧
      ∀ relation operation x y,
        relation x y →
        Option.isSome (operations operation x) ≠
          Option.isSome (operations operation y) →
        ¬StrongPartialCongruence operations relation := by
  exact ⟨strongPartialCongruence_intersection operations relations hStrong,
    fun relation operation x y =>
      different_definedness_refutes_strongness operations relation
        operation x y⟩

def definednessFixtureOperation (_ : Unit) : Bool → Option Bool
  | false => none
  | true => some true

def universalBoolRelation (_ _ : Bool) : Prop := True

/-- Exact partial-definedness obstruction fixture. -/
theorem fin_a6_definedness_03 :
    universalBoolRelation false true ∧
      ¬StrongPartialCongruence definednessFixtureOperation
        universalBoolRelation := by
  refine ⟨trivial, ?_⟩
  apply different_definedness_refutes_strongness
    definednessFixtureOperation universalBoolRelation () false true trivial
  decide

def runUnaryContext (operations : Operation → X → Option X) :
    List Operation → X → Option X
  | [], x => some x
  | operation :: context, x =>
      (operations operation x).bind (runUnaryContext operations context)

def CompleteUnaryContextRelation {Observation : Type*}
    (operations : Operation → X → Option X) (observe : X → Observation) :
    X → X → Prop :=
  fun x y => ∀ context,
    Option.map observe (runUnaryContext operations context x) =
      Option.map observe (runUnaryContext operations context y)

theorem completeUnaryContextRelation_equivalence
    {Observation : Type*}
    (operations : Operation → X → Option X) (observe : X → Observation) :
    Equivalence (CompleteUnaryContextRelation operations observe) := by
  constructor
  · intro x context
    rfl
  · intro x y hxy context
    exact (hxy context).symm
  · intro x y z hxy hyz context
    exact (hxy context).trans (hyz context)

theorem completeUnaryContextRelation_below_directKernel
    {Observation : Type*}
    (operations : Operation → X → Option X) (observe : X → Observation) :
    ∀ x y, CompleteUnaryContextRelation operations observe x y →
      observe x = observe y := by
  intro x y hxy
  simpa [runUnaryContext] using hxy []

theorem completeUnaryContextRelation_strong
    {Observation : Type*}
    (operations : Operation → X → Option X) (observe : X → Observation) :
    StrongPartialCongruence operations
      (CompleteUnaryContextRelation operations observe) := by
  constructor
  · exact completeUnaryContextRelation_equivalence operations observe
  · intro operation x y hxy
    have hOneStep := hxy [operation]
    have hDefined : Option.isSome (operations operation x) =
        Option.isSome (operations operation y) := by
      cases hx : operations operation x <;>
        cases hy : operations operation y <;>
        simp [runUnaryContext, hx, hy] at hOneStep ⊢
    refine ⟨hDefined, ?_⟩
    intro xResult yResult hx hy context
    have hExtended := hxy (operation :: context)
    simpa [runUnaryContext, hx, hy] using hExtended

/-- Every strong congruence below the direct observation kernel is contained
in complete contextual indistinguishability.  Thus the latter is the greatest
strong congruence below that kernel for the fixed unary partial signature. -/
theorem completeUnaryContextRelation_greatest
    {Observation : Type*}
    (operations : Operation → X → Option X) (observe : X → Observation)
    (relation : X → X → Prop)
    (hStrong : StrongPartialCongruence operations relation)
    (hBelow : ∀ x y, relation x y → observe x = observe y) :
    ∀ x y, relation x y →
      CompleteUnaryContextRelation operations observe x y := by
  intro x y hxy context
  induction context generalizing x y with
  | nil =>
      simp [runUnaryContext, hBelow x y hxy]
  | cons operation context inductionHypothesis =>
      have hCompatibility := hStrong.2 operation x y hxy
      cases hx : operations operation x with
      | none =>
          cases hy : operations operation y with
          | none => simp [runUnaryContext, hx, hy]
          | some yResult =>
              have : False := by
                have := hCompatibility.1
                simp [hx, hy] at this
              contradiction
      | some xResult =>
          cases hy : operations operation y with
          | none =>
              have : False := by
                have := hCompatibility.1
                simp [hx, hy] at this
              contradiction
          | some yResult =>
              have hResults : relation xResult yResult :=
                hCompatibility.2 xResult yResult hx hy
              simpa [runUnaryContext, hx, hy] using
                inductionHypothesis xResult yResult hResults

/-- Complete context enumeration supplies the greatest fixed-signature
contextual refinement below the direct kernel. -/
theorem fin_a6_greatestContextualRefinement
    {Observation : Type*}
    (operations : Operation → X → Option X) (observe : X → Observation) :
    StrongPartialCongruence operations
        (CompleteUnaryContextRelation operations observe) ∧
    (∀ x y, CompleteUnaryContextRelation operations observe x y →
      observe x = observe y) ∧
    (∀ relation,
      StrongPartialCongruence operations relation →
      (∀ x y, relation x y → observe x = observe y) →
      ∀ x y, relation x y →
        CompleteUnaryContextRelation operations observe x y) := by
  exact ⟨completeUnaryContextRelation_strong operations observe,
    completeUnaryContextRelation_below_directKernel operations observe,
    fun relation =>
      completeUnaryContextRelation_greatest operations observe relation⟩

end ContextualRelations

section FiniteRefinementTermination

variable {X : Type*}

/-- A finite binary relation is represented extensionally by its graph. -/
abbrev FiniteRelation (X : Type*) := Finset (X × X)

/-- One proper refinement removes at least one related pair. -/
def ProperRelationRefinement [DecidableEq X]
    (finer coarser : FiniteRelation X) : Prop :=
  finer ⊂ coarser

/-- Proper refinement of a finite relation is well founded.  This is the
machine-level termination measure behind any complete splitter on a fixed
finite carrier. -/
theorem properRelationRefinement_wellFounded [DecidableEq X] :
    WellFounded (@ProperRelationRefinement X inferInstance) := by
  apply Subrelation.wf
    (r := fun finer coarser : FiniteRelation X => finer.card < coarser.card)
  · intro finer coarser hProper
    exact Finset.card_lt_card hProper
  · exact (measure (fun relation : FiniteRelation X => relation.card)).wf

/-- The deterministic refinement sequence generated by `step`. -/
def refinementIterate (step : FiniteRelation X → FiniteRelation X) :
    Nat → FiniteRelation X → FiniteRelation X
  | 0, relation => relation
  | n + 1, relation => step (refinementIterate step n relation)

@[simp]
theorem refinementIterate_zero
    (step : FiniteRelation X → FiniteRelation X)
    (relation : FiniteRelation X) :
    refinementIterate step 0 relation = relation :=
  rfl

@[simp]
theorem refinementIterate_succ
    (step : FiniteRelation X → FiniteRelation X)
    (n : Nat) (relation : FiniteRelation X) :
    refinementIterate step (n + 1) relation =
      step (refinementIterate step n relation) :=
  rfl

theorem refinementIterate_from_step
    (step : FiniteRelation X → FiniteRelation X)
    (n : Nat) (relation : FiniteRelation X) :
    refinementIterate step n (step relation) =
      refinementIterate step (n + 1) relation := by
  induction n with
  | zero => rfl
  | succ n inductionHypothesis =>
      simpa only [refinementIterate_succ] using
        congrArg step inductionHypothesis

/-- Every contracting refinement procedure on a finite relation reaches a
fixed point after no more proper steps than the number of pairs initially
related. -/
theorem finiteRefinement_exists_stable [DecidableEq X]
    (step : FiniteRelation X → FiniteRelation X)
    (hContracting : ∀ relation, step relation ⊆ relation)
    (initial : FiniteRelation X) :
    ∃ n ≤ initial.card,
      refinementIterate step (n + 1) initial =
        refinementIterate step n initial := by
  induction hCard : initial.card using Nat.strong_induction_on generalizing initial with
  | h card inductionHypothesis =>
      by_cases hStable : step initial = initial
      · refine ⟨0, Nat.zero_le _, ?_⟩
        simp [hStable]
      · have hProper : step initial ⊂ initial :=
          Finset.ssubset_iff_subset_ne.2 ⟨hContracting initial, hStable⟩
        have hCardDecrease : (step initial).card < initial.card :=
          Finset.card_lt_card hProper
        obtain ⟨n, hBound, hNextStable⟩ :=
          inductionHypothesis (step initial).card
            (by simpa [hCard] using hCardDecrease) (step initial) rfl
        refine ⟨n + 1, ?_, ?_⟩
        · exact (Nat.succ_le_succ hBound).trans
            (Nat.succ_le_of_lt (by simpa [hCard] using hCardDecrease))
        · calc
            refinementIterate step ((n + 1) + 1) initial =
                refinementIterate step (n + 1) (step initial) := by
                  rw [refinementIterate_from_step]
            _ = refinementIterate step n (step initial) := hNextStable
            _ = refinementIterate step (n + 1) initial :=
              refinementIterate_from_step step n initial

/-- If a contracting splitter preserves an intended target relation and every
stable relation is contained in that target, finite iteration reaches the
target exactly.  The three hypotheses are the explicit preservation,
admission, and terminal-soundness proof requirements of contextual
refinement. -/
theorem finiteRefinement_reaches_target [DecidableEq X]
    (step : FiniteRelation X → FiniteRelation X)
    (initial target : FiniteRelation X)
    (hContracting : ∀ relation, step relation ⊆ relation)
    (hTargetInitial : target ⊆ initial)
    (hTargetPreserved : ∀ relation, target ⊆ relation →
      target ⊆ step relation)
    (hTerminalSound : ∀ relation, step relation = relation →
      relation ⊆ target) :
    ∃ n ≤ initial.card,
      refinementIterate step n initial = target ∧
      refinementIterate step (n + 1) initial =
        refinementIterate step n initial := by
  have hTargetEveryStage : ∀ n,
      target ⊆ refinementIterate step n initial := by
    intro n
    induction n with
    | zero => exact hTargetInitial
    | succ n inductionHypothesis =>
        exact hTargetPreserved _ inductionHypothesis
  obtain ⟨n, hBound, hStable⟩ :=
    finiteRefinement_exists_stable step hContracting initial
  have hStepFixed :
      step (refinementIterate step n initial) =
        refinementIterate step n initial := by
    simpa using hStable
  have hTerminalBelow : refinementIterate step n initial ⊆ target :=
    hTerminalSound _ hStepFixed
  have hExact : refinementIterate step n initial = target :=
    Finset.Subset.antisymm hTerminalBelow (hTargetEveryStage n)
  exact ⟨n, hBound, hExact, hStable⟩

/-- The graph of a relation on a finite carrier. -/
noncomputable def finiteRelationGraph [Fintype X]
    (relation : X → X → Prop) : FiniteRelation X := by
  classical
  exact Finset.univ.filter fun pair => relation pair.1 pair.2

theorem mem_finiteRelationGraph_iff [Fintype X]
    (relation : X → X → Prop) (x y : X) :
    (x, y) ∈ finiteRelationGraph relation ↔ relation x y := by
  classical
  simp [finiteRelationGraph]

theorem finiteRelationGraph_subset_iff [Fintype X]
    (first second : X → X → Prop) :
    finiteRelationGraph first ⊆ finiteRelationGraph second ↔
      ∀ x y, first x y → second x y := by
  classical
  constructor
  · intro hSubset x y hFirst
    exact (mem_finiteRelationGraph_iff second x y).1
      (hSubset ((mem_finiteRelationGraph_iff first x y).2 hFirst))
  · intro hPointwise pair hPair
    have hFirst := (mem_finiteRelationGraph_iff first pair.1 pair.2).1 hPair
    exact (mem_finiteRelationGraph_iff second pair.1 pair.2).2
      (hPointwise pair.1 pair.2 hFirst)

/-- FIN-A6 finite contextual-refinement metatheorem for the already proved
complete unary-context relation.  A concrete splitter need only discharge the
three displayed finite proof requirements; it then terminates and reaches the
greatest fixed-signature strong congruence below the direct kernel. -/
theorem fin_a6_finiteContextualRefinement_metaproof
    {Operation Observation : Type*}
    [Fintype X] [DecidableEq X]
    (operations : Operation → X → Option X) (observe : X → Observation)
    (step : FiniteRelation X → FiniteRelation X)
    (hContracting : ∀ relation, step relation ⊆ relation)
    (hTargetPreserved : ∀ relation,
      finiteRelationGraph (CompleteUnaryContextRelation operations observe) ⊆
          relation →
        finiteRelationGraph (CompleteUnaryContextRelation operations observe) ⊆
          step relation)
    (hTerminalSound : ∀ relation, step relation = relation →
      relation ⊆
        finiteRelationGraph (CompleteUnaryContextRelation operations observe)) :
    ∃ n ≤ (finiteRelationGraph
        (fun x y => observe x = observe y)).card,
      refinementIterate step n
          (finiteRelationGraph (fun x y => observe x = observe y)) =
        finiteRelationGraph (CompleteUnaryContextRelation operations observe) ∧
      refinementIterate step (n + 1)
          (finiteRelationGraph (fun x y => observe x = observe y)) =
        refinementIterate step n
          (finiteRelationGraph (fun x y => observe x = observe y)) := by
  apply finiteRefinement_reaches_target step
    (finiteRelationGraph (fun x y => observe x = observe y))
    (finiteRelationGraph (CompleteUnaryContextRelation operations observe))
    hContracting
  · exact (finiteRelationGraph_subset_iff _ _).2
      (completeUnaryContextRelation_below_directKernel operations observe)
  · exact hTargetPreserved
  · exact hTerminalSound

end FiniteRefinementTermination

end PhonologicalCalculus
