import PhonologicalCalculus.Finite.QueryFactorization
import Mathlib.Tactic

/-!
# Finite carrier algebra

This module develops the generic finite mathematics behind product-query
carriers, exact added-consumer price, irreversible loss, and collision
decomposition.  Every statement is parameterized by arbitrary finite types;
the registered finite fixtures are consequences rather than proof surrogates.
-/

namespace PhonologicalCalculus

/-- The direct product of an arbitrary finite family of typed consumers. -/
def ProductQuery {I X : Type*} {Answer : I → Type*}
    (queries : ∀ index, X → Answer index) (x : X) :
    ∀ index, Answer index :=
  fun index => queries index x

/-- Equality under the product query is exactly coordinatewise equality under
every registered consumer. -/
theorem productQuery_kernel_exact {I X : Type*} {Answer : I → Type*}
    (queries : ∀ index, X → Answer index) (x y : X) :
    ProductQuery queries x = ProductQuery queries y ↔
      ∀ index, queries index x = queries index y := by
  constructor
  · intro hequal index
    exact congrFun hequal index
  · intro hequal
    funext index
    exact hequal index

/-- Preserving every coordinate is equivalent to preserving the complete
typed product query. -/
theorem kernelRefines_productQuery_iff
    {I X Reduction : Type*} {Answer : I → Type*}
    (reduction : X → Reduction) (queries : ∀ index, X → Answer index) :
    KernelRefines reduction (ProductQuery queries) ↔
      ∀ index, KernelRefines reduction (queries index) := by
  constructor
  · intro hall index x y hxy
    exact congrFun (hall hxy) index
  · intro hall x y hxy
    funext index
    exact hall index hxy

/-- The reachable range of a stronger query maps canonically onto the
reachable range of every query whose kernel it refines. -/
noncomputable def reachableFactor {X Strong Weak : Type*}
    (strong : X → Strong) (weak : X → Weak)
    (_hrefines : KernelRefines strong weak) :
    Set.range strong → Set.range weak :=
  fun value =>
    ⟨weak (Classical.choose value.property),
      ⟨Classical.choose value.property, rfl⟩⟩

theorem reachableFactor_apply {X Strong Weak : Type*}
    (strong : X → Strong) (weak : X → Weak)
    (hrefines : KernelRefines strong weak) (x : X) :
    reachableFactor strong weak hrefines ⟨strong x, ⟨x, rfl⟩⟩ =
      ⟨weak x, ⟨x, rfl⟩⟩ := by
  apply Subtype.ext
  exact hrefines (Classical.choose_spec
    (show strong x ∈ Set.range strong from ⟨x, rfl⟩))

theorem reachableFactor_surjective {X Strong Weak : Type*}
    (strong : X → Strong) (weak : X → Weak)
    (hrefines : KernelRefines strong weak) :
    Function.Surjective (reachableFactor strong weak hrefines) := by
  rintro ⟨value, x, rfl⟩
  exact ⟨⟨strong x, ⟨x, rfl⟩⟩,
    reachableFactor_apply strong weak hrefines x⟩

/-- Kernel refinement imposes the exact finite lower bound on the cardinality
of a direct carrier's reachable image. -/
theorem reachable_card_le_of_kernelRefines
    {X Strong Weak : Type*} [Fintype X]
    (strong : X → Strong) (weak : X → Weak)
    (hrefines : KernelRefines strong weak) :
    Nat.card (Set.range weak) ≤ Nat.card (Set.range strong) := by
  letI : Finite (Set.range strong) := Finite.Set.finite_range strong
  exact Nat.card_le_card_of_surjective
    (reachableFactor strong weak hrefines)
    (reachableFactor_surjective strong weak hrefines)

/-- Any finite direct carrier that preserves a complete consumer family has
at least as many reachable labels as the family's product query. -/
theorem productQuery_minimum_carrier_cardinality
    {I X Reduction : Type*} {Answer : I → Type*}
    [Fintype X] (reduction : X → Reduction)
    (queries : ∀ index, X → Answer index)
    (hpreserves : ∀ index, KernelRefines reduction (queries index)) :
    Nat.card (Set.range (ProductQuery queries)) ≤
      Nat.card (Set.range reduction) := by
  apply reachable_card_le_of_kernelRefines
  exact (kernelRefines_productQuery_iff reduction queries).2 hpreserves

def jointToFirstRange {X A B : Type*} (first : X → A) (added : X → B) :
    Set.range (fun x => (first x, added x)) → Set.range first :=
  fun value =>
    ⟨value.1.1, by
      obtain ⟨x, hx⟩ := value.property
      exact ⟨x, congrArg Prod.fst hx⟩⟩

theorem jointToFirstRange_surjective {X A B : Type*}
    (first : X → A) (added : X → B) :
    Function.Surjective (jointToFirstRange first added) := by
  rintro ⟨value, x, rfl⟩
  refine ⟨⟨(first x, added x), ⟨x, rfl⟩⟩, ?_⟩
  rfl

abbrev SourceFiber {X A : Type*} (first : X → A)
    (value : Set.range first) :=
  {x : X // first x = value.1}

abbrev AddedFiberRange {X A B : Type*} (first : X → A)
    (added : X → B) (value : Set.range first) :=
  Set.range (fun x : SourceFiber first value => added x.1)

noncomputable def jointRangeToFiberSigma {X A B : Type*}
    (first : X → A) (added : X → B) :
    Set.range (fun x => (first x, added x)) →
      Σ value : Set.range first, AddedFiberRange first added value :=
  fun jointValue => by
    let source := Classical.choose jointValue.property
    have hsource := Classical.choose_spec jointValue.property
    let firstValue : Set.range first :=
      ⟨jointValue.1.1, ⟨source, congrArg Prod.fst hsource⟩⟩
    let fibreSource : SourceFiber first firstValue :=
      ⟨source, congrArg Prod.fst hsource⟩
    let addedValue : AddedFiberRange first added firstValue :=
      ⟨jointValue.1.2,
        ⟨fibreSource, congrArg Prod.snd hsource⟩⟩
    exact ⟨firstValue, addedValue⟩

noncomputable def fiberSigmaToJointRange {X A B : Type*}
    (first : X → A) (added : X → B) :
    (Σ value : Set.range first, AddedFiberRange first added value) →
      Set.range (fun x => (first x, added x)) :=
  fun fibreValue => by
    let source := Classical.choose fibreValue.2.property
    have hadded := Classical.choose_spec fibreValue.2.property
    exact ⟨(fibreValue.1.1, fibreValue.2.1),
      ⟨source.1, Prod.ext source.2 hadded⟩⟩

noncomputable def jointRangeFiberEquiv {X A B : Type*}
    (first : X → A) (added : X → B) :
    Set.range (fun x => (first x, added x)) ≃
      Σ value : Set.range first, AddedFiberRange first added value where
  toFun := jointRangeToFiberSigma first added
  invFun := fiberSigmaToJointRange first added
  left_inv := by
    intro jointValue
    apply Subtype.ext
    rfl
  right_inv := by
    intro fibreValue
    have hFirst :
        (jointRangeToFiberSigma first added
          (fiberSigmaToJointRange first added fibreValue)).1 =
          fibreValue.1 := by
      apply Subtype.ext
      rfl
    cases hFirst
    apply Sigma.ext rfl
    exact heq_of_eq (Subtype.ext (by rfl))

/-- The joint carrier cardinality is the sum of its realized added-label
cardinalities over all old carrier blocks. -/
theorem joint_range_card_eq_sum_fiber_cards
    {X A B : Type*} [Fintype X] (first : X → A) (added : X → B) :
    Nat.card (Set.range (fun x => (first x, added x))) =
      letI : Fintype (Set.range first) :=
        (Set.finite_range first).fintype
      ∑ value : Set.range first,
        Nat.card (AddedFiberRange first added value) := by
  letI : Fintype (Set.range first) := (Set.finite_range first).fintype
  letI : ∀ value : Set.range first,
      Finite (AddedFiberRange first added value) :=
    fun _ => Finite.Set.finite_range _
  calc
    Nat.card (Set.range (fun x => (first x, added x))) =
        Nat.card
          (Σ value : Set.range first,
            AddedFiberRange first added value) :=
      Nat.card_congr (jointRangeFiberEquiv first added)
    _ = ∑ value : Set.range first,
          Nat.card (AddedFiberRange first added value) := Nat.card_sigma

theorem jointToFirstRange_injective_iff_redundant {X A B : Type*}
    (first : X → A) (added : X → B) :
    Function.Injective (jointToFirstRange first added) ↔
      KernelRefines first added := by
  constructor
  · intro hinjective x y hfirst
    let left : Set.range (fun z => (first z, added z)) :=
      ⟨(first x, added x), ⟨x, rfl⟩⟩
    let right : Set.range (fun z => (first z, added z)) :=
      ⟨(first y, added y), ⟨y, rfl⟩⟩
    have hprojection :
        jointToFirstRange first added left =
          jointToFirstRange first added right := by
      apply Subtype.ext
      exact hfirst
    have hjoint := congrArg Subtype.val (hinjective hprojection)
    exact congrArg Prod.snd hjoint
  · intro hreduction left right hprojection
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg Subtype.val hprojection
    · obtain ⟨x, hx⟩ := left.property
      obtain ⟨y, hy⟩ := right.property
      have hfirst : first x = first y := by
        calc
          first x = left.1.1 := congrArg Prod.fst hx
          _ = right.1.1 := congrArg Subtype.val hprojection
          _ = first y := (congrArg Prod.fst hy).symm
      have hadded := hreduction hfirst
      calc
        left.1.2 = added x := (congrArg Prod.snd hx).symm
        _ = added y := hadded
        _ = right.1.2 := congrArg Prod.snd hy

/-- Equality of direct-carrier sizes is equivalent to redundancy of the added
consumer. -/
theorem joint_range_card_eq_iff_redundant
    {X A B : Type*} [Fintype X] (first : X → A) (added : X → B) :
    Nat.card (Set.range (fun x => (first x, added x))) =
        Nat.card (Set.range first) ↔
      KernelRefines first added := by
  letI : Finite (Set.range (fun x => (first x, added x))) :=
    Finite.Set.finite_range _
  letI : Finite (Set.range first) := Finite.Set.finite_range first
  letI : Fintype (Set.range (fun x => (first x, added x))) :=
    Fintype.ofFinite _
  letI : Fintype (Set.range first) := Fintype.ofFinite _
  have hsurjective := jointToFirstRange_surjective first added
  constructor
  · intro hcard
    have hcard' :
        Fintype.card (Set.range (fun x => (first x, added x))) =
          Fintype.card (Set.range first) := by
      simpa [← Nat.card_eq_fintype_card] using hcard
    have hbijective : Function.Bijective (jointToFirstRange first added) :=
      (Fintype.bijective_iff_surjective_and_card _).2
        ⟨hsurjective, hcard'⟩
    exact (jointToFirstRange_injective_iff_redundant first added).1
      hbijective.1
  · intro hreduction
    have hinjective :=
      (jointToFirstRange_injective_iff_redundant first added).2 hreduction
    have hcard := (Fintype.bijective_iff_injective_and_card _).1
      ⟨hinjective, hsurjective⟩ |>.2
    simpa [← Nat.card_eq_fintype_card] using hcard

/-- The added-consumer price is the number of new reachable labels beyond the
old direct carrier. -/
noncomputable def AddedConsumerPrice {X A B : Type*} [Fintype X]
    (first : X → A) (added : X → B) : Nat :=
  Nat.card (Set.range (fun x => (first x, added x))) -
    Nat.card (Set.range first)

/-- The blockwise price is the sum of the additional labels introduced inside
each old direct-carrier block. -/
noncomputable def BlockwiseAddedConsumerPrice
    {X A B : Type*} [Fintype X] (first : X → A) (added : X → B) : Nat := by
  letI : Fintype (Set.range first) := (Set.finite_range first).fintype
  exact ∑ value : Set.range first,
    (Nat.card (AddedFiberRange first added value) - 1)

/-- The blockwise price formula equals the difference between the refined and
old reachable carrier cardinalities. -/
theorem blockwiseAddedConsumerPrice_eq
    {X A B : Type*} [Fintype X] (first : X → A) (added : X → B) :
    BlockwiseAddedConsumerPrice first added =
      AddedConsumerPrice first added := by
  letI : Fintype (Set.range first) := (Set.finite_range first).fintype
  letI : ∀ value : Set.range first,
      Finite (AddedFiberRange first added value) :=
    fun _ => Finite.Set.finite_range _
  have hPositive : ∀ value : Set.range first,
      0 < Nat.card (AddedFiberRange first added value) := by
    intro value
    obtain ⟨source, hsource⟩ := value.property
    let fibreSource : SourceFiber first value := ⟨source, hsource⟩
    let addedValue : AddedFiberRange first added value :=
      ⟨added source, ⟨fibreSource, rfl⟩⟩
    letI : Nonempty (AddedFiberRange first added value) := ⟨addedValue⟩
    exact Nat.card_pos
  have hSum :
      (∑ value : Set.range first,
          (Nat.card (AddedFiberRange first added value) - 1)) +
          Fintype.card (Set.range first) =
        ∑ value : Set.range first,
          Nat.card (AddedFiberRange first added value) := by
    calc
      (∑ value : Set.range first,
          (Nat.card (AddedFiberRange first added value) - 1)) +
          Fintype.card (Set.range first) =
        (∑ value : Set.range first,
          (Nat.card (AddedFiberRange first added value) - 1)) +
          ∑ _value : Set.range first, 1 := by simp
      _ = ∑ value : Set.range first,
          ((Nat.card (AddedFiberRange first added value) - 1) + 1) := by
        rw [Finset.sum_add_distrib]
      _ = ∑ value : Set.range first,
          Nat.card (AddedFiberRange first added value) := by
        apply Finset.sum_congr rfl
        intro value _
        exact Nat.sub_add_cancel (hPositive value)
  have hDifference :
      (∑ value : Set.range first,
          (Nat.card (AddedFiberRange first added value) - 1)) =
        (∑ value : Set.range first,
          Nat.card (AddedFiberRange first added value)) -
            Fintype.card (Set.range first) :=
    Nat.eq_sub_of_add_eq hSum
  rw [BlockwiseAddedConsumerPrice, AddedConsumerPrice, hDifference]
  rw [← joint_range_card_eq_sum_fiber_cards first added]
  congr 1
  exact Nat.card_eq_fintype_card.symm

def priceFixtureFirst (_ : Fin 3) : Bool := false

def priceFixtureAdded (value : Fin 3) : Fin 3 := value

theorem priceFixtureJoint_injective :
    Function.Injective
      (fun value : Fin 3 =>
        (priceFixtureFirst value, priceFixtureAdded value)) := by
  intro first second hequal
  exact congrArg Prod.snd hequal

/-- Exact registered price-two fixture. -/
theorem fin_a5_price_02 :
    AddedConsumerPrice priceFixtureFirst priceFixtureAdded = 2 ∧
      BlockwiseAddedConsumerPrice priceFixtureFirst priceFixtureAdded = 2 := by
  have hJointCard :
      Nat.card
        (Set.range (fun value : Fin 3 =>
          (priceFixtureFirst value, priceFixtureAdded value))) = 3 := by
    rw [Nat.card_coe_set_eq,
      Set.ncard_range_of_injective priceFixtureJoint_injective]
    exact Nat.card_fin 3
  have hFirstRange : Set.range priceFixtureFirst = {false} := by
    ext value
    constructor
    · rintro ⟨source, rfl⟩
      simp [priceFixtureFirst]
    · intro hvalue
      have : value = false := by simpa using hvalue
      subst value
      exact ⟨0, rfl⟩
  have hFirstCard : Nat.card (Set.range priceFixtureFirst) = 1 := by
    rw [Nat.card_coe_set_eq, hFirstRange]
    simp
  have hDirect :
      AddedConsumerPrice priceFixtureFirst priceFixtureAdded = 2 := by
    unfold AddedConsumerPrice
    rw [hJointCard, hFirstCard]
  exact ⟨hDirect,
    (blockwiseAddedConsumerPrice_eq
      priceFixtureFirst priceFixtureAdded).trans hDirect⟩

theorem addedConsumerPrice_eq_zero_iff_redundant
    {X A B : Type*} [Fintype X] (first : X → A) (added : X → B) :
    AddedConsumerPrice first added = 0 ↔ KernelRefines first added := by
  letI : Finite (Set.range (fun x => (first x, added x))) :=
    Finite.Set.finite_range _
  have hle : Nat.card (Set.range first) ≤
      Nat.card (Set.range (fun x => (first x, added x))) :=
    Nat.card_le_card_of_surjective (jointToFirstRange first added)
      (jointToFirstRange_surjective first added)
  constructor
  · intro hzero
    have hreverse : Nat.card (Set.range (fun x => (first x, added x))) ≤
        Nat.card (Set.range first) :=
      Nat.sub_eq_zero_iff_le.mp (by
        simpa [AddedConsumerPrice] using hzero)
    exact (joint_range_card_eq_iff_redundant first added).1
      (Nat.le_antisymm hreverse hle)
  · intro hreduction
    have heq :=
      (joint_range_card_eq_iff_redundant first added).2 hreduction
    unfold AddedConsumerPrice
    rw [heq]
    exact Nat.sub_self _

/-- A collapsed distinction cannot be reconstructed by any deterministic
suffix that receives only the reduced value. -/
theorem irreversible_deterministic_loss {X S Q O : Type*}
    (reduction : X → S) (query : X → Q) (suffix : S → O)
    {x y : X} (hcollision : reduction x = reduction y)
    (hdistinction : query x ≠ query y) :
    suffix (reduction x) = suffix (reduction y) ∧
      ¬∃ reader : S → Q, query = reader ∘ reduction := by
  refine ⟨congrArg suffix hcollision, ?_⟩
  rintro ⟨reader, hreader⟩
  apply hdistinction
  rw [hreader]
  exact congrArg reader hcollision

/-- The same no-recovery result holds for a Markov suffix represented by its
complete output-probability row. -/
theorem irreversible_markov_loss {X S Q O : Type*}
    (reduction : X → S) (query : X → Q) (kernel : S → O → ℚ)
    {x y : X} (hcollision : reduction x = reduction y)
    (hdistinction : query x ≠ query y) :
    kernel (reduction x) = kernel (reduction y) ∧
      ¬∃ reader : S → Q, query = reader ∘ reduction := by
  exact ⟨congrArg kernel hcollision,
    (irreversible_deterministic_loss reduction query id
      hcollision hdistinction).2⟩

/-- A stage is the first loss point exactly when it fails to preserve the
query and every earlier stage preserves it. -/
def FirstLossAt {Index X State Answer : Type*} [LT Index]
    (stages : Index → X → State) (query : X → Answer) (index : Index) : Prop :=
  ¬KernelRefines (stages index) query ∧
    ∀ earlier, earlier < index → KernelRefines (stages earlier) query

noncomputable def lossIndexSet
    {Index X State Answer : Type*} [Fintype Index]
    (stages : Index → X → State) (query : X → Answer) : Finset Index := by
  classical
  exact Finset.univ.filter
    (fun index => ¬KernelRefines (stages index) query)

theorem mem_lossIndexSet_iff
    {Index X State Answer : Type*} [Fintype Index]
    (stages : Index → X → State) (query : X → Answer) (index : Index) :
    index ∈ lossIndexSet stages query ↔
      ¬KernelRefines (stages index) query := by
  classical
  simp [lossIndexSet]

theorem lossIndexSet_nonempty
    {Index X State Answer : Type*} [Fintype Index]
    (stages : Index → X → State) (query : X → Answer)
    (hloss : ∃ index, ¬KernelRefines (stages index) query) :
    (lossIndexSet stages query).Nonempty := by
  obtain ⟨index, hindex⟩ := hloss
  exact ⟨index, (mem_lossIndexSet_iff stages query index).2 hindex⟩

noncomputable def firstLossIndex
    {Index X State Answer : Type*} [Fintype Index] [LinearOrder Index]
    (stages : Index → X → State) (query : X → Answer)
    (hloss : ∃ index, ¬KernelRefines (stages index) query) : Index :=
  (lossIndexSet stages query).min'
    (lossIndexSet_nonempty stages query hloss)

/-- Every finite ordered chain with a loss has a least loss stage, and all
earlier stages preserve the query. -/
theorem firstLossIndex_specification
    {Index X State Answer : Type*} [Fintype Index] [LinearOrder Index]
    (stages : Index → X → State) (query : X → Answer)
    (hloss : ∃ index, ¬KernelRefines (stages index) query) :
    FirstLossAt stages query (firstLossIndex stages query hloss) := by
  classical
  let losses := lossIndexSet stages query
  have hNonempty : losses.Nonempty := lossIndexSet_nonempty stages query hloss
  have hMember : firstLossIndex stages query hloss ∈ losses := by
    exact Finset.min'_mem losses hNonempty
  constructor
  · exact (mem_lossIndexSet_iff stages query _).1 hMember
  · intro earlier hearlier
    by_contra hEarlierLoss
    have hEarlierMember : earlier ∈ losses :=
      (mem_lossIndexSet_iff stages query earlier).2 hEarlierLoss
    have hMinimum : firstLossIndex stages query hloss ≤ earlier := by
      exact Finset.min'_le losses earlier hEarlierMember
    exact (not_le_of_gt hearlier) hMinimum

/-- A declared first loss supplies a concrete collapsed distinction, and no
deterministic suffix receiving only that stage can reconstruct it. -/
theorem firstLossAt_supplies_irreversible_witness
    {Index X State Answer : Type*} [LT Index]
    (stages : Index → X → State) (query : X → Answer) (index : Index)
    (hloss : FirstLossAt stages query index) :
    ∃ x y, stages index x = stages index y ∧ query x ≠ query y ∧
      ∀ (Output : Type*) (suffix : State → Output),
        suffix (stages index x) = suffix (stages index y) := by
  classical
  simp only [FirstLossAt, KernelRefines] at hloss
  push Not at hloss
  obtain ⟨x, y, hcollision, hdistinction⟩ := hloss.1
  exact ⟨x, y, hcollision, hdistinction,
    fun _ suffix => congrArg suffix hcollision⟩

inductive TwoStageCarrier where
  | first
  | second
  deriving DecidableEq, Fintype, Repr

def registeredTwoStageReduction : Fin 2 → TwoStageCarrier → TwoStageCarrier
  | 0 => id
  | 1 => fun _ => .first

def registeredTwoStageQuery : TwoStageCarrier → TwoStageCarrier := id

/-- Exact registered two-stage fixture: stage zero preserves the distinction,
and stage one is the first loss. -/
theorem fin_a5_loss_03 :
    FirstLossAt registeredTwoStageReduction registeredTwoStageQuery 1 := by
  constructor
  · intro hrefines
    have hcollapse : registeredTwoStageQuery TwoStageCarrier.first =
        registeredTwoStageQuery TwoStageCarrier.second :=
      hrefines (show registeredTwoStageReduction 1 TwoStageCarrier.first =
        registeredTwoStageReduction 1 TwoStageCarrier.second from rfl)
    cases hcollapse
  · intro earlier hearlier
    fin_cases earlier
    · intro x y hxy
      exact hxy
    · norm_num at hearlier

def NewCollisionSet {X Y Z : Type*} [Fintype X]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (first : X → Y) (second : Y → Z) : Finset (X × X) :=
  (Finset.univ ×ˢ Finset.univ).filter
    (fun pair => pair.1 ≠ pair.2 ∧ first pair.1 ≠ first pair.2 ∧
      second (first pair.1) = second (first pair.2))

theorem mem_newCollisionSet_iff {X Y Z : Type*} [Fintype X]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (first : X → Y) (second : Y → Z) (x y : X) :
    (x, y) ∈ NewCollisionSet first second ↔
      x ≠ y ∧ first x ≠ first y ∧ second (first x) = second (first y) := by
  simp [NewCollisionSet]

/-- Composite collisions decompose into inherited collisions and exactly the
new collisions introduced at the next stage. -/
theorem collisionSet_comp_decomposition
    {X Y Z : Type*} [Fintype X]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (first : X → Y) (second : Y → Z) :
    CollisionSet (second ∘ first) =
      CollisionSet first ∪ NewCollisionSet first second := by
  ext pair
  rcases pair with ⟨x, y⟩
  simp only [mem_collisionSet_iff, Finset.mem_union,
    mem_newCollisionSet_iff, Function.comp_apply]
  constructor
  · rintro ⟨hne, hcomposite⟩
    by_cases hfirst : first x = first y
    · exact Or.inl ⟨hne, hfirst⟩
    · exact Or.inr ⟨hne, hfirst, hcomposite⟩
  · rintro (hinherited | hnew)
    · exact ⟨hinherited.1, congrArg second hinherited.2⟩
    · exact ⟨hnew.1, hnew.2.2⟩

theorem collisionSet_comp_decomposition_disjoint
    {X Y Z : Type*} [Fintype X]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (first : X → Y) (second : Y → Z) :
    Disjoint (CollisionSet first) (NewCollisionSet first second) := by
  apply Finset.disjoint_left.2
  intro pair hinherited hnew
  have hfirst := (mem_collisionSet_iff first pair.1 pair.2).1 hinherited |>.2
  have hnotFirst :=
    (mem_newCollisionSet_iff first second pair.1 pair.2).1 hnew |>.2.1
  exact hnotFirst hfirst

/-- Integrated FIN-A5 carrier-algebra theorem. -/
theorem fin_a5_carrierAlgebra
    {X A B S Q O : Type*} [Fintype X]
    (first : X → A) (added : X → B)
    (reduction : X → S) (query : X → Q) (suffix : S → O) :
    (Nat.card (Set.range (fun x => (first x, added x))) =
        Nat.card (Set.range first) ↔ KernelRefines first added) ∧
    (AddedConsumerPrice first added = 0 ↔ KernelRefines first added) ∧
    (∀ x y, reduction x = reduction y → query x ≠ query y →
      suffix (reduction x) = suffix (reduction y) ∧
        ¬∃ reader : S → Q, query = reader ∘ reduction) := by
  exact ⟨joint_range_card_eq_iff_redundant first added,
    addedConsumerPrice_eq_zero_iff_redundant first added,
    fun _ _ => irreversible_deterministic_loss reduction query suffix⟩

end PhonologicalCalculus
