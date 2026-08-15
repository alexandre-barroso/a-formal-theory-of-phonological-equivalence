import PhonologicalCalculus.MaxEnt.ExactCore
import Mathlib

/-!
Finite MaxEnt fibre masses and exact sign transport.

Candidate identity remains explicit in every finite sum.  Consequently,
distinct candidates with identical violation rows contribute with their full
multiplicity.  Integer violation rows are represented by Laurent monomials on
the positive activity cube.
-/

namespace PhonologicalCalculus.MaxEnt

open Set

section LaurentMass

variable {K J C Y : Type*}
  [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [Fintype J] [Fintype C] [DecidableEq Y]

/-- Laurent monomial associated with one integer violation row. -/
def laurentMonomial (row : J → ℤ) (activity : J → K) : K :=
  ∏ j, activity j ^ row j

/-- Unnormalized mass of one candidate label. -/
def candidateMass (baseMass : C → K) (row : C → J → ℤ)
    (activity : J → K) (candidate : C) : K :=
  baseMass candidate * laurentMonomial (row candidate) activity

/-- Complete partition mass over all candidate labels. -/
def partitionMass (baseMass : C → K) (row : C → J → ℤ)
    (activity : J → K) : K :=
  ∑ candidate, candidateMass baseMass row activity candidate

/-- Unnormalized mass of a declared consequence fibre. -/
def fibreMass (baseMass : C → K) (row : C → J → ℤ)
    (consequence : C → Y) (answer : Y) (activity : J → K) : K :=
  ∑ candidate, if consequence candidate = answer then
    candidateMass baseMass row activity candidate else 0

/-- Normalized probability of a declared consequence fibre. -/
def consequenceProbability (baseMass : C → K) (row : C → J → ℤ)
    (consequence : C → Y) (answer : Y) (activity : J → K) : K :=
  fibreMass baseMass row consequence answer activity /
    partitionMass baseMass row activity

/-- Every Laurent monomial is positive on the positive activity cube. -/
theorem laurentMonomial_pos (row : J → ℤ) (activity : J → K)
    (hactivity : ∀ j, 0 < activity j) :
    0 < laurentMonomial row activity := by
  exact Finset.prod_pos fun j _ ↦ zpow_pos (hactivity j) _

omit [Fintype C] in
/-- Every explicitly labelled candidate has positive mass when all declared
base masses and activities are positive. -/
theorem candidateMass_pos (baseMass : C → K) (row : C → J → ℤ)
    (activity : J → K) (hbase : ∀ c, 0 < baseMass c)
    (hactivity : ∀ j, 0 < activity j) (candidate : C) :
    0 < candidateMass baseMass row activity candidate :=
  mul_pos (hbase candidate)
    (laurentMonomial_pos (row candidate) activity hactivity)

/-- A nonempty complete finite candidate ledger has a positive partition
mass on the positive activity cube. -/
theorem partitionMass_pos [Nonempty C]
    (baseMass : C → K) (row : C → J → ℤ) (activity : J → K)
    (hbase : ∀ c, 0 < baseMass c) (hactivity : ∀ j, 0 < activity j) :
    0 < partitionMass baseMass row activity := by
  classical
  exact Finset.sum_pos' (fun c _ ↦ (candidateMass_pos baseMass row activity
    hbase hactivity c).le) (by
      let c : C := Classical.choice (inferInstance : Nonempty C)
      exact ⟨c, Finset.mem_univ c,
        candidateMass_pos baseMass row activity hbase hactivity c⟩)

/-- A consequence fibre containing an explicitly labelled candidate has
positive mass. -/
theorem fibreMass_pos_of_mem
    (baseMass : C → K) (row : C → J → ℤ) (consequence : C → Y)
    (answer : Y) (activity : J → K) (hbase : ∀ c, 0 < baseMass c)
    (hactivity : ∀ j, 0 < activity j)
    (candidate : C) (hcandidate : consequence candidate = answer) :
    0 < fibreMass baseMass row consequence answer activity := by
  classical
  apply Finset.sum_pos'
  · intro c _
    split_ifs
    · exact (candidateMass_pos baseMass row activity hbase hactivity c).le
    · exact le_rfl
  · refine ⟨candidate, Finset.mem_univ candidate, ?_⟩
    simp [hcandidate, candidateMass_pos baseMass row activity hbase hactivity]

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- The partition mass is the sum of all consequence-fibre masses.  This
identity records that the consequence map partitions, rather than deletes,
the complete candidate support. -/
theorem sum_fibreMass_eq_partitionMass [Fintype Y]
    (baseMass : C → K) (row : C → J → ℤ) (consequence : C → Y)
    (activity : J → K) :
    ∑ answer, fibreMass baseMass row consequence answer activity =
      partitionMass baseMass row activity := by
  classical
  simp only [fibreMass, partitionMass]
  rw [Finset.sum_comm]
  simp [eq_comm]

/-- Exact cross-input relative-partition margin.  Its orientation is chosen
so that nonnegativity means that the right-hand consequence probability is at
least the left-hand probability. -/
def relativePartitionMargin
    {C₁ C₂ : Type*} [Fintype C₁] [Fintype C₂]
    (baseMass₁ : C₁ → K) (row₁ : C₁ → J → ℤ)
    (consequence₁ : C₁ → Y) (answer₁ : Y)
    (baseMass₂ : C₂ → K) (row₂ : C₂ → J → ℤ)
    (consequence₂ : C₂ → Y) (answer₂ : Y)
    (activity : J → K) : K :=
  fibreMass baseMass₂ row₂ consequence₂ answer₂ activity *
      partitionMass baseMass₁ row₁ activity -
    fibreMass baseMass₁ row₁ consequence₁ answer₁ activity *
      partitionMass baseMass₂ row₂ activity

/-- **MAX-G1.CARRIER.01**.  For two complete nonempty finite ledgers, exact
cross-input consequence-probability order is equivalent to nonnegativity of
the relative-partition Laurent margin. -/
theorem max_g1_carrier_01
    {C₁ C₂ : Type*} [Fintype C₁] [Fintype C₂]
    [Nonempty C₁] [Nonempty C₂]
    (baseMass₁ : C₁ → K) (row₁ : C₁ → J → ℤ)
    (consequence₁ : C₁ → Y) (answer₁ : Y)
    (baseMass₂ : C₂ → K) (row₂ : C₂ → J → ℤ)
    (consequence₂ : C₂ → Y) (answer₂ : Y)
    (activity : J → K)
    (hbase₁ : ∀ c, 0 < baseMass₁ c) (hbase₂ : ∀ c, 0 < baseMass₂ c)
    (hactivity : ∀ j, 0 < activity j) :
    consequenceProbability baseMass₁ row₁ consequence₁ answer₁ activity ≤
        consequenceProbability baseMass₂ row₂ consequence₂ answer₂ activity ↔
      0 ≤ relativePartitionMargin baseMass₁ row₁ consequence₁ answer₁
        baseMass₂ row₂ consequence₂ answer₂ activity := by
  have hZ₁ := partitionMass_pos baseMass₁ row₁ activity hbase₁ hactivity
  have hZ₂ := partitionMass_pos baseMass₂ row₂ activity hbase₂ hactivity
  rw [consequenceProbability, consequenceProbability,
    normalized_order_iff_cross_product hZ₁ hZ₂]
  simp only [relativePartitionMargin, sub_nonneg]

/-- Positive multivariate monomial used to clear Laurent exponents. -/
def positiveClearingMonomial (shift : J → ℕ) (activity : J → K) : K :=
  ∏ j, activity j ^ shift j

/-- The Laurent-clearing monomial is strictly positive on the physical
activity cube. -/
theorem positiveClearingMonomial_pos (shift : J → ℕ) (activity : J → K)
    (hactivity : ∀ j, 0 < activity j) :
    0 < positiveClearingMonomial shift activity := by
  exact Finset.prod_pos fun j _ ↦ pow_pos (hactivity j) _

/-- **MAX-G1.CLEAR.02**.  Multiplication by the common positive clearing
monomial preserves equality, weak sign, and strict sign exactly. -/
theorem max_g1_clear_02 (shift : J → ℕ) (activity : J → K) (margin : K)
    (hactivity : ∀ j, 0 < activity j) :
    (positiveClearingMonomial shift activity * margin = 0 ↔ margin = 0) ∧
    (0 ≤ positiveClearingMonomial shift activity * margin ↔ 0 ≤ margin) ∧
    (0 < positiveClearingMonomial shift activity * margin ↔ 0 < margin) := by
  have hclear := positiveClearingMonomial_pos shift activity hactivity
  constructor
  · simp [ne_of_gt hclear]
  · constructor
    · exact positive_clearing_preserves_nonneg hclear
    · exact (mul_pos_iff_of_pos_left hclear)

end LaurentMass

section Closure

/-- Open physical activity cube for a finite constraint index. -/
def openActivityCube (J : Type*) : Set (J → ℝ) :=
  (Set.univ : Set J).pi fun _ ↦ Set.Ioo 0 1

/-- Closed cube used only to test universal polynomial nonnegativity. -/
def closedActivityCube (J : Type*) : Set (J → ℝ) :=
  (Set.univ : Set J).pi fun _ ↦ Set.Icc 0 1

/-- The open physical activity cube is dense in its closed cube. -/
theorem closure_openActivityCube (J : Type*) :
    closure (openActivityCube J) = closedActivityCube J := by
  rw [openActivityCube, closedActivityCube, closure_pi_set]
  congr 1
  funext _
  exact closure_Ioo zero_ne_one

/-- A continuous nonnegative function on a set is nonnegative on its closure. -/
theorem continuous_nonneg_on_closure {X : Type*} [TopologicalSpace X]
    (f : X → ℝ) (s : Set X) (hf : Continuous f)
    (hnonneg : ∀ x ∈ s, 0 ≤ f x) :
    ∀ x ∈ closure s, 0 ≤ f x := by
  have hclosed : IsClosed {x | 0 ≤ f x} := isClosed_Ici.preimage hf
  exact fun x hx ↦ (closure_minimal hnonneg hclosed) hx

/-- **MAX-G1.CLOSURE.03**.  For a continuous cleared polynomial, universal
nonnegativity on the open physical cube is equivalent to universal
nonnegativity on the closed cube.  The closed cube is a proof domain; it does
not add boundary grammars to the open-cube MaxEnt contract. -/
theorem max_g1_closure_03 {J : Type*} (polynomial : (J → ℝ) → ℝ)
    (hcontinuous : Continuous polynomial) :
    (∀ activity ∈ openActivityCube J, 0 ≤ polynomial activity) ↔
      (∀ activity ∈ closedActivityCube J, 0 ≤ polynomial activity) := by
  constructor
  · intro hopen activity hactivity
    rw [← closure_openActivityCube J] at hactivity
    exact continuous_nonneg_on_closure polynomial (openActivityCube J)
      hcontinuous hopen activity hactivity
  · intro hclosed activity hactivity
    apply hclosed activity
    exact fun j _ ↦ ⟨(hactivity j (Set.mem_univ j)).1.le,
      (hactivity j (Set.mem_univ j)).2.le⟩

end Closure

end PhonologicalCalculus.MaxEnt
