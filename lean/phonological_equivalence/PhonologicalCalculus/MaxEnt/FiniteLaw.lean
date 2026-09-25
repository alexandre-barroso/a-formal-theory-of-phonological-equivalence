import PhonologicalCalculus.MaxEnt.ExactCore
import Mathlib

namespace PhonologicalCalculus.MaxEnt

open Set

section LaurentMass

variable {K J C Y : Type*}
  [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [Fintype J] [Fintype C] [DecidableEq Y]

def laurentMonomial (row : J → ℤ) (activity : J → K) : K :=
  ∏ j, activity j ^ row j

def candidateMass (baseMass : C → K) (row : C → J → ℤ)
    (activity : J → K) (candidate : C) : K :=
  baseMass candidate * laurentMonomial (row candidate) activity

def partitionMass (baseMass : C → K) (row : C → J → ℤ)
    (activity : J → K) : K :=
  ∑ candidate, candidateMass baseMass row activity candidate

def fibreMass (baseMass : C → K) (row : C → J → ℤ)
    (consequence : C → Y) (answer : Y) (activity : J → K) : K :=
  ∑ candidate, if consequence candidate = answer then
    candidateMass baseMass row activity candidate else 0

def consequenceProbability (baseMass : C → K) (row : C → J → ℤ)
    (consequence : C → Y) (answer : Y) (activity : J → K) : K :=
  fibreMass baseMass row consequence answer activity /
    partitionMass baseMass row activity

theorem laurentMonomial_pos (row : J → ℤ) (activity : J → K)
    (hactivity : ∀ j, 0 < activity j) :
    0 < laurentMonomial row activity := by
  exact Finset.prod_pos fun j _ ↦ zpow_pos (hactivity j) _

omit [Fintype C] in
theorem candidateMass_pos (baseMass : C → K) (row : C → J → ℤ)
    (activity : J → K) (hbase : ∀ c, 0 < baseMass c)
    (hactivity : ∀ j, 0 < activity j) (candidate : C) :
    0 < candidateMass baseMass row activity candidate :=
  mul_pos (hbase candidate)
    (laurentMonomial_pos (row candidate) activity hactivity)

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
theorem sum_fibreMass_eq_partitionMass [Fintype Y]
    (baseMass : C → K) (row : C → J → ℤ) (consequence : C → Y)
    (activity : J → K) :
    ∑ answer, fibreMass baseMass row consequence answer activity =
      partitionMass baseMass row activity := by
  classical
  simp only [fibreMass, partitionMass]
  rw [Finset.sum_comm]
  simp [eq_comm]

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

def positiveClearingMonomial (shift : J → ℕ) (activity : J → K) : K :=
  ∏ j, activity j ^ shift j

theorem positiveClearingMonomial_pos (shift : J → ℕ) (activity : J → K)
    (hactivity : ∀ j, 0 < activity j) :
    0 < positiveClearingMonomial shift activity := by
  exact Finset.prod_pos fun j _ ↦ pow_pos (hactivity j) _

                  
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

def openActivityCube (J : Type*) : Set (J → ℝ) :=
  (Set.univ : Set J).pi fun _ ↦ Set.Ioo 0 1

def closedActivityCube (J : Type*) : Set (J → ℝ) :=
  (Set.univ : Set J).pi fun _ ↦ Set.Icc 0 1

theorem closure_openActivityCube (J : Type*) :
    closure (openActivityCube J) = closedActivityCube J := by
  rw [openActivityCube, closedActivityCube, closure_pi_set]
  congr 1
  funext _
  exact closure_Ioo zero_ne_one

theorem continuous_nonneg_on_closure {X : Type*} [TopologicalSpace X]
    (f : X → ℝ) (s : Set X) (hf : Continuous f)
    (hnonneg : ∀ x ∈ s, 0 ≤ f x) :
    ∀ x ∈ closure s, 0 ≤ f x := by
  have hclosed : IsClosed {x | 0 ≤ f x} := isClosed_Ici.preimage hf
  exact fun x hx ↦ (closure_minimal hnonneg hclosed) hx

                    
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
