                                     
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Order.SetNotation
import PhonologicalGrounding.Basic

universe u v w

set_option linter.checkUnivs false
set_option linter.unusedSectionVars false

namespace PhonologicalGrounding.QueryDiscovery

structure Protocols (X : Type u) where
  Index : Type v
  Readout : Index → Type w
  obs : (e : Index) → X → Readout e

namespace Protocols

variable {X : Type u} (P : Protocols.{u, v, w} X)

def kernelOn (E : Set P.Index) (x y : X) : Prop :=
  ∀ e ∈ E, P.obs e x = P.obs e y

def kernel (x y : X) : Prop := ∀ e, P.obs e x = P.obs e y

theorem kernel_eq_kernelOn_univ : P.kernel = P.kernelOn Set.univ := by
  funext x y
  simp [kernel, kernelOn]

theorem kernelOn_equivalence (E : Set P.Index) : Equivalence (P.kernelOn E) := by
  refine ⟨fun _ _ _ => rfl, fun h e he => (h e he).symm, ?_⟩
  intro x y z hxy hyz e he
  exact (hxy e he).trans (hyz e he)

def setoidOn (E : Set P.Index) : Setoid X where
  r := P.kernelOn E
  iseqv := P.kernelOn_equivalence E

def Answerable (E : Set P.Index) {A : Type*} (q : X → A) : Prop :=
  ∀ x y, P.kernelOn E x y → q x = q y

theorem answerable_iff_kernel_le (E : Set P.Index) {A : Type*} (q : X → A) :
    P.Answerable E q ↔ ∀ x y, P.kernelOn E x y → q x = q y :=
  Iff.rfl

theorem answerable_iff_factors (E : Set P.Index) {A : Type*} (q : X → A) :
    P.Answerable E q ↔
      ∃ g : Quotient (P.setoidOn E) → A, q = g ∘ Quotient.mk (P.setoidOn E) := by
  constructor
  · intro h
    refine ⟨Quotient.lift q h, ?_⟩
    funext x
    rfl
  · rintro ⟨g, rfl⟩ x y hxy
    exact congrArg g (Quotient.sound hxy)

theorem factor_unique (E : Set P.Index) {A : Type*}
    (g h : Quotient (P.setoidOn E) → A)
    (hgh : g ∘ Quotient.mk (P.setoidOn E) = h ∘ Quotient.mk (P.setoidOn E)) :
    g = h := by
  funext c
  induction c using Quotient.inductionOn with
  | h x => exact congrFun hgh x

theorem quotient_answerable (E : Set P.Index) :
    P.Answerable E (Quotient.mk (P.setoidOn E)) :=
  fun _ _ hxy => Quotient.sound hxy

theorem quotient_greatest (E : Set P.Index) {A : Type*} (q : X → A)
    (hq : P.Answerable E q) :
    ∃! g : Quotient (P.setoidOn E) → A, q = g ∘ Quotient.mk (P.setoidOn E) := by
  obtain ⟨g, hg⟩ := (P.answerable_iff_factors E q).1 hq
  refine ⟨g, hg, ?_⟩
  intro h hh
  exact P.factor_unique E h g (by rw [← hh, ← hg])

theorem quotient_unique_carrier {Y : Type*} (E : Set P.Index) (r : X → Y)
    (hsurj : Function.Surjective r)
    (hker : ∀ x y, r x = r y ↔ P.kernelOn E x y) :
    ∃ i : Quotient (P.setoidOn E) → Y,
      Function.Bijective i ∧ i ∘ Quotient.mk (P.setoidOn E) = r := by
  refine ⟨Quotient.lift r (fun x y h => (hker x y).2 h), ?_, rfl⟩
  constructor
  · intro a b hab
    induction a using Quotient.inductionOn with
    | h x =>
      induction b using Quotient.inductionOn with
      | h y => exact Quotient.sound ((hker x y).1 hab)
  · intro y
    obtain ⟨x, rfl⟩ := hsurj y
    exact ⟨Quotient.mk _ x, rfl⟩

                 
theorem kernelOn_antitone {E F : Set P.Index} (h : E ⊆ F) :
    ∀ x y, P.kernelOn F x y → P.kernelOn E x y :=
  fun _ _ hxy e he => hxy e (h he)

theorem kernelOn_insert (E : Set P.Index) (e : P.Index) :
    ∀ x y, P.kernelOn (insert e E) x y → P.kernelOn E x y :=
  P.kernelOn_antitone (Set.subset_insert e E)

theorem answerable_mono {E F : Set P.Index} (h : E ⊆ F) {A : Type*} {q : X → A}
    (hq : P.Answerable E q) : P.Answerable F q :=
  fun x y hxy => hq x y (P.kernelOn_antitone h x y hxy)

theorem kernelOn_insert_of_redundant (E : Set P.Index) (e : P.Index)
    (hred : ∀ x y, P.kernelOn E x y → P.obs e x = P.obs e y) :
    ∀ x y, P.kernelOn E x y ↔ P.kernelOn (insert e E) x y := by
  intro x y
  constructor
  · intro h f hf
    rcases hf with rfl | hf
    · exact hred x y h
    · exact h f hf
  · exact P.kernelOn_insert E e x y

                            
def redundancyClosure (E : Set P.Index) (A : Type*) : Set (X → A) :=
  {q | P.Answerable E q}

theorem redundancy_closure_eq_answerable (E : Set P.Index) (A : Type*) (q : X → A) :
    q ∈ P.redundancyClosure E A ↔ P.Answerable E q :=
  Iff.rfl

theorem redundancyClosure_monotone {E F : Set P.Index} (h : E ⊆ F) (A : Type*) :
    P.redundancyClosure E A ⊆ P.redundancyClosure F A :=
  fun _ hq => P.answerable_mono h hq

end Protocols

namespace Witness

def optionProtocols : Protocols Bool where
  Index := Unit
  Readout := fun _ => Option Bool
  obs := fun _ b => if b then some true else none

theorem option_separates :
    ¬ optionProtocols.kernelOn Set.univ true false := by
  intro h
  have := h () (Set.mem_univ _)
  simp [optionProtocols] at this

theorem empty_family_merges :
    optionProtocols.kernelOn (∅ : Set Unit) true false := by
  intro e he
  exact absurd he (Set.notMem_empty e)

theorem answerable_nonvacuous :
    optionProtocols.Answerable Set.univ (fun b : Bool => b) ∧
      optionProtocols.Answerable (∅ : Set Unit) (fun _ : Bool => ()) := by
  constructor
  · intro x y h
    have := h () (Set.mem_univ _)
    cases x <;> cases y <;> simp [optionProtocols] at this ⊢
  · intro _ _ _
    rfl

end Witness

namespace Battery

variable {X : Type u} {ι : Type v} {Ω : Type w}
variable [Fintype X] [DecidableEq X] [Fintype ι] [DecidableEq ι] [DecidableEq Ω]

def Separates (obs : ι → X → Ω) (E : Finset ι) : Prop :=
  ∀ x y : X, (∀ e ∈ E, obs e x = obs e y) → ∀ e : ι, obs e x = obs e y

instance decidableSeparates (obs : ι → X → Ω) (E : Finset ι) :
    Decidable (Separates obs E) := by
  unfold Separates
  infer_instance

theorem separates_univ (obs : ι → X → Ω) : Separates obs (Finset.univ : Finset ι) :=
  fun _ _ h e => h e (Finset.mem_univ e)

def separatingBatteries (obs : ι → X → Ω) : Finset (Finset ι) :=
  (Finset.univ : Finset (Finset ι)).filter (fun E => Separates obs E)

theorem mem_separatingBatteries (obs : ι → X → Ω) {E : Finset ι} :
    E ∈ separatingBatteries obs ↔ Separates obs E := by
  simp [separatingBatteries]

theorem separatingBatteries_nonempty (obs : ι → X → Ω) :
    (separatingBatteries obs).Nonempty :=
  ⟨Finset.univ, (mem_separatingBatteries obs).2 (separates_univ obs)⟩

def batteryCost (cost : ι → ℚ) (E : Finset ι) : ℚ := ∑ e ∈ E, cost e

theorem exists_min_cost (obs : ι → X → Ω) (cost : ι → ℚ) :
    ∃ E ∈ separatingBatteries obs,
      ∀ E' ∈ separatingBatteries obs, batteryCost cost E ≤ batteryCost cost E' :=
  Finset.exists_min_image _ (batteryCost cost) (separatingBatteries_nonempty obs)

def optima (obs : ι → X → Ω) (cost : ι → ℚ) : Finset (Finset ι) :=
  (separatingBatteries obs).filter
    (fun E => ∀ E' ∈ separatingBatteries obs, batteryCost cost E ≤ batteryCost cost E')

theorem optima_nonempty (obs : ι → X → Ω) (cost : ι → ℚ) :
    (optima obs cost).Nonempty := by
  obtain ⟨E, hE, hmin⟩ := exists_min_cost obs cost
  exact ⟨E, Finset.mem_filter.2 ⟨hE, hmin⟩⟩

theorem optima_all_equal_cost (obs : ι → X → Ω) (cost : ι → ℚ) {E E' : Finset ι}
    (hE : E ∈ optima obs cost) (hE' : E' ∈ optima obs cost) :
    batteryCost cost E = batteryCost cost E' := by
  rw [optima, Finset.mem_filter] at hE hE'
  exact le_antisymm (hE.2 E' hE'.1) (hE'.2 E hE.1)

theorem optima_subset_separating (obs : ι → X → Ω) (cost : ι → ℚ) :
    optima obs cost ⊆ separatingBatteries obs :=
  Finset.filter_subset _ _

variable {K : Type*} [Fintype K] [DecidableEq K]

def Dominates (criteria : K → Finset ι → ℚ) (E' E : Finset ι) : Prop :=
  (∀ k, criteria k E' ≤ criteria k E) ∧ ∃ k, criteria k E' < criteria k E

instance decidableDominates (criteria : K → Finset ι → ℚ) (E' E : Finset ι) :
    Decidable (Dominates criteria E' E) := by
  unfold Dominates
  infer_instance

def paretoFrontier (obs : ι → X → Ω) (criteria : K → Finset ι → ℚ) :
    Finset (Finset ι) :=
  (separatingBatteries obs).filter
    (fun E => ∀ E' ∈ separatingBatteries obs, ¬ Dominates criteria E' E)

theorem paretoFrontier_nonempty (obs : ι → X → Ω) (criteria : K → Finset ι → ℚ) :
    (paretoFrontier obs criteria).Nonempty := by
  classical
  obtain ⟨E, hE, hmin⟩ :=
    Finset.exists_min_image _ (fun E => ∑ k : K, criteria k E)
      (separatingBatteries_nonempty obs)
  refine ⟨E, Finset.mem_filter.2 ⟨hE, ?_⟩⟩
  rintro E' hE' ⟨hle, k, hlt⟩
  have hsum : ∑ k : K, criteria k E' < ∑ k : K, criteria k E :=
    Finset.sum_lt_sum (fun i _ => hle i) ⟨k, Finset.mem_univ k, hlt⟩
  exact absurd (hmin E' hE') (not_le.2 hsum)

end Battery

end PhonologicalGrounding.QueryDiscovery
