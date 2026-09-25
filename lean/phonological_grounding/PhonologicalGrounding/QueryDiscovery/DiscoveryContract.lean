                                        
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import PhonologicalGrounding.Basic

namespace PhonologicalGrounding.QueryDiscovery

def TargetIndependent {T Q : Type*} (sel : T → Q) : Prop :=
  ∀ t t', sel t = sel t'

                
def Registered {T Q : Type*} (sel : T → Q) : Prop :=
  ∃ q, ∀ t, sel t = q

theorem registered_iff_targetIndependent {T Q : Type*} [Nonempty T] (sel : T → Q) :
    Registered sel ↔ TargetIndependent sel := by
  constructor
  · rintro ⟨q, hq⟩ t t'
    rw [hq t, hq t']
  · intro h
    obtain ⟨t₀⟩ := ‹Nonempty T›
    exact ⟨sel t₀, fun t => h t t₀⟩

theorem discovered_not_independent {T Q : Type*} [Nonempty T] (sel : T → Q)
    (hnc : ∃ t t', sel t ≠ sel t') : ¬ TargetIndependent sel := by
  rintro h
  obtain ⟨t, t', hne⟩ := hnc
  exact hne (h t t')

theorem reregistration_independent {D T Q : Type*} (sel : D → Q) (d : D) :
    TargetIndependent (fun _ : T => sel d) :=
  fun _ _ => rfl

structure DiscoveryContract (D Q : Type*) where
  select : D → Q
  range : Finset Q
  range_covers : ∀ d, select d ∈ range
  provenance : String

structure RegistrationContract (Q : Type*) where
  query : Q
  frozenBeforeTarget : Bool
  provenance : String

def reregister {D Q : Type*} (C : DiscoveryContract D Q) (d : D) :
    RegistrationContract Q where
  query := C.select d
  frozenBeforeTarget := true
  provenance := "discovered by policy: " ++ C.provenance

theorem reregister_is_independent {D T Q : Type*} (C : DiscoveryContract D Q) (d : D) :
    TargetIndependent (fun _ : T => (reregister C d).query) :=
  reregistration_independent C.select d

theorem reregister_retains_provenance {D Q : Type*} (C : DiscoveryContract D Q) (d : D) :
    (reregister C d).provenance ≠ "" := by
  simp [reregister]

theorem adaptive_selection_cost {D Q Ω : Type*} [DecidableEq Ω]
    (C : DiscoveryContract D Q) (bad : Q → Finset Ω) [DecidableEq Q] :
    (∀ d, bad (C.select d) ⊆ C.range.biUnion bad) ∧
      (C.range.biUnion bad).card ≤ ∑ q ∈ C.range, (bad q).card := by
  constructor
  · intro d
    exact Finset.subset_biUnion_of_mem bad (C.range_covers d)
  · exact Finset.card_biUnion_le

theorem adaptive_selection_uniform_cost {D Q Ω : Type*} [DecidableEq Ω] [DecidableEq Q]
    (C : DiscoveryContract D Q) (bad : Q → Finset Ω) (k : ℕ)
    (hk : ∀ q ∈ C.range, (bad q).card ≤ k) (d : D) :
    (bad (C.select d)).card ≤ C.range.card * k := by
  have hsub : bad (C.select d) ⊆ C.range.biUnion bad :=
    Finset.subset_biUnion_of_mem bad (C.range_covers d)
  refine le_trans (Finset.card_le_card hsub) ?_
  refine le_trans Finset.card_biUnion_le ?_
  calc ∑ q ∈ C.range, (bad q).card
      ≤ ∑ _q ∈ C.range, k := Finset.sum_le_sum hk
    _ = C.range.card * k := by simp [Finset.sum_const]

namespace DiscoveryWitness

def policy : Bool → Bool := id

theorem policy_not_independent : ¬ TargetIndependent policy :=
  discovered_not_independent policy ⟨true, false, by simp [policy]⟩

theorem policy_reregisters : TargetIndependent (fun _ : Bool => policy true) :=
  reregistration_independent policy true

def contract : DiscoveryContract Bool Bool where
  select := policy
  range := {false, true}
  range_covers := by intro d; cases d <;> simp [policy]
  provenance := "inspect the development prediction and report it"

theorem price_is_two : contract.range.card = 2 := by decide

end DiscoveryWitness

end PhonologicalGrounding.QueryDiscovery
