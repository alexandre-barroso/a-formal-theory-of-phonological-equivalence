                    
import Mathlib.Logic.Equiv.Defs
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Pi
import PhonologicalGrounding.QueryDiscovery.Grounding

set_option linter.unusedSectionVars false

namespace PhonologicalGrounding.QueryDiscovery

namespace Invariance

variable {X ι Ω : Type*}

structure Admissible (obs : ι → X → Ω) where
  state : X ≃ X
  protocol : ι ≃ ι
  equivariant : ∀ e x, obs (protocol e) (state x) = obs e x

variable {obs : ι → X → Ω}

def Admissible.symm (T : Admissible obs) : Admissible obs where
  state := T.state.symm
  protocol := T.protocol.symm
  equivariant := by
    intro e x
    have h := T.equivariant (T.protocol.symm e) (T.state.symm x)
    rw [T.protocol.apply_symm_apply, T.state.apply_symm_apply] at h
    exact h.symm

variable (T : Admissible obs)

theorem kernel_equivariant (x y : X) :
    (∀ e, obs e x = obs e y) ↔ (∀ e, obs e (T.state x) = obs e (T.state y)) := by
  constructor
  · intro h e
    have hx := T.equivariant (T.protocol.symm e) x
    have hy := T.equivariant (T.protocol.symm e) y
    rw [T.protocol.apply_symm_apply] at hx hy
    rw [hx, hy]
    exact h _
  · intro h e
    rw [← T.equivariant e x, ← T.equivariant e y]
    exact h _

theorem separates_image [DecidableEq ι] (E : Finset ι)
    (h : ∀ x y : X, (∀ e ∈ E, obs e x = obs e y) → ∀ e, obs e x = obs e y) :
    ∀ x y : X, (∀ e ∈ E.image T.protocol, obs e x = obs e y) → ∀ e, obs e x = obs e y := by
  intro x y hx e
  have hxy : ∀ f ∈ E, obs f (T.state.symm x) = obs f (T.state.symm y) := by
    intro f hf
    have hfx := T.equivariant f (T.state.symm x)
    have hfy := T.equivariant f (T.state.symm y)
    rw [T.state.apply_symm_apply] at hfx hfy
    rw [← hfx, ← hfy]
    exact hx (T.protocol f) (Finset.mem_image_of_mem _ hf)
  have hall := h (T.state.symm x) (T.state.symm y) hxy
  have hex : obs e x = obs (T.protocol.symm e) (T.state.symm x) := by
    have hh := T.equivariant (T.protocol.symm e) (T.state.symm x)
    rw [T.protocol.apply_symm_apply, T.state.apply_symm_apply] at hh
    exact hh
  have hey : obs e y = obs (T.protocol.symm e) (T.state.symm y) := by
    have hh := T.equivariant (T.protocol.symm e) (T.state.symm y)
    rw [T.protocol.apply_symm_apply, T.state.apply_symm_apply] at hh
    exact hh
  rw [hex, hey]
  exact hall _

theorem image_protocol_symm [DecidableEq ι] (E : Finset ι) :
    (E.image T.protocol).image T.protocol.symm = E := by
  rw [Finset.image_image]
  simp

theorem separates_iff_image [DecidableEq ι] (E : Finset ι) :
    (∀ x y : X, (∀ e ∈ E, obs e x = obs e y) → ∀ e, obs e x = obs e y) ↔
      (∀ x y : X, (∀ e ∈ E.image T.protocol, obs e x = obs e y) →
        ∀ e, obs e x = obs e y) := by
  constructor
  · exact separates_image T E
  · intro h
    have := separates_image T.symm (E.image T.protocol) h
    rwa [Admissible.symm, image_protocol_symm] at this

theorem batteryCost_image [DecidableEq ι] (cost : ι → ℚ)
    (hcost : ∀ e, cost (T.protocol e) = cost e) (E : Finset ι) :
    ∑ e ∈ E.image T.protocol, cost e = ∑ e ∈ E, cost e := by
  rw [Finset.sum_image (fun a _ b _ h => T.protocol.injective h)]
  exact Finset.sum_congr rfl (fun e _ => hcost e)

end Invariance

namespace InvarianceWitness

def obs : Bool → (Bool × Bool) → Bool
  | false, x => x.1
  | true, x => x.2

def relabel : Invariance.Admissible obs where
  state := Equiv.prodComm Bool Bool
  protocol := Equiv.mk not not (by decide) (by decide)
  equivariant := by decide

theorem relabel_swaps :
    relabel.protocol false = true ∧ relabel.protocol true = false := by decide

theorem neither_separates_alone :
    (¬ ∀ x y : Bool × Bool, (∀ e ∈ ({false} : Finset Bool), obs e x = obs e y) →
        ∀ e, obs e x = obs e y) ∧
      (¬ ∀ x y : Bool × Bool, (∀ e ∈ ({true} : Finset Bool), obs e x = obs e y) →
        ∀ e, obs e x = obs e y) := by
  decide

theorem cost_invariant (cost : Bool → ℚ) (h : ∀ e, cost (relabel.protocol e) = cost e) :
    cost false = cost true := by
  have := h false
  rw [relabel_swaps.1] at this
  exact this.symm

end InvarianceWitness

end PhonologicalGrounding.QueryDiscovery
