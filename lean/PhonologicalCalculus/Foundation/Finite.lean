import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Logic.Function.Basic

/-!
Reusable finite mathematics for the typed preservation calculus.

Nothing in this module is a phonological theorem.  These are ordinary finite
set, kernel, factorization, and no-recovery lemmas proved in Lean rather than
added to the trusted foundation as project axioms.
-/

namespace PhonologicalCalculus

def SameUnder {X Y : Type*} (f : X → Y) (x y : X) : Prop := f x = f y

def KernelRefines {X S W : Type*} (strong : X → S) (weak : X → W) : Prop :=
  ∀ ⦃x y⦄, strong x = strong y → weak x = weak y

theorem kernelRefines_refl {X Y : Type*} (f : X → Y) :
    KernelRefines f f := by
  intro x y h
  exact h

theorem kernelRefines_trans {X A B C : Type*} {f : X → A} {g : X → B}
    {h : X → C} (hfg : KernelRefines f g) (hgh : KernelRefines g h) :
    KernelRefines f h := by
  intro x y hxy
  exact hgh (hfg hxy)

theorem sameUnder_pair_iff {X A B : Type*} (f : X → A) (g : X → B)
    (x y : X) :
    SameUnder (fun z => (f z, g z)) x y ↔
      SameUnder f x y ∧ SameUnder g x y := by
  simp [SameUnder]

theorem pair_kernel_refines_left {X A B : Type*} (f : X → A) (g : X → B) :
    KernelRefines (fun x => (f x, g x)) f := by
  intro x y hxy
  exact congrArg Prod.fst hxy

theorem pair_kernel_refines_right {X A B : Type*} (f : X → A) (g : X → B) :
    KernelRefines (fun x => (f x, g x)) g := by
  intro x y hxy
  exact congrArg Prod.snd hxy

noncomputable def factorOnRange {X S W : Type*} (strong : X → S)
    (weak : X → W) (_h : KernelRefines strong weak) : Set.range strong → W :=
  fun y => weak (Classical.choose y.property)

theorem factorOnRange_apply {X S W : Type*} (strong : X → S)
    (weak : X → W) (h : KernelRefines strong weak) (x : X) :
    factorOnRange strong weak h ⟨strong x, ⟨x, rfl⟩⟩ = weak x := by
  apply h
  exact Classical.choose_spec (show strong x ∈ Set.range strong from ⟨x, rfl⟩)

theorem factor_through_range_iff_kernel_refines {X S W : Type*}
    (strong : X → S) (weak : X → W) :
    (∃ g : Set.range strong → W,
        ∀ x, g ⟨strong x, ⟨x, rfl⟩⟩ = weak x) ↔
      KernelRefines strong weak := by
  constructor
  · rintro ⟨g, hg⟩ x y hxy
    calc
      weak x = g ⟨strong x, ⟨x, rfl⟩⟩ := (hg x).symm
      _ = g ⟨strong y, ⟨y, rfl⟩⟩ := by
        congr
      _ = weak y := hg y
  · intro h
    exact ⟨factorOnRange strong weak h, factorOnRange_apply strong weak h⟩

theorem factorization_implies_kernel_refines {X S W : Type*}
    (strong : X → S) (weak : X → W) (g : S → W)
    (hfactor : weak = g ∘ strong) : KernelRefines strong weak := by
  intro x y hxy
  rw [hfactor]
  exact congrArg g hxy

theorem deterministic_suffix_cannot_recover {X S O : Type*}
    (reduce : X → S) (suffix : S → O) {x y : X}
    (hcollision : reduce x = reduce y) :
    suffix (reduce x) = suffix (reduce y) := by
  exact congrArg suffix hcollision

universe u v

theorem injective_iff_all_consumers_preserved {X : Type u} {S : Type v}
    (reduce : X → S) :
    Function.Injective reduce ↔
      ∀ (O : Type u) (consumer : X → O) ⦃x y : X⦄,
        reduce x = reduce y → consumer x = consumer y := by
  constructor
  · intro hinj O consumer x y hxy
    exact congrArg consumer (hinj hxy)
  · intro hall x y hxy
    exact hall X id hxy

def CollisionSet {X Y : Type*} [Fintype X] [DecidableEq X]
    [DecidableEq Y] (f : X → Y) : Finset (X × X) :=
  (Finset.univ ×ˢ Finset.univ).filter
    (fun xy => xy.1 ≠ xy.2 ∧ f xy.1 = f xy.2)

theorem mem_collisionSet_iff {X Y : Type*} [Fintype X]
    [DecidableEq X] [DecidableEq Y] (f : X → Y) (x y : X) :
    (x, y) ∈ CollisionSet f ↔ x ≠ y ∧ f x = f y := by
  simp [CollisionSet]

theorem collisionSet_empty_iff_injective {X Y : Type*} [Fintype X]
    [DecidableEq X] [DecidableEq Y] (f : X → Y) :
    CollisionSet f = ∅ ↔ Function.Injective f := by
  constructor
  · intro hempty x y hxy
    by_contra hne
    have hmem : (x, y) ∈ CollisionSet f :=
      (mem_collisionSet_iff f x y).2 ⟨hne, hxy⟩
    simp [hempty] at hmem
  · intro hinj
    apply Finset.eq_empty_iff_forall_notMem.2
    rintro ⟨x, y⟩ hmem
    have h := (mem_collisionSet_iff f x y).1 hmem
    exact h.1 (hinj h.2)

def HasInverseOnRange {X Y : Type*} (f : X → Y) : Prop :=
  ∃ g : Set.range f → X, ∀ x, g ⟨f x, ⟨x, rfl⟩⟩ = x

theorem hasInverseOnRange_iff_injective {X Y : Type*} (f : X → Y) :
    HasInverseOnRange f ↔ Function.Injective f := by
  constructor
  · rintro ⟨g, hg⟩ x y hxy
    calc
      x = g ⟨f x, ⟨x, rfl⟩⟩ := (hg x).symm
      _ = g ⟨f y, ⟨y, rfl⟩⟩ := by
        congr
      _ = y := hg y
  · intro hinj
    let g : Set.range f → X := fun y => Classical.choose y.property
    refine ⟨g, ?_⟩
    intro x
    apply hinj
    exact Classical.choose_spec (show f x ∈ Set.range f from ⟨x, rfl⟩)

theorem nonempty_range_of_nonempty {X Y : Type*} [Nonempty X] (f : X → Y) :
    (Set.range f).Nonempty := by
  let x : X := Classical.choice inferInstance
  exact ⟨f x, ⟨x, rfl⟩⟩

end PhonologicalCalculus
