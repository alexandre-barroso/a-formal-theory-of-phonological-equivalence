import PhonologicalCalculus.Foundation.Finite

/-!
Exact kernel and factorization lemmas underlying FIN-A4 and FIN-A5.
-/

namespace PhonologicalCalculus

theorem stronger_query_preservation_implies_weaker
    {X Strong Weak : Type*} (strong : X → Strong) (weak : X → Weak)
    (g : Strong → Weak) (hfactor : weak = g ∘ strong)
    {x y : X} (hstrong : strong x = strong y) : weak x = weak y := by
  rw [hfactor]
  exact congrArg g hstrong

theorem adding_consumer_refines_kernel {X A B : Type*}
    (first : X → A) (added : X → B) :
    KernelRefines (fun x => (first x, added x)) first :=
  pair_kernel_refines_left first added

theorem product_query_kernel_exact {X A B : Type*}
    (first : X → A) (second : X → B) (x y : X) :
    (first x, second x) = (first y, second y) ↔
      first x = first y ∧ second x = second y := by
  simp

theorem finite_query_factorization_on_reachable_image
    {X Strong Weak : Type*} [Fintype X]
    (strong : X → Strong) (weak : X → Weak) :
    (∃ g : Set.range strong → Weak,
        ∀ x, g ⟨strong x, ⟨x, rfl⟩⟩ = weak x) ↔
      KernelRefines strong weak :=
  factor_through_range_iff_kernel_refines strong weak

inductive ConverseWitness where
  | left
  | right
  deriving DecidableEq, Repr

def constantQuery (_ : ConverseWitness) : Bool := false

def identityQuery : ConverseWitness → ConverseWitness := id

theorem weak_preservation_does_not_imply_strong :
    constantQuery ConverseWitness.left = constantQuery ConverseWitness.right ∧
      identityQuery ConverseWitness.left ≠ identityQuery ConverseWitness.right := by
  decide

theorem added_consumer_can_strictly_refine :
    SameUnder constantQuery ConverseWitness.left ConverseWitness.right ∧
      ¬SameUnder (fun x => (constantQuery x, identityQuery x))
        ConverseWitness.left ConverseWitness.right := by
  simp [SameUnder, constantQuery, identityQuery]

/-- Integrated query-and-consumer monotonicity theorem on a finite reachable
domain.  Factorization makes the stronger query kernel refine the weaker one;
pairing an added consumer refines the original kernel; and reachable-image
factorization is equivalent to kernel refinement. -/
theorem fin_a4_query_consumer_monotonicity
    {X Strong Weak Reduction A B : Type*} [Fintype X]
    (strong : X → Strong) (weak : X → Weak)
    (reduction : X → Reduction) (first : X → A) (added : X → B) :
    (∀ g : Strong → Weak, weak = g ∘ strong →
      KernelRefines strong weak ∧
        (KernelRefines reduction strong →
          KernelRefines reduction weak)) ∧
    (∀ x y,
      SameUnder (fun z => (first z, added z)) x y ↔
        SameUnder first x y ∧ SameUnder added x y) ∧
    ((∃ g : Set.range strong → Weak,
        ∀ x, g ⟨strong x, ⟨x, rfl⟩⟩ = weak x) ↔
      KernelRefines strong weak) := by
  refine ⟨?_, ?_,
    finite_query_factorization_on_reachable_image strong weak⟩
  intro g hFactor
  have hStrongWeak :=
    factorization_implies_kernel_refines strong weak g hFactor
  exact ⟨hStrongWeak, fun hReductionStrong =>
    kernelRefines_trans hReductionStrong hStrongWeak⟩
  intro x y
  exact product_query_kernel_exact first added x y

/-- The registered converse boundary is nonvacuous: equality under a weaker
constant query does not entail equality under a stronger identity query, and
an added consumer can split the weak equivalence class. -/
theorem fin_a4_converse_boundary :
    (constantQuery ConverseWitness.left = constantQuery ConverseWitness.right ∧
      identityQuery ConverseWitness.left ≠ identityQuery ConverseWitness.right) ∧
    (SameUnder constantQuery ConverseWitness.left ConverseWitness.right ∧
      ¬SameUnder (fun x => (constantQuery x, identityQuery x))
        ConverseWitness.left ConverseWitness.right) := by
  exact ⟨weak_preservation_does_not_imply_strong,
    added_consumer_can_strictly_refine⟩

end PhonologicalCalculus
