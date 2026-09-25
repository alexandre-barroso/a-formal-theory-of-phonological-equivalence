                                          
import PhonologicalCalculus.Contract.FiniteDecision
import PhonologicalCalculus.Finite.QueryFactorization
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Rat.Defs

namespace PhonologicalCalculus.OrderComparison

def profile : Fin 3 → Nat × Nat
  | 0 => (0, 0)
  | 1 => (0, 1)
  | _ => (1, 0)

def orderedProfile (reverse : Bool) (x : Fin 3) : Nat × Nat :=
  if reverse then ((profile x).2, (profile x).1) else profile x

def better (reverse : Bool) (x y : Fin 3) : Bool :=
  let a := orderedProfile reverse x
  let b := orderedProfile reverse y
  a.1 < b.1 || (a.1 == b.1 && a.2 < b.2)

def winners (reverse : Bool) : Finset (Fin 3) :=
  Finset.univ.filter fun x => ∀ y : Fin 3, better reverse y x = false

def orderEdges (reverse : Bool) : Finset (Fin 3 × Fin 3) :=
  Finset.univ.filter fun p => better reverse p.1 p.2

def changedPairs : Finset (Fin 3 × Fin 3) :=
  Finset.univ.filter fun p => better false p.1 p.2 ≠ better true p.1 p.2

def canonicalChangedPairs : Finset (Fin 3 × Fin 3) :=
  changedPairs.filter fun p => p.1 < p.2

theorem source_order : orderEdges false = {(0,1),(0,2),(1,2)} := by decide +kernel

theorem target_order : orderEdges true = {(0,1),(0,2),(2,1)} := by decide +kernel

theorem common_winner : winners false = {0} ∧ winners true = {0} := by decide +kernel

theorem complete_changed_pairs : changedPairs = {(1,2),(2,1)} := by decide +kernel

theorem canonical_changed_pair : canonicalChangedPairs = {(1,2)} := by decide +kernel

def orderRequest : FiniteRequest (Fin 3 × Fin 3) Bool Bool where
  rows := Finset.univ
  formed := True
  admitted := True
  formedDecision := inferInstance
  admittedDecision := inferInstance
  sourceAnswer p := better false p.1 p.2
  targetAnswer p := better true p.1 p.2
  transport := id

def winnerRequest : FiniteRequest Unit (Finset (Fin 3)) (Finset (Fin 3)) where
  rows := {()}
  formed := True
  admitted := True
  formedDecision := inferInstance
  admittedDecision := inferInstance
  sourceAnswer _ := winners false
  targetAnswer _ := winners true
  transport := id

theorem order_request_mismatches : orderRequest.mismatchSet = {(1,2),(2,1)} := by
  decide +kernel

theorem winner_conservative : winnerRequest.evaluate = Verdict.conservative := by decide +kernel

theorem order_nonconservative : orderRequest.evaluate = Verdict.nonconservative := by decide +kernel

theorem transported_factorization {S S' W W' : Type*}
    (strongTransport : S → S') (weakTransport : W → W')
    (sourceFactor : S → W) (targetFactor : S' → W')
    (commutes : ∀ s, weakTransport (sourceFactor s) = targetFactor (strongTransport s))
    (source : S) (target : S') (conserved : strongTransport source = target) :
    weakTransport (sourceFactor source) = targetFactor target := by
  rw [commutes, conserved]

def mass (squared : Bool) : Fin 3 → ℚ
  | 0 => if squared then 16 else 4
  | 1 => if squared then 4 else 2
  | _ => 1

def probability (squared : Bool) (x : Fin 3) : ℚ :=
  mass squared x / (mass squared 0 + mass squared 1 + mass squared 2)

theorem probability_same_order :
    (∀ x y : Fin 3, mass false x < mass false y ↔ mass true x < mass true y) ∧
    probability false 0 ≠ probability true 0 := by decide +kernel

theorem both_probability_laws :
    (∀ b : Bool, (∀ x : Fin 3, 0 < probability b x) ∧
      probability b 0 + probability b 1 + probability b 2 = 1) := by decide +kernel

def deletionWinners : Finset (Fin 3) :=
  ({0,1} : Finset (Fin 3)).filter fun x => ∀ y ∈ ({0,1} : Finset (Fin 3)),
    better false y x = false

theorem deletion_winner_same_probability_changed :
    deletionWinners = winners false ∧
    mass false 0 / (mass false 0 + mass false 1) ≠ probability false 0 := by decide +kernel

end PhonologicalCalculus.OrderComparison
