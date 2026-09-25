import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.List.Lex
import Mathlib.Tactic.NormNum

                 

namespace PhonologicalCalculus.MaxEnt

def basicSyllableLedger : List (List (List Nat)) :=
  [
    [[0, 0, 0, 0], [0, 1, 1, 0], [1, 0, 0, 1], [1, 1, 1, 1]],
    [[0, 0, 0, 1], [0, 1, 0, 0], [1, 0, 0, 2], [1, 1, 0, 1]],
    [[0, 0, 1, 0], [0, 1, 2, 0], [1, 0, 0, 0], [1, 1, 1, 0]],
    [[0, 0, 1, 1], [0, 1, 1, 0], [1, 0, 0, 1], [1, 1, 0, 0]]
  ]

def basicSyllableRankings : List (List Nat) :=
  [
    [0, 1, 2, 3], [0, 1, 3, 2], [0, 2, 1, 3], [0, 2, 3, 1],
    [0, 3, 1, 2], [0, 3, 2, 1], [1, 0, 2, 3], [1, 0, 3, 2],
    [1, 2, 0, 3], [1, 2, 3, 0], [1, 3, 0, 2], [1, 3, 2, 0],
    [2, 0, 1, 3], [2, 0, 3, 1], [2, 1, 0, 3], [2, 1, 3, 0],
    [2, 3, 0, 1], [2, 3, 1, 0], [3, 0, 1, 2], [3, 0, 2, 1],
    [3, 1, 0, 2], [3, 1, 2, 0], [3, 2, 0, 1], [3, 2, 1, 0]
  ]

theorem basicSyllableRankings_wellFormed :
    basicSyllableRankings.Nodup ∧
      ∀ ranking ∈ basicSyllableRankings,
        ranking.Perm [0, 1, 2, 3] := by
  decide

def rankedViolationKey (ranking row : List Nat) : List Nat :=
  ranking.map fun constraint => row.getD constraint 0

def strictLexLess : List Nat → List Nat → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys =>
      if x < y then true else if y < x then false else strictLexLess xs ys

def selectStrictRankingWinner (ranking : List Nat) :
    (List Nat × Nat) → List (List Nat × Nat) → (List Nat × Nat)
  | best, [] => best
  | best, candidate :: rest =>
      let next := if strictLexLess (rankedViolationKey ranking candidate.1)
          (rankedViolationKey ranking best.1) then candidate else best
      selectStrictRankingWinner ranking next rest

def strictRankingWinner (rows : List (List Nat)) (ranking : List Nat) : Nat :=
  match rows.zipIdx with
  | [] => 0
  | first :: rest => (selectStrictRankingWinner ranking first rest).2 + 1

def basicSyllableWinnerMap (ranking : List Nat) : List Nat :=
  basicSyllableLedger.map fun rows => strictRankingWinner rows ranking

def basicSyllableWinnerMaps : Finset (List Nat) :=
  (basicSyllableRankings.map basicSyllableWinnerMap).toFinset

def expectedBasicSyllableWinnerMaps : Finset (List Nat) :=
  [[1, 1, 1, 1], [1, 1, 3, 3], [1, 2, 1, 2], [1, 2, 3, 4]].toFinset

def basicSyllableMappings : List (Nat × Nat) :=
  [
    (1, 1), (1, 2), (1, 3), (1, 4),
    (2, 1), (2, 2), (2, 3), (2, 4),
    (3, 1), (3, 2), (3, 3), (3, 4),
    (4, 1), (4, 2), (4, 3), (4, 4)
  ]

def basicSyllableWinnerMapList : List (List Nat) :=
  [[1, 1, 1, 1], [1, 1, 3, 3], [1, 2, 1, 2], [1, 2, 3, 4]]

def basicSyllableEventMask (mapping : Nat × Nat) : List Bool :=
  basicSyllableWinnerMapList.map fun winnerMap =>
    winnerMap.getD (mapping.1 - 1) 0 == mapping.2

def eventMaskSubset : List Bool → List Bool → Bool
  | [], [] => true
  | left :: lefts, right :: rights =>
      (!left || right) && eventMaskSubset lefts rights
  | _, _ => false

def basicSyllableMappingPairs : List ((Nat × Nat) × (Nat × Nat)) :=
  basicSyllableMappings.flatMap fun left =>
    basicSyllableMappings.map fun right => (left, right)

def basicSyllableImplications : List ((Nat × Nat) × (Nat × Nat)) :=
  basicSyllableMappingPairs.filter fun pair =>
    (pair.1 != pair.2) &&
      eventMaskSubset (basicSyllableEventMask pair.1)
        (basicSyllableEventMask pair.2)

def basicSyllableImplicationsWithReflexive :
    List ((Nat × Nat) × (Nat × Nat)) :=
  basicSyllableMappingPairs.filter fun pair =>
    eventMaskSubset (basicSyllableEventMask pair.1)
      (basicSyllableEventMask pair.2)

def basicSyllableEmptyAntecedentMappings : List (Nat × Nat) :=
  basicSyllableMappings.filter fun mapping =>
    !(basicSyllableEventMask mapping).any id

def basicSyllableEmptyAntecedentImplications :
    List ((Nat × Nat) × (Nat × Nat)) :=
  basicSyllableImplications.filter fun pair =>
    !(basicSyllableEventMask pair.1).any id

def basicSyllableLiveImplications :
    List ((Nat × Nat) × (Nat × Nat)) :=
  basicSyllableImplications.filter fun pair =>
    (basicSyllableEventMask pair.1).any id

set_option maxRecDepth 100000 in
                 
theorem max_g6_enum_01 :
    basicSyllableRankings.length = 24 ∧
    basicSyllableWinnerMaps = expectedBasicSyllableWinnerMaps ∧
    basicSyllableWinnerMapList.toFinset = basicSyllableWinnerMaps ∧
    basicSyllableImplicationsWithReflexive.length = 137 ∧
    basicSyllableImplications.length = 121 ∧
    basicSyllableEmptyAntecedentMappings.length = 7 ∧
    basicSyllableEmptyAntecedentImplications.length = 105 ∧
    basicSyllableLiveImplications.length = 16 := by
  decide

end PhonologicalCalculus.MaxEnt
