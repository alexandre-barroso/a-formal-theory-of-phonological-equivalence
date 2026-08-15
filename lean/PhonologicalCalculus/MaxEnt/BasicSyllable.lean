import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.List.Lex
import Mathlib.Tactic.NormNum

/-!
Kernel-reduced reconstruction of the fixed Basic Syllable inventory registered
as MAX-G6.ENUM.01.

The definitions below mirror the public exact-witness procedure: enumerate all
permutations of the four constraints, select the unique lexicographic winner
for each of four inputs, deduplicate the resulting winner maps, and then count
all nonreflexive event inclusions, partitioned by empty versus live antecedent.
The final proof uses ordinary decidable reduction, whose proof term is checked
by Lean's kernel rather than by a native-code evaluator.
-/

namespace PhonologicalCalculus.MaxEnt

/-- The registered four-input, four-candidate, four-constraint violation
tensor. -/
def basicSyllableLedger : List (List (List Nat)) :=
  [
    [[0, 0, 0, 0], [0, 1, 1, 0], [1, 0, 0, 1], [1, 1, 1, 1]],
    [[0, 0, 0, 1], [0, 1, 0, 0], [1, 0, 0, 2], [1, 1, 0, 1]],
    [[0, 0, 1, 0], [0, 1, 2, 0], [1, 0, 0, 0], [1, 1, 1, 0]],
    [[0, 0, 1, 1], [0, 1, 1, 0], [1, 0, 0, 1], [1, 1, 0, 0]]
  ]

/-- All four strict constraint rankings. -/
def basicSyllableRankings : List (List Nat) :=
  [
    [0, 1, 2, 3], [0, 1, 3, 2], [0, 2, 1, 3], [0, 2, 3, 1],
    [0, 3, 1, 2], [0, 3, 2, 1], [1, 0, 2, 3], [1, 0, 3, 2],
    [1, 2, 0, 3], [1, 2, 3, 0], [1, 3, 0, 2], [1, 3, 2, 0],
    [2, 0, 1, 3], [2, 0, 3, 1], [2, 1, 0, 3], [2, 1, 3, 0],
    [2, 3, 0, 1], [2, 3, 1, 0], [3, 0, 1, 2], [3, 0, 2, 1],
    [3, 1, 0, 2], [3, 1, 2, 0], [3, 2, 0, 1], [3, 2, 1, 0]
  ]

/-- The explicit ranking ledger is duplicate-free and every row is a
permutation of the four constraint indices. -/
theorem basicSyllableRankings_wellFormed :
    basicSyllableRankings.Nodup ∧
      ∀ ranking ∈ basicSyllableRankings,
        ranking.Perm [0, 1, 2, 3] := by
  decide

/-- A violation row read in strict-ranking order. -/
def rankedViolationKey (ranking row : List Nat) : List Nat :=
  ranking.map fun constraint => row.getD constraint 0

/-- Executable strict lexicographic comparison. -/
def strictLexLess : List Nat → List Nat → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys =>
      if x < y then true else if y < x then false else strictLexLess xs ys

/-- Select the least ranked candidate from a nonempty indexed tail. -/
def selectStrictRankingWinner (ranking : List Nat) :
    (List Nat × Nat) → List (List Nat × Nat) → (List Nat × Nat)
  | best, [] => best
  | best, candidate :: rest =>
      let next := if strictLexLess (rankedViolationKey ranking candidate.1)
          (rankedViolationKey ranking best.1) then candidate else best
      selectStrictRankingWinner ranking next rest

/-- The one-based candidate index selected by lexicographic strict ranking. -/
def strictRankingWinner (rows : List (List Nat)) (ranking : List Nat) : Nat :=
  match rows.zipIdx with
  | [] => 0
  | first :: rest => (selectStrictRankingWinner ranking first rest).2 + 1

/-- The four-input winner map induced by one strict ranking. -/
def basicSyllableWinnerMap (ranking : List Nat) : List Nat :=
  basicSyllableLedger.map fun rows => strictRankingWinner rows ranking

/-- The exact set of distinct winner maps induced by all strict rankings. -/
def basicSyllableWinnerMaps : Finset (List Nat) :=
  (basicSyllableRankings.map basicSyllableWinnerMap).toFinset

/-- The registered expected winner-map inventory. -/
def expectedBasicSyllableWinnerMaps : Finset (List Nat) :=
  [[1, 1, 1, 1], [1, 1, 3, 3], [1, 2, 1, 2], [1, 2, 3, 4]].toFinset

/-- Sixteen input-output mappings. -/
def basicSyllableMappings : List (Nat × Nat) :=
  [
    (1, 1), (1, 2), (1, 3), (1, 4),
    (2, 1), (2, 2), (2, 3), (2, 4),
    (3, 1), (3, 2), (3, 3), (3, 4),
    (4, 1), (4, 2), (4, 3), (4, 4)
  ]

/-- The deduplicated winner maps, retained as a list for transparent kernel
evaluation of the implication inventory. -/
def basicSyllableWinnerMapList : List (List Nat) :=
  [[1, 1, 1, 1], [1, 1, 3, 3], [1, 2, 1, 2], [1, 2, 3, 4]]

/-- Boolean characteristic vector of the event associated with a mapping. -/
def basicSyllableEventMask (mapping : Nat × Nat) : List Bool :=
  basicSyllableWinnerMapList.map fun winnerMap =>
    winnerMap.getD (mapping.1 - 1) 0 == mapping.2

/-- Inclusion of two finite Boolean event masks. -/
def eventMaskSubset : List Bool → List Bool → Bool
  | [], [] => true
  | left :: lefts, right :: rights =>
      (!left || right) && eventMaskSubset lefts rights
  | _, _ => false

/-- The complete Cartesian square of the sixteen mappings. -/
def basicSyllableMappingPairs : List ((Nat × Nat) × (Nat × Nat)) :=
  basicSyllableMappings.flatMap fun left =>
    basicSyllableMappings.map fun right => (left, right)

/-- All nonreflexive categorical implications under event inclusion. -/
def basicSyllableImplications : List ((Nat × Nat) × (Nat × Nat)) :=
  basicSyllableMappingPairs.filter fun pair =>
    (pair.1 != pair.2) &&
      eventMaskSubset (basicSyllableEventMask pair.1)
        (basicSyllableEventMask pair.2)

/-- All categorical implications, including the sixteen reflexive pairs. -/
def basicSyllableImplicationsWithReflexive :
    List ((Nat × Nat) × (Nat × Nat)) :=
  basicSyllableMappingPairs.filter fun pair =>
    eventMaskSubset (basicSyllableEventMask pair.1)
      (basicSyllableEventMask pair.2)

/-- The seven mappings whose categorical event is empty. -/
def basicSyllableEmptyAntecedentMappings : List (Nat × Nat) :=
  basicSyllableMappings.filter fun mapping =>
    !(basicSyllableEventMask mapping).any id

/-- Implications whose antecedent event is empty. -/
def basicSyllableEmptyAntecedentImplications :
    List ((Nat × Nat) × (Nat × Nat)) :=
  basicSyllableImplications.filter fun pair =>
    !(basicSyllableEventMask pair.1).any id

/-- Implications whose antecedent event is nonempty. -/
def basicSyllableLiveImplications :
    List ((Nat × Nat) × (Nat × Nat)) :=
  basicSyllableImplications.filter fun pair =>
    (basicSyllableEventMask pair.1).any id

set_option maxRecDepth 100000 in
/-- **MAX-G6.ENUM.01**.  Exact kernel-checked reconstruction of the complete
finite inventory: 24 strict rankings, four distinct winner maps, 121
nonreflexive implications (137 with reflexive pairs), seven empty events, and
the nonreflexive partition into 105 empty-antecedent and 16 live implications. -/
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
