import PhonologicalCalculus.MaxEnt.NormalizerRelation
import Mathlib.Data.List.Sublists

/-!
# Executable proper-CNF selector branch

This module gives the bounded `{1,2}` selector construction a concrete finite
representation.  Clauses are literal lists, residual rows are finite bit
vectors, and both compilation and complement verification return explicit
operation counts.  Separate theorems relate these executable objects to the
semantic objects in `NormalizerRelation`.
-/

namespace PhonologicalCalculus.MaxEnt

/-! ## Concrete source syntax -/

/-- One proper clause represented by duplicate-free positive and negative
literal lists. -/
structure ExecutableProperClause (variableCount : ℕ) where
  positive : List (Fin variableCount)
  negative : List (Fin variableCount)
  positive_nodup : positive.Nodup
  negative_nodup : negative.Nodup
  signs_disjoint : Disjoint positive.toFinset negative.toFinset
  nonempty : (positive.toFinset ∪ negative.toFinset).Nonempty
  width_le_three : positive.length + negative.length ≤ 3

/-- Erasure of the concrete literal lists into the established semantic
clause type. -/
def ExecutableProperClause.toSemantic
    {variableCount : ℕ}
    (clause : ExecutableProperClause variableCount) :
    ProperAtMostThreeClause (Fin variableCount) where
  positive := clause.positive.toFinset
  negative := clause.negative.toFinset
  signs_disjoint := clause.signs_disjoint
  nonempty := clause.nonempty
  width_le_three := by
    simpa [List.toFinset_card_of_nodup clause.positive_nodup,
      List.toFinset_card_of_nodup clause.negative_nodup] using
      clause.width_le_three

/-- A concrete proper at-most-three-CNF formula. -/
structure ExecutableProperCNFCode where
  variableCount : ℕ
  clauses : List (ExecutableProperClause variableCount)
  atLeastTwoClauses : 2 ≤ clauses.length

def ExecutableProperCNFCode.clauseCount
    (input : ExecutableProperCNFCode) : ℕ :=
  input.clauses.length

/-- Exact semantic formula represented by the concrete source syntax. -/
def ExecutableProperCNFCode.toSemanticFormula
    (input : ExecutableProperCNFCode) :
    ProperAtMostThreeCNF (Fin input.variableCount) (Fin input.clauseCount) where
  clause := fun index => (input.clauses.get index).toSemantic
  atLeastTwoClauses := by
    rw [Fintype.card_fin]
    exact input.atLeastTwoClauses

/-- Exact semantic source code represented by the concrete syntax. -/
def ExecutableProperCNFCode.toSemanticCode
    (input : ExecutableProperCNFCode) : ProperAtMostThreeCNFCode where
  variableCount := input.variableCount
  clauseCount := input.clauseCount
  formula := input.toSemanticFormula

/-- Concrete source size: one cell per variable, clause, and stored literal,
plus one positive sentinel. -/
def executableProperCNFCodeSize (input : ExecutableProperCNFCode) : ℕ :=
  input.variableCount + input.clauseCount +
    (input.clauses.map
      (fun clause => clause.positive.length + clause.negative.length)).sum + 1

theorem executableProperCNFCodeSize_positive
    (input : ExecutableProperCNFCode) :
    0 < executableProperCNFCodeSize input := by
  unfold executableProperCNFCodeSize
  omega

/-! ## Finite bit-vector target syntax -/

/-- A concrete bit vector of statically known length. -/
abbrev FiniteBitVector (length : ℕ) := Fin length → Bool

/-- Convert a contiguous bit vector into the split coordinate type used by
the established selector semantics. -/
def FiniteBitVector.toSplit
    {leftCount rightCount : ℕ}
    (row : FiniteBitVector (leftCount + rightCount)) :
    Sum (Fin leftCount) (Fin rightCount) → Bool :=
  fun coordinate => row (finSumFinEquiv coordinate)

theorem finiteBitVector_toSplit_injective
    {leftCount rightCount : ℕ} :
    Function.Injective
      (FiniteBitVector.toSplit (leftCount := leftCount)
        (rightCount := rightCount)) := by
  intro first second hRows
  funext coordinate
  have hCoordinate := congrFun hRows (finSumFinEquiv.symm coordinate)
  simpa [FiniteBitVector.toSplit] using hCoordinate

/-- Executable finite table.  Rows are stored as lists of finite bit vectors;
the duplicate-free compiler applies explicit list normalization. -/
structure ExecutableOneTwoTable where
  leftCoordinateCount : ℕ
  rightCoordinateCount : ℕ
  positiveRows : List
    (FiniteBitVector (leftCoordinateCount + rightCoordinateCount))
  negativeRows : List
    (FiniteBitVector (leftCoordinateCount + rightCoordinateCount))

def ExecutableOneTwoTable.coordinateCount
    (table : ExecutableOneTwoTable) : ℕ :=
  table.leftCoordinateCount + table.rightCoordinateCount

def ExecutableOneTwoTable.positiveRowSet
    (table : ExecutableOneTwoTable) :
    Finset (Sum (Fin table.leftCoordinateCount)
      (Fin table.rightCoordinateCount) → Bool) :=
  (table.positiveRows.map FiniteBitVector.toSplit).toFinset

def ExecutableOneTwoTable.negativeRowSet
    (table : ExecutableOneTwoTable) :
    Finset (Sum (Fin table.leftCoordinateCount)
      (Fin table.rightCoordinateCount) → Bool) :=
  (table.negativeRows.map FiniteBitVector.toSplit).toFinset

/-- Stored table size in the explicit row model. -/
def executableOneTwoTableSize (table : ExecutableOneTwoTable) : ℕ :=
  (table.coordinateCount + 1) *
    (table.positiveRows.length + table.negativeRows.length + 1)

/-- Deterministic duplicate elimination on both row lists. -/
def normalizeExecutableOneTwoTable
    (table : ExecutableOneTwoTable) : ExecutableOneTwoTable where
  leftCoordinateCount := table.leftCoordinateCount
  rightCoordinateCount := table.rightCoordinateCount
  positiveRows := table.positiveRows.dedup
  negativeRows := table.negativeRows.dedup

theorem normalizeExecutableOneTwoTable_positiveRowSet
    (table : ExecutableOneTwoTable) :
    (normalizeExecutableOneTwoTable table).positiveRowSet =
      table.positiveRowSet := by
  classical
  change
    ((table.positiveRows.dedup.map
      (fun executableRow => FiniteBitVector.toSplit executableRow)).toFinset) =
    ((table.positiveRows.map
      (fun executableRow => FiniteBitVector.toSplit executableRow)).toFinset)
  ext row
  simp only [List.mem_toFinset, List.mem_map, List.mem_dedup]

theorem normalizeExecutableOneTwoTable_negativeRowSet
    (table : ExecutableOneTwoTable) :
    (normalizeExecutableOneTwoTable table).negativeRowSet =
      table.negativeRowSet := by
  classical
  change
    ((table.negativeRows.dedup.map
      (fun executableRow => FiniteBitVector.toSplit executableRow)).toFinset) =
    ((table.negativeRows.map
      (fun executableRow => FiniteBitVector.toSplit executableRow)).toFinset)
  ext row
  simp only [List.mem_toFinset, List.mem_map, List.mem_dedup]

theorem normalizeExecutableOneTwoTable_size_le
    (table : ExecutableOneTwoTable) :
    executableOneTwoTableSize (normalizeExecutableOneTwoTable table) ≤
      executableOneTwoTableSize table := by
  have hPositive := (List.dedup_sublist table.positiveRows).length_le
  have hNegative := (List.dedup_sublist table.negativeRows).length_le
  unfold executableOneTwoTableSize ExecutableOneTwoTable.coordinateCount
  dsimp [normalizeExecutableOneTwoTable]
  exact Nat.mul_le_mul_left _
    (Nat.add_le_add_right (Nat.add_le_add hPositive hNegative) 1)

/-- A list table whose concrete rows are duplicate-free both within and
across signs. -/
structure ExecutableDuplicateFreeOneTwoTable where
  table : ExecutableOneTwoTable
  positive_nodup : table.positiveRows.Nodup
  negative_nodup : table.negativeRows.Nodup
  rows_disjoint : List.Disjoint table.positiveRows table.negativeRows

theorem normalizeExecutableOneTwoTable_rows_disjoint
    (table : ExecutableOneTwoTable)
    (hRows : Disjoint table.positiveRowSet table.negativeRowSet) :
    List.Disjoint (normalizeExecutableOneTwoTable table).positiveRows
      (normalizeExecutableOneTwoTable table).negativeRows := by
  rw [List.disjoint_left]
  intro row hPositive hNegative
  have hPositiveSet : FiniteBitVector.toSplit row ∈ table.positiveRowSet := by
    rw [← normalizeExecutableOneTwoTable_positiveRowSet table]
    unfold ExecutableOneTwoTable.positiveRowSet
    apply List.mem_toFinset.mpr
    apply List.mem_map.mpr
    exact ⟨row, hPositive, rfl⟩
  have hNegativeSet : FiniteBitVector.toSplit row ∈ table.negativeRowSet := by
    rw [← normalizeExecutableOneTwoTable_negativeRowSet table]
    unfold ExecutableOneTwoTable.negativeRowSet
    apply List.mem_toFinset.mpr
    apply List.mem_map.mpr
    exact ⟨row, hNegative, rfl⟩
  exact Finset.disjoint_left.mp hRows hPositiveSet hNegativeSet

/-- Exact semantic erasure of a proof-bearing duplicate-free list table. -/
def ExecutableDuplicateFreeOneTwoTable.toSemanticCode
    (input : ExecutableDuplicateFreeOneTwoTable) :
    DuplicateFreeOneTwoOrderCode where
  leftCoordinateCount := input.table.leftCoordinateCount
  rightCoordinateCount := input.table.rightCoordinateCount
  positiveRows := input.table.positiveRowSet
  negativeRows := input.table.negativeRowSet
  rows_disjoint := by
    rw [Finset.disjoint_left]
    intro row hPositive hNegative
    unfold ExecutableOneTwoTable.positiveRowSet at hPositive
    unfold ExecutableOneTwoTable.negativeRowSet at hNegative
    simp only [List.mem_toFinset] at hPositive hNegative
    obtain ⟨positiveRow, hPositiveRow, hPositiveEq⟩ :=
      List.mem_map.mp hPositive
    obtain ⟨negativeRow, hNegativeRow, hNegativeEq⟩ :=
      List.mem_map.mp hNegative
    have hRowsEqual : positiveRow = negativeRow := by
      apply finiteBitVector_toSplit_injective
      exact hPositiveEq.trans hNegativeEq.symm
    subst negativeRow
    exact input.rows_disjoint hPositiveRow hNegativeRow

/-! ## Deterministic selector compiler -/

/-- One executable expansion term: a clause index and one sublist of its
positive literals. -/
structure ExecutableSelectorTerm (input : ExecutableProperCNFCode) where
  clause : Fin input.clauseCount
  selected : List (Fin input.variableCount)
  selected_sublist : List.Sublist selected
    (input.clauses.get clause).positive

/-- Deterministic clause-major enumeration of all selector expansion terms. -/
def executableSelectorTerms (input : ExecutableProperCNFCode) :
    List (ExecutableSelectorTerm input) :=
  (List.finRange input.clauseCount).flatMap fun clause =>
    ((input.clauses.get clause).positive.sublists.attach.map fun selected =>
      ⟨clause, selected.1, List.mem_sublists.mp selected.2⟩)

/-- Semantic expansion term represented by one executable term. -/
def ExecutableSelectorTerm.toSemantic
    {input : ExecutableProperCNFCode}
    (term : ExecutableSelectorTerm input) :
    SelectorExpansionTerm (Fin input.variableCount) (Fin input.clauseCount)
      input.toSemanticFormula where
  clause := term.clause
  selected := term.selected.toFinset
  selected_subset := by
    intro v hv
    have hvList : v ∈ term.selected := by simpa using hv
    have hvPositive : v ∈ (input.clauses.get term.clause).positive :=
      term.selected_sublist.subset hvList
    simpa [ExecutableProperCNFCode.toSemanticFormula,
      ExecutableProperClause.toSemantic] using hvPositive

theorem executableCNFSelectorTerm_eq_of_fields
    {input : ExecutableProperCNFCode}
    {first second : ExecutableSelectorTerm input}
    (hClause : first.clause = second.clause)
    (hSelected : first.selected = second.selected) :
    first = second := by
  cases first
  cases second
  cases hClause
  cases hSelected
  rfl

theorem executableSelectorTerm_mem_terms
    {input : ExecutableProperCNFCode}
    (term : ExecutableSelectorTerm input) :
    term ∈ executableSelectorTerms input := by
  unfold executableSelectorTerms
  apply List.mem_flatMap.mpr
  refine ⟨term.clause, List.mem_finRange term.clause, ?_⟩
  apply List.mem_map.mpr
  let selected :
      {items // items ∈ (input.clauses.get term.clause).positive.sublists} :=
    ⟨term.selected, List.mem_sublists.mpr term.selected_sublist⟩
  refine ⟨selected, List.mem_attach _ selected, ?_⟩
  apply executableCNFSelectorTerm_eq_of_fields <;> rfl

/-- Canonical executable representative of a semantic expansion term.  The
source literal order is retained and all unselected literals are removed. -/
def executableSelectorTermOfSemantic
    (input : ExecutableProperCNFCode)
    (term : SelectorExpansionTerm (Fin input.variableCount)
      (Fin input.clauseCount) input.toSemanticFormula) :
    ExecutableSelectorTerm input where
  clause := term.clause
  selected := (input.clauses.get term.clause).positive.filter
    (fun literal => literal ∈ term.selected)
  selected_sublist := List.filter_sublist

theorem executableCNFSemanticSelectorTerm_eq_of_fields
    {input : ExecutableProperCNFCode}
    {first second : SelectorExpansionTerm (Fin input.variableCount)
      (Fin input.clauseCount) input.toSemanticFormula}
    (hClause : first.clause = second.clause)
    (hSelected : first.selected = second.selected) :
    first = second := by
  cases first
  cases second
  cases hClause
  cases hSelected
  rfl

theorem executableSelectorTermOfSemantic_toSemantic
    (input : ExecutableProperCNFCode)
    (term : SelectorExpansionTerm (Fin input.variableCount)
      (Fin input.clauseCount) input.toSemanticFormula) :
    (executableSelectorTermOfSemantic input term).toSemantic = term := by
  apply executableCNFSemanticSelectorTerm_eq_of_fields
  · rfl
  · ext literal
    simp only [ExecutableSelectorTerm.toSemantic,
      executableSelectorTermOfSemantic, List.mem_toFinset,
      List.mem_filter, decide_eq_true_eq]
    constructor
    · exact fun membership => membership.2
    · intro membership
      refine ⟨?_, membership⟩
      have hPositive := term.selected_subset membership
      simpa [ExecutableProperCNFCode.toSemanticFormula,
        ExecutableProperClause.toSemantic] using hPositive

/-- Residual bit row associated with one executable expansion term. -/
def executableSelectorTermRow
    (input : ExecutableProperCNFCode)
    (term : ExecutableSelectorTerm input) :
    FiniteBitVector (input.variableCount + input.clauseCount) :=
  fun coordinate =>
    match finSumFinEquiv.symm coordinate with
    | .inl v =>
        decide (v ∈ (input.clauses.get term.clause).negative ∨
          v ∈ term.selected)
    | .inr clause => decide (clause = term.clause)

/-- Exact row erasure into the established selector construction. -/
theorem executableSelectorTermRow_toSplit
    (input : ExecutableProperCNFCode)
    (term : ExecutableSelectorTerm input) :
    FiniteBitVector.toSplit (executableSelectorTermRow input term) =
      selectorClauseRow term.toSemantic := by
  funext coordinate
  cases coordinate with
  | inl v =>
      simp [FiniteBitVector.toSplit, executableSelectorTermRow,
        selectorClauseRow, ExecutableSelectorTerm.toSemantic,
        ExecutableProperCNFCode.toSemanticFormula,
        ExecutableProperClause.toSemantic]
  | inr clause =>
      simp [FiniteBitVector.toSplit, executableSelectorTermRow,
        selectorClauseRow, ExecutableSelectorTerm.toSemantic]

/-- Single negative global-selector row. -/
def executableSelectorGlobalRow
    (input : ExecutableProperCNFCode) :
    FiniteBitVector (input.variableCount + input.clauseCount) :=
  fun coordinate =>
    match finSumFinEquiv.symm coordinate with
    | .inl _ => false
    | .inr _ => true

theorem executableSelectorGlobalRow_toSplit
    (input : ExecutableProperCNFCode) :
    FiniteBitVector.toSplit (executableSelectorGlobalRow input) =
      (selectorGlobalRow :
        Sum (Fin input.variableCount) (Fin input.clauseCount) → Bool) := by
  funext coordinate
  cases coordinate <;>
    simp [FiniteBitVector.toSplit, executableSelectorGlobalRow,
      selectorGlobalRow]

/-- Positive parity is computed directly from the selected-list length. -/
def executableSelectorTermPositive
    {input : ExecutableProperCNFCode}
    (term : ExecutableSelectorTerm input) : Bool :=
  decide (Even term.selected.length)

theorem ExecutableSelectorTerm.selected_card
    {input : ExecutableProperCNFCode}
    (term : ExecutableSelectorTerm input) :
    term.toSemantic.selected.card = term.selected.length := by
  have hNodup : term.selected.Nodup :=
    (input.clauses.get term.clause).positive_nodup.sublist
      term.selected_sublist
  simp [ExecutableSelectorTerm.toSemantic,
    List.toFinset_card_of_nodup hNodup]

theorem executableSelectorTermPositive_eq_true_iff
    {input : ExecutableProperCNFCode}
    (term : ExecutableSelectorTerm input) :
    executableSelectorTermPositive term = true ↔
      Even term.toSemantic.selected.card := by
  unfold executableSelectorTermPositive
  rw [decide_eq_true_eq, term.selected_card]

theorem executableSelectorTermPositive_eq_false_iff
    {input : ExecutableProperCNFCode}
    (term : ExecutableSelectorTerm input) :
    executableSelectorTermPositive term = false ↔
      ¬ Even term.toSemantic.selected.card := by
  unfold executableSelectorTermPositive
  rw [decide_eq_false_iff_not, term.selected_card]

def executableSelectorPositiveRows (input : ExecutableProperCNFCode) :
    List (FiniteBitVector (input.variableCount + input.clauseCount)) :=
  ((executableSelectorTerms input).filter
      (fun term => executableSelectorTermPositive term)).map
    (executableSelectorTermRow input)

def executableSelectorNegativeRows (input : ExecutableProperCNFCode) :
    List (FiniteBitVector (input.variableCount + input.clauseCount)) :=
  executableSelectorGlobalRow input ::
    (((executableSelectorTerms input).filter
        (fun term => !(executableSelectorTermPositive term))).map
      (executableSelectorTermRow input))

/-- Deterministic executable selector compilation. -/
def compileExecutableProperCNFSelector
    (input : ExecutableProperCNFCode) : ExecutableOneTwoTable where
  leftCoordinateCount := input.variableCount
  rightCoordinateCount := input.clauseCount
  positiveRows := executableSelectorPositiveRows input
  negativeRows := executableSelectorNegativeRows input

theorem compileExecutableProperCNFSelector_positiveRowSet_eq
    (input : ExecutableProperCNFCode) :
    (compileExecutableProperCNFSelector input).positiveRowSet =
      selectorPositiveRows input.toSemanticFormula := by
  classical
  change
    ((executableSelectorPositiveRows input).map
      (fun executableRow => FiniteBitVector.toSplit executableRow)).toFinset =
      selectorPositiveRows input.toSemanticFormula
  ext row
  constructor
  · intro hRow
    have hMapped : row ∈
        (executableSelectorPositiveRows input).map
          (fun executableRow => FiniteBitVector.toSplit executableRow) := by
      simpa only [List.mem_toFinset] using hRow
    obtain ⟨termRow, hTermRow, hRowEq⟩ := List.mem_map.mp hMapped
    unfold executableSelectorPositiveRows at hTermRow
    obtain ⟨term, hFiltered, hTermRowEq⟩ := List.mem_map.mp hTermRow
    have hTerm := List.mem_filter.mp hFiltered
    rw [selectorPositiveRows, Finset.mem_image]
    refine ⟨term.toSemantic, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (executableSelectorTermPositive_eq_true_iff term).mp hTerm.2
    · calc
        selectorClauseRow term.toSemantic =
            FiniteBitVector.toSplit (executableSelectorTermRow input term) :=
          (executableSelectorTermRow_toSplit input term).symm
        _ = FiniteBitVector.toSplit termRow := by rw [hTermRowEq]
        _ = row := hRowEq
  · intro hRow
    rw [selectorPositiveRows, Finset.mem_image] at hRow
    obtain ⟨term, hTerm, rfl⟩ := hRow
    let executableTerm := executableSelectorTermOfSemantic input term
    have hExecutableTerm : executableTerm ∈ executableSelectorTerms input :=
      executableSelectorTerm_mem_terms executableTerm
    have hPositive : executableSelectorTermPositive executableTerm = true := by
      rw [executableSelectorTermPositive_eq_true_iff,
        executableSelectorTermOfSemantic_toSemantic]
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hTerm
    apply List.mem_toFinset.mpr
    apply List.mem_map.mpr
    refine ⟨executableSelectorTermRow input executableTerm, ?_, ?_⟩
    · unfold executableSelectorPositiveRows
      apply List.mem_map.mpr
      refine ⟨executableTerm,
        List.mem_filter.mpr ⟨hExecutableTerm, hPositive⟩, rfl⟩
    · rw [executableSelectorTermRow_toSplit,
        executableSelectorTermOfSemantic_toSemantic]

theorem compileExecutableProperCNFSelector_negativeRowSet_eq
    (input : ExecutableProperCNFCode) :
    (compileExecutableProperCNFSelector input).negativeRowSet =
      selectorNegativeRows input.toSemanticFormula := by
  classical
  change
    ((executableSelectorNegativeRows input).map
      (fun executableRow => FiniteBitVector.toSplit executableRow)).toFinset =
      selectorNegativeRows input.toSemanticFormula
  ext row
  constructor
  · intro hRow
    have hMapped : row ∈
        (executableSelectorNegativeRows input).map
          (fun executableRow => FiniteBitVector.toSplit executableRow) := by
      simpa only [List.mem_toFinset] using hRow
    obtain ⟨termRow, hTermRow, hRowEq⟩ := List.mem_map.mp hMapped
    unfold executableSelectorNegativeRows at hTermRow
    have hRowCases :
        termRow = executableSelectorGlobalRow input ∨
          termRow ∈
            (List.filter (fun term =>
              !executableSelectorTermPositive term)
              (executableSelectorTerms input)).map
                (executableSelectorTermRow input) := by
      simpa only [List.mem_cons] using hTermRow
    rw [selectorNegativeRows, Finset.mem_insert]
    rcases hRowCases with hGlobal | hTail
    · left
      subst termRow
      simpa [executableSelectorGlobalRow_toSplit] using hRowEq.symm
    · obtain ⟨term, hFiltered, hTermRowEq⟩ := List.mem_map.mp hTail
      have hTerm := List.mem_filter.mp hFiltered
      right
      rw [Finset.mem_image]
      refine ⟨term.toSemantic, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        apply (executableSelectorTermPositive_eq_false_iff term).mp
        cases hValue : executableSelectorTermPositive term <;> simp_all
      · calc
          selectorClauseRow term.toSemantic =
              FiniteBitVector.toSplit (executableSelectorTermRow input term) :=
            (executableSelectorTermRow_toSplit input term).symm
          _ = FiniteBitVector.toSplit termRow := by rw [hTermRowEq]
          _ = row := hRowEq
  · intro hRow
    rw [selectorNegativeRows, Finset.mem_insert] at hRow
    rcases hRow with hGlobal | hTermRow
    · apply List.mem_toFinset.mpr
      apply List.mem_map.mpr
      refine ⟨executableSelectorGlobalRow input, ?_, ?_⟩
      · exact List.mem_cons_self
      · rw [executableSelectorGlobalRow_toSplit]
        exact hGlobal.symm
    · rw [Finset.mem_image] at hTermRow
      obtain ⟨term, hTerm, rfl⟩ := hTermRow
      let executableTerm := executableSelectorTermOfSemantic input term
      have hExecutableTerm : executableTerm ∈ executableSelectorTerms input :=
        executableSelectorTerm_mem_terms executableTerm
      have hNegative : executableSelectorTermPositive executableTerm = false := by
        rw [executableSelectorTermPositive_eq_false_iff,
          executableSelectorTermOfSemantic_toSemantic]
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hTerm
      apply List.mem_toFinset.mpr
      apply List.mem_map.mpr
      refine ⟨executableSelectorTermRow input executableTerm, ?_, ?_⟩
      · unfold executableSelectorNegativeRows
        apply List.mem_cons_of_mem
        apply List.mem_map.mpr
        refine ⟨executableTerm, ?_, rfl⟩
        apply List.mem_filter.mpr
        refine ⟨hExecutableTerm, ?_⟩
        simp [hNegative]
      · rw [executableSelectorTermRow_toSplit,
          executableSelectorTermOfSemantic_toSemantic]

theorem compileExecutableProperCNFSelector_rowSets_disjoint
    (input : ExecutableProperCNFCode) :
    Disjoint (compileExecutableProperCNFSelector input).positiveRowSet
      (compileExecutableProperCNFSelector input).negativeRowSet := by
  rw [compileExecutableProperCNFSelector_positiveRowSet_eq,
    compileExecutableProperCNFSelector_negativeRowSet_eq]
  exact selectorRows_disjoint input.toSemanticFormula

/-- Proof-bearing semantic target emitted by the executable list compiler. -/
def compileExecutableProperCNFSelectorCode
    (input : ExecutableProperCNFCode) : DuplicateFreeOneTwoOrderCode where
  leftCoordinateCount := input.variableCount
  rightCoordinateCount := input.clauseCount
  positiveRows := (compileExecutableProperCNFSelector input).positiveRowSet
  negativeRows := (compileExecutableProperCNFSelector input).negativeRowSet
  rows_disjoint := compileExecutableProperCNFSelector_rowSets_disjoint input

theorem compileExecutableProperCNFSelectorCode_eq_semanticCompiler
    (input : ExecutableProperCNFCode) :
    compileExecutableProperCNFSelectorCode input =
      compileProperCNFSelector input.toSemanticCode := by
  unfold compileExecutableProperCNFSelectorCode compileProperCNFSelector
  congr 1
  · exact compileExecutableProperCNFSelector_positiveRowSet_eq input
  · exact compileExecutableProperCNFSelector_negativeRowSet_eq input

theorem compileExecutableProperCNFSelectorCode_correct
    (input : ExecutableProperCNFCode) :
    duplicateFreeOneTwoUniversalOrder.accepts
        (compileExecutableProperCNFSelectorCode input) ↔
      ¬ input.toSemanticFormula.Satisfiable := by
  rw [compileExecutableProperCNFSelectorCode_eq_semanticCompiler]
  exact compileProperCNFSelector_correct input.toSemanticCode

/-- Concrete duplicate-free compiler: duplicate elimination is part of the
returned list value, and all three list invariants are proved. -/
def compileDuplicateFreeExecutableProperCNFSelector
    (input : ExecutableProperCNFCode) :
    ExecutableDuplicateFreeOneTwoTable where
  table := normalizeExecutableOneTwoTable
    (compileExecutableProperCNFSelector input)
  positive_nodup := List.nodup_dedup _
  negative_nodup := List.nodup_dedup _
  rows_disjoint := normalizeExecutableOneTwoTable_rows_disjoint
    (compileExecutableProperCNFSelector input)
    (compileExecutableProperCNFSelector_rowSets_disjoint input)

theorem compileDuplicateFreeExecutableProperCNFSelector_semanticCode_eq
    (input : ExecutableProperCNFCode) :
    (compileDuplicateFreeExecutableProperCNFSelector input).toSemanticCode =
      compileExecutableProperCNFSelectorCode input := by
  unfold compileDuplicateFreeExecutableProperCNFSelector
  unfold ExecutableDuplicateFreeOneTwoTable.toSemanticCode
  unfold compileExecutableProperCNFSelectorCode
  congr 1
  · exact normalizeExecutableOneTwoTable_positiveRowSet
      (compileExecutableProperCNFSelector input)
  · exact normalizeExecutableOneTwoTable_negativeRowSet
      (compileExecutableProperCNFSelector input)

theorem compileDuplicateFreeExecutableProperCNFSelector_correct
    (input : ExecutableProperCNFCode) :
    duplicateFreeOneTwoUniversalOrder.accepts
        (compileDuplicateFreeExecutableProperCNFSelector input).toSemanticCode ↔
      ¬ input.toSemanticFormula.Satisfiable := by
  rw [compileDuplicateFreeExecutableProperCNFSelector_semanticCode_eq]
  exact compileExecutableProperCNFSelectorCode_correct input

/-! ## Value-coupled recursive complement verification -/

/-- A value paired with the number of recursive primitive steps used to
produce that value. -/
structure ExecutableCNFCosted (Result : Type) where
  value : Result
  steps : ℕ

/-- Recursive scan of a declared coordinate list.  Each nonempty scan performs
one row test and one Boolean conjunction after the recursive call. -/
def executableCNFRowActiveLoop
    {coordinateCount : ℕ}
    (row assignment : FiniteBitVector coordinateCount) :
    List (Fin coordinateCount) → ExecutableCNFCosted Bool
  | [] => ⟨true, 1⟩
  | coordinate :: coordinates =>
      let remainder :=
        executableCNFRowActiveLoop row assignment coordinates
      let headValue :=
        if row coordinate = true then assignment coordinate else true
      ⟨headValue && remainder.value, remainder.steps + 2⟩

theorem executableCNFRowActiveLoop_value_iff
    {coordinateCount : ℕ}
    (row assignment : FiniteBitVector coordinateCount)
    (coordinates : List (Fin coordinateCount)) :
    (executableCNFRowActiveLoop row assignment coordinates).value = true ↔
      ∀ coordinate ∈ coordinates,
        row coordinate = true → assignment coordinate = true := by
  induction coordinates with
  | nil => simp [executableCNFRowActiveLoop]
  | cons coordinate coordinates inductionHypothesis =>
      cases hRow : row coordinate <;>
        cases hAssignment : assignment coordinate <;>
          simp [executableCNFRowActiveLoop, inductionHypothesis,
            hRow, hAssignment]

theorem executableCNFRowActiveLoop_steps
    {coordinateCount : ℕ}
    (row assignment : FiniteBitVector coordinateCount)
    (coordinates : List (Fin coordinateCount)) :
    (executableCNFRowActiveLoop row assignment coordinates).steps =
      2 * coordinates.length + 1 := by
  induction coordinates with
  | nil => simp [executableCNFRowActiveLoop]
  | cons coordinate coordinates inductionHypothesis =>
      simp [executableCNFRowActiveLoop, inductionHypothesis]
      omega

/-- Full finite-coordinate activity scan. -/
def executableCNFRowActive
    {coordinateCount : ℕ}
    (row assignment : FiniteBitVector coordinateCount) :
    ExecutableCNFCosted Bool :=
  executableCNFRowActiveLoop row assignment
    (List.finRange coordinateCount)

theorem executableCNFRowActive_value_iff
    {coordinateCount : ℕ}
    (row assignment : FiniteBitVector coordinateCount) :
    (executableCNFRowActive row assignment).value = true ↔
      residualRowActive row assignment := by
  rw [executableCNFRowActive,
    executableCNFRowActiveLoop_value_iff]
  unfold residualRowActive
  constructor
  · intro hActive coordinate hRow
    exact hActive coordinate (List.mem_finRange coordinate) hRow
  · intro hActive coordinate _ hRow
    exact hActive coordinate hRow

theorem executableCNFRowActive_steps
    {coordinateCount : ℕ}
    (row assignment : FiniteBitVector coordinateCount) :
    (executableCNFRowActive row assignment).steps =
      2 * coordinateCount + 1 := by
  rw [executableCNFRowActive,
    executableCNFRowActiveLoop_steps, List.length_finRange]

/-- Recursive active-row counter.  Its value is computed from the value of
each recursive coordinate scan, so the step field cannot be detached from an
arbitrary external result. -/
def executableCNFActiveRowCount
    {coordinateCount : ℕ}
    (assignment : FiniteBitVector coordinateCount) :
    List (FiniteBitVector coordinateCount) → ExecutableCNFCosted ℕ
  | [] => ⟨0, 1⟩
  | row :: rows =>
      let active := executableCNFRowActive row assignment
      let remainder := executableCNFActiveRowCount assignment rows
      let value := if active.value = true then remainder.value + 1
        else remainder.value
      ⟨value, active.steps + remainder.steps + 2⟩

theorem executableCNFActiveRowCount_value
    {coordinateCount : ℕ}
    (rows : List (FiniteBitVector coordinateCount))
    (assignment : FiniteBitVector coordinateCount) :
    (executableCNFActiveRowCount assignment rows).value =
      (rows.filter (fun row =>
        (executableCNFRowActive row assignment).value)).length := by
  induction rows with
  | nil => simp [executableCNFActiveRowCount]
  | cons row rows inductionHypothesis =>
      simp [executableCNFActiveRowCount, inductionHypothesis]
      cases hActive : (executableCNFRowActive row assignment).value <;>
        simp [hActive]

theorem executableCNFActiveRowCount_steps
    {coordinateCount : ℕ}
    (rows : List (FiniteBitVector coordinateCount))
    (assignment : FiniteBitVector coordinateCount) :
    (executableCNFActiveRowCount assignment rows).steps =
      rows.length * (2 * coordinateCount + 3) + 1 := by
  induction rows with
  | nil => simp [executableCNFActiveRowCount]
  | cons row rows inductionHypothesis =>
      simp [executableCNFActiveRowCount, inductionHypothesis,
        executableCNFRowActive_steps]
      ring

theorem finiteBitVector_residualRowActive_toSplit_iff
    {leftCount rightCount : ℕ}
    (row assignment : FiniteBitVector (leftCount + rightCount)) :
    residualRowActive (FiniteBitVector.toSplit row)
        (FiniteBitVector.toSplit assignment) ↔
      residualRowActive row assignment := by
  unfold residualRowActive
  constructor
  · intro hActive coordinate hRow
    have hAtCoordinate := hActive (finSumFinEquiv.symm coordinate)
    have hResult := hAtCoordinate (by
      simpa [FiniteBitVector.toSplit] using hRow)
    simpa [FiniteBitVector.toSplit] using hResult
  · intro hActive coordinate hRow
    have hAtCoordinate := hActive (finSumFinEquiv coordinate)
    have hResult := hAtCoordinate (by
      simpa [FiniteBitVector.toSplit] using hRow)
    simpa [FiniteBitVector.toSplit] using hResult

theorem executableCNFActiveRowCount_eq_semantic
    {leftCount rightCount : ℕ}
    (rows : List (FiniteBitVector (leftCount + rightCount)))
    (hRows : rows.Nodup)
    (assignment : FiniteBitVector (leftCount + rightCount)) :
    (executableCNFActiveRowCount assignment rows).value =
      activeResidualRowCount
        ((rows.map (fun row => FiniteBitVector.toSplit row)).toFinset)
        (FiniteBitVector.toSplit assignment) := by
  classical
  rw [executableCNFActiveRowCount_value]
  unfold activeResidualRowCount
  let activeRows := rows.filter (fun row =>
    (executableCNFRowActive row assignment).value)
  have hActiveRowsNodup :
      (activeRows.map (fun row => FiniteBitVector.toSplit row)).Nodup := by
    apply (hRows.filter _).map
    exact finiteBitVector_toSplit_injective
  have hActiveRowSet :
      (activeRows.map (fun row => FiniteBitVector.toSplit row)).toFinset =
        (rows.map (fun row => FiniteBitVector.toSplit row)).toFinset.filter
          (fun row => residualRowActive row
            (FiniteBitVector.toSplit assignment)) := by
    ext splitRow
    constructor
    · intro hSplitRow
      have hMapped : splitRow ∈
          activeRows.map (fun row => FiniteBitVector.toSplit row) := by
        simpa only [List.mem_toFinset] using hSplitRow
      obtain ⟨row, hActiveRow, hRowEq⟩ := List.mem_map.mp hMapped
      have hFiltered := List.mem_filter.mp hActiveRow
      rw [Finset.mem_filter]
      constructor
      · apply List.mem_toFinset.mpr
        apply List.mem_map.mpr
        exact ⟨row, hFiltered.1, hRowEq⟩
      · rw [← hRowEq]
        apply (finiteBitVector_residualRowActive_toSplit_iff row assignment).2
        exact (executableCNFRowActive_value_iff row assignment).1 hFiltered.2
    · intro hSplitRow
      rw [Finset.mem_filter] at hSplitRow
      have hMapped : splitRow ∈
          rows.map (fun row => FiniteBitVector.toSplit row) := by
        simpa only [List.mem_toFinset] using hSplitRow.1
      obtain ⟨row, hRow, hRowEq⟩ := List.mem_map.mp hMapped
      apply List.mem_toFinset.mpr
      apply List.mem_map.mpr
      refine ⟨row, ?_, hRowEq⟩
      apply List.mem_filter.mpr
      refine ⟨hRow, ?_⟩
      apply (executableCNFRowActive_value_iff row assignment).2
      apply (finiteBitVector_residualRowActive_toSplit_iff row assignment).1
      rw [hRowEq]
      exact hSplitRow.2
  change activeRows.length = _
  calc
    activeRows.length =
        (activeRows.map (fun row => FiniteBitVector.toSplit row)).length := by
      simp
    _ = (activeRows.map
          (fun row => FiniteBitVector.toSplit row)).toFinset.card := by
      symm
      exact List.toFinset_card_of_nodup hActiveRowsNodup
    _ = _ := congrArg Finset.card hActiveRowSet

/-- Deterministic complement verifier for a duplicate-free executable table. -/
def executableCNFNegativeVerifier
    (input : ExecutableDuplicateFreeOneTwoTable)
    (proofWitness : FiniteBitVector
      (input.table.leftCoordinateCount + input.table.rightCoordinateCount)) :
    ExecutableCNFCosted Bool :=
  let positive := executableCNFActiveRowCount proofWitness
    input.table.positiveRows
  let negative := executableCNFActiveRowCount proofWitness
    input.table.negativeRows
  ⟨decide (positive.value < negative.value),
    positive.steps + negative.steps + 1⟩

theorem executableCNFNegativeVerifier_value_iff
    (input : ExecutableDuplicateFreeOneTwoTable)
    (proofWitness : FiniteBitVector
      (input.table.leftCoordinateCount + input.table.rightCoordinateCount)) :
    (executableCNFNegativeVerifier input proofWitness).value = true ↔
      input.toSemanticCode.toOrderInstance.negativeBooleanWitness
        (input.toSemanticCode.proofWitnessAssignment proofWitness) := by
  classical
  unfold executableCNFNegativeVerifier
  dsimp
  rw [decide_eq_true_eq,
    executableCNFActiveRowCount_eq_semantic
      input.table.positiveRows input.positive_nodup proofWitness,
    executableCNFActiveRowCount_eq_semantic
      input.table.negativeRows input.negative_nodup proofWitness]
  change
    activeResidualRowCount input.toSemanticCode.positiveRows
        (input.toSemanticCode.proofWitnessAssignment proofWitness) <
      activeResidualRowCount input.toSemanticCode.negativeRows
        (input.toSemanticCode.proofWitnessAssignment proofWitness) ↔
      input.toSemanticCode.toOrderInstance.negativeBooleanWitness
        (input.toSemanticCode.proofWitnessAssignment proofWitness)
  exact (negativeBooleanWitness_iff_activeRowCount_lt
    input.toSemanticCode.toOrderInstance
    (input.toSemanticCode.proofWitnessAssignment proofWitness)).symm

theorem executableCNFNegativeVerifier_steps
    (input : ExecutableDuplicateFreeOneTwoTable)
    (proofWitness : FiniteBitVector
      (input.table.leftCoordinateCount + input.table.rightCoordinateCount)) :
    (executableCNFNegativeVerifier input proofWitness).steps =
      (input.table.positiveRows.length + input.table.negativeRows.length) *
          (2 * input.table.coordinateCount + 3) + 3 := by
  unfold executableCNFNegativeVerifier
  dsimp
  rw [executableCNFActiveRowCount_steps,
    executableCNFActiveRowCount_steps]
  unfold ExecutableOneTwoTable.coordinateCount
  ring_nf

theorem executableCNFNegativeVerifier_steps_le_tableSize
    (input : ExecutableDuplicateFreeOneTwoTable)
    (proofWitness : FiniteBitVector
      (input.table.leftCoordinateCount + input.table.rightCoordinateCount)) :
    (executableCNFNegativeVerifier input proofWitness).steps ≤
      3 * executableOneTwoTableSize input.table := by
  rw [executableCNFNegativeVerifier_steps]
  let rowCount :=
    input.table.positiveRows.length + input.table.negativeRows.length
  let coordinateCount := input.table.coordinateCount
  have hFactor : 2 * coordinateCount + 3 ≤ 3 * (coordinateCount + 1) := by
    omega
  have hConstant : 3 ≤ 3 * (coordinateCount + 1) := by
    omega
  unfold executableOneTwoTableSize
  change rowCount * (2 * coordinateCount + 3) + 3 ≤
    3 * ((coordinateCount + 1) * (rowCount + 1))
  calc
    rowCount * (2 * coordinateCount + 3) + 3 ≤
        rowCount * (3 * (coordinateCount + 1)) +
          3 * (coordinateCount + 1) :=
      Nat.add_le_add (Nat.mul_le_mul_left rowCount hFactor) hConstant
    _ = 3 * ((coordinateCount + 1) * (rowCount + 1)) := by ring

theorem executableCNF_not_accepts_iff_proofWitness
    (input : ExecutableDuplicateFreeOneTwoTable) :
    ¬ duplicateFreeOneTwoUniversalOrder.accepts input.toSemanticCode ↔
      ∃ proofWitness : FiniteBitVector
        (input.table.leftCoordinateCount + input.table.rightCoordinateCount),
        (executableCNFNegativeVerifier input proofWitness).value = true := by
  rw [duplicateFreeOneTwo_not_accepts_iff_proofWitness]
  constructor
  · rintro ⟨proofWitness, hProofWitness⟩
    refine ⟨proofWitness, ?_⟩
    apply (executableCNFNegativeVerifier_value_iff input proofWitness).2
    exact (duplicateFreeOneTwoNegativeVerifier_eq_true_iff
      input.toSemanticCode proofWitness).1 hProofWitness
  · rintro ⟨proofWitness, hProofWitness⟩
    refine ⟨proofWitness, ?_⟩
    apply (duplicateFreeOneTwoNegativeVerifier_eq_true_iff
      input.toSemanticCode proofWitness).2
    exact (executableCNFNegativeVerifier_value_iff
      input proofWitness).1 hProofWitness

theorem executableSelectorTerms_length_eq
    (input : ExecutableProperCNFCode) :
    (executableSelectorTerms input).length =
      ∑ clause : Fin input.clauses.length,
        2 ^ (input.clauses.get clause).positive.length := by
  simp only [executableSelectorTerms, List.length_flatMap,
    List.length_map, List.length_attach, List.length_sublists,
    ExecutableProperCNFCode.clauseCount]
  rw [← List.sum_toFinset _ (List.nodup_finRange _),
    List.toFinset_finRange]

/-- At most eight expansion terms are emitted per width-three clause. -/
theorem executableSelectorTerms_length_le
    (input : ExecutableProperCNFCode) :
    (executableSelectorTerms input).length ≤ 8 * input.clauseCount := by
  rw [executableSelectorTerms_length_eq]
  calc
    (∑ clause : Fin input.clauses.length,
        2 ^ (input.clauses.get clause).positive.length) ≤
        ∑ _clause : Fin input.clauses.length, 8 := by
      apply Finset.sum_le_sum
      intro clause _
      have hLength : (input.clauses.get clause).positive.length ≤ 3 := by
        have hWidth := (input.clauses.get clause).width_le_three
        omega
      calc
        2 ^ (input.clauses.get clause).positive.length ≤ 2 ^ 3 :=
          Nat.pow_le_pow_right (by norm_num) hLength
        _ = 8 := by norm_num
    _ = 8 * input.clauseCount := by
      simp [ExecutableProperCNFCode.clauseCount, Nat.mul_comm]

theorem executableSelector_row_count
    (input : ExecutableProperCNFCode) :
    (executableSelectorPositiveRows input).length +
        (executableSelectorNegativeRows input).length =
      (executableSelectorTerms input).length + 1 := by
  unfold executableSelectorPositiveRows executableSelectorNegativeRows
  simp only [List.length_map, List.length_cons]
  have hPartition := List.length_eq_length_filter_add
    (l := executableSelectorTerms input)
    (fun term => executableSelectorTermPositive term)
  omega

/-- Declared construction charge for the unnormalized selector table.  It
counts coordinate writes, parity classification, clause enumeration, and the
final constructor.  This local arithmetic measure is not, by itself, a
machine-model running-time theorem. -/
def executableSelectorCompilerCost (input : ExecutableProperCNFCode) : ℕ :=
  (executableSelectorTerms input).length *
      (input.variableCount + input.clauseCount + 2) +
    input.clauseCount + 1

/-- Compiler result paired with its deterministic operation count. -/
def compileExecutableProperCNFSelectorWithCost
    (input : ExecutableProperCNFCode) : ExecutableOneTwoTable × ℕ :=
  (compileExecutableProperCNFSelector input,
    executableSelectorCompilerCost input)

@[simp] theorem compileExecutableProperCNFSelectorWithCost_output
    (input : ExecutableProperCNFCode) :
    (compileExecutableProperCNFSelectorWithCost input).1 =
      compileExecutableProperCNFSelector input := rfl

@[simp] theorem compileExecutableProperCNFSelectorWithCost_cost
    (input : ExecutableProperCNFCode) :
    (compileExecutableProperCNFSelectorWithCost input).2 =
      executableSelectorCompilerCost input := rfl

theorem compileExecutableProperCNFSelector_rowCount_le
    (input : ExecutableProperCNFCode) :
    (compileExecutableProperCNFSelector input).positiveRows.length +
        (compileExecutableProperCNFSelector input).negativeRows.length ≤
      1 + 8 * input.clauseCount := by
  rw [show
    (compileExecutableProperCNFSelector input).positiveRows.length +
        (compileExecutableProperCNFSelector input).negativeRows.length =
      (executableSelectorTerms input).length + 1 by
    exact executableSelector_row_count input]
  have hTerms := executableSelectorTerms_length_le input
  omega

/-- Explicit table output is quadratic in the concrete source size. -/
theorem compileExecutableProperCNFSelector_size_le
    (input : ExecutableProperCNFCode) :
    executableOneTwoTableSize
        (compileExecutableProperCNFSelector input) ≤
      10 * executableProperCNFCodeSize input ^ 2 := by
  let sourceSize := executableProperCNFCodeSize input
  have hSourcePositive : 0 < sourceSize := by
    exact executableProperCNFCodeSize_positive input
  have hCoordinateFactor :
      input.variableCount + input.clauseCount + 1 ≤ sourceSize := by
    dsimp [sourceSize, executableProperCNFCodeSize]
    omega
  have hClause : input.clauseCount ≤ sourceSize := by
    dsimp [sourceSize, executableProperCNFCodeSize]
    omega
  have hRows := compileExecutableProperCNFSelector_rowCount_le input
  have hRowFactor :
      (compileExecutableProperCNFSelector input).positiveRows.length +
          (compileExecutableProperCNFSelector input).negativeRows.length + 1 ≤
        10 * sourceSize := by
    calc
      _ ≤ (1 + 8 * input.clauseCount) + 1 :=
        Nat.add_le_add_right hRows 1
      _ ≤ 10 * sourceSize := by omega
  unfold executableOneTwoTableSize ExecutableOneTwoTable.coordinateCount
  change
    (input.variableCount + input.clauseCount + 1) *
        ((compileExecutableProperCNFSelector input).positiveRows.length +
          (compileExecutableProperCNFSelector input).negativeRows.length + 1) ≤
      10 * sourceSize ^ 2
  calc
    _ ≤ sourceSize * (10 * sourceSize) :=
      Nat.mul_le_mul hCoordinateFactor hRowFactor
    _ = 10 * sourceSize ^ 2 := by ring

/-- The instrumented compiler cost is bounded quadratically in source size. -/
theorem executableSelectorCompilerCost_le
    (input : ExecutableProperCNFCode) :
    executableSelectorCompilerCost input ≤
      20 * executableProperCNFCodeSize input ^ 2 := by
  let sourceSize := executableProperCNFCodeSize input
  have hSourcePositive : 0 < sourceSize :=
    executableProperCNFCodeSize_positive input
  have hSourceOne : 1 ≤ sourceSize := hSourcePositive
  have hClause : input.clauseCount ≤ sourceSize := by
    dsimp [sourceSize, executableProperCNFCodeSize]
    omega
  have hCoordinates :
      input.variableCount + input.clauseCount + 2 ≤ 2 * sourceSize := by
    dsimp [sourceSize, executableProperCNFCodeSize]
    omega
  have hTerms : (executableSelectorTerms input).length ≤ 8 * sourceSize :=
    (executableSelectorTerms_length_le input).trans
      (Nat.mul_le_mul_left 8 hClause)
  have hProduct :
      (executableSelectorTerms input).length *
          (input.variableCount + input.clauseCount + 2) ≤
        (8 * sourceSize) * (2 * sourceSize) :=
    Nat.mul_le_mul hTerms hCoordinates
  have hLinear : input.clauseCount + 1 ≤ 2 * sourceSize := by omega
  have hLinearQuadratic : 2 * sourceSize ≤ 2 * sourceSize ^ 2 := by
    apply Nat.mul_le_mul_left
    calc
      sourceSize = sourceSize ^ 1 := by simp
      _ ≤ sourceSize ^ 2 := pow_le_pow_right' hSourceOne (by omega)
  unfold executableSelectorCompilerCost
  calc
    _ ≤ (8 * sourceSize) * (2 * sourceSize) + 2 * sourceSize :=
      Nat.add_le_add hProduct hLinear
    _ ≤ (8 * sourceSize) * (2 * sourceSize) + 2 * sourceSize ^ 2 :=
      Nat.add_le_add_left hLinearQuadratic _
    _ = 18 * sourceSize ^ 2 := by ring
    _ ≤ 20 * sourceSize ^ 2 := by omega

theorem compileDuplicateFreeExecutableProperCNFSelector_size_le
    (input : ExecutableProperCNFCode) :
    executableOneTwoTableSize
        (compileDuplicateFreeExecutableProperCNFSelector input).table ≤
      10 * executableProperCNFCodeSize input ^ 2 := by
  calc
    executableOneTwoTableSize
        (compileDuplicateFreeExecutableProperCNFSelector input).table ≤
        executableOneTwoTableSize
          (compileExecutableProperCNFSelector input) := by
      exact normalizeExecutableOneTwoTable_size_le
        (compileExecutableProperCNFSelector input)
    _ ≤ 10 * executableProperCNFCodeSize input ^ 2 :=
      compileExecutableProperCNFSelector_size_le input

theorem compiledExecutableCNFNegativeVerifier_steps_le
    (input : ExecutableProperCNFCode)
    (proofWitness : FiniteBitVector
      (input.variableCount + input.clauseCount)) :
    (executableCNFNegativeVerifier
        (compileDuplicateFreeExecutableProperCNFSelector input)
        proofWitness).steps ≤
      30 * executableProperCNFCodeSize input ^ 2 := by
  calc
    (executableCNFNegativeVerifier
        (compileDuplicateFreeExecutableProperCNFSelector input)
        proofWitness).steps ≤
        3 * executableOneTwoTableSize
          (compileDuplicateFreeExecutableProperCNFSelector input).table :=
      executableCNFNegativeVerifier_steps_le_tableSize _ _
    _ ≤ 3 * (10 * executableProperCNFCodeSize input ^ 2) :=
      Nat.mul_le_mul_left 3
        (compileDuplicateFreeExecutableProperCNFSelector_size_le input)
    _ = 30 * executableProperCNFCodeSize input ^ 2 := by ring

/-! ## Registered executable decision problems -/

/-- Unsatisfiability over the concrete literal-list source encoding. -/
def executableProperCNFUnsatisfiability : EncodedDecisionProblem where
  Instance := ExecutableProperCNFCode
  accepts := fun input => ¬ input.toSemanticFormula.Satisfiable
  size := executableProperCNFCodeSize
  size_positive := executableProperCNFCodeSize_positive

/-- Universal order over proof-bearing duplicate-free row lists. -/
def executableDuplicateFreeOneTwoUniversalOrder : EncodedDecisionProblem where
  Instance := ExecutableDuplicateFreeOneTwoTable
  accepts := fun input =>
    duplicateFreeOneTwoUniversalOrder.accepts input.toSemanticCode
  size := fun input => executableOneTwoTableSize input.table
  size_positive := by
    intro input
    unfold executableOneTwoTableSize
    positivity

/-- Exact local semantic-size reduction realized by the concrete compiler. -/
def executableProperCNFSelectorReduction :
    PolynomialSizeManyOneReduction
      executableProperCNFUnsatisfiability
      executableDuplicateFreeOneTwoUniversalOrder where
  map := compileDuplicateFreeExecutableProperCNFSelector
  correct := by
    intro input
    exact compileDuplicateFreeExecutableProperCNFSelector_correct input
  coefficient := 10
  degree := 2
  coefficient_positive := by norm_num
  size_bound := compileDuplicateFreeExecutableProperCNFSelector_size_le

/-- Concrete complement proof-witness contract backed by the recursive scan
verifier above. -/
def executableCNFComplementProofWitness :
    PolynomialComplementProofWitness
      executableDuplicateFreeOneTwoUniversalOrder where
  proofWitnessLength := fun input =>
    input.table.leftCoordinateCount + input.table.rightCoordinateCount
  verify := fun input proofWitness =>
    (executableCNFNegativeVerifier input proofWitness).value
  correctness := executableCNF_not_accepts_iff_proofWitness
  lengthCoefficient := 1
  lengthDegree := 1
  lengthCoefficient_positive := by norm_num
  length_bound := by
    intro input
    simp only [one_mul, pow_one]
    unfold executableDuplicateFreeOneTwoUniversalOrder
    dsimp
    unfold executableOneTwoTableSize ExecutableOneTwoTable.coordinateCount
    have hRowFactor :
        1 ≤ input.table.positiveRows.length +
          input.table.negativeRows.length + 1 := by omega
    calc
      input.table.leftCoordinateCount + input.table.rightCoordinateCount ≤
          input.table.leftCoordinateCount +
            input.table.rightCoordinateCount + 1 := by omega
      _ ≤ (input.table.leftCoordinateCount +
            input.table.rightCoordinateCount + 1) *
          (input.table.positiveRows.length +
            input.table.negativeRows.length + 1) :=
        Nat.le_mul_of_pos_right _ hRowFactor
  verificationCost := fun input proofWitness =>
    (executableCNFNegativeVerifier input proofWitness).steps
  costCoefficient := 3
  costDegree := 1
  costCoefficient_positive := by norm_num
  cost_bound := by
    intro input proofWitness
    simp only [pow_one]
    exact executableCNFNegativeVerifier_steps_le_tableSize input proofWitness

/-- External boundary for a conventional complexity reading.  The local file
proves the concrete reduction and recursive verifier; this record supplies
only the source-completeness theorem and the generic machine-model bridge from
a polynomial complement proof-witness contract to class membership.  No field
mentions the compiled target language. -/
structure ExecutableCNFConventionalBoundary
    (coNP : EncodedDecisionClass) : Prop where
  source_complete :
    CompleteFor coNP executableProperCNFUnsatisfiability
  complementProofWitness_mem : ∀ problem,
    PolynomialComplementProofWitness problem → coNP problem

/-- Conditional conventional completeness, with the machine-model boundary
kept explicit. -/
theorem max_g4_executableCNF_conditionalCompleteness
    {coNP : EncodedDecisionClass}
    (boundary : ExecutableCNFConventionalBoundary coNP) :
    CompleteFor coNP executableDuplicateFreeOneTwoUniversalOrder := by
  exact complete_of_complete_source boundary.source_complete
    (boundary.complementProofWitness_mem _
      executableCNFComplementProofWitness)
    executableProperCNFSelectorReduction

/-- Conservative comparison-and-copy charge for list normalization.  One
row comparison is charged one complete coordinate scan. -/
def executableSelectorNormalizationCharge
    (input : ExecutableProperCNFCode) : ℕ :=
  let table := compileExecutableProperCNFSelector input
  let rowCount := table.positiveRows.length + table.negativeRows.length
  rowCount * (rowCount + 1) * (table.coordinateCount + 1)

/-- Normalized compiler value paired with the sum of the construction and
normalization charges.  The charge is an explicit conservative list-model
accounting device; no standard machine-time conclusion is drawn from it. -/
def compileDuplicateFreeExecutableProperCNFSelectorWithCharge
    (input : ExecutableProperCNFCode) :
    ExecutableDuplicateFreeOneTwoTable × ℕ :=
  (compileDuplicateFreeExecutableProperCNFSelector input,
    executableSelectorCompilerCost input +
      executableSelectorNormalizationCharge input)

@[simp] theorem compileDuplicateFreeExecutableProperCNFSelectorWithCharge_output
    (input : ExecutableProperCNFCode) :
    (compileDuplicateFreeExecutableProperCNFSelectorWithCharge input).1 =
      compileDuplicateFreeExecutableProperCNFSelector input := rfl

@[simp] theorem compileDuplicateFreeExecutableProperCNFSelectorWithCharge_charge
    (input : ExecutableProperCNFCode) :
    (compileDuplicateFreeExecutableProperCNFSelectorWithCharge input).2 =
      executableSelectorCompilerCost input +
        executableSelectorNormalizationCharge input := rfl

theorem executableSelectorNormalizationCharge_le
    (input : ExecutableProperCNFCode) :
    executableSelectorNormalizationCharge input ≤
      90 * executableProperCNFCodeSize input ^ 3 := by
  let sourceSize := executableProperCNFCodeSize input
  let table := compileExecutableProperCNFSelector input
  let rowCount := table.positiveRows.length + table.negativeRows.length
  have hSourcePositive : 0 < sourceSize :=
    executableProperCNFCodeSize_positive input
  have hClause : input.clauseCount ≤ sourceSize := by
    dsimp [sourceSize, executableProperCNFCodeSize]
    omega
  have hRowsBase := compileExecutableProperCNFSelector_rowCount_le input
  have hRows : rowCount ≤ 9 * sourceSize := by
    dsimp [rowCount, table]
    calc
      _ ≤ 1 + 8 * input.clauseCount := hRowsBase
      _ ≤ 9 * sourceSize := by omega
  have hRowsSucc : rowCount + 1 ≤ 10 * sourceSize := by omega
  have hCoordinates : table.coordinateCount + 1 ≤ sourceSize := by
    dsimp [table, compileExecutableProperCNFSelector,
      ExecutableOneTwoTable.coordinateCount, sourceSize,
      executableProperCNFCodeSize]
    omega
  unfold executableSelectorNormalizationCharge
  change rowCount * (rowCount + 1) * (table.coordinateCount + 1) ≤
    90 * sourceSize ^ 3
  calc
    rowCount * (rowCount + 1) * (table.coordinateCount + 1) ≤
        (9 * sourceSize) * (10 * sourceSize) * sourceSize :=
      Nat.mul_le_mul (Nat.mul_le_mul hRows hRowsSucc) hCoordinates
    _ = 90 * sourceSize ^ 3 := by ring

theorem compileDuplicateFreeExecutableProperCNFSelectorWithCharge_le
    (input : ExecutableProperCNFCode) :
    (compileDuplicateFreeExecutableProperCNFSelectorWithCharge input).2 ≤
      110 * executableProperCNFCodeSize input ^ 3 := by
  let sourceSize := executableProperCNFCodeSize input
  have hSourceOne : 1 ≤ sourceSize :=
    executableProperCNFCodeSize_positive input
  have hCompiler := executableSelectorCompilerCost_le input
  have hCompilerCubic :
      executableSelectorCompilerCost input ≤ 20 * sourceSize ^ 3 := by
    calc
      executableSelectorCompilerCost input ≤ 20 * sourceSize ^ 2 :=
        hCompiler
      _ ≤ 20 * sourceSize ^ 3 := by
        apply Nat.mul_le_mul_left
        exact Nat.pow_le_pow_right hSourceOne (by omega)
  have hNormalization := executableSelectorNormalizationCharge_le input
  unfold compileDuplicateFreeExecutableProperCNFSelectorWithCharge
  dsimp
  calc
    executableSelectorCompilerCost input +
        executableSelectorNormalizationCharge input ≤
      20 * sourceSize ^ 3 + 90 * sourceSize ^ 3 :=
        Nat.add_le_add hCompilerCubic hNormalization
    _ = 110 * sourceSize ^ 3 := by ring

end PhonologicalCalculus.MaxEnt
