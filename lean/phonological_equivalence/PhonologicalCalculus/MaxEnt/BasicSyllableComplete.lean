import PhonologicalCalculus.MaxEnt.BasicSyllable
import PhonologicalCalculus.MaxEnt.BasicSyllableCone
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

namespace PhonologicalCalculus.MaxEnt

set_option maxRecDepth 100000 in
theorem max_g6_provenance_03 :
    basicSyllableImplications.length = 121 ∧
      basicSyllableEmptyAntecedentImplications.length = 105 ∧
      basicSyllableLiveImplications.length = 16 ∧
      basicSyllableImplications ≠ basicSyllableLiveImplications := by
  decide

def basicSyllableCollapseMatrix : Matrix (Fin 2) (Fin 4) ℤ :=
  !![-1, 0, 0, -1;
     0, -1, -1, 0]

def BasicSyllableMixedCone (weight : Fin 4 → ℝ) : Prop :=
  (∀ coordinate, 0 ≤ weight coordinate) ∧
    0 ≤ -(weight 0) - weight 3 ∧
    0 ≤ -(weight 1) - weight 2

theorem basicSyllableCollapseMultiplier_exact :
    Matrix.vecMul (fun _ : Fin 2 => (-1 : ℤ)) basicSyllableCollapseMatrix =
      ![(1 : ℤ), 1, 1, 1] := by
  funext coordinate
  fin_cases coordinate <;>
    norm_num [basicSyllableCollapseMatrix, Matrix.vecMul,
      dotProduct, Fin.sum_univ_succ]

theorem basicSyllableMixedCone_iff_zero (weight : Fin 4 → ℝ) :
    BasicSyllableMixedCone weight ↔ weight = 0 := by
  constructor
  · rintro ⟨hNonnegative, hFirst, hSecond⟩
    funext coordinate
    fin_cases coordinate
    · have hZero := hNonnegative 0
      have hThree := hNonnegative 3
      change weight 0 = 0
      linarith
    · have hOne := hNonnegative 1
      have hTwo := hNonnegative 2
      change weight 1 = 0
      linarith
    · have hOne := hNonnegative 1
      have hTwo := hNonnegative 2
      change weight 2 = 0
      linarith
    · have hZero := hNonnegative 0
      have hThree := hNonnegative 3
      change weight 3 = 0
      linarith
  · rintro rfl
    constructor
    · intro coordinate
      simp
    · norm_num

         
theorem max_g6_completeBasicSyllableDecomposition
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] :
    (basicSyllableRankings.length = 24 ∧
      basicSyllableWinnerMaps = expectedBasicSyllableWinnerMaps ∧
      basicSyllableWinnerMapList.toFinset = basicSyllableWinnerMaps ∧
      basicSyllableImplicationsWithReflexive.length = 137 ∧
      basicSyllableImplications.length = 121 ∧
      basicSyllableEmptyAntecedentMappings.length = 7 ∧
      basicSyllableEmptyAntecedentImplications.length = 105 ∧
      basicSyllableLiveImplications.length = 16) ∧
    (basicSyllableImplications.length = 121 ∧
      basicSyllableEmptyAntecedentImplications.length = 105 ∧
      basicSyllableLiveImplications.length = 16 ∧
      basicSyllableImplications ≠ basicSyllableLiveImplications) ∧
    (∀ a b c d : K,
      0 < a → a ≤ 1 → 0 < b → b ≤ 1 →
      0 < c → c ≤ 1 → 0 < d → d ≤ 1 →
      (basicSyllableAllLiveOrders a b c d ↔
        0 ≤ basicSyllableFacetD b c d ∧
          0 ≤ basicSyllableFacetC a c d)) ∧
    (basicSyllableFacetD (1 / 2 : K) (1 / 2 : K) (1 / 2 : K) = 3 / 8 ∧
      basicSyllableFacetC (1 / 2 : K) (1 / 2 : K) (1 / 2 : K) = 3 / 8) ∧
    (∀ weight : Fin 4 → ℝ,
      BasicSyllableMixedCone weight ↔ weight = 0) := by
  exact ⟨max_g6_enum_01, max_g6_provenance_03, max_g6_cone_02,
    basicSyllableRegisteredInterior, basicSyllableMixedCone_iff_zero⟩

end PhonologicalCalculus.MaxEnt
