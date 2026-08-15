import PhonologicalCalculus.MaxEnt.BasicSyllable
import PhonologicalCalculus.MaxEnt.BasicSyllableCone

/-!
# Basic Syllable proof reuse

The source-facing application reuses the exact finite inventory and live-cone
theorems.  No second reconstruction is introduced: the application theorem is
a projection of the same kernel-checked declarations used by `MAX-G6`.
-/

namespace PhonologicalCalculus.Application

open PhonologicalCalculus.MaxEnt

/-- **APP-BASIC.REUSE.01**.  The exact nonreflexive implication inventory
partitions into 105 empty-antecedent implications and 16 live implications. -/
theorem app_basic_reuse :
    basicSyllableImplications.length = 121 ∧
    basicSyllableEmptyAntecedentImplications.length = 105 ∧
    basicSyllableLiveImplications.length = 16 := by
  exact ⟨max_g6_enum_01.2.2.2.2.1,
    max_g6_enum_01.2.2.2.2.2.2.1,
    max_g6_enum_01.2.2.2.2.2.2.2⟩

/-- The reused live-cone result retains both exact irredundant facets on the
positive unit cube. -/
theorem app_basic_liveCone
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (a b c d : K)
    (ha : 0 < a) (ha1 : a ≤ 1) (hb : 0 < b) (hb1 : b ≤ 1)
    (hc : 0 < c) (hc1 : c ≤ 1) (hd : 0 < d) (hd1 : d ≤ 1) :
    basicSyllableAllLiveOrders a b c d ↔
      (0 ≤ basicSyllableFacetD b c d ∧
        0 ≤ basicSyllableFacetC a c d) := by
  exact max_g6_cone_02 a b c d ha ha1 hb hb1 hc hc1 hd hd1

end PhonologicalCalculus.Application
