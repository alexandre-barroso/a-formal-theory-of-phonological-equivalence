import PhonologicalCalculus.Finite.OrbitRecovery
import Mathlib.Tactic

/-!
# Proof-carrying finite response import

An exact response family may be imported through a finite symbolic code only
when the reachable image, interpretation, semantic equality, registered
reader, descended transformation, and two commuting squares are supplied.
Carrier classification is independent of a source section.  Lifting a code
witness back to a source representative is a separate proof requirement.
-/

namespace PhonologicalCalculus

structure ResponseImport
    (Source Code Semantic Answer : Type*) [DecidableEq Code] where
  reachable : Finset Code
  encode : Source → Code
  interpret : Code → Semantic
  response : Source → Semantic
  semanticEq : Semantic → Semantic → Bool
  reader : Code → Answer
  semanticQuery : Semantic → Answer
  sourceTransform : Source → Source
  descent : Code → Code
  semanticTransform : Semantic → Semantic
  reachable_exact : ∀ code, code ∈ reachable ↔ ∃ source, encode source = code
  interpretation_exact : ∀ source,
    interpret (encode source) = response source
  semanticEq_exact : ∀ first second,
    semanticEq first second = true ↔ first = second
  reader_faithful : ∀ code ∈ reachable,
    reader code = semanticQuery (interpret code)
  descent_reachable : ∀ code ∈ reachable, descent code ∈ reachable
  code_square : ∀ source,
    descent (encode source) = encode (sourceTransform source)
  semantic_square : ∀ code ∈ reachable,
    interpret (descent code) = semanticTransform (interpret code)

variable {Source Code Semantic Answer : Type*} [DecidableEq Code]

theorem ResponseImport.source_code_reachable
    (bridge : ResponseImport Source Code Semantic Answer) (source : Source) :
    bridge.encode source ∈ bridge.reachable :=
  (bridge.reachable_exact _).2 ⟨source, rfl⟩

/-- The code reader recovers the registered source answer exactly. -/
theorem ResponseImport.reader_encode
    (bridge : ResponseImport Source Code Semantic Answer) (source : Source) :
    bridge.reader (bridge.encode source) =
      bridge.semanticQuery (bridge.response source) := by
  rw [bridge.reader_faithful _ (bridge.source_code_reachable source)]
  congr 1
  exact bridge.interpretation_exact source

/-- The descended code comparison is the source-transformed comparison under
the same registered reader. -/
theorem ResponseImport.query_square
    (bridge : ResponseImport Source Code Semantic Answer) (source : Source) :
    bridge.reader (bridge.descent (bridge.encode source)) =
      bridge.semanticQuery
        (bridge.semanticTransform (bridge.response source)) := by
  have hReachable := bridge.source_code_reachable source
  rw [bridge.reader_faithful _ (bridge.descent_reachable _ hReachable)]
  rw [bridge.semantic_square _ hReachable]
  rw [bridge.interpretation_exact source]

def ResponseImport.mismatchCodes [DecidableEq Answer]
    (bridge : ResponseImport Source Code Semantic Answer) : Finset Code :=
  bridge.reachable.filter
    (fun code => bridge.reader code ≠ bridge.reader (bridge.descent code))

theorem ResponseImport.mem_mismatchCodes_iff [DecidableEq Answer]
    (bridge : ResponseImport Source Code Semantic Answer) (code : Code) :
    code ∈ bridge.mismatchCodes ↔
      code ∈ bridge.reachable ∧
        bridge.reader code ≠ bridge.reader (bridge.descent code) := by
  simp [ResponseImport.mismatchCodes]

/-- Every carrier mismatch computed on the reachable code image denotes an
actual source response, independently of whether a chosen source section has
been registered. -/
theorem ResponseImport.mismatch_has_source [DecidableEq Answer]
    (bridge : ResponseImport Source Code Semantic Answer)
    {code : Code} (hmismatch : code ∈ bridge.mismatchCodes) :
    ∃ source, bridge.encode source = code := by
  exact (bridge.reachable_exact code).1
    ((bridge.mem_mismatchCodes_iff code).1 hmismatch).1

def IsSectionOn {Source Code : Type*} (encode : Source → Code)
    (domain : Set Code) (sectionMap : Code → Source) : Prop :=
  ∀ code ∈ domain, encode (sectionMap code) = code

theorem one_proved_preimage_lifts {Source Code : Type*}
    (encode : Source → Code) (source : Source) (code : Code)
    (hpreimage : encode source = code) :
    ∃ witness : Source, encode witness = code :=
  ⟨source, hpreimage⟩

theorem section_lifts_every_code {Source Code : Type*}
    (encode : Source → Code) (domain : Set Code)
    (sectionMap : Code → Source)
    (hsection : IsSectionOn encode domain sectionMap) :
    ∀ code ∈ domain, ∃ source, encode source = code := by
  intro code hcode
  exact ⟨sectionMap code, hsection code hcode⟩

/-- If the code map is injective, a section on its reachable image is unique.
This is a set-theoretic statement and does not assert an effective inversion
algorithm for an externally represented source. -/
theorem sectionOnRange_unique_of_injective {Source Code : Type*}
    (encode : Source → Code) (hinjective : Function.Injective encode)
    (first second : Code → Source)
    (hFirst : IsSectionOn encode (Set.range encode) first)
    (hSecond : IsSectionOn encode (Set.range encode) second) :
    ∀ code ∈ Set.range encode, first code = second code := by
  intro code hcode
  apply hinjective
  exact (hFirst code hcode).trans (hSecond code hcode).symm

section FiniteLeastSection

variable {FiniteSource FiniteCode : Type*}
    [Fintype FiniteSource] [DecidableEq FiniteCode]

def preimageFinset (encode : FiniteSource → FiniteCode)
    (code : FiniteCode) : Finset FiniteSource :=
  Finset.univ.filter (fun source => encode source = code)

theorem preimageFinset_nonempty (encode : FiniteSource → FiniteCode)
    (code : Set.range encode) : (preimageFinset encode code.1).Nonempty := by
  obtain ⟨source, hsource⟩ := code.property
  exact ⟨source, by simp [preimageFinset, hsource]⟩

variable [LinearOrder FiniteSource]

/-- Finite ordered source carriers have a computable least-preimage section
on the complete reachable image, without an injectivity assumption. -/
def finiteLeastSection (encode : FiniteSource → FiniteCode) :
    Set.range encode → FiniteSource :=
  fun code => (preimageFinset encode code.1).min'
    (preimageFinset_nonempty encode code)

theorem finiteLeastSection_is_section
    (encode : FiniteSource → FiniteCode) (code : Set.range encode) :
    encode (finiteLeastSection encode code) = code.1 := by
  have hmember := Finset.min'_mem (preimageFinset encode code.1)
    (preimageFinset_nonempty encode code)
  exact (Finset.mem_filter.1 hmember).2

theorem finiteLeastSection_is_least
    (encode : FiniteSource → FiniteCode) (code : Set.range encode)
    {source : FiniteSource} (hsource : encode source = code.1) :
    finiteLeastSection encode code ≤ source := by
  apply Finset.min'_le
  simp [preimageFinset, hsource]

end FiniteLeastSection

structure ResponseFormationChecklist where
  codeCarrier : Bool
  interpretation : Bool
  semanticEquality : Bool
  reachableImage : Bool
  reader : Bool
  descent : Bool
  commutingSquares : Bool
  sourceSection : Bool
  deriving DecidableEq, Repr

def ResponseFormationChecklist.carrierReady
    (checklist : ResponseFormationChecklist) : Bool :=
  checklist.codeCarrier && checklist.interpretation &&
    checklist.semanticEquality && checklist.reachableImage &&
    checklist.reader && checklist.descent && checklist.commutingSquares

def ResponseFormationChecklist.sourceWitnessReady
    (checklist : ResponseFormationChecklist) : Bool :=
  checklist.carrierReady && checklist.sourceSection

/-- Omitting only the source section preserves carrier availability while
refusing the stronger source-witness output. -/
theorem missing_section_preserves_carrier_decision
    (checklist : ResponseFormationChecklist)
    (hCore : checklist.carrierReady = true)
    (hSection : checklist.sourceSection = false) :
    checklist.carrierReady = true ∧
      checklist.sourceWitnessReady = false := by
  simp [ResponseFormationChecklist.sourceWitnessReady, hCore, hSection]

/-- Every core formation field is load-bearing for the carrier decision. -/
theorem missing_core_field_refuses_carrier
    (checklist : ResponseFormationChecklist)
    (hMissing : checklist.codeCarrier = false ∨
      checklist.interpretation = false ∨
      checklist.semanticEquality = false ∨
      checklist.reachableImage = false ∨
      checklist.reader = false ∨ checklist.descent = false ∨
      checklist.commutingSquares = false) :
    checklist.carrierReady = false := by
  rcases hMissing with h | h | h | h | h | h | h <;>
    simp [ResponseFormationChecklist.carrierReady, h]

/-- Integrated FIN-A7 response-import theorem. -/
theorem fin_a7_responseImport
    [DecidableEq Answer]
    (bridge : ResponseImport Source Code Semantic Answer) :
    (∀ source,
      bridge.reader (bridge.encode source) =
        bridge.semanticQuery (bridge.response source)) ∧
    (∀ first second,
      bridge.semanticEq first second = true ↔ first = second) ∧
    (∀ source,
      bridge.reader (bridge.descent (bridge.encode source)) =
        bridge.semanticQuery
          (bridge.semanticTransform (bridge.response source))) ∧
    (∀ code ∈ bridge.mismatchCodes,
      ∃ source, bridge.encode source = code) := by
  exact ⟨bridge.reader_encode, bridge.semanticEq_exact,
    bridge.query_square, fun _ => bridge.mismatch_has_source⟩

end PhonologicalCalculus
