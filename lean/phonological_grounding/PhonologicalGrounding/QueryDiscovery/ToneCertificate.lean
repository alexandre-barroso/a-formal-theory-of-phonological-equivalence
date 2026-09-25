import Mathlib.Data.List.Basic
import PhonologicalGrounding.Basic

namespace PhonologicalGrounding.QueryDiscovery

namespace Tone

                      
structure Origin where
  segment : Nat
  present : Bool
  tone : Option Bool
deriving DecidableEq, Repr

def segments (l : List Origin) : List Nat :=
  (l.filter (·.present)).map (·.segment)

def segTone (l : List Origin) : List (Nat × Option Bool) :=
  (l.filter (·.present)).map (fun o => (o.segment, o.tone))

theorem no_attribute_bridge_separates {B : Type*} (g : List (Nat × Option Bool) → B)
    {x y : List Origin} (h : segTone x = segTone y) :
    g (segTone x) = g (segTone y) :=
  congrArg g h

theorem segments_factors (l : List Origin) :
    segments l = (segTone l).map Prod.fst := by
  simp [segments, segTone, List.map_map, Function.comp_def]

def leftSurvives (pre post : List Origin) (s : Nat) (tL tR : Option Bool) : List Origin :=
  pre ++ ⟨s, true, tL⟩ :: ⟨s, false, tR⟩ :: post

def rightSurvives (pre post : List Origin) (s : Nat) (tL tR : Option Bool) : List Origin :=
  pre ++ ⟨s, false, tL⟩ :: ⟨s, true, tR⟩ :: post

theorem segments_append (l m : List Origin) : segments (l ++ m) = segments l ++ segments m := by
  simp [segments, List.filter_append, List.map_append]

theorem segTone_append (l m : List Origin) : segTone (l ++ m) = segTone l ++ segTone m := by
  simp [segTone, List.filter_append, List.map_append]

theorem hiatus_segments_merge (pre post : List Origin) (s : Nat) (tL tR : Option Bool) :
    segments (leftSurvives pre post s tL tR) = segments (rightSurvives pre post s tL tR) := by
  simp [leftSurvives, rightSurvives, segments_append, segments]

theorem hiatus_tone_separates_iff (pre post : List Origin) (s : Nat) (tL tR : Option Bool) :
    segTone (leftSurvives pre post s tL tR) ≠ segTone (rightSurvives pre post s tL tR)
      ↔ tL ≠ tR := by
  simp [leftSurvives, rightSurvives, segTone_append, segTone]

theorem hiatus_tone_merges_iff (pre post : List Origin) (s : Nat) (tL tR : Option Bool) :
    segTone (leftSurvives pre post s tL tR) = segTone (rightSurvives pre post s tL tR)
      ↔ tL = tR := by
  simp [leftSurvives, rightSurvives, segTone_append, segTone]

def or38Left : List Origin :=
  [ ⟨1, true, some true⟩,
    ⟨0, true, none⟩,
    ⟨7, true, some false⟩,
    ⟨0, true, none⟩,
    ⟨0, false, some false⟩,
    ⟨6, true, some true⟩,
    ⟨0, true, none⟩,
    ⟨10, true, some false⟩ ]

def or38Right : List Origin :=
  [ ⟨1, true, some true⟩,
    ⟨0, true, none⟩,
    ⟨7, true, some false⟩,
    ⟨0, true, none⟩,
    ⟨6, true, some false⟩,
    ⟨0, false, some true⟩,
    ⟨0, true, none⟩,
    ⟨10, true, some false⟩ ]

theorem or38_segments_merge : segments or38Left = segments or38Right := by decide

theorem or38_tone_separates : segTone or38Left ≠ segTone or38Right := by decide

def c21bLeft : List Origin :=
  [ ⟨12, true, none⟩,
    ⟨9, true, some false⟩,
    ⟨0, true, none⟩,
    ⟨0, false, some true⟩,
    ⟨9, true, some true⟩,
    ⟨0, true, none⟩,
    ⟨3, true, some false⟩ ]

def c21bRight : List Origin :=
  [ ⟨12, true, none⟩,
    ⟨9, true, some false⟩,
    ⟨0, true, none⟩,
    ⟨9, true, some true⟩,
    ⟨0, false, some true⟩,
    ⟨0, true, none⟩,
    ⟨3, true, some false⟩ ]

theorem c21b_segments_merge : segments c21bLeft = segments c21bRight := by decide

theorem c21b_tone_merges : segTone c21bLeft = segTone c21bRight := by decide

theorem c21b_no_attribute_bridge_separates {B : Type*}
    (g : List (Nat × Option Bool) → B) :
    g (segTone c21bLeft) = g (segTone c21bRight) :=
  no_attribute_bridge_separates g c21b_tone_merges

theorem tone_bridge_partial :
    (segments or38Left = segments or38Right ∧ segTone or38Left ≠ segTone or38Right) ∧
      (segments c21bLeft = segments c21bRight ∧ segTone c21bLeft = segTone c21bRight) :=
  ⟨⟨or38_segments_merge, or38_tone_separates⟩,
   ⟨c21b_segments_merge, c21b_tone_merges⟩⟩

end Tone

end PhonologicalGrounding.QueryDiscovery
