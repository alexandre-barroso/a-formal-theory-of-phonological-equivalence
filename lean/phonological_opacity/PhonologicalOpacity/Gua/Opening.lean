                              
import PhonologicalOpacity.Gua.Core

namespace Retained

def openingParts (i : Nat) : List Nat :=
  let cs := counts g34a i
  let terms := (cs.zip weights).map fun (r,w) => w * (8 * r[2]! + r[3]!)
  [terms[0]!+terms[1]!+terms[2]!+terms[3]!+terms[8]!, terms[4]!, terms[5]!, score8 g34a 1 i]

theorem opening_reference : expand g34a 566 = g34a.origin ∧
    openingParts 566 = [0,32,64,96] := by decide +kernel

theorem opening_observed : realize g34a 774 = "ahetɔɔkpʊkɔ" ∧
    openingParts 774 = [24,0,0,24] := by decide +kernel

theorem opening_rival : realize g34a 605 = "ahɛtɔɔkpʊkɔ" ∧
    openingParts 605 = [16,32,0,48] := by decide +kernel

theorem opening_current_markedness :
    ([4,5,6,7].map fun k => (((counts g34a 774)[k]!)[4]!, ((counts g34a 774)[k]!)[5]!)) =
    ([4,5,6,7].map fun k => (((counts g34a 605)[k]!)[4]!, ((counts g34a 605)[k]!)[5]!)) := by
  decide +kernel

end Retained
