import PhonologicalOpacity.Lithuanian.Proofs
import Lean
namespace Lithuanian
open Lean
def jsonNums (xs : List Nat) : Json := toJson xs
def jsonRow (u j : Nat) : Json := Json.mkObj [
  ("j",toJson j),("bits",jsonNums (bits j)),("morph",toJson (morph u j)),
  ("observation",toJson (observe u j)),("ordinary",jsonNums (mark u j)),
  ("tabulated",jsonNums (tabulated u j)),
  ("tabulated_agrees",toJson (if (tabulated u j)[4]! = (mark u j)[0]! then (1:Nat) else 0)),
  ("configs",Json.arr (((List.range 6).map fun cfg => Json.mkObj [
    ("name",toJson (configName cfg)),("initial",toJson (readers u (configMode cfg) (2*sourceVoice u))),
    ("current",toJson (readers u (configMode cfg) j)),("coefficients",jsonNums (coeff u (configMode cfg) j)),
    ("score8",toJson (score8 u cfg j))]).toArray))]
def jsonSummary (u cfg : Nat) : Json :=
  let ms := minima u cfg
  Json.mkObj [("name",toJson (configName cfg)),("minimum8",toJson (score8 u cfg ms[0]!)),
    ("minima",jsonNums ms),("outputs",toJson (ms.map (observe u)))]
def jsonInput (u : Nat) : Json := Json.mkObj [
  ("id",toJson ((["PG","PB","TT"] : List String)[u]!)),
  ("input",toJson (morph u (2*sourceVoice u))),("input_index",toJson (2*sourceVoice u)),
  ("h",toJson (if homorganic u then (1:Nat) else 0)),("target",toJson (target u)),
  ("correct_fiber",jsonNums (fiber u (target u))),
  ("rows",Json.arr (((List.range 8).map (jsonRow u)).toArray)),
  ("fibers",Json.arr (((List.range 8).map fun j => Json.mkObj [
    ("observation",toJson (observe u j)),("members",jsonNums (fiber u (observe u j)))]).toArray)),
  ("summaries",Json.arr (((List.range 6).map (jsonSummary u)).toArray))]
def exportBody : Json := Json.arr (((List.range 3).map jsonInput).toArray)
#eval do
  IO.FS.createDirAll "../../results/opacity"
  IO.FS.writeFile ("../../results/opacity/" ++ "lean_lithuanian.json") (exportBody.pretty ++ "\n")
  IO.println "24 states, 144 scores, full fields and all minima exported from actual Lean definitions."
end Lithuanian
