import PhonologicalOpacity.Gua.Deletion.Bindings
import Lean
open Retained Deletion Lean
namespace DeletionExport
def jl (xs : List Json) : Json := Json.arr xs.toArray
def records (u : Input) : List Json := (carrier u).map fun i => Id.run do
  let s := expand u i
  let all := (List.range 9).map fun k => (positions u).map fun q => read u s k q
  let lex := (List.range u.phrases.length).map fun w =>
    String.join ((s.zipIdx.filter (fun (p,q) => word u q == w && p != "∅")).map Prod.fst)
  return jl [toJson i,toJson (coords u i),toJson s,toJson (realize u i),toJson lex,
    toJson (all.map fun r => r.map Reading.context),toJson (all.map fun r => r.map Reading.defined),
    toJson (all.map fun r => r.map Reading.good),
    toJson ((positions u).map fun q => match source u s q with | none => (-1:Int) | some n => n),
    toJson (counts u i),toJson ([0,1,2].map fun pol => score u pol i)]
def caseJson (name : String) (u : Retained.Input) (start : Nat) (out : String) : Json :=
  Json.mkObj [("id",toJson name),("start",toJson start),("fiber",toJson (fiber u out)),("records",jl (records u))]
#eval do
  let result := Json.mkObj [("cases",jl [caseJson "OR38" or38 1254 "atʃɔsiku",
    caseJson "C21b" c21 122 "wʊsʊsɛ",caseJson "C23UE" c23 120 "wʊswɛbɪ"])]
  IO.FS.createDirAll "../../results/opacity"
  IO.FS.writeFile ("../../results/opacity/" ++ "lean_deletion.json") (result.compress++"\n")
  IO.println "PASS complete Lean reader export of the three deletion products"
end DeletionExport
