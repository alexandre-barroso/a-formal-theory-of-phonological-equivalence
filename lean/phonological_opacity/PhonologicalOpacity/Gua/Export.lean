import PhonologicalOpacity.Gua.Core
import Lean
open Retained Lean

def jlist (xs : List Json) : Json := Json.arr xs.toArray
def jnat (n : Nat) : Json := toJson n
def jstr (s : String) : Json := toJson s
def records (u : Input) : List Json := (carrier u).map fun i => Id.run do
  let s := expand u i
  let all := (List.range 9).map fun k => (positions u).map fun q => read u s k q
  let cs := counts u i
  let es := (coords u i).zipIdx.flatMap fun (old,k) =>
    ((List.range 13).filter (fun v => v != old)).map fun v =>
      i - old*13^(u.focal.length-1-k) + v*13^(u.focal.length-1-k)
  let lex := (List.range u.phrases.length).map fun w =>
    String.join ((s.zipIdx.filter (fun (p,q) => word u q == w && p != "∅")).map Prod.fst)
  return jlist [jnat i,jlist ((coords u i).map jnat),jlist (s.map jstr),jstr (realize u i),
    jlist (lex.map jstr), jlist (all.map fun r => jlist (r.map fun b => toJson b.context)),
    jlist (all.map fun r => jlist (r.map fun b => toJson b.defined)),
    jlist (all.map fun r => jlist (r.map fun b => toJson b.good)),
    jlist ((positions u).map fun q => toJson (match source u s q with | none => (-1:Int) | some n => n)),
    toJson cs,toJson ([0,1,2].map fun mode => score8 u mode i),jlist (es.map jnat)]

#eval do
  let result := Json.mkObj [("cases",jlist [Json.mkObj [("id",jstr "G34a"),("start",jnat 566),("fiber",toJson (fiber g34a "ahetɔɔkpʊkɔ")),("records",jlist (records g34a))],
    Json.mkObj [("id",jstr "G34b"),("start",jnat 892),("fiber",toJson (fiber g34b "afɪsoohili")),("records",jlist (records g34b))],
    Json.mkObj [("id",jstr "N7"),("start",jnat 69),("fiber",toJson (fiber n7 "atʃijeli")),("records",jlist (records n7))],
    Json.mkObj [("id",jstr "G37c"),("start",jnat 1566),("fiber",toJson (fiber g37 "ɔtʃʊsejbie")),("records",jlist (records g37))],
    Json.mkObj [("id",jstr "C24ei"),("start",jnat 58),("fiber",toJson (fiber c24 "kpejsi")),("records",jlist (records c24))]])]
  IO.FS.createDirAll "../../results/opacity"
  IO.FS.writeFile ("../../results/opacity/" ++ "lean_selection.json") (result.compress ++ "\n")
  IO.println "PASS complete Lean reader export of the five selection products"
