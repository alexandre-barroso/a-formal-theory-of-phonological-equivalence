import Mathlib.Tactic

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace Retained

structure Feature where
  nuclear : Bool
  present : Bool
  atr : Option Bool
  quality : Option Nat
  high : Bool
  deriving Repr, DecidableEq, Inhabited

def ft : String → Feature
  | "∅" => ⟨false,false,none,none,false⟩
  | "a" => ⟨true,true,some false,some 0,false⟩
  | "ɜ" => ⟨true,true,some true,some 0,false⟩
  | "ɛ" => ⟨true,true,some false,some 1,false⟩
  | "e" => ⟨true,true,some true,some 1,false⟩
  | "ɪ" => ⟨true,true,some false,some 2,true⟩
  | "i" => ⟨true,true,some true,some 2,true⟩
  | "ɔ" => ⟨true,true,some false,some 3,false⟩
  | "o" => ⟨true,true,some true,some 3,false⟩
  | "ʊ" => ⟨true,true,some false,some 4,true⟩
  | "u" => ⟨true,true,some true,some 4,true⟩
  | "j" => ⟨false,true,none,some 2,false⟩
  | "w" => ⟨false,true,none,some 4,false⟩
  | _ => ⟨false,true,none,none,false⟩

def alphabet : List String := ["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]

structure Input where
  origin : List String
  words : List Nat
  focal : List Nat
  phrases : List Nat
  deriving Repr, DecidableEq

def n7 : Input := ⟨["a","tʃ","ɪ","j","e","l","i"],[0,0,0,1,1,1,1],[2,4],[0,0]⟩
def g37 : Input := ⟨["ɔ","tʃ","ʊ","s","ɛ","i","b","i","e"],[0,0,0,1,1,2,2,2,2],[2,4,5],[0,0,0]⟩
def coords (u : Input) (i : Nat) : List Nat :=
  (List.range u.focal.length).map fun k => i / 13^(u.focal.length-1-k) % 13
def expand (u : Input) (i : Nat) : List String :=
  u.origin.zipIdx.map fun (p,q) =>
    match u.focal.zipIdx.find? (fun z => z.1 == q) with
    | none => p
    | some (_,k) => alphabet[(coords u i)[k]!]!
def carrier (u : Input) : List Nat := List.range (13^u.focal.length)
def realize (u : Input) (i : Nat) : String :=
  String.join ((expand u i).filter (fun p => p != "∅"))
def fiber (u : Input) (output : String) : List Nat :=
  (carrier u).filter (fun i => realize u i == output)

def word (u : Input) (q : Nat) : Nat := u.words[q]!
def samePhrase (u : Input) (q r : Nat) : Bool :=
  u.phrases[word u q]! == u.phrases[word u r]!
def positions (u : Input) : List Nat := List.range u.origin.length
def nextLive (u : Input) (s : List String) (q : Nat) : Option Nat :=
  if (ft s[q]!).present then (positions u).find? (fun r => q < r && (ft s[r]!).present) else none
def prevLive (u : Input) (s : List String) (q : Nat) : Option Nat :=
  if (ft s[q]!).present then (positions u).reverse.find? (fun r => r < q && (ft s[r]!).present) else none
def source (u : Input) (s : List String) (q : Nat) : Option Nat :=
  (positions u).find? fun r => q < r && word u q < word u r &&
    samePhrase u q r && (ft s[r]!).nuclear

structure Reading where
  context : Bool
  defined : Bool
  good : Bool
  deriving Repr, DecidableEq, Inhabited

def read (u : Input) (s : List String) (k q : Nat) : Reading :=
  let f := ft s[q]!
  let r := ft u.origin[q]!
  let n := nextLive u s q
  let v := prevLive u s q
  match k with
  | 0 => ⟨true,true,f.present⟩
  | 1 => ⟨true,f.nuclear && r.nuclear,f.atr == r.atr⟩
  | 2 => ⟨true,f.present && f.quality.isSome && r.quality.isSome,f.quality == r.quality⟩
  | 3 => ⟨true,f.present,f.nuclear == r.nuclear⟩
  | 4 => ⟨f.nuclear && !((positions u).any (fun j => q < j && word u q == word u j && (ft s[j]!).nuclear)) &&
      (source u s q).any (fun j => (ft s[j]!).atr == some true), f.nuclear,f.atr == some true⟩
  | 5 => ⟨f.nuclear && !f.high && n.any (fun j => word u j == word u q + 1 && samePhrase u q j &&
      (ft s[j]!).nuclear && !(ft s[j]!).high),true,!f.present || n.any (fun j => s[q]! == s[j]!)⟩
  | 6 => ⟨f.nuclear && f.high && [v,n].any (fun o => o.any (fun j =>
      (word u j == word u q + 1 || word u q == word u j + 1) && samePhrase u q j &&
      (ft s[j]!).nuclear && !(ft s[j]!).high)),true,!f.nuclear⟩
  | 7 => ⟨f.nuclear && f.high && v.any (fun j => word u j + 1 == word u q && samePhrase u q j &&
      (ft s[j]!).nuclear && (ft s[j]!).high),true,!f.present⟩
  | 8 => ⟨r.nuclear && (q == 0 || word u (q-1) != word u q),f.present && f.quality.isSome,
      f.quality == r.quality && (!f.nuclear || f.atr == r.atr)⟩
  | _ => ⟨false,false,true⟩

end Retained
