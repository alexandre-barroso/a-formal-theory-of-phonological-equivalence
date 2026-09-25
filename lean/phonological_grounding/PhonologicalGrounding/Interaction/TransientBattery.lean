                    
                
import Mathlib.Data.List.Forall2

namespace TransientBattery

inductive Seg where | x | y | c | v | i | absent
  deriving DecidableEq, Repr
open Seg

def choices : Seg → List Seg
  | x => [x,y]
  | v => [v,absent]
  | a => [a]

def generate : List Seg → List (List Seg)
  | [] => [[]]
  | a::as => (choices a).flatMap fun b => (generate as).map (b::·)

def nextIdx (s : List Seg) (j : Nat) : Option Nat :=
  (List.range s.length).find? fun k => j < k && s[k]?.getD absent != absent

def segmentAt (s : List Seg) (j : Nat) : Seg := s[j]?.getD absent
def next (s : List Seg) (j : Nat) : Seg := (nextIdx s j).map (segmentAt s) |>.getD absent
def act (s : List Seg) (j : Nat) (trig : Seg) : Bool := segmentAt s j == x && next s j == trig

def term (a cur pressure : Bool) : Nat :=
  if pressure then (if a then 4 else if cur then 1 else 0) else 0

def score (existence : Bool) (u s : List Seg) : Nat :=
  ((List.range u.length).map fun j =>
    (if segmentAt u j == x && segmentAt s j == y then 8 else 0) +
    (if segmentAt u j == v && segmentAt s j == absent then 4 else 0) +
    4 * term (act u j i) (act s j i) (segmentAt s j != y) +
    4 * term (act u j c && (!existence || nextIdx u j == nextIdx s j))
      (act s j c) (!((!existence || (nextIdx s j).isSome) && segmentAt s j == y)) +
    (if segmentAt u j == v && next u j == c && segmentAt s j != absent then 12 else 0)).sum

def surface (s : List Seg) := s.filter (· != absent)
def winners (e : Bool) (u : List Seg) : List (List Seg) :=
  (generate u).filter fun s => (generate u).all fun t => score e u s ≤ score e u t

def battery : List (List Seg × List Seg) :=
  [([x,c],[y,c]),([x,i],[y,i]),([x,v],[x,v]),([x,v,c],[x,c]),
   ([x],[x]),([c],[c]),([v],[v]),([i],[i])]

theorem complete_diagnostics : ∀ e ∈ [false,true],
    ∀ p ∈ battery, (winners e p.1).map surface = [p.2] := by decide +kernel

theorem candidate_count : (battery.map fun p => (generate p.1).length).sum = 18 := by decide +kernel

theorem generated_complete (u : List Seg) (s : List Seg) :
    s ∈ generate u ↔ List.Forall₂ (fun a b => b ∈ choices a) u s := by
  induction u generalizing s with
  | nil => cases s <;> simp [generate]
  | cons a as ih =>
    cases s with
    | nil => simp [generate]
    | cons b bs => simp [generate,ih]

end TransientBattery
