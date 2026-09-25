import Mathlib.Data.Real.Basic
import Mathlib.Tactic
namespace Lithuanian
set_option maxRecDepth 10000
set_option maxHeartbeats 0
def bits (j : Nat) : List Nat := [j/4,(j/2)%2,j%2]
def sourceVoice (u : Nat) : Nat := if u=2 then 0 else 1
def homorganic (u : Nat) : Bool := u != 0
def mark (u j : Nat) : List Nat :=
  let b := bits j
  [if b[2]! = 0 ∧ b[0]! ≠ b[1]! then 1 else 0,
   if b[2]! = 0 ∧ homorganic u ∧ b[0]! = b[1]! then 1 else 0]
def reader (u mode j k : Nat) : List Nat :=
  let b := bits j
  let C : Nat := if b[2]! = 0 then 1 else 0
  let D : Nat := if (mode / 2^k)%2 = 1 ∨ b[2]! = 0 then 1 else 0
  let G : Nat := if k=0 then (if b[0]! = b[1]! then 1 else 0)
    else (if homorganic u ∧ b[0]! = b[1]! then 0 else 1)
  let p := D*(1-G)
  [C,D,G,p,C*p]
def readers (u mode j : Nat) : List (List Nat) := [reader u mode j 0,reader u mode j 1]
def coeff (u mode j : Nat) : List Nat :=
  let b := bits j
  let old := mark u (2*sourceVoice u)
  let A := reader u mode j 0
  let N := reader u mode j 1
  [b[0]!,if b[1]! ≠ sourceVoice u then 1 else 0,b[2]!,
   old[0]!*A[3]!, (1-old[0]!)*A[4]!,old[1]!*N[3]!, (1-old[1]!)*N[4]!]
def pPhone (u x : Nat) : String := if u=2 then (if x=0 then "t" else "d") else (if x=0 then "p" else "b")
def sPhone (u y : Nat) : String := if u=0 then (if y=0 then "k" else "g") else pPhone u y
def tail (u : Nat) : String := if u=0 then "auti" else if u=1 then "erti" else "aiki:ti"
def morph (u j : Nat) : String :=
  let b := bits j
  "a" ++ pPhone u b[0]! ++ (if b[2]! = 1 then "i" else "") ++ "-" ++ sPhone u b[1]! ++ tail u
def observe (u j : Nat) : String :=
  let b := bits j
  "a" ++ pPhone u b[0]! ++ (if b[2]! = 1 then "i" else "") ++ sPhone u b[1]! ++ tail u
def target (u : Nat) : String := if u=0 then "abgauti" else if u=1 then "apiberti" else "atitaiki:ti"
def goal (u : Nat) : Fin 8 := if u=0 then 6 else if u=1 then 3 else 1
def tabulated (u j : Nat) : List Nat :=
  let b := bits j
  let C : Nat := if b[2]! = 0 then 1 else 0
  let G : Nat := if b[0]! = sourceVoice u then 1 else 0
  [C,1,G,1-G,C*(1-G)]
noncomputable def pressure (u mode : Nat) (c r d a n lam : ℝ) (j : Fin 8) : ℝ :=
  let q := coeff u mode j.val
  c*q[0]! + r*q[1]! + d*q[2]! + a*(q[3]!+lam*q[4]!) + n*(q[5]!+lam*q[6]!)
noncomputable def ordinary (u : Nat) (c r d a n : ℝ) (j : Fin 8) : ℝ :=
  let q := coeff u 0 j.val
  let m := mark u j.val
  c*q[0]! + r*q[1]! + d*q[2]! + a*m[0]! + n*m[1]!
def Strict (P : Fin 8 → ℝ) (g : Fin 8) : Prop := ∀ j, j≠g → P g < P j
def Joint (mode : Nat) (c r d a n lam : ℝ) : Prop :=
  Strict (pressure 0 mode c r d a n lam) 6 ∧
  Strict (pressure 1 mode c r d a n lam) 3 ∧
  Strict (pressure 2 mode c r d a n lam) 1
def Region (c r d a n lam : ℝ) : Prop :=
  0<c ∧ c<d ∧ c<r ∧ d<a ∧ d<n ∧ d<c+lam*n ∧ d<c+lam*a
def OrdinaryRegion (c r d a n : ℝ) : Prop := 0<c ∧ c<d ∧ c<r ∧ d<a ∧ d<n
def Exclusive (u : Nat) (P : Fin 8 → ℝ) : Prop :=
  (∃ j, ∀ t, P j ≤ P t) ∧ ∀ j, (∀ t, P j ≤ P t) → observe u j.val = target u
def configMode (cfg : Nat) : Nat := if cfg=2 then 1 else if cfg=3 then 2 else if cfg=4 then 3 else 0
def configName (cfg : Nat) : String := (["O","RR","SR","RS","SS","RR0"] : List String)[cfg]!
def score8 (u cfg j : Nat) : Nat :=
  let q := coeff u (configMode cfg) j
  let m := mark u j
  8*q[0]!+32*q[1]!+16*q[2]! +
    if cfg=0 then 128*(m[0]!+m[1]!) else
      128*(q[3]!+q[5]!)+(if cfg=5 then 0 else 16)*(q[4]!+q[6]!)
def goals (u cfg : Nat) : List Nat :=
  if u=0 then [6] else if u=1 then (if cfg=2 ∨ cfg=4 then [6,7] else if cfg=5 then [6] else [3])
  else (if cfg=3 ∨ cfg=4 then [4,5] else if cfg=5 then [4] else [1])
def minima (u cfg : Nat) : List Nat :=
  (List.range 8).filter fun j => (List.range 8).all fun t => score8 u cfg j ≤ score8 u cfg t
def fiber (u : Nat) (s : String) : List Nat := (List.range 8).filter fun j => observe u j == s
theorem all_factorizations : ∀ u : Fin 3, ∀ m : Fin 4, ∀ j : Fin 8,
    [(reader u.val m.val j.val 0)[4]!, (reader u.val m.val j.val 1)[4]!] = mark u.val j.val := by decide
theorem full_fibers : ∀ u : Fin 3, ∀ j : Fin 8, fiber u.val (observe u.val j.val) = [j.val] := by decide
theorem target_binding : ∀ u : Fin 3, fiber u.val (target u.val) = [(goal u.val).val] := by decide
theorem tabulated_mismatches :
  (tabulated 0 0)[4]! = 1 ∧ (mark 0 0)[0]! = 0 ∧ (tabulated 0 4)[4]! = 0 ∧ (mark 0 4)[0]! = 1 ∧
  (tabulated 2 2)[4]! = 0 ∧ (mark 2 2)[0]! = 1 ∧ (tabulated 2 6)[4]! = 1 ∧ (mark 2 6)[0]! = 0 := by decide
theorem all_minima : ∀ u : Fin 3, ∀ cfg : Fin 6, ∀ j : Fin 8,
    (∀ t : Fin 8, score8 u.val cfg.val j.val ≤ score8 u.val cfg.val t.val) ↔ j.val ∈ goals u.val cfg.val := by decide
theorem minima_binding : ∀ u : Fin 3, ∀ cfg : Fin 6, minima u.val cfg.val = goals u.val cfg.val := by decide
#print axioms all_factorizations
#print axioms full_fibers
#print axioms target_binding
#print axioms tabulated_mismatches
#print axioms all_minima
#print axioms minima_binding
end Lithuanian
