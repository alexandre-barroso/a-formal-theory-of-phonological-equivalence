                     
                   
import Mathlib.Tactic

namespace RuleReaders

abbrev K := Option Bool

def knot : K → K := Option.map Bool.not
def kand : K → K → K
  | some false, _ => some false
  | _, some false => some false
  | some true, some true => some true
  | _, _ => none
def kor : K → K → K
  | some true, _ => some true
  | _, some true => some true
  | some false, some false => some false
  | _, _ => none

def classAtom (resolves feature : Bool) : K :=
  kand (some resolves) (if resolves then some feature else none)

theorem guarded_class_total (r f : Bool) : classAtom r f = some (r && f) := by
  cases r <;> cases f <;> rfl

def conjunction : List K → K
  | [] => some true
  | x :: xs => kand x (conjunction xs)

theorem conjunction_total (xs : List Bool) : conjunction (xs.map some) = some xs.and := by
  induction xs with
  | nil => rfl
  | cons a xs ih => cases a <;> cases h : xs.and <;> simp [conjunction,ih,kand,h]

inductive Mode | discharge | retain | ltr | rtl deriving DecidableEq,Fintype

def carried (m : Mode) (l r : Bool) : Bool := match m with
  | .discharge => l && r
  | .retain => true
  | .ltr => l
  | .rtl => r

def consequence (m : Mode) (l r : Bool) (repair : K) : K := match m with
  | .retain => repair
  | _ => kor (knot (some (carried m l r))) repair

def pressure (v : K) : Bool := v == some false

theorem surviving_pressure (m : Mode) (l r repaired : Bool) :
    pressure (consequence m l r (some repaired)) = ((!repaired) && carried m l r) := by
  cases m <;> cases l <;> cases r <;> cases repaired <;> rfl

theorem deleted_pressure (m : Mode) (l r deletionRepair : Bool) :
    pressure (consequence m l r (if deletionRepair then some true else none)) = false := by
  cases m <;> cases l <;> cases r <;> cases deletionRepair <;> rfl

theorem activation_formula (m : Mode) (target l r repaired : Bool) :
    (target && l && r && pressure (consequence m l r (some repaired))) =
      (target && l && r && !repaired) := by
  rw [surviving_pressure]
  cases m <;> cases target <;> cases l <;> cases r <;> cases repaired <;> rfl

def contribution (w lam : ℝ) (a c p : Bool) : ℝ :=
  w * ((if p && a then 1 else 0) + lam * (if p && !a && c then 1 else 0))

theorem contribution_local (w lam : ℝ) (a c p : Bool) :
    contribution w lam a c p =
      w * (if p then 1 else 0) * ((if a then 1 else 0) + lam * (if !a && c then 1 else 0)) := by
  cases a <;> cases c <;> cases p <;> simp [contribution]

theorem deleted_contribution (w lam : ℝ) (a c : Bool) : contribution w lam a c false = 0 := by
  simp [contribution]

end RuleReaders
