                      
import PhonologicalRequirements.Kleene

namespace PhonologicalRequirements

variable {σ V : Type}

inductive Term (σ V : Type) where
  | const  (v : K)
  | exists_ (s : σ)
  | acc    (s : σ) (p : V → K)
  | neg    (a : Term σ V)
  | conj   (a b : Term σ V)
  | disj   (a b : Term σ V)

abbrev Assign (σ V : Type) := σ → Option V

def Term.eval [DecidableEq σ] : Term σ V → Assign σ V → K
  | .const v,    _ => v
  | .exists_ s,  a => match a s with | some _ => K.tt | none => K.ff
  | .acc s p,    a => match a s with | some v => p v | none => K.uu
  | .neg t,      a => K.not (t.eval a)
  | .conj t u,   a => K.and (t.eval a) (u.eval a)
  | .disj t u,   a => K.or  (t.eval a) (u.eval a)

def Term.mentions [DecidableEq σ] : Term σ V → σ → Prop
  | .const _,   _ => False
  | .exists_ s, x => s = x
  | .acc s _,   x => s = x
  | .neg t,     x => t.mentions x
  | .conj t u,  x => t.mentions x ∨ u.mentions x
  | .disj t u,  x => t.mentions x ∨ u.mentions x

def Term.accessFree [DecidableEq σ] (s : σ) : Term σ V → Prop
  | .const _   => True
  | .exists_ _ => True
  | .acc x _   => x ≠ s
  | .neg t     => t.accessFree s
  | .conj t u  => t.accessFree s ∧ u.accessFree s
  | .disj t u  => t.accessFree s ∧ u.accessFree s

structure Readers where
  ctx : Bool
  def_ : Bool
  good : Bool
deriving DecidableEq, Repr

def readersOf [DecidableEq σ] (cons act : Term σ V) (a : Assign σ V) : Readers :=
  { ctx  := K.collapse (act.eval a)
  , def_ := (cons.eval a) ≠ K.uu
  , good := (cons.eval a) = K.tt }

def Readers.pressure (r : Readers) : Nat := if r.def_ && !r.good then 1 else 0
def Readers.marked  (r : Readers) : Nat := if r.ctx && r.def_ && !r.good then 1 else 0

end PhonologicalRequirements
