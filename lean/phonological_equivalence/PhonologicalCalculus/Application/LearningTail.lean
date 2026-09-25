                         
                          
import PhonologicalCalculus.Application.LearningExact

set_option maxHeartbeats 8000000
namespace PhonologicalCalculus.LearningTail
open LearningExact
inductive Seg where
  | other : Nat → Seg
  | obs : Nat → Bool → Seg
  deriving DecidableEq, BEq
abbrev Cell := Option Seg × Option Seg

def nextInitial : List Cell → Option Seg
  | [] => none
  | (none, _) :: t => nextInitial t
  | (some s, _) :: _ => some s

def nextReference : List Cell → Option Seg
  | [] => none
  | (none, _) :: t => nextReference t
  | (some _, s) :: _ => s

def nextCurrent : List Cell → Option Seg
  | [] => none
  | (_, none) :: t => nextCurrent t
  | (_, some s) :: _ => some s

def partner (static : Bool) (t : List Cell) : Option Seg :=
  if static then nextReference t else nextCurrent t

def agreeBad : Option Seg → Option Seg → Bool
  | some (.obs _ x), some (.obs _ y) => x != y
  | _, _ => false

def nogemBad : Option Seg → Option Seg → Bool
  | some (.obs p x), some (.obs q y) => (p == q) && (x == y)
  | _, _ => false

def localMarked (w : W) (h : H) (c : Cell) (t : List Cell) : ℝ :=
  (if agreeBad c.1 (nextInitial t) then w.a else w.anew) *
    bit (agreeBad c.2 (partner h.1 t)) +
  (if nogemBad c.1 (nextInitial t) then w.n else w.nnew) *
    bit (nogemBad c.2 (partner h.2 t))

def marked (w : W) (h : H) : List Cell → ℝ
  | [] => 0
  | c :: t => localMarked w h c t + marked w h t

def identityBad : Option Seg → Option Seg → Bool
  | some (.obs _ x), some (.obs _ y) => x != y
  | _, _ => false

def localFaith (w : W) (idw maxw : ℝ) (c : Cell) : ℝ :=
  idw * bit (identityBad c.1 c.2) +
  w.dep * bit (c.1.isNone && c.2.isSome) +
  maxw * bit (c.1.isSome && c.2.isNone)

def faith (w : W) (idw maxw : ℝ) : List Cell → ℝ
  | [] => 0
  | c :: t => localFaith w idw maxw c + faith w idw maxw t

def sameCells (t : List Seg) : List Cell := t.map fun s => (some s, some s)

def prefixCells (p q : Nat) (v1 v2 : Bool) (c : C) : List Cell :=
  [(some (.other 0), some (.other 0)),
   (some (.obs p v1), some (.obs p c.1)),
   (none, if c.2.2 then some (.other 1) else none),
   (some (.obs q v2), some (.obs q c.2.1))]

def fullCost (w : W) (maxw : ℝ) (p q : Nat) (v1 v2 : Bool)
    (h : H) (c : C) (tail : List Seg) : ℝ :=
  let cells := prefixCells p q v1 v2 c ++ sameCells tail
  faith w w.p maxw (cells.take 2) + faith w w.s maxw (cells.drop 2) + marked w h cells

def AllowedTail : List Seg → Prop
  | [] => True
  | .other _ :: _ => True
  | _ => False

theorem faithful_tail (w : W) (idw maxw : ℝ) (t : List Seg) :
    faith w idw maxw (sameCells t) = 0 := by
  induction t with
  | nil => simp [faith, sameCells]
  | cons s t ih =>
    cases s <;> simp_all [sameCells, faith, localFaith, identityBad, bit]

theorem tail_cost_decomposition (w : W) (maxw : ℝ) (p q : Nat)
    (v1 v2 : Bool) (h : H) (c : C) (tail : List Seg) (ht : AllowedTail tail) :
    fullCost w maxw p q v1 v2 h c tail =
      score w v1 v2 (p == q) h c + marked w h (sameCells tail) := by
  rcases h with ⟨ha, hn⟩
  rcases c with ⟨x, y, z⟩
  have hf := faithful_tail w w.s maxw tail
  cases tail with
  | nil =>
    by_cases hp : p = q <;>
      cases v1 <;> cases v2 <;> cases ha <;> cases hn <;>
      cases x <;> cases y <;> cases z <;>
      simp [fullCost, prefixCells, sameCells, faith, localFaith, identityBad, List.take, List.drop,
        marked, localMarked, agreeBad, nogemBad, partner, nextInitial,
        nextReference, nextCurrent, score, bit, hp] <;> ring
  | cons s t =>
    cases s with
    | obs r b => simp [AllowedTail] at ht
    | other k =>
      by_cases hp : p = q <;>
        cases v1 <;> cases v2 <;> cases ha <;> cases hn <;>
        cases x <;> cases y <;> cases z <;>
        simp_all [fullCost, prefixCells, sameCells, faith, localFaith, identityBad, List.take, List.drop,
          marked, localMarked, agreeBad, nogemBad, partner, nextInitial,
          nextReference, nextCurrent, score, bit] <;> ring

def surface (p q : Nat) (c : C) (tail : List Seg) : List Seg :=
  [.other 0, .obs p c.1] ++
  (if c.2.2 then [.other 1] else []) ++ [.obs q c.2.1] ++ tail

theorem surface_correspondence (p q : Nat) (v1 v2 : Bool) (c : C) (tail : List Seg) :
    ((prefixCells p q v1 v2 c ++ sameCells tail).filterMap Prod.snd) =
      surface p q c tail := by
  rcases c with ⟨x,y,z⟩
  cases z <;> simp [prefixCells, sameCells, surface, List.filterMap_map,
    List.append_assoc]

theorem surface_injective (p q : Nat) (tail : List Seg) :
    Function.Injective (fun c : C => surface p q c tail) := by
  intro c d he
  rcases c with ⟨x,y,z⟩
  rcases d with ⟨a,b,k⟩
  simp only [surface, List.append_assoc, List.append_cancel_right_eq] at he
  cases z <;> cases k <;> simp_all

theorem full_minimizers (w : W) (hr : region w) (maxw : ℝ) (p q : Nat)
    (v1 v2 : Bool) (h : H) (c : C) (tail : List Seg) (ht : AllowedTail tail) :
    (∀ d, fullCost w maxw p q v1 v2 h c tail ≤
          fullCost w maxw p q v1 v2 h d tail) ↔
      predicted v1 v2 (p == q) h c = true := by
  simp_rw [tail_cost_decomposition w maxw p q v1 v2 h _ tail ht,
    add_le_add_iff_right]
  exact exact_minimizers w hr v1 v2 (p == q) h c

def observedSet (p q : Nat) (v1 v2 : Bool) (h : H) (tail : List Seg) : Finset (List Seg) :=
  (outputSet v1 v2 (p == q) h).image (fun c => surface p q c tail)

theorem observedSet_exact (w : W) (hr : region w) (maxw : ℝ) (p q : Nat)
    (v1 v2 : Bool) (h : H) (tail : List Seg) (ht : AllowedTail tail) (o : List Seg) :
    o ∈ observedSet p q v1 v2 h tail ↔
      ∃ c, (∀ d, fullCost w maxw p q v1 v2 h c tail ≤
                   fullCost w maxw p q v1 v2 h d tail) ∧ surface p q c tail = o := by
  simp only [full_minimizers w hr maxw p q v1 v2 h _ tail ht]
  simp only [observedSet, Finset.mem_image, outputSet, Finset.mem_filter,
    Finset.mem_univ, true_and]

theorem two_surface_probes_separate (p : Nat) (tail : List Seg) :
    Function.Injective (fun h : H =>
      (observedSet p p false false h tail, observedSet p p false true h tail)) := by
  intro h k he
  apply two_probes_separate
  apply Prod.ext
  · have hh := congrArg Prod.fst he
    simp only [observedSet, beq_self_eq_true] at hh
    exact Finset.image_injective (surface_injective p p tail) hh
  · have hh := congrArg Prod.snd he
    simp only [observedSet, beq_self_eq_true] at hh
    exact Finset.image_injective (surface_injective p p tail) hh

theorem no_single_surface_probe (p q : Nat) (v1 v2 : Bool) (tail : List Seg) :
    ¬ Function.Injective (fun h : H => observedSet p q v1 v2 h tail) := by
  intro hi
  apply no_single_probe v1 v2 (p == q)
  intro h k he
  apply hi
  exact congrArg (Finset.image (fun c => surface p q c tail)) he

#print axioms tail_cost_decomposition
#print axioms surface_correspondence
#print axioms surface_injective
#print axioms full_minimizers
#print axioms observedSet_exact
#print axioms two_surface_probes_separate
#print axioms no_single_surface_probe
end PhonologicalCalculus.LearningTail
