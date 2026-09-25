                          
import PhonologicalCalculus.Application.LithuanianEncodings
import Mathlib.Data.List.Permutation
import Mathlib.Data.List.Lex

namespace LithuanianComparison

open LithuanianEncodings

set_option maxHeartbeats 8000000
set_option maxRecDepth 10000

def candidates : List Candidate :=
  [false,true].flatMap fun x => [false,true].flatMap fun y => [false,true].map fun z => (x,y,z)

def counts (i : Fin 3) (s : Candidate) : Fin 5 → Nat :=
  fun k => if k=0 then (if s.1 then 1 else 0)
    else if k=1 then (if s.2.1 = referenceVoice i then 0 else 1)
    else if k=2 then (if s.2.2 then 1 else 0)
    else if k=3 then (if !s.2.2 && (s.1 != s.2.1) then 1 else 0)
    else (if !s.2.2 && samePlace i && (s.1 == s.2.1) then 1 else 0)

def lexScore (ranking : List (Fin 5)) (i : Fin 3) (s : Candidate) : List Nat :=
  ranking.map (counts i s)

def wins (ranking : List (Fin 5)) (i : Fin 3) (t : Candidate) : Bool :=
  candidates.all fun s => decide (s=t) ||
    decide (List.Lex (· < ·) (lexScore ranking i t) (lexScore ranking i s))

def basic (ranking : List (Fin 5)) : Bool :=
  wins ranking 0 (true,true,false) && wins ranking 2 (false,false,true)

def rankings : List (List (Fin 5)) := ([0,1,2,3,4] : List (Fin 5)).permutations'

theorem candidates_complete (s : Candidate) : s ∈ candidates := by
  obtain ⟨x,y,z⟩ := s
  cases x <;> cases y <;> cases z <;> decide

theorem ranking_count : rankings.length = 120 := by decide +kernel

theorem rankings_complete (ranking : List (Fin 5))
    (h : ranking.Perm [0,1,2,3,4]) : ranking ∈ rankings := by
  exact List.mem_permutations'.mpr h

theorem basic_count : (rankings.filter basic).length = 8 := by decide +kernel

theorem table_transfer : ∀ ranking ∈ rankings, basic ranking = true →
    wins ranking 1 (false,true,true) = true := by decide +kernel

theorem native_ranked_transfer (ranking : List (Fin 5))
    (h : ranking.Perm [0,1,2,3,4]) (hb : basic ranking = true) :
    wins ranking 1 (false,true,true) = true :=
  table_transfer ranking (rankings_complete ranking h) hb

theorem wins_semantics (ranking : List (Fin 5)) (i : Fin 3) (t : Candidate) :
    wins ranking i t = true ↔ ∀ s : Candidate, s ≠ t →
      List.Lex (· < ·) (lexScore ranking i t) (lexScore ranking i s) := by
  simp only [wins,List.all_eq_true,Bool.or_eq_true,decide_eq_true_eq]
  constructor
  · intro h s hs
    exact (h s (candidates_complete s)).resolve_left hs
  · intro h s _
    by_cases hs : s=t
    · exact Or.inl hs
    · exact Or.inr (h s hs)

def WinsCore (ma mn : Mode) (i : Fin 3) (c r d a n l : ℝ) (t : Candidate) : Prop :=
  ∀ x y z : Bool, (x,y,z) ≠ t → score ma mn i c r d a n l t < score ma mn i c r d a n l (x,y,z)

def BasicCore (ma mn : Mode) (c r d a n l : ℝ) : Prop :=
  WinsCore ma mn 0 c r d a n l (true,true,false) ∧
  WinsCore ma mn 2 c r d a n l (false,false,true)

theorem core_retained_geminate :
    BasicCore .relational .relational 1 8 2 16 3 (1/8) ∧
    WinsCore .relational .relational 1 1 8 2 16 3 (1/8) (true,true,false) := by
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have h10 : (1 : Fin 3) ≠ 0 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have hro : Mode.relational ≠ .origin := by decide
  have hre : Mode.relational ≠ .existence := by decide
  norm_num [BasicCore,WinsCore,Bool.forall_bool,score,contribution,pressure,
    context,active,resolves,referenceVoice,samePlace,h02,h10,h12,h20,hro,hre]

theorem core_current_hg_counterexample :
    BasicCore .relational .relational 1 8 2 (3/2) 3 1 ∧
    WinsCore .relational .relational 1 1 8 2 (3/2) 3 1 (false,true,false) := by
  have h02 : (0 : Fin 3) ≠ 2 := by decide
  have h10 : (1 : Fin 3) ≠ 0 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have hro : Mode.relational ≠ .origin := by decide
  have hre : Mode.relational ≠ .existence := by decide
  norm_num [BasicCore,WinsCore,Bool.forall_bool,score,contribution,pressure,
    context,active,resolves,referenceVoice,samePlace,h02,h10,h12,h20,hro,hre]

theorem current_hg_score (i : Fin 3) (s : Candidate) (c r d a n : ℝ) :
    score .relational .relational i c r d a n 1 s =
      counts i s 0*c + counts i s 1*r + counts i s 2*d + counts i s 3*a + counts i s 4*n := by
  obtain ⟨x,y,z⟩ := s
  fin_cases i <;> cases x <;> cases y <;> cases z <;>
    simp [score,contribution,pressure,context,active,resolves,referenceVoice,samePlace,counts]

end LithuanianComparison
