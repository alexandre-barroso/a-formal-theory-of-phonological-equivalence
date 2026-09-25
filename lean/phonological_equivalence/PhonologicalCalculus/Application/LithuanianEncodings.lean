                          
import PhonologicalCalculus.Application.OCPRegion

namespace LithuanianEncodings

set_option maxHeartbeats 4000000

inductive Mode | relational | existence | origin
  deriving DecidableEq

inductive Profile | positive | counterbleeding
  deriving DecidableEq

abbrev Candidate := Bool × Bool × Bool

def referenceVoice (i : Fin 3) : Bool := i != 2
def samePlace (i : Fin 3) : Bool := i != 0

def resolves (m : Mode) (z : Bool) : Bool := !z || decide (m = .origin)

def pressure (m : Mode) (agreement : Bool) (x y z : Bool) : Bool :=
  if resolves m z then (if agreement then x != y else x == y)
  else decide (m = .existence)

def context (m : Mode) (agreement : Bool) (i : Fin 3) (z : Bool) : Bool :=
  resolves m z && (agreement || samePlace i)

def active (agreement : Bool) (i : Fin 3) : Bool :=
  if agreement then referenceVoice i else samePlace i && !referenceVoice i

noncomputable def contribution (m : Mode) (agreement : Bool) (i : Fin 3)
    (w l : ℝ) (x y z : Bool) : ℝ :=
  if pressure m agreement x y z then
    if active agreement i then w else if context m agreement i z then l*w else 0
  else 0

noncomputable def score (ma mn : Mode) (i : Fin 3) (c r d a n l : ℝ)
    (s : Candidate) : ℝ :=
  (if s.1 then c else 0) + (if s.2.1 = referenceVoice i then 0 else r) +
    (if s.2.2 then d else 0) + contribution ma true i a l s.1 s.2.1 s.2.2 +
    contribution mn false i n l s.1 s.2.1 s.2.2

def target (p : Profile) (i : Fin 3) : Candidate :=
  if i = 0 then (true,true,false)
  else if i = 1 then (decide (p = .counterbleeding),true,true)
  else (false,false,true)

def Selective (ma mn : Mode) (p : Profile) (c r d a n l : ℝ) : Prop :=
  ∀ i : Fin 3, ∀ x y z : Bool, (x,y,z) ≠ target p i →
    score ma mn i c r d a n l (target p i) < score ma mn i c r d a n l (x,y,z)

def Region (ma mn : Mode) (p : Profile) (c r d a n l : ℝ) : Prop :=
  match ma,mn,p with
  | .relational,.relational,.positive =>
      0<c ∧ c<d ∧ c<r ∧ d<a ∧ d<n ∧ d<c+l*a ∧ d<c+l*n
  | .origin,.relational,.counterbleeding =>
      0<d ∧ c<r ∧ c+d<a ∧ d<l*n ∧ d<n ∧ d<c+l*a
  | _,_,_ => False

theorem exact_regions (ma mn : Mode) (p : Profile) (c r d a n l : ℝ)
    (hc : 0≤c) (hr : 0≤r) (hd : 0≤d) (ha : 0≤a) (hn : 0≤n) (hl : 0≤l) :
    Selective ma mn p c r d a n l ↔ Region ma mn p c r d a n l := by
  have hla := mul_nonneg hl ha
  have hln := mul_nonneg hl hn
  cases ma <;> cases mn <;> cases p <;>
    simp [Selective, Fin.forall_fin_succ, Bool.forall_bool, target, score,
      contribution, pressure, context, active, resolves, referenceVoice, samePlace,
      Region] <;>
    (aesop (config := { terminal := false, maxRuleApplications := 100 })) <;> linarith

theorem attenuation_positive (ma mn : Mode) (p : Profile) (c r d a n l : ℝ)
    (hc : 0≤c) (hr : 0≤r) (hd : 0≤d) (ha : 0≤a) (hn : 0≤n) (hl : 0≤l)
    (h : Selective ma mn p c r d a n l) : 0<l := by
  have hh := (exact_regions ma mn p c r d a n l hc hr hd ha hn hl).mp h
  by_contra hh'
  have hz : l=0 := le_antisymm (le_of_not_gt hh') hl
  subst l
  cases ma <;> cases mn <;> cases p <;> simp [Region] at hh <;> linarith

theorem positive_witness (l : ℝ) (hl : 0<l) :
    Selective .relational .relational .positive 1 4 2 (4+3/l) (4+3/l) l := by
  have hq : 0<3/l := div_pos (by norm_num) hl
  have he : l*(4+3/l) = 4*l+3 := by field_simp
  apply (exact_regions _ _ _ _ _ _ _ _ _ (by norm_num) (by norm_num)
    (by norm_num) (by linarith) (by linarith) (le_of_lt hl)).mpr
  simp only [Region]
  rw [he]
  exact ⟨by norm_num,by norm_num,by norm_num,by linarith,by linarith,by linarith,by linarith⟩

theorem counterbleeding_witness (l : ℝ) (hl : 0<l) :
    Selective .origin .relational .counterbleeding 1 4 2 (4+3/l) (4+3/l) l := by
  have hq : 0<3/l := div_pos (by norm_num) hl
  have he : l*(4+3/l) = 4*l+3 := by field_simp
  apply (exact_regions _ _ _ _ _ _ _ _ _ (by norm_num) (by norm_num)
    (by norm_num) (by linarith) (by linarith) (le_of_lt hl)).mpr
  simp only [Region]
  rw [he]
  exact ⟨by norm_num,by norm_num,by linarith,by linarith,by linarith,by linarith⟩

theorem no_attenuation_only_exclusion (c r d a n l : ℝ)
    (hc : 0≤c) (hr : 0≤r) (hd : 0≤d) (ha : 0≤a) (hn : 0≤n) (hl : 0≤l)
    (h : Selective .relational .relational .positive c r d a n l) :
    Selective .origin .relational .counterbleeding 1 4 2 (4+3/l) (4+3/l) l :=
  counterbleeding_witness l (attenuation_positive _ _ _ _ _ _ _ _ _ hc hr hd ha hn hl h)

end LithuanianEncodings
