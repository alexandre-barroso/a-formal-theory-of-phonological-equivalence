import Mathlib.Tactic

                         
set_option maxHeartbeats 8000000
namespace PhonologicalCalculus.LearningExact
abbrev H := Bool × Bool
abbrev C := Bool × Bool × Bool
def bit (b : Bool) : ℝ := if b then 1 else 0
structure W where
  p : ℝ
  s : ℝ
  dep : ℝ
  a : ℝ
  n : ℝ
  anew : ℝ
  nnew : ℝ
def score (w : W) (v1 v2 same : Bool) (h : H) (c : C) : ℝ :=
  w.p * bit (c.1 != v1) + w.s * bit (c.2.1 != v2) +
  w.dep * bit c.2.2 +
  (if v1 != v2 then w.a else w.anew) * bit (c.1 != c.2.1) * bit (h.1 || !c.2.2) +
  (if v1 == v2 then w.n else w.nnew) * bit (c.1 == c.2.1) * bit same * bit (h.2 || !c.2.2)

def instantiate (p s d a n lam : ℝ) : W := ⟨p,s,d,a,n,lam*a,lam*n⟩

def properScore (w : W) := score w
def predicted (v1 v2 same : Bool) (h : H) (c : C) : Bool :=
  c.2.1 == v2 &&
  if !same then c.1 == v2 && !c.2.2
  else if v1 == v2 then
    if !h.2 then c.1 == v1 && c.2.2
    else c.1 == !v1 && (!h.1 || !c.2.2)
  else if !h.1 then c.1 == v1 && c.2.2
    else c.1 == !v1 && (!h.2 || !c.2.2)
def region (w : W) : Prop :=
  0 < w.p ∧ w.p < w.dep ∧ w.p < w.s ∧ w.dep = w.anew ∧ w.dep = w.nnew ∧
  w.p+w.dep < w.a ∧ w.p+w.dep < w.n
def exactComparisons (w : W) : Prop := ∀ v1 v2 same h c d,
  predicted v1 v2 same h c = true →
  if predicted v1 v2 same h d then properScore w v1 v2 same h c = properScore w v1 v2 same h d
  else properScore w v1 v2 same h c < properScore w v1 v2 same h d

theorem region_suffices (w : W) (hr : region w) : exactComparisons w := by
  rcases hr with ⟨hp,hd,hs,ha,hn,ha',hn'⟩
  intro v1 v2 same h c d hc
  rcases h with ⟨ar,nr⟩
  rcases c with ⟨x,y,z⟩
  rcases d with ⟨dx,dy,dz⟩
  cases v1 <;> cases v2 <;> cases same <;> cases ar <;> cases nr <;> cases x <;> cases y <;> cases z <;>
    simp_all [predicted] <;>
    cases dx <;> cases dy <;> cases dz <;>
    simp_all [predicted,properScore,score,bit] <;> linarith

theorem region_necessary (w : W) (h : exactComparisons w) : region w := by
  have hp := h false false true (false,false) (false,false,true) (true,false,true) (by decide)
  have hd := h false true false (false,false) (true,true,false) (false,true,true) (by decide)
  have hs := h false true false (false,false) (true,true,false) (false,false,false) (by decide)
  have ha := h false false true (false,true) (true,false,false) (true,false,true) (by decide)
  have hn := h false true true (true,false) (true,true,false) (true,true,true) (by decide)
  have ha' := h false true true (true,true) (true,true,false) (false,true,false) (by decide)
  have hn' := h false false true (true,true) (true,false,false) (false,false,false) (by decide)
  simp [predicted,properScore,score,bit] at hp hd hs ha hn ha' hn'
  exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith,by linarith,by linarith⟩

theorem exact_region (w : W) : exactComparisons w ↔ region w :=
  ⟨region_necessary w,region_suffices w⟩

def outputSet (v1 v2 same : Bool) (h : H) : Finset C :=
  Finset.univ.filter fun c => predicted v1 v2 same h c
theorem sets_nonempty : ∀ v1 v2 same h, (outputSet v1 v2 same h).Nonempty := by decide +kernel
theorem two_probes_separate : Function.Injective (fun h : H => (outputSet false false true h,outputSet false true true h)) := by decide +kernel
theorem no_single_probe : ∀ v1 v2 same, ¬Function.Injective (outputSet v1 v2 same) := by decide +kernel

theorem exact_minimizers (w : W) (hr : region w) (v1 v2 same : Bool) (h : H) (c : C) :
    (∀ d, properScore w v1 v2 same h c ≤ properScore w v1 v2 same h d) ↔ predicted v1 v2 same h c = true := by
  constructor
  · intro hmin
    obtain ⟨d,hd⟩ := sets_nonempty v1 v2 same h
    have hd' : predicted v1 v2 same h d = true := by simpa [outputSet] using hd
    have hh := region_suffices w hr v1 v2 same h d c hd'
    cases hc : predicted v1 v2 same h c with
    | false => simp only [hc,Bool.false_eq_true,↓reduceIte] at hh; exact False.elim ((not_lt_of_ge (hmin d)) hh)
    | true => rfl
  · intro hc d
    have hh := region_suffices w hr v1 v2 same h c d hc
    cases hd : predicted v1 v2 same h d with
    | false => simp only [hd,Bool.false_eq_true,↓reduceIte] at hh; exact hh.le
    | true => simp only [hd,↓reduceIte] at hh; exact hh.le

theorem printed_one : region (instantiate 1 4 2 16 16 (1/8)) := by norm_num [region,instantiate]
theorem printed_two : region (instantiate 2 9 5 40 40 (1/8)) := by norm_num [region,instantiate]


theorem retained_region (p s d a n lam : ℝ) :
    exactComparisons (instantiate p s d a n lam) ↔
    0 < p ∧ p < d ∧ p < s ∧ d = lam*a ∧ d = lam*n ∧ p+d<a ∧ p+d<n :=
  exact_region _

theorem attenuation_necessary (p s d a n lam : ℝ)
    (h : region (instantiate p s d a n lam)) : 0 < lam ∧ lam < 1 := by
  rcases h with ⟨hp,hd,hs,ha,hn,ha',hn'⟩
  change 0 < p at hp
  change p < d at hd
  change d = lam*a at ha
  change p+d<a at ha'
  have hapos : 0 < a := by linarith
  constructor
  · by_contra hh
    have : lam*a ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hh) hapos.le
    linarith
  · by_contra hh
    have : a ≤ lam*a := by nlinarith [le_of_not_gt hh]
    linarith

theorem attenuation_witness (lam : ℝ) (h0 : 0 < lam) (h1 : lam < 1) :
    region (instantiate (lam*(1-lam)) 2 lam 1 1 lam) := by
  have ha : 0 < 1-lam := by linarith
  have hp := mul_pos h0 ha
  have hl2 := sq_pos_of_pos h0
  have hdiff := sq_pos_of_pos ha
  dsimp [region,instantiate]
  constructor
  · exact hp
  constructor
  · nlinarith
  constructor
  · nlinarith [sq_nonneg lam]
  constructor
  · ring
  constructor
  · ring
  constructor <;> nlinarith

theorem attenuation_projection (lam : ℝ) :
    (∃ p s d a n, exactComparisons (instantiate p s d a n lam)) ↔ 0 < lam ∧ lam < 1 := by
  constructor
  · rintro ⟨p,s,d,a,n,h⟩
    exact attenuation_necessary p s d a n lam ((exact_region _).mp h)
  · rintro ⟨h0,h1⟩
    exact ⟨lam*(1-lam),2,lam,1,1,(exact_region _).mpr (attenuation_witness lam h0 h1)⟩

#print axioms attenuation_projection
#print axioms exact_region
#print axioms exact_minimizers
#print axioms two_probes_separate
#print axioms no_single_probe
end PhonologicalCalculus.LearningExact
