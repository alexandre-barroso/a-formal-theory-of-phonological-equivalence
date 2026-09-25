import PhonologicalCalculus.MaxEnt.SlovenianDomain

namespace SlovenianTwoClass

open scoped BigOperators
open SlovenianRetention

inductive Kind where
  | mid | low | fixed

noncomputable def siteEnergy (k : Kind) (input output : Bool) (M N G l : ℝ) : ℝ :=
  match k with
  | .mid => energy input M G 0 0 l (output,false)
  | .low => if output then l*N+G else 0
  | .fixed => 0

noncomputable def canonicalSite (k : Kind) (input output : Bool) (a b h : ℝ) : ℝ :=
  match k with
  | .mid => if input then (if output then b else 0) else (if output then a else 0)
  | .low => if output then h else 0
  | .fixed => 0

def markedMid (k : Kind) (input : Bool) : Bool :=
  match k with
  | .mid => input
  | _ => false

theorem site_correspondence (k : Kind) (input output : Bool) (M N G l : ℝ) :
    siteEnergy k input output M N G l =
      canonicalSite k input output (l*M+G) (M-G) (l*N+G) +
        (if markedMid k input then G else 0) := by
  cases k <;> cases input <;> cases output <;>
    simp [siteEnergy,canonicalSite,markedMid,energy] <;> ring

noncomputable def totalEnergy {ι κ : Type*} [Fintype κ]
    (kind : κ → Kind) (input : κ → Bool) (output : ι → κ → Bool)
    (extra : ι → ℝ) (M N G l : ℝ) (c : ι) : ℝ :=
  extra c + ∑ j, siteEnergy (kind j) (input j) (output c j) M N G l

noncomputable def canonicalEnergy {ι κ : Type*} [Fintype κ]
    (kind : κ → Kind) (input : κ → Bool) (output : ι → κ → Bool)
    (extra : ι → ℝ) (a b h : ℝ) (c : ι) : ℝ :=
  extra c + ∑ j, canonicalSite (kind j) (input j) (output c j) a b h

theorem total_correspondence {ι κ : Type*} [Fintype κ]
    (kind : κ → Kind) (input : κ → Bool) (output : ι → κ → Bool)
    (extra : ι → ℝ) (M N G l : ℝ) (c : ι) :
    totalEnergy kind input output extra M N G l c =
      canonicalEnergy kind input output extra (l*M+G) (M-G) (l*N+G) c +
        ∑ j, (if markedMid (kind j) (input j) then G else 0) := by
  unfold totalEnergy canonicalEnergy
  simp_rw [site_correspondence]
  rw [Finset.sum_add_distrib]
  ring

theorem law_correspondence {ι κ : Type*} [Fintype ι] [Fintype κ]
    (kind : κ → Kind) (input : κ → Bool) (output : ι → κ → Bool)
    (extra : ι → ℝ) (M N G l : ℝ) (c : ι) :
    probability (totalEnergy kind input output extra M N G l) c =
      probability (canonicalEnergy kind input output extra (l*M+G) (M-G) (l*N+G)) c := by
  have he : totalEnergy kind input output extra M N G l = fun x =>
      canonicalEnergy kind input output extra (l*M+G) (M-G) (l*N+G) x +
        ∑ j, (if markedMid (kind j) (input j) then G else 0) := by
    funext x
    exact total_correspondence kind input output extra M N G l x
  rw [he]
  exact probability_shift _ _ _

theorem coordinate_identities (M N G l : ℝ) :
    (l*M+G)+(M-G) = (1+l)*M ∧
    (l*M+G)-l*(M-G) = (1+l)*G ∧
    l*((l*N+G)+(M-G))+(l*N+G)-(l*M+G) = l*(1+l)*N := by
  constructor
  · ring
  constructor <;> ring

theorem coordinate_admissible_iff (M N G l : ℝ) (hl : 0<l) :
    (0≤M ∧ 0≤N ∧ 0≤G) ↔
      (0≤(l*M+G)+(M-G) ∧ 0≤(l*M+G)-l*(M-G) ∧
        0≤l*((l*N+G)+(M-G))+(l*N+G)-(l*M+G)) := by
  rcases coordinate_identities M N G l with ⟨h1,h2,h3⟩
  rw [h1,h2,h3]
  have hp : 0<1+l := by linarith
  have hq : 0<l*(1+l) := mul_pos hl hp
  constructor
  · rintro ⟨hm,hn,hg⟩
    exact ⟨mul_nonneg (le_of_lt hp) hm, mul_nonneg (le_of_lt hp) hg,
      mul_nonneg (le_of_lt hq) hn⟩
  · rintro ⟨hm,hg,hn⟩
    constructor
    · nlinarith
    constructor <;> nlinarith

theorem inverse_coordinates (a b h l : ℝ) (hl : 0<l) :
    let M := (a+b)/(1+l)
    let G := (a-l*b)/(1+l)
    let N := (h-G)/l
    l*M+G=a ∧ M-G=b ∧ l*N+G=h := by
  dsimp
  have hl0 : l≠0 := ne_of_gt hl
  have hd : 1+l≠0 := ne_of_gt (by linarith : 0<1+l)
  constructor
  · field_simp
    <;> ring
  constructor
  · field_simp
    <;> ring
  · field_simp
    <;> ring

theorem positive_feasibility_iff (a b h l : ℝ) (hl : 0<l) :
    (∃ M N G : ℝ, 0≤M ∧ 0≤N ∧ 0≤G ∧ l*M+G=a ∧ M-G=b ∧ l*N+G=h) ↔
      (0≤a+b ∧ 0≤a-l*b ∧ 0≤l*(h+b)+h-a) := by
  constructor
  · rintro ⟨M,N,G,hm,hn,hg,ha,hb,hh⟩
    have hc := (coordinate_admissible_iff M N G l hl).mp ⟨hm,hn,hg⟩
    simpa only [ha,hb,hh] using hc
  · intro hc
    let M := (a+b)/(1+l)
    let G := (a-l*b)/(1+l)
    let N := (h-G)/l
    have hi : l*M+G=a ∧ M-G=b ∧ l*N+G=h := inverse_coordinates a b h l hl
    have hw : 0≤M ∧ 0≤N ∧ 0≤G := by
      apply (coordinate_admissible_iff M N G l hl).mpr
      simpa only [hi.1,hi.2.1,hi.2.2] using hc
    exact ⟨M,N,G,hw.1,hw.2.1,hw.2.2,hi.1,hi.2.1,hi.2.2⟩

theorem zero_feasibility_iff (a b h : ℝ) :
    (∃ M N G : ℝ, 0≤M ∧ 0≤N ∧ 0≤G ∧ (0:ℝ)*M+G=a ∧ M-G=b ∧ (0:ℝ)*N+G=h) ↔
      (0≤a ∧ 0≤a+b ∧ h=a) := by
  simp only [zero_mul,zero_add]
  constructor
  · rintro ⟨M,N,G,hm,hn,hg,ha,hb,hh⟩
    constructor
    · linarith
    constructor <;> linarith
  · rintro ⟨ha,hab,hh⟩
    refine ⟨a+b,0,a,hab,le_rfl,ha,rfl,?_,hh.symm⟩
    ring

theorem ordinary_feasibility_iff (a b h : ℝ) :
    (∃ M N G : ℝ, 0≤M ∧ 0≤N ∧ 0≤G ∧ M+G=a ∧ M-G=b ∧ N+G=h) ↔
      (0≤a+b ∧ 0≤a-b ∧ 0≤2*h+b-a) := by
  have hp := positive_feasibility_iff a b h 1 (by norm_num)
  have he : h+b+h-a = 2*h+b-a := by ring
  simpa only [one_mul,he] using hp

theorem interior_coordinate_witness :
    (∃ M N G : ℝ, 0≤M ∧ 0≤N ∧ 0≤G ∧ (1/4:ℝ)*M+G=1 ∧ M-G=3 ∧ (1/4:ℝ)*N+G=9/20) ∧
    ¬(∃ M N G : ℝ, 0≤M ∧ 0≤N ∧ 0≤G ∧ M+G=1 ∧ M-G=3 ∧ N+G=9/20) ∧
    ¬(∃ M N G : ℝ, 0≤M ∧ 0≤N ∧ 0≤G ∧ (0:ℝ)*M+G=1 ∧ M-G=3 ∧ (0:ℝ)*N+G=9/20) := by
  rw [positive_feasibility_iff _ _ _ _ (by norm_num),ordinary_feasibility_iff,zero_feasibility_iff]
  norm_num

theorem witness_identified_interval (l : ℝ) (hl : 0<l) :
    (∃ M N G : ℝ, 0≤M ∧ 0≤N ∧ 0≤G ∧ l*M+G=1 ∧ M-G=3 ∧ l*N+G=9/20) ↔
      (11/69≤l ∧ l≤1/3) := by
  rw [positive_feasibility_iff _ _ _ _ hl]
  constructor
  · rintro ⟨h1,h2,h3⟩
    constructor <;> linarith
  · rintro ⟨h1,h2⟩
    constructor
    · norm_num
    constructor <;> linarith

end SlovenianTwoClass
