import PhonologicalCalculus.MaxEnt.SchwaAttenuation

namespace SlovenianRetention

open scoped BigOperators

abbrev Candidate := Bool × Bool

noncomputable def energy (inputLax : Bool) (M G P S l : ℝ) (c : Candidate) : ℝ :=
  (if c.1 then (if inputLax then M else l*M) else 0) +
  (if c.1 != inputLax then G + (if c.2 then 0 else P) else 0) +
  (if c.2 then S else 0)

noncomputable def probability {ι : Type*} [Fintype ι] (e : ι → ℝ) (c : ι) : ℝ :=
  Real.exp (-e c) / ∑ x, Real.exp (-e x)

theorem probability_shift {ι : Type*} [Fintype ι] (e : ι → ℝ) (k : ℝ) (c : ι) :
    probability (fun x => e x + k) c = probability e c := by
  simp only [probability, neg_add, Real.exp_add]
  rw [← Finset.sum_mul]
  exact mul_div_mul_right _ _ (Real.exp_ne_zero _)

theorem reparameterized_energy (inputLax : Bool) (M G P S l t : ℝ)
    (ht : 1+t ≠ 0) (c : Candidate) :
    energy inputLax ((1+l)*M/(1+t)) (G+(1+l)*M/(1+t)-M) P S t c =
    energy inputLax M G P S l c + (if inputLax then (1+l)*M/(1+t)-M else 0) := by
  rcases c with ⟨v,s⟩
  cases inputLax <;> cases v <;> cases s <;> norm_num [energy] <;> field_simp <;> ring

theorem reparameterized_law (inputLax : Bool) (M G P S l t : ℝ)
    (ht : 1+t ≠ 0) (c : Candidate) :
    probability (energy inputLax ((1+l)*M/(1+t)) (G+(1+l)*M/(1+t)-M) P S t) c =
    probability (energy inputLax M G P S l) c := by
  have he : energy inputLax ((1+l)*M/(1+t)) (G+(1+l)*M/(1+t)-M) P S t =
      fun x => energy inputLax M G P S l x + (if inputLax then (1+l)*M/(1+t)-M else 0) := by
    funext x
    exact reparameterized_energy inputLax M G P S l t ht x
  rw [he]
  exact probability_shift _ _ _

theorem zero_attenuation_law (inputLax : Bool) (M G P S l : ℝ) (c : Candidate) :
    probability (energy inputLax ((1+l)*M) (G+l*M) P S 0) c =
    probability (energy inputLax M G P S l) c := by
  have h := reparameterized_law inputLax M G P S l 0 (by norm_num) c
  convert h using 1 <;> congr 2 <;> ring

theorem zero_attenuation_admissible (M G l : ℝ) (hM : 0≤M) (hG : 0≤G) (hl : 0≤l) :
    0≤(1+l)*M ∧ 0≤G+l*M := by
  constructor
  · exact mul_nonneg (by linarith) hM
  · exact add_nonneg hG (mul_nonneg hl hM)

theorem ordinary_map_admissible_iff (M G l : ℝ) :
    0≤G+(1+l)*M/2-M ↔ (1-l)*M≤2*G := by
  constructor <;> intro h <;> nlinarith

theorem positive_attenuation_not_identified (M G P S l : ℝ)
    (hM : 0≤M) (hG : 0≤G) (hl : 0<l) :
    ∃ M' G', 0≤M' ∧ 0≤G' ∧ l≠0 ∧
      ∀ inputLax c, probability (energy inputLax M' G' P S 0) c =
        probability (energy inputLax M G P S l) c := by
  have ha := zero_attenuation_admissible M G l hM hG (le_of_lt hl)
  exact ⟨(1+l)*M,G+l*M,ha.1,ha.2,ne_of_gt hl,fun i c => zero_attenuation_law i M G P S l c⟩

end SlovenianRetention
