import PhonologicalCalculus.MaxEnt.SlovenianRetention

namespace SlovenianDomain

open scoped BigOperators
open SlovenianRetention

noncomputable def totalEnergy {ι κ : Type*} [Fintype κ]
    (input : κ → Bool) (output : ι → κ → Bool) (extra : ι → ℝ)
    (M G l : ℝ) (c : ι) : ℝ :=
  extra c + ∑ j, energy (input j) M G 0 0 l (output c j, false)

theorem expanded_energy_shift {ι κ : Type*} [Fintype κ]
    (input : κ → Bool) (output : ι → κ → Bool) (extra : ι → ℝ)
    (M G l t : ℝ) (ht : 1+t ≠ 0) (c : ι) :
    totalEnergy input output extra ((1+l)*M/(1+t)) (G+(1+l)*M/(1+t)-M) t c =
      totalEnergy input output extra M G l c +
      ∑ j, (if input j then (1+l)*M/(1+t)-M else 0) := by
  unfold totalEnergy
  simp_rw [reparameterized_energy (M := M) (G := G) (P := 0) (S := 0) (l := l) (t := t) (ht := ht)]
  rw [Finset.sum_add_distrib]
  ring

theorem expanded_law {ι κ : Type*} [Fintype ι] [Fintype κ]
    (input : κ → Bool) (output : ι → κ → Bool) (extra : ι → ℝ)
    (M G l t : ℝ) (ht : 1+t ≠ 0) (c : ι) :
    probability (totalEnergy input output extra ((1+l)*M/(1+t)) (G+(1+l)*M/(1+t)-M) t) c =
      probability (totalEnergy input output extra M G l) c := by
  have h : totalEnergy input output extra ((1+l)*M/(1+t)) (G+(1+l)*M/(1+t)-M) t =
      fun x => totalEnergy input output extra M G l x +
        ∑ j, (if input j then (1+l)*M/(1+t)-M else 0) := by
    funext x
    exact expanded_energy_shift input output extra M G l t ht x
  rw [h]
  exact probability_shift _ _ _

theorem observation_kernel_preservation {ι κ ω : Type*} [Fintype ι] [Fintype κ]
    (input : κ → Bool) (output : ι → κ → Bool) (extra : ι → ℝ)
    (kernel : ι → ω → ℝ) (M G l t : ℝ) (ht : 1+t ≠ 0) (o : ω) :
    (∑ c, probability (totalEnergy input output extra ((1+l)*M/(1+t))
      (G+(1+l)*M/(1+t)-M) t) c * kernel c o) =
    ∑ c, probability (totalEnergy input output extra M G l) c * kernel c o := by
  apply Finset.sum_congr rfl
  intro c _
  rw [expanded_law input output extra M G l t ht c]

theorem expanded_zero_law {ι κ : Type*} [Fintype ι] [Fintype κ]
    (input : κ → Bool) (output : ι → κ → Bool) (extra : ι → ℝ)
    (M G l : ℝ) (c : ι) :
    probability (totalEnergy input output extra ((1+l)*M) (G+l*M) 0) c =
      probability (totalEnergy input output extra M G l) c := by
  have h := expanded_law input output extra M G l 0 (by norm_num) c
  convert h using 1 <;> congr 2 <;> ring

end SlovenianDomain
