                  
                   
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.Topology.Algebra.Group.SubmonoidClosure
import Mathlib.Tactic

namespace NativeIrrational
noncomputable def beta : ℝ := Real.sqrt 2
noncomputable def residue (n : ℕ) : ℝ := Int.fract ((n : ℝ) * beta)

theorem beta_bounds : 1 < beta ∧ beta < 2 := by
  have h := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hn := Real.sqrt_nonneg (2:ℝ)
  dsimp [beta]
  constructor <;> nlinarith

theorem residue_bounds (n : ℕ) : 0 ≤ residue n ∧ residue n < 1 :=
  ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

theorem residue_injective : Function.Injective residue := by
  intro m n h
  obtain ⟨z,hz⟩ := Int.fract_eq_fract.mp h
  by_contra hne
  have d : (m : ℤ) - n ≠ 0 := by omega
  have irr := (irrational_intCast_mul_iff (m := (m : ℤ) - n)).2 ⟨d,irrational_sqrt_two⟩
  have e : (((m : ℤ) - n : ℤ) : ℝ) * Real.sqrt 2 = (z : ℝ) := by
    push_cast
    dsimp [beta] at hz
    nlinarith
  rw [e] at irr
  exact irr.ne_int z rfl

theorem residue_pos {n : ℕ} (hn : n ≠ 0) : 0 < residue n := by
  have h : residue n ≠ residue 0 := fun h => hn (residue_injective h)
  have h0 : residue 0 = 0 := by simp [residue]
  rw [h0] at h
  exact lt_of_le_of_ne (residue_bounds n).1 h.symm

theorem positive_orbit_dense (l u : ℝ) (hl : 0 ≤ l) (hlu : l < u) (hu : u ≤ 1) :
    ∃ n : ℕ, 0 < n ∧ l < residue n ∧ residue n < u := by
  letI : Fact (0 < (1:ℝ)) := ⟨by norm_num⟩
  have hz : DenseRange (fun n : ℤ => n • (beta : AddCircle (1:ℝ))) :=
    AddCircle.denseRange_zsmul_coe_iff.mpr (by simpa [beta] using irrational_sqrt_two)
  have hd : DenseRange (fun n : ℕ => n • (beta : AddCircle (1:ℝ))) :=
    denseRange_zsmul_iff_nsmul.mp hz
  have hop : IsOpen ((fun x : ℝ => (x : AddCircle (1:ℝ))) '' Set.Ioo l u) :=
    QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo
  have hne : ((fun x : ℝ => (x : AddCircle (1:ℝ))) '' Set.Ioo l u).Nonempty :=
    (Set.nonempty_Ioo.mpr hlu).image _
  obtain ⟨n,y,hy,he⟩ := hd.exists_mem_open hop hne
  have hf : (residue n : AddCircle (1:ℝ)) = n • (beta : AddCircle (1:ℝ)) := by
    dsimp [residue]
    rw [AddCircle.coe_fract, ← nsmul_eq_mul, AddCircle.coe_nsmul]
  have eq : y = residue n := (AddCircle.coe_eq_coe_iff_of_mem_Ico
    (show y ∈ Set.Ico (0:ℝ) (0+1) by constructor <;> linarith [hy.1,hy.2])
    (show residue n ∈ Set.Ico (0:ℝ) (0+1) by simpa using residue_bounds n)).mp
    (he.trans hf.symm)
  refine ⟨n,?_,?_,?_⟩
  · by_contra hn
    have : n = 0 := by omega
    subst n
    simp [residue] at eq
    linarith [hy.1]
  · simpa [eq] using hy.1
  · simpa [eq] using hy.2
end NativeIrrational
