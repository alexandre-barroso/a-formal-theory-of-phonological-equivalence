import PhonologicalOpacity.Lithuanian.Core
namespace Lithuanian
set_option maxRecDepth 10000
set_option maxHeartbeats 0
theorem exclusive_iff_strict (u : Fin 3) (P : Fin 8 → ℝ) :
    Exclusive u.val P ↔ Strict P (goal u.val) := by
  have obs_goal : observe u.val (goal u.val).val = target u.val := by
    fin_cases u <;> decide
  have obs_only (j : Fin 8) (h : observe u.val j.val = target u.val) : j=goal u.val := by
    have hf : j.val ∈ fiber u.val (target u.val) := by simp [fiber,h,j.isLt]
    rw [target_binding u] at hf
    apply Fin.ext
    simpa using hf
  constructor
  · rintro ⟨⟨i,hi⟩,ho⟩ j hj
    have hg := obs_only i (ho i hi)
    subst i
    have le := hi j
    by_contra hn
    have jr : P j ≤ P (goal u.val) := le_of_not_gt hn
    exact hj (obs_only j (ho j (fun t => le_trans jr (hi t))))
  · intro hs
    have hm : ∀ t, P (goal u.val) ≤ P t := by
      intro t
      by_cases h:t=goal u.val
      · subst t; exact le_rfl
      · exact le_of_lt (hs t h)
    refine ⟨⟨goal u.val,hm⟩,?_⟩
    intro j hj
    by_cases h:j=goal u.val
    · simpa [h] using obs_goal
    · exact False.elim ((not_lt_of_ge (hj (goal u.val))) (hs j h))

theorem rr_region_iff (c r d a n lam : ℝ)
    (hc : 0≤c) (hr : 0≤r) (hd : 0≤d) (ha : 0≤a) (hn : 0≤n) (hl : 0≤lam) :
    Joint 0 c r d a n lam ↔ Region c r d a n lam := by
  constructor
  · rintro ⟨pg,pb,tt⟩
    have hcd := pg 3 (by decide)
    have hcr := pg 0 (by decide)
    have hcp := pb 7 (by decide)
    have hda := pb 2 (by decide)
    have hdn := tt 0 (by decide)
    have hdln := pb 6 (by decide)
    have hdla := tt 4 (by decide)
    norm_num [pressure,coeff,reader,mark,bits,sourceVoice,homorganic] at hcd hcr hcp hda hdn hdln hdla
    dsimp [Region]
    constructor
    · linarith
    refine ⟨hcd,hcr,hda,hdn,?_,?_⟩ <;> nlinarith
  · rintro ⟨hpos,hcd,hcr,hda,hdn,hdln,hdla⟩
    dsimp [Joint,Strict]
    refine ⟨?_,?_,?_⟩
    all_goals
      intro j hj
      fin_cases j <;> norm_num [Fin.ext_iff,pressure,coeff,reader,mark,bits,sourceVoice,homorganic] at * <;> nlinarith

theorem ordinary_binding (u : Fin 3) (j : Fin 8) (c r d a n : ℝ) :
    pressure u.val 0 c r d a n 1 j = ordinary u.val c r d a n j := by
  fin_cases u <;> fin_cases j <;> norm_num [pressure,ordinary,coeff,reader,mark,bits,sourceVoice,homorganic]
theorem ordinary_region_iff (c r d a n : ℝ)
    (hc : 0≤c) (hr : 0≤r) (hd : 0≤d) (ha : 0≤a) (hn : 0≤n) :
    Joint 0 c r d a n 1 ↔ OrdinaryRegion c r d a n := by
  rw [rr_region_iff c r d a n 1 hc hr hd ha hn (by norm_num)]
  dsimp [Region,OrdinaryRegion]
  constructor
  · rintro ⟨hp,hcd,hcr,hda,hdn,_,_⟩; exact ⟨hp,hcd,hcr,hda,hdn⟩
  · rintro ⟨hp,hcd,hcr,hda,hdn⟩
    refine ⟨hp,hcd,hcr,hda,hdn,?_,?_⟩ <;> linarith

theorem surviving_A_profiles (mode : Nat) (hm : mode=1 ∨ mode=3) (c r d a n lam : ℝ) :
    pressure 0 mode c r d a n lam 6 = c ∧ pressure 0 mode c r d a n lam 2 = a ∧
    pressure 1 mode c r d a n lam 3 = d+a ∧ pressure 1 mode c r d a n lam 7 = d+c := by
  rcases hm with rfl|rfl
  all_goals norm_num [pressure,coeff,reader,mark,bits,sourceVoice,homorganic] <;> ring
theorem surviving_A_delta (mode : Nat) (hm : mode=1 ∨ mode=3) (c r d a n lam : ℝ) :
    pressure 1 mode c r d a n lam 7 - pressure 1 mode c r d a n lam 3 = c-a := by
  obtain ⟨_,_,hb,hab⟩ := surviving_A_profiles mode hm c r d a n lam
  rw [hb,hab]; ring
theorem no_surviving_A (mode : Nat) (hm : mode=1 ∨ mode=3) (c r d a n lam : ℝ) :
    ¬ (Strict (pressure 0 mode c r d a n lam) 6 ∧ Strict (pressure 1 mode c r d a n lam) 3) := by
  rintro ⟨pg,pb⟩
  have h1:=pg 2 (by decide)
  have h2:=pb 7 (by decide)
  obtain ⟨hg,hf,hb,hab⟩ := surviving_A_profiles mode hm c r d a n lam
  rw [hg,hf] at h1
  rw [hb,hab] at h2
  linarith
theorem surviving_N_profiles (mode : Nat) (hm : mode=2 ∨ mode=3) (c r d a n lam : ℝ) :
    pressure 2 mode c r d a n lam 0 = n ∧ pressure 2 mode c r d a n lam 1 = d+n := by
  rcases hm with rfl|rfl <;> norm_num [pressure,coeff,reader,mark,bits,sourceVoice,homorganic]
theorem no_surviving_N (mode : Nat) (hm : mode=2 ∨ mode=3) (c r d a n lam : ℝ) (hd : 0≤d) :
    ¬ Strict (pressure 2 mode c r d a n lam) 1 := by
  intro tt
  have h:=tt 0 (by decide)
  obtain ⟨hf,hb⟩ := surviving_N_profiles mode hm c r d a n lam
  rw [hf,hb] at h
  linarith
theorem no_zero_RR (c r d a n : ℝ) : ¬ Joint 0 c r d a n 0 := by
  rintro ⟨pg,pb,_⟩
  have h1:=pg 3 (by decide)
  have h2:=pb 6 (by decide)
  norm_num [pressure,coeff,reader,mark,bits,sourceVoice,homorganic] at h1 h2
  linarith
theorem fixed_region : Region 1 4 2 16 16 (1/8) := by norm_num [Region]
theorem fixed_RR : Joint 0 1 4 2 16 16 (1/8) :=
  (rr_region_iff 1 4 2 16 16 (1/8) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)).mpr fixed_region
theorem score_binding (u : Fin 3) (cfg : Fin 6) (j : Fin 8) :
    (score8 u.val cfg.val j.val : ℝ) = 8 *
      (if cfg.val=0 then ordinary u.val 1 4 2 16 16 j else
        pressure u.val (configMode cfg.val) 1 4 2 16 16 (if cfg.val=5 then 0 else 1/8) j) := by
  fin_cases u <;> fin_cases cfg <;> fin_cases j <;>
    norm_num [score8,configMode,ordinary,pressure,coeff,reader,mark,bits,sourceVoice,homorganic]
#print axioms exclusive_iff_strict
#print axioms rr_region_iff
#print axioms ordinary_binding
#print axioms ordinary_region_iff
#print axioms surviving_A_profiles
#print axioms surviving_A_delta
#print axioms no_surviving_A
#print axioms surviving_N_profiles
#print axioms no_surviving_N
#print axioms no_zero_RR
#print axioms fixed_RR
#print axioms score_binding
end Lithuanian
