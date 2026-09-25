import PhonologicalOpacity.Attenuation.Productive.Baseline.ProductiveFamily
namespace ProductiveGua
set_option maxHeartbeats 0

theorem exclusive_strict {rows : List (List String)} {P : List String → ℝ}
    {out : String} {g r : List String} (h : Exclusive rows P out)
    (hf : ∀ s, Generated rows s → observe s=out → s=g)
    (hr : Generated rows r) (ho : observe r≠out) : P g < P r := by
  obtain ⟨⟨m,hm,hmin⟩,hall⟩ := h
  have he := hf m hm (hall m hm hmin)
  subst m
  have hle := hmin r hr
  apply lt_of_le_of_ne hle
  intro heq
  have hminr : ∀ t, Generated rows t → P r ≤ P t := by
    intro t ht
    rw [← heq]
    exact hmin t ht
  exact ho (hall r hr hminr)

theorem selected_of_check {u : Retained.Input} {g0 g1 : Int} {out : String}
    {rows : List (List String)} {g : List String}
    (hc : check u g0 g1 out [] rows=true) (hg : Generated rows g) (ho : observe g=out)
    (he : ∀ l : ℝ, fullScore u (weightFamily l) l g=(g0:ℝ)+g1*l)
    (l : ℝ) (h0 : 0≤l) (h1 : l<1/2) :
    Exclusive rows (fullScore u (weightFamily l) l) out := by
  apply exclusive_of_separation hg ho
  intro s hs
  have h := check_sound hc hs l h0 h1
  simp only [List.nil_append] at h
  rcases h with ho | hlt
  · exact Or.inl ho
  · right
    rw [he,fullScore_family]
    exact hlt

theorem scalar_necessary (wA wH l : ℝ) (hw : 0≤wH)
    (hA : 0<wA-l*wH) (hB : 0<(1-l)*wH-wA) : l<1/2 := by
  by_contra hn
  have hhalf : 1/2≤l := le_of_not_gt hn
  have hp : 0≤(2*l-1)*wH := mul_nonneg (by linarith) hw
  nlinarith
end ProductiveGua
