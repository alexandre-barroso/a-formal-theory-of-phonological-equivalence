import PhonologicalCalculus.Support.EndpointWinnerComplete

namespace PhonologicalCalculus.Support

open Set

                                                                                      
theorem exists_local_positive_improvement_of_hasDerivAt_neg
    {f : ℝ → ℝ} {slope : ℝ}
    (hderiv : HasDerivAt f slope 0) (hslope : slope < 0)
    (radius : ℝ) (hradius : 0 < radius) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < radius ∧ f epsilon < f 0 := by
  by_contra hnone
  push Not at hnone
  have hminimum : IsMinOn f (Ico (0 : ℝ) radius) 0 := by
    intro epsilon hepsilon
    change f 0 ≤ f epsilon
    rcases eq_or_lt_of_le hepsilon.1 with hzero | hpositive
    · simpa only [← hzero] using le_refl (f (0 : ℝ))
    · exact hnone epsilon hpositive hepsilon.2
  have hone : (1 : ℝ) ∈ posTangentConeAt (Ico (0 : ℝ) radius) 0 := by
    rw [one_mem_posTangentConeAt_iff_mem_closure]
    have hinter : Ioi (0 : ℝ) ∩ Ico 0 radius = Ioo 0 radius := by
      ext x
      simp only [mem_inter_iff, mem_Ioi, mem_Ico, mem_Ioo]
      constructor
      · rintro ⟨hx, _, hxrad⟩
        exact ⟨hx, hxrad⟩
      · rintro ⟨hx, hxrad⟩
        exact ⟨hx, le_of_lt hx, hxrad⟩
    rw [hinter, closure_Ioo (ne_of_lt hradius)]
    exact ⟨le_rfl, le_of_lt hradius⟩
  have hnonnegative := hminimum.localize.hasFDerivWithinAt_nonneg
    hderiv.hasFDerivAt.hasFDerivWithinAt hone
  have : 0 ≤ slope := by
    simpa [ContinuousLinearMap.toSpanSingleton_apply] using hnonnegative
  exact (not_lt_of_ge this) hslope

                                                                                   
                                                                    
structure FeasibleEndpointConditions
    (edge site : ℝ → ℝ) (horizon positiveLength : ℕ)
    (flux : ℕ → ℝ)
    (siteSlope edgeSlopeAtOne boundaryPrevious boundaryIncomingSlope : ℝ) : Prop where
  positiveLength_le_horizon : positiveLength ≤ horizon
  edgeSlope_zero : HasDerivAt edge 0 0
  siteSlope_zero : HasDerivAt site siteSlope 0
  edgeSlope_boundary : HasDerivAt edge boundaryIncomingSlope boundaryPrevious
  boundaryIncomingSlope_pos : positiveLength < horizon → 0 < boundaryIncomingSlope
  boundary_feasible_minimum : positiveLength < horizon →
    ∃ radius : ℝ, 0 < radius ∧ ∀ epsilon : ℝ,
      0 < epsilon → epsilon < radius →
      zeroSiteLiftObjective edge site boundaryPrevious 0 ≤
        zeroSiteLiftObjective edge site boundaryPrevious epsilon
  flux_drop : ∀ index, index < positiveLength →
    flux (index + 1) + siteSlope ≤ flux index
  terminal_flux_nonneg : 0 ≤ flux positiveLength
  edgeSlopeAtOne_pos : 0 < edgeSlopeAtOne
  initial_flux_strict : 0 < positiveLength → flux 0 < edgeSlopeAtOne

theorem feasible_zeroSlope_fullPositivePrefix
    {edge site : ℝ → ℝ} {horizon positiveLength : ℕ} {flux : ℕ → ℝ}
    {edgeSlopeAtOne boundaryPrevious boundaryIncomingSlope : ℝ}
    (h : FeasibleEndpointConditions edge site horizon positiveLength flux 0
      edgeSlopeAtOne boundaryPrevious boundaryIncomingSlope) :
    positiveLength = horizon := by
  apply Nat.le_antisymm h.positiveLength_le_horizon
  by_contra hnot
  have hfirstZero : positiveLength < horizon := Nat.lt_of_not_ge hnot
  obtain ⟨radius, hradius, hmin⟩ := h.boundary_feasible_minimum hfirstZero
  have hderiv := zeroSiteLiftObjective_hasDerivAt
    h.edgeSlope_zero h.edgeSlope_boundary h.siteSlope_zero
  have hslope := zeroLiftingRightDerivative_negative (h.boundaryIncomingSlope_pos hfirstZero)
  obtain ⟨epsilon, heps, hsmall, hlower⟩ :=
    exists_local_positive_improvement_of_hasDerivAt_neg hderiv hslope radius hradius
  exact (not_lt_of_ge (hmin epsilon heps hsmall)) hlower

theorem feasible_positiveSlope_strictPrefixBound
    {edge site : ℝ → ℝ} {horizon positiveLength : ℕ} {flux : ℕ → ℝ}
    {siteSlope edgeSlopeAtOne boundaryPrevious boundaryIncomingSlope : ℝ}
    (h : FeasibleEndpointConditions edge site horizon positiveLength flux siteSlope
      edgeSlopeAtOne boundaryPrevious boundaryIncomingSlope) :
    (positiveLength : ℝ) * siteSlope < edgeSlopeAtOne := by
  by_cases hzero : positiveLength = 0
  · simpa [hzero] using h.edgeSlopeAtOne_pos
  · have hpositive : 0 < positiveLength := Nat.pos_of_ne_zero hzero
    have htelescope := flux_drop_telescope flux siteSlope positiveLength h.flux_drop
    have hinitial := h.initial_flux_strict hpositive
    have hterminal := h.terminal_flux_nonneg
    linarith

theorem feasible_positiveSlope_integerPrefixBound
    {edge site : ℝ → ℝ} {horizon positiveLength : ℕ} {flux : ℕ → ℝ}
    {siteSlope edgeSlopeAtOne boundaryPrevious boundaryIncomingSlope : ℝ}
    (h : FeasibleEndpointConditions edge site horizon positiveLength flux siteSlope
      edgeSlopeAtOne boundaryPrevious boundaryIncomingSlope)
    (hc : 0 < siteSlope) :
    positiveLength ≤ Nat.ceil (edgeSlopeAtOne / siteSlope) - 1 := by
  exact strictPositivePrefix_le_ceil_sub_one positiveLength hc
    (feasible_positiveSlope_strictPrefixBound h)

end PhonologicalCalculus.Support
