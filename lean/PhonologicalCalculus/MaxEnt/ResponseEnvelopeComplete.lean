import PhonologicalCalculus.MaxEnt.ResponseEnvelope

/-!
Exact relative-interior and equality clauses for the finite arbitrary-mass
MaxEnt response envelope.

The finite ledger is represented by a nonempty `Finset` of violation rows.
Strictly positive normalized candidate masses give every relative-interior
conditional mean, and no boundary mean.  Independent fibres therefore give
exactly the intrinsic interior of the closed response envelope.  The final
theorems state the corresponding equality criteria without replacing the
closed envelope by a fixed-mass response field.
-/

namespace PhonologicalCalculus.MaxEnt

open Set

section IntrinsicConvexity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- Convex combinations with a positive coefficient on an intrinsic-interior
point remain in the intrinsic interior. -/
theorem Convex.intrinsicInterior_combo_self_mem
    {s : Set E} (hs : Convex ℝ s) {x y : E}
    (hx : x ∈ intrinsicInterior ℝ s) (hy : y ∈ s)
    {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a • x + b • y ∈ intrinsicInterior ℝ s := by
  rcases hx with ⟨x', hx', rfl⟩
  letI : Nonempty (affineSpan ℝ s) := ⟨x'⟩
  let y' : affineSpan ℝ s := ⟨y, subset_affineSpan ℝ s hy⟩
  let equivalence := AffineIsometryEquiv.constVSub ℝ x'
  let transformed : Set (affineSpan ℝ s).direction :=
    equivalence.symm ⁻¹' ((↑) ⁻¹' s : Set (affineSpan ℝ s))
  have htransformedConvex : Convex ℝ transformed := by
    exact hs.affine_preimage
      ((affineSpan ℝ s).subtype.comp equivalence.symm.toAffineMap)
  have hxTransformed : equivalence x' ∈ interior transformed := by
    have hxPreimage : equivalence x' ∈
        equivalence.symm.toHomeomorph ⁻¹'
          interior ((↑) ⁻¹' s : Set (affineSpan ℝ s)) := by
      simpa using hx'
    rw [equivalence.symm.toHomeomorph.preimage_interior] at hxPreimage
    simpa [transformed] using hxPreimage
  have hyTransformed : equivalence y' ∈ transformed := by
    change (equivalence.symm (equivalence y') : affineSpan ℝ s) ∈
      ((↑) ⁻¹' s : Set (affineSpan ℝ s))
    simpa [y'] using hy
  have hcombo := htransformedConvex.combo_interior_self_mem_interior
    hxTransformed hyTransformed ha hb hab
  refine ⟨equivalence.symm
    (a • equivalence x' + b • equivalence y'), ?_, ?_⟩
  · have hpreimage : equivalence.symm
        (a • equivalence x' + b • equivalence y') ∈
          equivalence.toHomeomorph ⁻¹' interior transformed := by
      simpa using hcombo
    rw [equivalence.toHomeomorph.preimage_interior] at hpreimage
    have hsets : equivalence.toHomeomorph ⁻¹' transformed =
        ((↑) ⁻¹' s : Set (affineSpan ℝ s)) := by
      ext z
      simp [transformed]
    rw [hsets] at hpreimage
    exact hpreimage
  · have hline : a • equivalence x' + b • equivalence y' =
        AffineMap.lineMap (equivalence y') (equivalence x') a := by
      rw [AffineMap.lineMap_apply_module, show 1 - a = b by linarith]
      abel
    rw [hline]
    have hinverse : equivalence.symm
        (AffineMap.lineMap (equivalence y') (equivalence x') a) =
          AffineMap.lineMap y' x' a := by
      have hmap := equivalence.toAffineEquiv.apply_lineMap y' x' a
      change equivalence (AffineMap.lineMap y' x' a) =
        AffineMap.lineMap (equivalence y') (equivalence x') a at hmap
      rw [← hmap]
      simp
    rw [hinverse]
    simp only [AffineMap.lineMap_apply]
    change a • (↑x' - y) + y = a • ↑x' + b • y
    rw [show b = 1 - a by linarith]
    module

omit [FiniteDimensional ℝ E] in
/-- An intrinsic-interior point absorbs every point of the same convex set
with a strictly positive coefficient.  The second endpoint is obtained by a
short extension of the segment through the interior point. -/
theorem Convex.exists_strict_combo_of_mem_intrinsicInterior
    {s : Set E} (_hs : Convex ℝ s) {x y : E}
    (hx : x ∈ intrinsicInterior ℝ s) (hy : y ∈ s) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ a + b = 1 ∧
      ∃ z ∈ s, x = a • y + b • z := by
  rcases hx with ⟨x', hxInterior, hxValue⟩
  letI : Nonempty (affineSpan ℝ s) := ⟨x'⟩
  let y' : affineSpan ℝ s := ⟨y, subset_affineSpan ℝ s hy⟩
  have hneighborhood :
      ((↑) ⁻¹' s : Set (affineSpan ℝ s)) ∈ nhds x' :=
    mem_interior_iff_mem_nhds.mp hxInterior
  obtain ⟨radius, hradius, hball⟩ :=
    Metric.mem_nhds_iff.mp hneighborhood
  let distance : ℝ := dist y' x'
  let rate : ℝ := radius / (2 * (distance + 1))
  have hdistance : 0 ≤ distance := dist_nonneg
  have hdenominator : 0 < 2 * (distance + 1) := by positivity
  have hrate : 0 < rate := div_pos hradius hdenominator
  let z' : affineSpan ℝ s := AffineMap.lineMap y' x' (1 + rate)
  have hzDistance : dist z' x' < radius := by
    rw [show dist z' x' = rate * distance by
      dsimp [z']
      rw [dist_lineMap_right]
      have hnorm : ‖1 - (1 + rate)‖ = rate := by
        rw [show 1 - (1 + rate) = -rate by ring, norm_neg, Real.norm_eq_abs,
          abs_of_pos hrate]
      rw [hnorm]]
    dsimp [rate]
    rw [div_mul_eq_mul_div, div_lt_iff₀ hdenominator]
    nlinarith
  have hz : (z' : E) ∈ s :=
    hball (by simpa [Metric.mem_ball] using hzDistance)
  let a : ℝ := rate / (1 + rate)
  let b : ℝ := 1 / (1 + rate)
  have hdenominatorOne : 0 < 1 + rate := by linarith
  have ha : 0 < a := div_pos hrate hdenominatorOne
  have hb : 0 < b := div_pos zero_lt_one hdenominatorOne
  have hab : a + b = 1 := by
    dsimp [a, b]
    field_simp [hdenominatorOne.ne']
    ring
  refine ⟨a, b, ha, hb, hab, z', hz, ?_⟩
  rw [← hxValue]
  have hzFormula : (z' : E) =
      (1 + rate) • (x' : E) - rate • y := by
    dsimp [z']
    rw [AffineMap.lineMap_apply]
    change (1 + rate) • ((x' : E) - y) + y =
      (1 + rate) • (x' : E) - rate • y
    module
  rw [hzFormula]
  have hbScale : b * (1 + rate) = 1 := by
    dsimp [b]
    field_simp [hdenominatorOne.ne']
  have hcancel : a - b * rate = 0 := by
    dsimp [a, b]
    field_simp [hdenominatorOne.ne']
    ring
  symm
  calc
    a • y + b • ((1 + rate) • (x' : E) - rate • y) =
        (b * (1 + rate)) • (x' : E) + (a - b * rate) • y := by
          module
    _ = (x' : E) := by rw [hbScale, hcancel, one_smul, zero_smul, add_zero]

omit [FiniteDimensional ℝ E] in
/-- A positive coefficient in a convex decomposition may be decreased while
keeping the other endpoint inside the same convex set. -/
theorem Convex.exists_combo_of_smaller_coefficient
    {s : Set E} (hs : Convex ℝ s) {x centre endpoint : E}
    (hcentre : centre ∈ s) (hendpoint : endpoint ∈ s)
    {a b epsilon : ℝ} (_ha : 0 < a) (hb : 0 < b)
    (hab : a + b = 1) (_hepsilon : 0 < epsilon)
    (hepsilonA : epsilon < a)
    (hx : x = a • centre + b • endpoint) :
    ∃ remainder ∈ s,
      x = epsilon • centre + (1 - epsilon) • remainder := by
  have haOne : a < 1 := by linarith
  have hepsilonOne : epsilon < 1 := hepsilonA.trans haOne
  have hdenominator : 0 < 1 - epsilon := sub_pos.mpr hepsilonOne
  let c : ℝ := (a - epsilon) / (1 - epsilon)
  let d : ℝ := b / (1 - epsilon)
  have hc : 0 ≤ c :=
    div_nonneg (sub_nonneg.mpr hepsilonA.le) hdenominator.le
  have hd : 0 ≤ d := div_nonneg hb.le hdenominator.le
  have hcd : c + d = 1 := by
    dsimp [c, d]
    field_simp [hdenominator.ne']
    linarith
  let remainder : E := c • centre + d • endpoint
  have hremainder : remainder ∈ s :=
    hs hcentre hendpoint hc hd hcd
  refine ⟨remainder, hremainder, ?_⟩
  rw [hx]
  dsimp [remainder]
  have hcScale : (1 - epsilon) * c = a - epsilon := by
    dsimp [c]
    field_simp [hdenominator.ne']
  have hdScale : (1 - epsilon) * d = b := by
    dsimp [d]
    field_simp [hdenominator.ne']
  rw [smul_add, smul_smul, smul_smul, hcScale, hdScale]
  module

end IntrinsicConvexity

section PositiveBarycentricInterior

variable {I : Type*} [Fintype I] [Nonempty I]

/-- The least coordinate of a finite weight vector. -/
noncomputable def leastWeight (weight : I → ℝ) : ℝ :=
  (Finset.univ.image weight).min' (by
    classical
    exact (Finset.univ_nonempty.image weight))

/-- The least coordinate is bounded above by every coordinate. -/
theorem leastWeight_le (weight : I → ℝ) (i : I) :
    leastWeight weight ≤ weight i := by
  classical
  exact Finset.min'_le _ _ (Finset.mem_image.mpr
    ⟨i, Finset.mem_univ i, rfl⟩)

/-- A strictly positive finite vector has a strictly positive least
coordinate. -/
theorem leastWeight_pos {weight : I → ℝ} (hweight : ∀ i, 0 < weight i) :
    0 < leastWeight weight := by
  classical
  unfold leastWeight
  rw [Finset.lt_min'_iff]
  intro value hvalue
  rcases Finset.mem_image.mp hvalue with ⟨i, _, rfl⟩
  exact hweight i

end PositiveBarycentricInterior

section ConditionalMeanInterior

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Strictly positive masses realize only intrinsic-interior means. -/
theorem positiveMassMeanSet_subset_intrinsicInterior
    (points : Finset E) (hpoints : points.Nonempty) :
    positiveMassMeanSet points ⊆
      intrinsicInterior ℝ (convexHull ℝ (points : Set E)) := by
  letI : Nonempty points := hpoints.to_subtype
  intro mean hmean
  rcases hmean with ⟨weight, hweight, rfl⟩
  let hull : Set E := convexHull ℝ (points : Set E)
  have hhullConvex : Convex ℝ hull := convex_convexHull ℝ _
  have hhullNonempty : hull.Nonempty :=
    (hpoints.to_set : (points : Set E).Nonempty).mono (subset_convexHull ℝ _)
  obtain ⟨centre, hcentreInterior⟩ :=
    Set.Nonempty.intrinsicInterior hhullConvex hhullNonempty
  have hcentreHull : centre ∈ hull :=
    intrinsicInterior_subset hcentreInterior
  change centre ∈ convexHull ℝ (points : Set E) at hcentreHull
  rw [convexHull_eq_finiteMeanMap_image] at hcentreHull
  rcases hcentreHull with ⟨centreWeight, hcentreWeight, hcentre⟩
  let minimum : ℝ := leastWeight weight
  let a : ℝ := minimum / 2
  let b : ℝ := 1 - a
  have hminimumPos : 0 < minimum := leastWeight_pos hweight.1
  have ha : 0 < a := div_pos hminimumPos (by norm_num)
  have hminimumLeOne : minimum ≤ 1 := by
    let i : points := Classical.choice (inferInstance : Nonempty points)
    exact (leastWeight_le weight i).trans
      (mem_Icc_of_mem_stdSimplex
        (strictSimplex_subset_stdSimplex points hweight) i).2
  have hb : 0 < b := by dsimp [b, a]; linarith
  let remainderWeight : points → ℝ :=
    fun i ↦ (weight i - a * centreWeight i) / b
  have hremainderWeight : remainderWeight ∈ stdSimplex ℝ points := by
    constructor
    · intro i
      have hcentreLeOne := mem_Icc_of_mem_stdSimplex hcentreWeight i
      have hminimumLe : minimum ≤ weight i := leastWeight_le weight i
      have haCentre : a * centreWeight i ≤ a :=
        mul_le_of_le_one_right ha.le hcentreLeOne.2
      dsimp [remainderWeight]
      exact div_nonneg (by dsimp [a] at haCentre ⊢; linarith) hb.le
    · dsimp [remainderWeight]
      rw [← Finset.sum_div, Finset.sum_sub_distrib]
      rw [← Finset.mul_sum]
      have hweightSum : ∑ i ∈ points.attach, weight i = 1 := by
        simpa using hweight.2
      have hcentreWeightSum : ∑ i ∈ points.attach, centreWeight i = 1 := by
        simpa using hcentreWeight.2
      rw [hweightSum, hcentreWeightSum]
      field_simp [hb.ne']
      ring
  let remainder := finiteMeanMap points remainderWeight
  have hremainderHull : remainder ∈ hull := by
    change remainder ∈ convexHull ℝ (points : Set E)
    rw [convexHull_eq_finiteMeanMap_image]
    exact ⟨remainderWeight, hremainderWeight, rfl⟩
  have hdecomposition :
      finiteMeanMap points weight = a • centre + b • remainder := by
    rw [← hcentre]
    dsimp [remainder, remainderWeight]
    rw [← (finiteMeanMap points).map_smul,
      ← (finiteMeanMap points).map_smul,
      ← (finiteMeanMap points).map_add]
    congr 1
    funext i
    dsimp [b]
    have hdenominator : 1 - a ≠ 0 := by linarith
    field_simp [hdenominator]
    ring
  rw [hdecomposition]
  exact Convex.intrinsicInterior_combo_self_mem hhullConvex hcentreInterior
    hremainderHull ha hb.le (by dsimp [b]; ring)

omit [FiniteDimensional ℝ E] in
/-- Every intrinsic-interior point of a finite convex hull has a
representation using strictly positive mass on every declared row. -/
theorem intrinsicInterior_subset_positiveMassMeanSet
    (points : Finset E) (hpoints : points.Nonempty) :
    intrinsicInterior ℝ (convexHull ℝ (points : Set E)) ⊆
      positiveMassMeanSet points := by
  letI : Nonempty points := hpoints.to_subtype
  intro mean hmean
  rcases hmean with ⟨mean', hmeanInterior, hmeanValue⟩
  letI : Nonempty (affineSpan ℝ (convexHull ℝ (points : Set E))) :=
    ⟨mean'⟩
  let uniformWeight : points → ℝ := uniformSimplexPoint points
  have huniformWeight : uniformWeight ∈ strictSimplex points :=
    uniformSimplexPoint_mem points
  let uniformMean : E := finiteMeanMap points uniformWeight
  have huniformHull : uniformMean ∈ convexHull ℝ (points : Set E) :=
    positiveMassMeanSet_subset_convexHull points
      ⟨uniformWeight, huniformWeight, rfl⟩
  let uniformMean' : affineSpan ℝ (convexHull ℝ (points : Set E)) :=
    ⟨uniformMean, subset_affineSpan ℝ _ huniformHull⟩
  have hneighborhood :
      ((↑) ⁻¹' convexHull ℝ (points : Set E) :
        Set (affineSpan ℝ (convexHull ℝ (points : Set E)))) ∈ nhds mean' :=
    mem_interior_iff_mem_nhds.mp hmeanInterior
  obtain ⟨radius, hradius, hball⟩ :=
    Metric.mem_nhds_iff.mp hneighborhood
  let distance : ℝ := dist uniformMean' mean'
  let rate : ℝ := radius / (2 * (distance + 1))
  have hdistance : 0 ≤ distance := dist_nonneg
  have hdenominator : 0 < 2 * (distance + 1) := by positivity
  have hrate : 0 < rate := div_pos hradius hdenominator
  let extended : affineSpan ℝ (convexHull ℝ (points : Set E)) :=
    AffineMap.lineMap uniformMean' mean' (1 + rate)
  have hextendedDistance : dist extended mean' < radius := by
    rw [show dist extended mean' = rate * distance by
      dsimp [extended]
      rw [dist_lineMap_right]
      have hnorm : ‖1 - (1 + rate)‖ = rate := by
        rw [show 1 - (1 + rate) = -rate by ring, norm_neg, Real.norm_eq_abs,
          abs_of_pos hrate]
      rw [hnorm]]
    dsimp [rate]
    rw [div_mul_eq_mul_div, div_lt_iff₀ hdenominator]
    nlinarith
  have hextendedHull :
      (extended : E) ∈ convexHull ℝ (points : Set E) := by
    exact hball (by simpa [Metric.mem_ball] using hextendedDistance)
  let extendedValue : E := extended
  have hextendedHullValue :
      extendedValue ∈ convexHull ℝ (points : Set E) := hextendedHull
  rw [convexHull_eq_finiteMeanMap_image] at hextendedHullValue
  rcases hextendedHullValue with
    ⟨extendedWeight, hextendedWeight, hextendedMean⟩
  let a : ℝ := rate / (1 + rate)
  let b : ℝ := 1 / (1 + rate)
  have hdenominatorOne : 0 < 1 + rate := by linarith
  have ha : 0 < a := div_pos hrate hdenominatorOne
  have hb : 0 < b := div_pos zero_lt_one hdenominatorOne
  have hab : a + b = 1 := by
    dsimp [a, b]
    field_simp [hdenominatorOne.ne']
    ring
  let mixedWeight : points → ℝ :=
    fun i ↦ a * uniformWeight i + b * extendedWeight i
  have hmixedWeight : mixedWeight ∈ strictSimplex points := by
    constructor
    · intro i
      have hleft : 0 < a * uniformWeight i :=
        mul_pos ha (huniformWeight.1 i)
      have hright : 0 ≤ b * extendedWeight i :=
        mul_nonneg hb.le (hextendedWeight.1 i)
      dsimp [mixedWeight]
      linarith
    · dsimp [mixedWeight]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        show ∑ i ∈ points.attach, uniformWeight i = 1 by
          simpa using huniformWeight.2,
        show ∑ i ∈ points.attach, extendedWeight i = 1 by
          simpa using hextendedWeight.2]
      simpa using hab
  refine ⟨mixedWeight, hmixedWeight, ?_⟩
  have hextendedFormula :
      (extended : E) = (1 + rate) • mean - rate • uniformMean := by
    dsimp [extended]
    rw [AffineMap.lineMap_apply]
    change (1 + rate) • ((mean' : E) - uniformMean) + uniformMean =
      (1 + rate) • mean - rate • uniformMean
    rw [hmeanValue]
    module
  change extendedValue = (1 + rate) • mean - rate • uniformMean at hextendedFormula
  have hmixedFunction : mixedWeight =
      a • uniformWeight + b • extendedWeight := by
    funext i
    simp [mixedWeight]
  rw [hmixedFunction, (finiteMeanMap points).map_add,
    (finiteMeanMap points).map_smul, (finiteMeanMap points).map_smul]
  rw [hextendedMean]
  rw [hextendedFormula]
  have hbScale : b * (1 + rate) = 1 := by
    dsimp [b]
    field_simp [hdenominatorOne.ne']
  have hcancel : a - b * rate = 0 := by
    dsimp [a, b]
    field_simp [hdenominatorOne.ne']
    ring
  calc
    a • uniformMean + b • ((1 + rate) • mean - rate • uniformMean) =
        (b * (1 + rate)) • mean + (a - b * rate) • uniformMean := by
          module
    _ = mean := by rw [hbScale, hcancel, one_smul, zero_smul, add_zero]

/-- **MAX-G9.CONVEX.03**, relative-interior clause.  For every nonempty
finite violation-row ledger, the arbitrary-positive-mass conditional means
are exactly the intrinsic (relative) interior of its convex hull. -/
theorem max_g9_convex_03_relativeInterior
    (points : Finset E) (hpoints : points.Nonempty) :
    positiveMassMeanSet points =
      intrinsicInterior ℝ (convexHull ℝ (points : Set E)) := by
  exact Set.Subset.antisymm
    (positiveMassMeanSet_subset_intrinsicInterior points hpoints)
    (intrinsicInterior_subset_positiveMassMeanSet points hpoints)

end ConditionalMeanInterior

section ResponseRelativeInterior

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- The difference image of two convex sets is convex. -/
theorem convex_responseDifference {left right : Set E}
    (hleft : Convex ℝ left) (hright : Convex ℝ right) :
    Convex ℝ (responseDifference left right) := by
  rintro _ ⟨⟨leftOne, rightOne⟩, ⟨hleftOne, hrightOne⟩, rfl⟩
    _ ⟨⟨leftTwo, rightTwo⟩, ⟨hleftTwo, hrightTwo⟩, rfl⟩
    a b ha hb hab
  refine ⟨⟨a • leftOne + b • leftTwo,
    a • rightOne + b • rightTwo⟩,
    ⟨hleft hleftOne hleftTwo ha hb hab,
      hright hrightOne hrightTwo ha hb hab⟩, ?_⟩
  module

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The difference image of two nonempty sets is nonempty. -/
theorem responseDifference_nonempty {left right : Set E}
    (hleft : left.Nonempty) (hright : right.Nonempty) :
    (responseDifference left right).Nonempty := by
  rcases hleft with ⟨leftPoint, hleftPoint⟩
  rcases hright with ⟨rightPoint, hrightPoint⟩
  exact ⟨rightPoint - leftPoint,
    ⟨⟨leftPoint, rightPoint⟩, ⟨hleftPoint, hrightPoint⟩, rfl⟩⟩

/-- Positive independent fibre masses produce response vectors only in the
intrinsic interior of the closed response envelope. -/
theorem positiveMassResponseSet_subset_intrinsicInterior_envelope
    (left right : Finset E) (hleft : left.Nonempty)
    (hright : right.Nonempty) :
    positiveMassResponseSet left right ⊆
      intrinsicInterior ℝ (convexHullResponseEnvelope left right) := by
  let leftHull : Set E := convexHull ℝ (left : Set E)
  let rightHull : Set E := convexHull ℝ (right : Set E)
  have hleftConvex : Convex ℝ leftHull := convex_convexHull ℝ _
  have hrightConvex : Convex ℝ rightHull := convex_convexHull ℝ _
  have hleftNonempty : leftHull.Nonempty := by
    rcases hleft with ⟨point, hpoint⟩
    exact ⟨point, subset_convexHull ℝ _ hpoint⟩
  have hrightNonempty : rightHull.Nonempty := by
    rcases hright with ⟨point, hpoint⟩
    exact ⟨point, subset_convexHull ℝ _ hpoint⟩
  have henvelopeConvex :
      Convex ℝ (convexHullResponseEnvelope left right) := by
    exact convex_responseDifference hleftConvex hrightConvex
  have henvelopeNonempty :
      (convexHullResponseEnvelope left right).Nonempty := by
    exact responseDifference_nonempty hleftNonempty hrightNonempty
  obtain ⟨centre, hcentreInterior⟩ :=
    henvelopeNonempty.intrinsicInterior henvelopeConvex
  have hcentreEnvelope : centre ∈ convexHullResponseEnvelope left right :=
    intrinsicInterior_subset hcentreInterior
  rcases hcentreEnvelope with
    ⟨⟨leftCentre, rightCentre⟩, ⟨hleftCentre, hrightCentre⟩,
      hcentreValue⟩
  intro response hresponse
  rcases hresponse with
    ⟨⟨leftMean, rightMean⟩, ⟨hleftMean, hrightMean⟩,
      hresponseValue⟩
  have hleftMeanInterior : leftMean ∈ intrinsicInterior ℝ leftHull := by
    rw [← max_g9_convex_03_relativeInterior left hleft]
    exact hleftMean
  have hrightMeanInterior : rightMean ∈ intrinsicInterior ℝ rightHull := by
    rw [← max_g9_convex_03_relativeInterior right hright]
    exact hrightMean
  obtain ⟨leftA, leftB, hleftA, hleftB, hleftAB,
      leftEndpoint, hleftEndpoint, hleftDecomposition⟩ :=
    Convex.exists_strict_combo_of_mem_intrinsicInterior hleftConvex
      hleftMeanInterior hleftCentre
  obtain ⟨rightA, rightB, hrightA, hrightB, hrightAB,
      rightEndpoint, hrightEndpoint, hrightDecomposition⟩ :=
    Convex.exists_strict_combo_of_mem_intrinsicInterior hrightConvex
      hrightMeanInterior hrightCentre
  let epsilon : ℝ := min leftA rightA / 2
  have hminimum : 0 < min leftA rightA := lt_min hleftA hrightA
  have hepsilon : 0 < epsilon := by
    dsimp [epsilon]
    linarith
  have hepsilonLeft : epsilon < leftA := by
    dsimp [epsilon]
    have hminimumLeft : min leftA rightA ≤ leftA := min_le_left _ _
    linarith
  have hepsilonRight : epsilon < rightA := by
    dsimp [epsilon]
    have hminimumRight : min leftA rightA ≤ rightA := min_le_right _ _
    linarith
  obtain ⟨leftRemainder, hleftRemainder, hleftCommon⟩ :=
    Convex.exists_combo_of_smaller_coefficient hleftConvex
      hleftCentre hleftEndpoint hleftA hleftB hleftAB hepsilon
      hepsilonLeft hleftDecomposition
  obtain ⟨rightRemainder, hrightRemainder, hrightCommon⟩ :=
    Convex.exists_combo_of_smaller_coefficient hrightConvex
      hrightCentre hrightEndpoint hrightA hrightB hrightAB hepsilon
      hepsilonRight hrightDecomposition
  have hepsilonOne : epsilon < 1 := by
    have hleftAOne : leftA < 1 := by linarith
    exact hepsilonLeft.trans hleftAOne
  have hremainderEnvelope :
      rightRemainder - leftRemainder ∈
        convexHullResponseEnvelope left right :=
    ⟨⟨leftRemainder, rightRemainder⟩,
      ⟨hleftRemainder, hrightRemainder⟩, rfl⟩
  have hresponseCombo :
      epsilon • centre + (1 - epsilon) •
          (rightRemainder - leftRemainder) ∈
        intrinsicInterior ℝ (convexHullResponseEnvelope left right) :=
    Convex.intrinsicInterior_combo_self_mem henvelopeConvex
      hcentreInterior hremainderEnvelope hepsilon
      (sub_nonneg.mpr hepsilonOne.le) (by ring)
  rw [← hresponseValue]
  change rightMean - leftMean ∈
    intrinsicInterior ℝ (convexHullResponseEnvelope left right)
  have hidentity :
      rightMean - leftMean =
        epsilon • centre + (1 - epsilon) •
          (rightRemainder - leftRemainder) := by
    rw [hleftCommon, hrightCommon, ← hcentreValue]
    module
  rw [hidentity]
  exact hresponseCombo

/-- Every intrinsic-interior response of the closed envelope is realized by
strictly positive independent masses in the two fibres. -/
theorem intrinsicInterior_envelope_subset_positiveMassResponseSet
    (left right : Finset E) (hleft : left.Nonempty)
    (hright : right.Nonempty) :
    intrinsicInterior ℝ (convexHullResponseEnvelope left right) ⊆
      positiveMassResponseSet left right := by
  letI : Nonempty left := hleft.to_subtype
  letI : Nonempty right := hright.to_subtype
  let leftHull : Set E := convexHull ℝ (left : Set E)
  let rightHull : Set E := convexHull ℝ (right : Set E)
  have hleftConvex : Convex ℝ leftHull := convex_convexHull ℝ _
  have hrightConvex : Convex ℝ rightHull := convex_convexHull ℝ _
  have henvelopeConvex :
      Convex ℝ (convexHullResponseEnvelope left right) :=
    convex_responseDifference hleftConvex hrightConvex
  let leftBase : E :=
    finiteMeanMap left (uniformSimplexPoint left)
  let rightBase : E :=
    finiteMeanMap right (uniformSimplexPoint right)
  have hleftBase : leftBase ∈ positiveMassMeanSet left := by
    exact ⟨uniformSimplexPoint left, uniformSimplexPoint_mem left, rfl⟩
  have hrightBase : rightBase ∈ positiveMassMeanSet right := by
    exact ⟨uniformSimplexPoint right, uniformSimplexPoint_mem right, rfl⟩
  have hleftBaseInterior : leftBase ∈ intrinsicInterior ℝ leftHull := by
    rw [← max_g9_convex_03_relativeInterior left hleft]
    exact hleftBase
  have hrightBaseInterior : rightBase ∈ intrinsicInterior ℝ rightHull := by
    rw [← max_g9_convex_03_relativeInterior right hright]
    exact hrightBase
  have hbaseResponse :
      rightBase - leftBase ∈ positiveMassResponseSet left right :=
    ⟨⟨leftBase, rightBase⟩, ⟨hleftBase, hrightBase⟩, rfl⟩
  have hbaseEnvelope :
      rightBase - leftBase ∈ convexHullResponseEnvelope left right :=
    positiveMassResponseSet_subset_envelope left right hbaseResponse
  intro response hresponseInterior
  obtain ⟨a, b, ha, hb, hab, remainder, hremainder,
      hresponseDecomposition⟩ :=
    Convex.exists_strict_combo_of_mem_intrinsicInterior henvelopeConvex
      hresponseInterior hbaseEnvelope
  rcases hremainder with
    ⟨⟨leftRemainder, rightRemainder⟩,
      ⟨hleftRemainder, hrightRemainder⟩, hremainderValue⟩
  let leftMean : E := a • leftBase + b • leftRemainder
  let rightMean : E := a • rightBase + b • rightRemainder
  have hleftMeanInterior : leftMean ∈ intrinsicInterior ℝ leftHull :=
    Convex.intrinsicInterior_combo_self_mem hleftConvex
      hleftBaseInterior hleftRemainder ha hb.le hab
  have hrightMeanInterior : rightMean ∈ intrinsicInterior ℝ rightHull :=
    Convex.intrinsicInterior_combo_self_mem hrightConvex
      hrightBaseInterior hrightRemainder ha hb.le hab
  have hleftMean : leftMean ∈ positiveMassMeanSet left := by
    rw [max_g9_convex_03_relativeInterior left hleft]
    exact hleftMeanInterior
  have hrightMean : rightMean ∈ positiveMassMeanSet right := by
    rw [max_g9_convex_03_relativeInterior right hright]
    exact hrightMeanInterior
  refine ⟨⟨leftMean, rightMean⟩, ⟨hleftMean, hrightMean⟩, ?_⟩
  change rightMean - leftMean = response
  rw [hresponseDecomposition, ← hremainderValue]
  dsimp [leftMean, rightMean]
  module

/-- **MAX-G9.CONVEX.03**, exact-attainment clause.  Strictly positive
independent masses realize exactly the intrinsic interior of the closed
convex-hull response envelope. -/
theorem max_g9_convex_03_response_relativeInterior
    (left right : Finset E) (hleft : left.Nonempty)
    (hright : right.Nonempty) :
    positiveMassResponseSet left right =
      intrinsicInterior ℝ (convexHullResponseEnvelope left right) := by
  exact Set.Subset.antisymm
    (positiveMassResponseSet_subset_intrinsicInterior_envelope
      left right hleft hright)
    (intrinsicInterior_envelope_subset_positiveMassResponseSet
      left right hleft hright)

/-- **MAX-G9.CONVEX.03**, complete response-equality clause.  For nonempty
finite fibres, two arbitrary-positive-mass response systems have exactly the
same attainable first-order responses if and only if their closed convex-hull
response envelopes are equal. -/
theorem max_g9_positiveMassResponseSet_eq_iff_envelope_eq
    (leftOne rightOne leftTwo rightTwo : Finset E)
    (hleftOne : leftOne.Nonempty) (hrightOne : rightOne.Nonempty)
    (hleftTwo : leftTwo.Nonempty) (hrightTwo : rightTwo.Nonempty) :
    positiveMassResponseSet leftOne rightOne =
        positiveMassResponseSet leftTwo rightTwo ↔
      convexHullResponseEnvelope leftOne rightOne =
        convexHullResponseEnvelope leftTwo rightTwo := by
  constructor
  · intro hresponses
    have hclosures := congrArg closure hresponses
    rw [max_g9_convex_03_closed_envelope leftOne rightOne
        hleftOne hrightOne,
      max_g9_convex_03_closed_envelope leftTwo rightTwo
        hleftTwo hrightTwo] at hclosures
    exact hclosures
  · intro henvelopes
    rw [max_g9_convex_03_response_relativeInterior leftOne rightOne
        hleftOne hrightOne,
      max_g9_convex_03_response_relativeInterior leftTwo rightTwo
        hleftTwo hrightTwo,
      henvelopes]

/-- Nonnegative polar of a response set, represented by continuous linear
directions whose value is nonnegative on every response. -/
def nonnegativePolar (responses : Set E) : Set (E →L[ℝ] ℝ) :=
  {direction | ∀ response ∈ responses, 0 ≤ direction response}

/-- Qualitative robust-sign directions for an arbitrary-positive-mass
response system. -/
def positiveMassRobustSignDirections (left right : Finset E) :
    Set (E →L[ℝ] ℝ) :=
  nonnegativePolar (positiveMassResponseSet left right)

/-- **MAX-G9.CONVEX.03**, robust-sign clause.  Testing nonnegative response
in every strictly-positive-mass realization gives exactly the nonnegative
polar of the closed response envelope.  Boundary responses add no new
qualitative sign condition because continuous directions extend across the
closure. -/
theorem max_g9_robustSignDirections_eq_nonnegativePolar_envelope
    (left right : Finset E) (hleft : left.Nonempty)
    (hright : right.Nonempty) :
    positiveMassRobustSignDirections left right =
      nonnegativePolar (convexHullResponseEnvelope left right) := by
  ext direction
  constructor
  · intro hdirection
    intro response hresponse
    have hhalfspaceClosed :
        IsClosed {point : E | 0 ≤ direction point} :=
      isClosed_le continuous_const direction.continuous
    have hclosureSubset :
        closure (positiveMassResponseSet left right) ⊆
          {point : E | 0 ≤ direction point} :=
      closure_minimal hdirection hhalfspaceClosed
    rw [max_g9_convex_03_closed_envelope left right hleft hright]
      at hclosureSubset
    exact hclosureSubset hresponse
  · intro hdirection response hresponse
    exact hdirection response
      (positiveMassResponseSet_subset_envelope left right hresponse)

end ResponseRelativeInterior

end PhonologicalCalculus.MaxEnt
