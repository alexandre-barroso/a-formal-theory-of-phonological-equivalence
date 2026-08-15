import PhonologicalCalculus.MaxEnt.ProjectiveResponse
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Convex.Topology

/-!
Arbitrary-positive-mass conditional means and response envelopes.

For a nonempty finite point configuration, normalized positive masses form
the strict standard simplex.  This module proves that the strict simplex is
dense in the closed standard simplex and transports that density through the
finite conditional-mean map.  Hence the closure of the attainable mean set is
exactly the finite convex hull.
-/

namespace PhonologicalCalculus.MaxEnt

open Set

section StrictSimplex

variable (I : Type*) [Fintype I]

/-- Strict standard simplex: every labelled mass is positive and the masses
sum to one. -/
def strictSimplex : Set (I → ℝ) :=
  {weight | (∀ i, 0 < weight i) ∧ ∑ i, weight i = 1}

/-- Uniform point of the strict simplex. -/
noncomputable def uniformSimplexPoint [Nonempty I] : I → ℝ :=
  fun _ ↦ 1 / Fintype.card I

/-- The strict simplex is contained in the standard simplex. -/
theorem strictSimplex_subset_stdSimplex :
    strictSimplex I ⊆ stdSimplex ℝ I := by
  rintro weight ⟨hpositive, hsum⟩
  exact ⟨fun i ↦ (hpositive i).le, hsum⟩

/-- The uniform weight vector lies in the strict simplex. -/
theorem uniformSimplexPoint_mem [Nonempty I] :
    uniformSimplexPoint I ∈ strictSimplex I := by
  have hcard : 0 < Fintype.card I := Fintype.card_pos
  constructor
  · intro i
    exact div_pos zero_lt_one (by exact_mod_cast hcard)
  · simp [uniformSimplexPoint, hcard.ne']

/-- Every closed-simplex point is approached by mixing it with the uniform
strict point. -/
theorem stdSimplex_subset_closure_strictSimplex [Nonempty I] :
    stdSimplex ℝ I ⊆ closure (strictSimplex I) := by
  intro weight hweight
  let uniform : I → ℝ := uniformSimplexPoint I
  let path : ℝ → I → ℝ :=
    fun t ↦ (1 - t) • weight + t • uniform
  have huniform : uniform ∈ strictSimplex I := uniformSimplexPoint_mem I
  have hpath : path '' Set.Ioo (0 : ℝ) 1 ⊆ strictSimplex I := by
    rintro candidate ⟨t, ht, rfl⟩
    constructor
    · intro i
      dsimp [path]
      have hleft : 0 ≤ (1 - t) * weight i :=
        mul_nonneg (sub_nonneg.mpr ht.2.le) (hweight.1 i)
      have hright : 0 < t * uniform i :=
        mul_pos ht.1 (huniform.1 i)
      linarith
    · dsimp [path]
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [hweight.2, huniform.2]
      ring
  have hcontinuous : Continuous path := by
    dsimp [path]
    fun_prop
  have hzero : (0 : ℝ) ∈ closure (Set.Ioo (0 : ℝ) 1) := by
    rw [closure_Ioo zero_ne_one]
    norm_num
  have himage : path 0 ∈ closure (path '' Set.Ioo (0 : ℝ) 1) :=
    image_closure_subset_closure_image hcontinuous ⟨0, hzero, rfl⟩
  have := closure_mono hpath himage
  simpa [path] using this

/-- The closure of the strict simplex is exactly the standard simplex. -/
theorem closure_strictSimplex_eq_stdSimplex [Nonempty I] :
    closure (strictSimplex I) = stdSimplex ℝ I := by
  apply Set.Subset.antisymm
  · exact closure_minimal (strictSimplex_subset_stdSimplex I)
      (isClosed_stdSimplex ℝ I)
  · exact stdSimplex_subset_closure_strictSimplex I

end StrictSimplex

section ConditionalMeans

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Linear conditional-mean map for a finite set of violation rows. -/
def finiteMeanMap (points : Finset E) :
    (points → ℝ) →ₗ[ℝ] E :=
  ∑ point : points,
    (LinearMap.proj (R := ℝ) point).smulRight point.1

/-- Attainable conditional means under independently variable positive
candidate masses.  Scaling all masses has already been normalized away. -/
def positiveMassMeanSet (points : Finset E) : Set E :=
  finiteMeanMap points '' strictSimplex points

omit [FiniteDimensional ℝ E] in
/-- The conditional-mean map evaluates as the expected finite weighted sum. -/
theorem finiteMeanMap_apply (points : Finset E)
    (weight : points → ℝ) :
    finiteMeanMap points weight = ∑ point : points, weight point • point.1 := by
  simp [finiteMeanMap]

omit [FiniteDimensional ℝ E] in
/-- Every attainable positive-mass conditional mean belongs to the convex
hull of the declared finite row set. -/
theorem positiveMassMeanSet_subset_convexHull (points : Finset E) :
    positiveMassMeanSet points ⊆ convexHull ℝ (points : Set E) := by
  rintro mean ⟨weight, hweight, rfl⟩
  rw [finiteMeanMap_apply]
  exact mem_convexHull_of_exists_fintype weight (fun point : points ↦ point.1)
    (fun i ↦ (hweight.1 i).le) hweight.2 (fun i ↦ i.2) rfl

omit [FiniteDimensional ℝ E] in
/-- The convex hull is the image of the closed standard simplex under the
same conditional-mean map. -/
theorem convexHull_eq_finiteMeanMap_image (points : Finset E) :
    convexHull ℝ (points : Set E) =
      finiteMeanMap points '' stdSimplex ℝ points := by
  ext mean
  constructor
  · intro hmean
    rw [Finset.mem_convexHull'] at hmean
    rcases hmean with ⟨weight, hnonneg, hsum, hcenter⟩
    let restricted : points → ℝ := fun point ↦ weight point.1
    refine ⟨restricted, ?_, ?_⟩
    · constructor
      · exact fun point ↦ hnonneg point.1 point.2
      · change ∑ point : points, weight point.1 = 1
        exact (Finset.sum_attach points (fun point ↦ weight point)).trans hsum
    · rw [finiteMeanMap_apply]
      change ∑ point : points, weight point.1 • point.1 = mean
      exact (Finset.sum_attach points
        (fun point ↦ weight point • point)).trans hcenter
  · rintro ⟨weight, hweight, rfl⟩
    rw [finiteMeanMap_apply]
    exact mem_convexHull_of_exists_fintype weight (fun point : points ↦ point.1)
      hweight.1 hweight.2 (fun point ↦ point.2) rfl

omit [FiniteDimensional ℝ E] in
/-- The closure of arbitrary-positive-mass conditional means is exactly the
convex hull of the finite violation-row configuration. -/
theorem closure_positiveMassMeanSet_eq_convexHull
    (points : Finset E) (hpoints : points.Nonempty) :
    closure (positiveMassMeanSet points) = convexHull ℝ (points : Set E) := by
  letI : Nonempty points := hpoints.to_subtype
  apply Set.Subset.antisymm
  · exact closure_minimal (positiveMassMeanSet_subset_convexHull points)
      (points.finite_toSet.isClosed_convexHull ℝ)
  · rw [convexHull_eq_finiteMeanMap_image,
      ← closure_strictSimplex_eq_stdSimplex points]
    exact image_closure_subset_closure_image
      (finiteMeanMap points).continuous_of_finiteDimensional

/-- Difference image of two sets in a common response space. -/
def responseDifference (left right : Set E) : Set E :=
  (fun pair : E × E ↦ pair.2 - pair.1) '' (left ×ˢ right)

/-- Attainable first-order response set under arbitrary positive masses in
each of two nonempty consequence fibres. -/
def positiveMassResponseSet (left right : Finset E) : Set E :=
  responseDifference (positiveMassMeanSet left) (positiveMassMeanSet right)

/-- Closed convex-hull response envelope. -/
def convexHullResponseEnvelope (left right : Finset E) : Set E :=
  responseDifference (convexHull ℝ (left : Set E))
    (convexHull ℝ (right : Set E))

omit [FiniteDimensional ℝ E] in
/-- The positive-mass response set lies in the convex-hull difference
envelope. -/
theorem positiveMassResponseSet_subset_envelope (left right : Finset E) :
    positiveMassResponseSet left right ⊆
      convexHullResponseEnvelope left right := by
  rintro response ⟨pair, ⟨hleft, hright⟩, rfl⟩
  exact ⟨pair,
    ⟨positiveMassMeanSet_subset_convexHull left hleft,
      positiveMassMeanSet_subset_convexHull right hright⟩, rfl⟩

omit [FiniteDimensional ℝ E] in
/-- The finite convex-hull response envelope is compact and therefore closed. -/
theorem isCompact_convexHullResponseEnvelope (left right : Finset E) :
    IsCompact (convexHullResponseEnvelope left right) := by
  apply IsCompact.image
  · exact (left.finite_toSet.isCompact_convexHull ℝ).prod
      (right.finite_toSet.isCompact_convexHull ℝ)
  · fun_prop

omit [FiniteDimensional ℝ E] in
/-- **MAX-G9.CONVEX.03**, closed-envelope clause.  For nonempty finite
violation-row configurations, the closure of the attainable arbitrary-
positive-mass response set is exactly the Minkowski difference of their
convex hulls. -/
theorem max_g9_convex_03_closed_envelope
    (left right : Finset E) (hleft : left.Nonempty) (hright : right.Nonempty) :
    closure (positiveMassResponseSet left right) =
      convexHullResponseEnvelope left right := by
  apply Set.Subset.antisymm
  · exact closure_minimal (positiveMassResponseSet_subset_envelope left right)
      (isCompact_convexHullResponseEnvelope left right).isClosed
  · rw [positiveMassResponseSet, convexHullResponseEnvelope,
      ← closure_positiveMassMeanSet_eq_convexHull left hleft,
      ← closure_positiveMassMeanSet_eq_convexHull right hright]
    rw [responseDifference, responseDifference, ← closure_prod_eq]
    exact image_closure_subset_closure_image (by fun_prop)

end ConditionalMeans

end PhonologicalCalculus.MaxEnt
