import PhonologicalCalculus.MaxEnt.ExactCore

/-!
Exact ordered-field reconstruction of the Basic Syllable live MaxEnt cone.

The sixteen entries below are the registered factorized cross-product margins
in `formal/proofs/maxent/MAX-G6.exact-witness.json`, in witness order.
Keeping the full list makes the finite left side of MAX-G6.CONE.02 inspectable
rather than defining it to be the two-facet right side.
-/

namespace PhonologicalCalculus.MaxEnt

section BasicSyllableCone

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- First irredundant Basic Syllable live-cone facet. -/
def basicSyllableFacetD {R : Type*} [CommRing R] (b c d : R) : R :=
  d - b ^ 2 * c

/-- Second irredundant Basic Syllable live-cone facet. -/
def basicSyllableFacetC {R : Type*} [CommRing R] (a c d : R) : R :=
  c - a ^ 2 * d

/-- The sixteen exact factorized live polynomial-order margins, in the order
of the public exact witness.  Repeated entries correspond to distinct
categorical implications with the same polynomial margin. -/
def basicSyllableLiveMargins {R : Type*} [CommRing R]
    (a b c d : R) : List R :=
  [
    b * (1 + a * d) * (1 - c * d),
    (1 + a * d) * basicSyllableFacetD b c d,
    a * (1 + b * c) * (1 - c * d),
    (1 + b * c) * basicSyllableFacetC a c d,
    (1 - c * d) * (a * b + b * c + a * d + a * b * c * d),
    a * (b + d) * (1 - c * d),
    b * (a + c) * (1 - c * d),
    a * (b + d) * (1 - c * d) +
      c * (1 + a * d) * basicSyllableFacetD b c d,
    a * (b + d) * (1 - c * d),
    (a + c) * basicSyllableFacetD b c d,
    a * b * (1 - c * d) + b * c * (1 - a ^ 2 * d ^ 2) +
      d * basicSyllableFacetC a c d,
    (b + d) * basicSyllableFacetC a c d,
    b * (a + c) * (1 - c * d),
    (1 - a * b) * (b * c + a * d + c * d + a * b * c * d),
    (b + d) * basicSyllableFacetC a c d,
    (a + c) * basicSyllableFacetD b c d
  ]

/-- All sixteen registered live orders hold exactly when every registered
margin is nonnegative. -/
def basicSyllableAllLiveOrders (a b c d : K) : Prop :=
  (basicSyllableLiveMargins a b c d).Forall fun margin => 0 ≤ margin

/-- The registered live margin ledger contains sixteen entries. -/
theorem basicSyllableLiveMargins_length {R : Type*} [CommRing R]
    (a b c d : R) :
    (basicSyllableLiveMargins a b c d).length = 16 := by
  rfl

/-- **MAX-G6.CONE.02**.  On the positive unit cube, all sixteen exact Basic
Syllable live polynomial orders hold if and only if the two registered facet
inequalities hold. -/
theorem max_g6_cone_02 :
    ∀ a b c d : K,
      0 < a → a ≤ 1 → 0 < b → b ≤ 1 →
      0 < c → c ≤ 1 → 0 < d → d ≤ 1 →
      (basicSyllableAllLiveOrders a b c d ↔
        (0 ≤ basicSyllableFacetD b c d ∧
          0 ≤ basicSyllableFacetC a c d)) := by
  intro a b c d ha ha1 hb hb1 hc hc1 hd hd1
  have ha0 : 0 ≤ a := ha.le
  have hb0 : 0 ≤ b := hb.le
  have hc0 : 0 ≤ c := hc.le
  have hd0 : 0 ≤ d := hd.le
  have hcd : 0 ≤ 1 - c * d := by nlinarith [mul_le_mul hc0 hd1, mul_le_mul hd0 hc1]
  have hab : 0 ≤ 1 - a * b := by nlinarith [mul_le_mul ha0 hb1, mul_le_mul hb0 ha1]
  have ha2d2 : 0 ≤ 1 - a ^ 2 * d ^ 2 := by
    have ha2 : a ^ 2 ≤ 1 := by nlinarith [sq_nonneg (1 - a)]
    have hd2 : d ^ 2 ≤ 1 := by nlinarith [sq_nonneg (1 - d)]
    have ha20 : 0 ≤ a ^ 2 := sq_nonneg a
    have hd20 : 0 ≤ d ^ 2 := sq_nonneg d
    nlinarith [mul_le_mul ha20 hd2, mul_le_mul hd20 ha2]
  constructor
  · intro hall
    simp only [basicSyllableAllLiveOrders, basicSyllableLiveMargins,
      List.forall_cons] at hall
    rcases hall with
      ⟨_, hFacetDProduct, _, hFacetCProduct, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
    constructor
    · exact nonneg_of_mul_nonneg_right hFacetDProduct (by positivity)
    · exact nonneg_of_mul_nonneg_right hFacetCProduct (by positivity)
  · rintro ⟨hFacetD, hFacetC⟩
    simp only [basicSyllableAllLiveOrders, basicSyllableLiveMargins,
      List.forall_cons]
    constructor
    · positivity
    constructor
    · exact mul_nonneg (by positivity) hFacetD
    constructor
    · positivity
    constructor
    · exact mul_nonneg (by positivity) hFacetC
    constructor
    · positivity
    constructor
    · positivity
    constructor
    · positivity
    constructor
    · exact add_nonneg (by positivity)
        (mul_nonneg (mul_nonneg hc0 (by positivity)) hFacetD)
    constructor
    · positivity
    constructor
    · exact mul_nonneg (by positivity) hFacetD
    constructor
    · exact add_nonneg (add_nonneg (by positivity) (by positivity))
        (mul_nonneg hd0 hFacetC)
    constructor
    · exact mul_nonneg (by positivity) hFacetC
    constructor
    · positivity
    constructor
    · exact mul_nonneg hab (by positivity)
    constructor
    · exact mul_nonneg (by positivity) hFacetC
    constructor
    · exact mul_nonneg (by positivity) hFacetD
    · trivial

/-- At the registered interior point `(1/2,1/2,1/2,1/2)`, both facet slacks
are exactly `3/8`; in particular the live cone has strict interior. -/
theorem basicSyllableRegisteredInterior :
    basicSyllableFacetD (1 / 2 : K) (1 / 2 : K) (1 / 2 : K) = 3 / 8 ∧
    basicSyllableFacetC (1 / 2 : K) (1 / 2 : K) (1 / 2 : K) = 3 / 8 := by
  norm_num [basicSyllableFacetD, basicSyllableFacetC]

end BasicSyllableCone

end PhonologicalCalculus.MaxEnt
