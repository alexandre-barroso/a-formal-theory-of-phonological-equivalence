import Mathlib.Algebra.Polynomial.RuleOfSigns
import Mathlib.Algebra.Polynomial.EraseLead
import Mathlib.Data.Real.Basic
import PhonologicalCalculus.MaxEnt.ResponseQuotientGerm
import Mathlib.Tactic

/-!
# Finite-MaxEnt contact--phase capacity

Along a commensurate weight ray, a collected finite-MaxEnt comparison is a
real polynomial in the positive activity variable.  This module proves the
exact contact--phase budget for that carrier and proves the sharp construction
for every finite packet of positive contact roots, including repeated roots.

For arbitrary distinct real projected exponents, the module states the precise
Rolle-with-multiplicity foundation contract and proves the project-specific
normalization, differentiation, support reduction, and induction that yield
the universal `q - 1` bound.  The foundation contract remains an explicit
It is passed as a theorem parameter rather than added to Lean's trusted base.
The balanced strict-interior
constructor supplies the exact contact, reversal, balance, slice, mass, and
normalized-probability bridges used by the registered result.
-/

namespace PhonologicalCalculus.MaxEnt

open Polynomial

/-- The number of uncancelled activity slices in a polynomial comparison. -/
def activitySliceCount (p : ℝ[X]) : ℕ :=
  p.support.card

/-- A packet records roots with their full registered multiplicities. -/
def registeredContactPacket (contacts reversals : Finset ℝ)
    (multiplicity : ℝ → ℕ) : Multiset ℝ :=
  (∑ x ∈ contacts, Multiset.replicate (multiplicity x) x) + reversals.1

@[simp]
theorem card_registeredContactPacket (contacts reversals : Finset ℝ)
    (multiplicity : ℝ → ℕ) :
    (registeredContactPacket contacts reversals multiplicity).card =
      (∑ x ∈ contacts, multiplicity x) + reversals.card := by
  simp [registeredContactPacket, Multiset.card_sum]

theorem count_replicate_finset_sum (contacts : Finset ℝ)
    (multiplicity : ℝ → ℕ) (x : ℝ) :
    (∑ y ∈ contacts, Multiset.replicate (multiplicity y) y).count x =
      if x ∈ contacts then multiplicity x else 0 := by
  classical
  induction contacts using Finset.induction_on with
  | empty => simp
  | @insert a contacts ha ih =>
      rw [Finset.sum_insert ha, Multiset.count_add, ih]
      by_cases hxa : x = a
      · subst x
        simp [ha]
      · have hxmem : x ∉ Multiset.replicate (multiplicity a) a := by
          intro hmem
          exact hxa (Multiset.mem_replicate.mp hmem).2
        simp [hxa, hxmem]

/-- A registered contact occurs in its packet with exactly the declared
multiplicity when contacts and reversal roots are disjoint. -/
theorem count_registeredContactPacket_of_mem_contacts
    {contacts reversals : Finset ℝ} {multiplicity : ℝ → ℕ}
    (hdisjoint : Disjoint contacts reversals) {x : ℝ}
    (hx : x ∈ contacts) :
    (registeredContactPacket contacts reversals multiplicity).count x =
      multiplicity x := by
  classical
  have hxnot : x ∉ reversals :=
    Finset.disjoint_left.mp hdisjoint hx
  simp [registeredContactPacket, count_replicate_finset_sum, hx, hxnot]

/-- A registered reversal occurs once in its packet when the two root sets
are disjoint. -/
theorem count_registeredContactPacket_of_mem_reversals
    {contacts reversals : Finset ℝ} {multiplicity : ℝ → ℕ}
    (hdisjoint : Disjoint contacts reversals) {x : ℝ}
    (hx : x ∈ reversals) :
    (registeredContactPacket contacts reversals multiplicity).count x = 1 := by
  classical
  have hxnot : x ∉ contacts :=
    Finset.disjoint_right.mp hdisjoint hx
  rw [registeredContactPacket, Multiset.count_add,
    count_replicate_finset_sum]
  rw [if_neg hxnot]
  simpa using Multiset.count_eq_one_of_mem reversals.nodup hx

/-- A polynomial with zero constant coefficient has at most one activity
slice for each positive exponent up to its degree. -/
theorem activitySliceCount_le_natDegree_of_coeff_zero
    {p : ℝ[X]} (hcoeff : p.coeff 0 = 0) :
    activitySliceCount p ≤ p.natDegree := by
  have hsubset :
      p.support ⊆ (Finset.range (p.natDegree + 1)).erase 0 := by
    intro n hn
    apply Finset.mem_erase.mpr
    constructor
    · intro hn0
      subst n
      exact (Polynomial.mem_support_iff.mp hn) hcoeff
    · exact Polynomial.supp_subset_range_natDegree_succ hn
  calc
    activitySliceCount p = p.support.card := rfl
    _ ≤ ((Finset.range (p.natDegree + 1)).erase 0).card :=
      Finset.card_le_card hsubset
    _ = p.natDegree := by simp

/-- The number of coefficient sign variations never exceeds the number of
nonzero activity slices minus one. -/
theorem signVariations_le_activitySliceCount_sub_one (p : ℝ[X]) :
    p.signVariations ≤ activitySliceCount p - 1 := by
  generalize hcard : activitySliceCount p = n
  induction n using Nat.strong_induction_on generalizing p with
  | h n ih =>
      by_cases hp : p = 0
      · subst p
        simp
      by_cases herase : p.eraseLead = 0
      · have hmono :
            Polynomial.monomial p.natDegree p.leadingCoeff = p := by
          simpa [herase] using
            (Polynomial.eraseLead_add_monomial_natDegree_leadingCoeff p)
        have hsupport : activitySliceCount p = 1 := by
          simpa [activitySliceCount] using
            Polynomial.card_support_eq_one_of_eraseLead_eq_zero hp herase
        have hsign : p.signVariations = 0 := by
          rw [← hmono, Polynomial.signVariations_monomial]
        rw [hsign]
        have hn : n = 1 := hcard.symm.trans hsupport
        omega
      · have hsmaller :
            activitySliceCount p.eraseLead < n := by
          rw [← hcard]
          exact Polynomial.eraseLead_support_card_lt hp
        have hih :
            p.eraseLead.signVariations ≤
              activitySliceCount p.eraseLead - 1 :=
          ih (activitySliceCount p.eraseLead) hsmaller p.eraseLead rfl
        have hstep := Polynomial.signVariations_le_eraseLead_succ p
        have hsupport :
            activitySliceCount p.eraseLead + 1 = activitySliceCount p := by
          simpa [activitySliceCount] using
            Polynomial.card_support_eraseLead_add_one hp
        have hpositive : 0 < activitySliceCount p.eraseLead := by
          rw [activitySliceCount]
          exact Nat.pos_of_ne_zero fun hzero =>
            herase (Polynomial.card_support_eq_zero.mp hzero)
        omega

/-- A registered positive root packet cannot contain more copies than the
positive roots of the polynomial. -/
theorem registeredPacket_card_le_positiveRoots
    {p : ℝ[X]} {packet : Multiset ℝ}
    (hpacket : packet ≤ p.roots)
    (hpositive : ∀ x ∈ packet, 0 < x) :
    packet.card ≤ p.roots.countP (0 < ·) := by
  rw [Multiset.countP_eq_card_filter]
  exact Multiset.card_le_card ((Multiset.le_filter).2 ⟨hpacket, hpositive⟩)

/-- Polynomial contact--phase capacity.  Every registered contact copy and
every additional reversal root spends one sign-variation unit. -/
theorem polynomialContactPhaseCapacity
    {p : ℝ[X]} {packet : Multiset ℝ}
    (hpacket : packet ≤ p.roots)
    (hpositive : ∀ x ∈ packet, 0 < x) :
    packet.card ≤ activitySliceCount p - 1 := by
  calc
    packet.card ≤ p.roots.countP (0 < ·) :=
      registeredPacket_card_le_positiveRoots hpacket hpositive
    _ ≤ p.signVariations :=
      Polynomial.roots_countP_pos_le_signVariations p
    _ ≤ activitySliceCount p - 1 :=
      signVariations_le_activitySliceCount_sub_one p

/-- **MAX-G8.CHEBYSHEV.04**, polynomial activity branch.  Descartes' rule
gives the complete positive-root budget, counted with multiplicity, and the
support lemma converts it to the number of uncancelled slices. -/
theorem max_g8_chebyshev_04_polynomial (p : ℝ[X]) :
    p.roots.countP (0 < ·) ≤ p.signVariations ∧
    p.signVariations ≤ activitySliceCount p - 1 ∧
    p.roots.countP (0 < ·) ≤ activitySliceCount p - 1 := by
  have hdescartes := Polynomial.roots_countP_pos_le_signVariations p
  have hsupport := signVariations_le_activitySliceCount_sub_one p
  exact ⟨hdescartes, hsupport, hdescartes.trans hsupport⟩

/-- A strict sign reversal of a polynomial comparison contains a root in the
open interval. -/
theorem polynomial_strictReversal_has_root
    {p : ℝ[X]} {a b : ℝ} (hab : a < b)
    (hreversal : p.eval a * p.eval b < 0) :
    ∃ x ∈ Set.Ioo a b, p.IsRoot x := by
  rcases (mul_neg_iff.mp hreversal) with h | h
  · have hzero : (0 : ℝ) ∈ Set.Icc (p.eval b) (p.eval a) :=
      ⟨h.2.le, h.1.le⟩
    rcases intermediate_value_Icc' hab.le p.continuousOn hzero with
      ⟨x, hx, hxeval⟩
    refine ⟨x, ⟨?_, ?_⟩, ?_⟩
    · exact lt_of_le_of_ne hx.1 fun hxa => by
        subst x
        linarith
    · exact lt_of_le_of_ne hx.2 fun hxb => by
        subst x
        linarith
    · exact hxeval
  · have hzero : (0 : ℝ) ∈ Set.Icc (p.eval a) (p.eval b) :=
      ⟨h.1.le, h.2.le⟩
    rcases intermediate_value_Icc hab.le p.continuousOn hzero with
      ⟨x, hx, hxeval⟩
    refine ⟨x, ⟨?_, ?_⟩, ?_⟩
    · exact lt_of_le_of_ne hx.1 fun hxa => by
        subst x
        linarith
    · exact lt_of_le_of_ne hx.2 fun hxb => by
        subst x
        linarith
    · exact hxeval

/-- **MAX-G8.CAPACITY.02**, polynomial activity branch.  Full contact
multiplicities and additional reversal roots share the same finite slice
budget. -/
theorem max_g8_capacity_02_polynomial
    {p : ℝ[X]} (contacts reversals : Finset ℝ)
    (multiplicity : ℝ → ℕ)
    (_hdisjoint : Disjoint contacts reversals)
    (_hmultiplicity : ∀ x ∈ contacts, 0 < multiplicity x)
    (hpacket : registeredContactPacket contacts reversals multiplicity ≤
      p.roots)
    (hcontacts : ∀ x ∈ contacts, 0 < x)
    (hreversals : ∀ x ∈ reversals, 0 < x) :
    (∑ x ∈ contacts, multiplicity x) + reversals.card ≤
      activitySliceCount p - 1 := by
  rw [← card_registeredContactPacket]
  apply polynomialContactPhaseCapacity hpacket
  intro x hx
  rw [registeredContactPacket, Multiset.mem_add] at hx
  rcases hx with hx | hx
  · have hxsum :
        ∃ y ∈ contacts, x ∈ Multiset.replicate (multiplicity y) y :=
      Multiset.mem_sum.mp hx
    obtain ⟨y, hy, hxy⟩ := hxsum
    exact (Multiset.mem_replicate.mp hxy).2 ▸ hcontacts y hy
  · exact hreversals x hx

/-- Named-candidate probability when `R` is the total competitor-to-named
mass ratio. -/
noncomputable def namedCandidateProbability (R : ℝ) : ℝ :=
  1 / (1 + R)

/-- Probability orientation for the separate-input construction.  The
positive denominator preserves the zeros and signs of `R_A - R_B`. -/
theorem max_g8_probability_orientation
    {RA RB : ℝ} (hRA : 0 ≤ RA) (hRB : 0 ≤ RB) :
    namedCandidateProbability RB - namedCandidateProbability RA =
        (RA - RB) / ((1 + RA) * (1 + RB)) ∧
      0 < (1 + RA) * (1 + RB) ∧
      (namedCandidateProbability RB - namedCandidateProbability RA = 0 ↔
        RA - RB = 0) ∧
      (0 < namedCandidateProbability RB - namedCandidateProbability RA ↔
        0 < RA - RB) := by
  have hA : 0 < 1 + RA := by linarith
  have hB : 0 < 1 + RB := by linarith
  have hden : 0 < (1 + RA) * (1 + RB) := mul_pos hA hB
  have hid :
      namedCandidateProbability RB - namedCandidateProbability RA =
        (RA - RB) / ((1 + RA) * (1 + RB)) := by
    unfold namedCandidateProbability
    field_simp [ne_of_gt hA, ne_of_gt hB]
    ring
  refine ⟨hid, hden, ?_, ?_⟩
  · rw [hid, div_eq_zero_iff]
    simp [ne_of_gt hden]
  · rw [hid, div_pos_iff]
    constructor
    · rintro (h | h)
      · exact h.1
      · exact (not_lt_of_ge hden.le h.2).elim
    · intro h
      exact Or.inl ⟨h, hden⟩

/-- The sharp activity polynomial for a packet of positive roots.  The extra
factor `X` removes the constant slice without adding a positive root. -/
noncomputable def sharpContactPolynomial (packet : Multiset ℝ) : ℝ[X] :=
  X * (packet.map fun x => X - C x).prod

theorem sharpContactPolynomial_factor_ne_zero (packet : Multiset ℝ) :
    (packet.map fun x : ℝ => X - C x).prod ≠ 0 := by
  apply Multiset.prod_ne_zero
  simp [Polynomial.X_sub_C_ne_zero]

theorem sharpContactPolynomial_ne_zero (packet : Multiset ℝ) :
    sharpContactPolynomial packet ≠ 0 := by
  exact mul_ne_zero Polynomial.X_ne_zero
    (sharpContactPolynomial_factor_ne_zero packet)

theorem sharpContactPolynomial_roots (packet : Multiset ℝ) :
    (sharpContactPolynomial packet).roots = {0} + packet := by
  rw [sharpContactPolynomial,
    Polynomial.roots_mul (sharpContactPolynomial_ne_zero packet),
    Polynomial.roots_X,
    Polynomial.roots_multiset_prod_X_sub_C]

theorem sharpContactPolynomial_natDegree (packet : Multiset ℝ) :
    (sharpContactPolynomial packet).natDegree = packet.card + 1 := by
  rw [sharpContactPolynomial,
    Polynomial.natDegree_X_mul (sharpContactPolynomial_factor_ne_zero packet),
    Polynomial.natDegree_multiset_prod_X_sub_C_eq_card]

theorem sharpContactPolynomial_coeff_zero (packet : Multiset ℝ) :
    (sharpContactPolynomial packet).coeff 0 = 0 := by
  rw [Polynomial.coeff_zero_eq_eval_zero, sharpContactPolynomial,
    Polynomial.eval_mul, Polynomial.eval_X]
  simp

theorem sharpContactPolynomial_positiveRoots
    {packet : Multiset ℝ} (hpositive : ∀ x ∈ packet, 0 < x) :
    (sharpContactPolynomial packet).roots.countP (0 < ·) = packet.card := by
  rw [sharpContactPolynomial_roots, Multiset.countP_add]
  have hpacket : packet.countP (0 < ·) = packet.card := by
    rw [Multiset.countP_eq_card_filter,
      Multiset.filter_eq_self.mpr hpositive]
  rw [hpacket]
  simp [Multiset.countP_eq_card_filter]

/-- Every finite positive root packet attains the contact--phase bound.  The
number of slices is exactly one more than the packet's total multiplicity,
and the number of sign variations is exactly the packet's cardinality. -/
theorem sharpContactPolynomial_exact
    {packet : Multiset ℝ} (hpositive : ∀ x ∈ packet, 0 < x) :
    activitySliceCount (sharpContactPolynomial packet) = packet.card + 1 ∧
    (sharpContactPolynomial packet).signVariations = packet.card ∧
    (sharpContactPolynomial packet).roots = {0} + packet := by
  have hrootCount :
      (sharpContactPolynomial packet).roots.countP (0 < ·) = packet.card :=
    sharpContactPolynomial_positiveRoots hpositive
  have hdescartes :
      packet.card ≤ (sharpContactPolynomial packet).signVariations := by
    rw [← hrootCount]
    exact Polynomial.roots_countP_pos_le_signVariations _
  have hsign :
      (sharpContactPolynomial packet).signVariations ≤
        activitySliceCount (sharpContactPolynomial packet) - 1 :=
    signVariations_le_activitySliceCount_sub_one _
  have hsupport :
      activitySliceCount (sharpContactPolynomial packet) ≤ packet.card + 1 := by
    rw [← sharpContactPolynomial_natDegree]
    exact activitySliceCount_le_natDegree_of_coeff_zero
      (sharpContactPolynomial_coeff_zero packet)
  have hslicePositive :
      0 < activitySliceCount (sharpContactPolynomial packet) := by
    rw [activitySliceCount]
    exact Nat.pos_of_ne_zero fun hzero =>
      (sharpContactPolynomial_ne_zero packet)
        (Polynomial.card_support_eq_zero.mp hzero)
  constructor
  · omega
  · constructor
    · omega
    · exact sharpContactPolynomial_roots packet

/-- **MAX-G8.SHARP.01**, polynomial activity branch.  Every declared
allocation of positive contact multiplicities and disjoint positive reversal
roots has a polynomial comparison that attains the exact budget. -/
theorem max_g8_sharp_01_polynomial
    (contacts reversals : Finset ℝ) (multiplicity : ℝ → ℕ)
    (hdisjoint : Disjoint contacts reversals)
    (_hmultiplicity : ∀ x ∈ contacts, 0 < multiplicity x)
    (hcontacts : ∀ x ∈ contacts, 0 < x)
    (hreversals : ∀ x ∈ reversals, 0 < x) :
    let packet := registeredContactPacket contacts reversals multiplicity
    activitySliceCount (sharpContactPolynomial packet) =
        1 + (∑ x ∈ contacts, multiplicity x) + reversals.card ∧
      (sharpContactPolynomial packet).signVariations =
        (∑ x ∈ contacts, multiplicity x) + reversals.card ∧
      (sharpContactPolynomial packet).roots = {0} + packet ∧
      (∀ x ∈ contacts,
        (sharpContactPolynomial packet).roots.count x = multiplicity x) ∧
      (∀ x ∈ reversals,
        (sharpContactPolynomial packet).roots.count x = 1) := by
  dsimp only
  have hpositive :
      ∀ x ∈ registeredContactPacket contacts reversals multiplicity,
        0 < x := by
    intro x hx
    rw [registeredContactPacket, Multiset.mem_add] at hx
    rcases hx with hx | hx
    · have hxsum :
          ∃ y ∈ contacts, x ∈ Multiset.replicate (multiplicity y) y :=
        Multiset.mem_sum.mp hx
      obtain ⟨y, hy, hxy⟩ := hxsum
      exact (Multiset.mem_replicate.mp hxy).2 ▸ hcontacts y hy
    · exact hreversals x hx
  rcases sharpContactPolynomial_exact hpositive with
    ⟨hslices, hsigns, hroots⟩
  rw [card_registeredContactPacket] at hslices hsigns
  constructor
  · omega
  · constructor
    · exact hsigns
    · constructor
      · exact hroots
      · constructor
        · intro x hx
          rw [hroots, Multiset.count_add]
          have hx0 : x ≠ 0 := ne_of_gt (hcontacts x hx)
          rw [count_registeredContactPacket_of_mem_contacts hdisjoint hx]
          simp [hx0]
        · intro x hx
          rw [hroots, Multiset.count_add]
          have hx0 : x ≠ 0 := ne_of_gt (hreversals x hx)
          rw [count_registeredContactPacket_of_mem_reversals hdisjoint hx]
          simp [hx0]

/-- **MAX-G8.BOUNDARY.03**.  A contact matching derivatives through order
`m` has multiplicity `m+1`; adding `r` reversals therefore requires exactly
`m+r+2` slices in the sharp construction.  Registering one additional
balance root requires exactly `m+r+3`. -/
theorem max_g8_boundary_03 (m r : ℕ) :
    1 + ((m + 1) + r) = m + r + 2 ∧
    1 + (1 + (m + 1) + r) = m + r + 3 := by
  omega

/-- If a polynomial comparison contains the declared packet, its slice count
is at least the sharp minimum. -/
theorem polynomialContactPhase_minimumSlices
    {p : ℝ[X]} {packet : Multiset ℝ}
    (hp : p ≠ 0)
    (hpacket : packet ≤ p.roots)
    (hpositive : ∀ x ∈ packet, 0 < x) :
    packet.card + 1 ≤ activitySliceCount p := by
  have hcapacity := polynomialContactPhaseCapacity hpacket hpositive
  have hslice : 0 < activitySliceCount p := by
    rw [activitySliceCount]
    exact Nat.pos_of_ne_zero fun hzero =>
      hp (Polynomial.card_support_eq_zero.mp hzero)
  omega

/-- The sharp construction realizes the minimum slice count for every
positive packet. -/
theorem polynomialContactPhase_sharpMinimum
    {packet : Multiset ℝ} (hpositive : ∀ x ∈ packet, 0 < x) :
    activitySliceCount (sharpContactPolynomial packet) = packet.card + 1 ∧
    ∀ p : ℝ[X], p ≠ 0 → packet ≤ p.roots →
      packet.card + 1 ≤ activitySliceCount p := by
  constructor
  · exact (sharpContactPolynomial_exact hpositive).1
  · intro p hp hpacket
    exact polynomialContactPhase_minimumSlices hp hpacket hpositive

/-! ## Arbitrary distinct real exponential rates -/

/-- A collected nonzero finite exponential comparison.  Projected exponents
are ordered strictly, so equal rates have already been combined and cancelled;
every retained coefficient is nonzero. -/
structure CollectedDistinctExponentialResponse (q : ℕ) where
  exponent : Fin q → ℝ
  coefficient : Fin q → ℝ
  q_pos : 0 < q
  exponent_strictMono : StrictMono exponent
  coefficient_ne_zero : ∀ i, coefficient i ≠ 0

/-- The response represented by an ordered collected exponential ledger. -/
noncomputable def CollectedDistinctExponentialResponse.response {q : ℕ}
    (data : CollectedDistinctExponentialResponse q) : ℝ → ℝ :=
  finiteExponentialResponse (fun i ↦ -data.exponent i) data.coefficient

/-- A multiset packet is supported by zeros with at least its registered
multiplicity when all derivatives below the local count vanish. -/
def supportsZeroMultiplicity (response : ℝ → ℝ)
    (packet : Multiset ℝ) : Prop :=
  ∀ point, ∀ order, order < packet.count point →
    iteratedDeriv order response point = 0

/-- Every registered point lies strictly inside one declared interval. -/
def packetInsideOpenInterval (packet : Multiset ℝ)
    (left right : ℝ) : Prop :=
  ∀ point ∈ packet, point ∈ Set.Ioo left right

/-- Local contact of at least the declared derivative multiplicity. -/
def responseContactMultiplicityAt (response : ℝ → ℝ)
    (point : ℝ) (multiplicity : ℕ) : Prop :=
  ∀ order, order < multiplicity → iteratedDeriv order response point = 0

/-- A registered strict order reversal contains its zero together with an
explicit pair of opposite-sign witnesses around that zero. -/
def strictResponseReversalAt (response : ℝ → ℝ)
    (point : ℝ) : Prop :=
  response point = 0 ∧
    ∃ left right, left < point ∧ point < right ∧
      response left * response right < 0

/-- Project-specific packet bridge: contact jets contribute their full
multiplicity, while every strict reversal contributes exactly its zeroth-order
zero. -/
theorem registeredContactPacket_supportsZeroMultiplicity
    (response : ℝ → ℝ) (contacts reversals : Finset ℝ)
    (multiplicity : ℝ → ℕ)
    (hdisjoint : Disjoint contacts reversals)
    (hcontacts : ∀ x ∈ contacts,
      responseContactMultiplicityAt response x (multiplicity x))
    (hreversals : ∀ x ∈ reversals, strictResponseReversalAt response x) :
    supportsZeroMultiplicity response
      (registeredContactPacket contacts reversals multiplicity) := by
  intro point order horder
  by_cases hcontact : point ∈ contacts
  · rw [count_registeredContactPacket_of_mem_contacts
      hdisjoint hcontact] at horder
    exact hcontacts point hcontact order horder
  · by_cases hreversal : point ∈ reversals
    · rw [count_registeredContactPacket_of_mem_reversals
        hdisjoint hreversal] at horder
      have horderZero : order = 0 := by omega
      subst order
      simpa [strictResponseReversalAt] using
        (hreversals point hreversal).1
    · have hcount :
          (registeredContactPacket contacts reversals multiplicity).count
              point = 0 := by
        simp [registeredContactPacket, count_replicate_finset_sum,
          hcontact, hreversal]
      omega

/-- Project-specific interval bridge from the two registered root sets to the
multiplicity packet consumed by the analytic theorem. -/
theorem registeredContactPacket_insideOpenInterval
    (contacts reversals : Finset ℝ) (multiplicity : ℝ → ℕ)
    (left right : ℝ)
    (hcontacts : ∀ x ∈ contacts, x ∈ Set.Ioo left right)
    (hreversals : ∀ x ∈ reversals, x ∈ Set.Ioo left right) :
    packetInsideOpenInterval
      (registeredContactPacket contacts reversals multiplicity) left right := by
  intro point hpoint
  rw [registeredContactPacket, Multiset.mem_add] at hpoint
  rcases hpoint with hpoint | hpoint
  · obtain ⟨x, hx, hpointx⟩ := Multiset.mem_sum.mp hpoint
    exact (Multiset.mem_replicate.mp hpointx).2 ▸ hcontacts x hx
  · exact hreversals point hpoint

/-- A collected positive-cardinality response is not the zero function.
Vandermonde jet identification discharges the possible cancellation concern. -/
theorem CollectedDistinctExponentialResponse.response_ne_zero {q : ℕ}
    (data : CollectedDistinctExponentialResponse q) :
    data.response ≠ 0 := by
  intro hzero
  have hjet : ∀ order : Fin q,
      iteratedDeriv order data.response 0 = 0 := by
    intro order
    rw [hzero]
    simp
  have hcoeff : data.coefficient = 0 :=
    finiteExponentialResponse_coefficients_eq_zero_of_jet
      (fun i ↦ -data.exponent i) data.coefficient
      (fun i j hij ↦
        data.exponent_strictMono.injective (neg_injective hij))
      0 hjet
  obtain ⟨i⟩ := Fin.pos_iff_nonempty.mp data.q_pos
  exact data.coefficient_ne_zero i (congrFun hcoeff i)

/-! ## Balanced strict-interior constructor -/

/-- The `i`th later reversal activity in the balanced constructor. -/
noncomputable def balancedReversalActivity (r : ℕ) (i : Fin r) : ℝ :=
  (i.1 + 1 : ℝ) / (2 * (r + 1 : ℝ))

/-- The duplicate-free packet of later reversal activities. -/
noncomputable def balancedReversalPacket (r : ℕ) : Multiset ℝ :=
  (Finset.univ : Finset (Fin r)).1.map
    (balancedReversalActivity r)

/-- The complete balanced packet: an audit root of multiplicity `c`, the
zero-weight balance root, and `r` later simple reversals. -/
noncomputable def balancedInteriorPacket (c r : ℕ) : Multiset ℝ :=
  Multiset.replicate c (1 / 2 : ℝ) + {1} + balancedReversalPacket r

theorem balancedReversalActivity_pos (r : ℕ) (i : Fin r) :
    0 < balancedReversalActivity r i := by
  unfold balancedReversalActivity
  positivity

theorem balancedReversalActivity_lt_half (r : ℕ) (i : Fin r) :
    balancedReversalActivity r i < (1 / 2 : ℝ) := by
  unfold balancedReversalActivity
  have hi : (i.1 : ℝ) < r := by exact_mod_cast i.2
  have hr : (0 : ℝ) < 2 * (r + 1 : ℝ) := by positivity
  rw [div_lt_iff₀ hr]
  nlinarith

theorem balancedReversalActivity_injective (r : ℕ) :
    Function.Injective (balancedReversalActivity r) := by
  intro i j hij
  apply Fin.ext
  unfold balancedReversalActivity at hij
  have hden : (2 * (r + 1 : ℝ)) ≠ 0 := by positivity
  have hnum : (i.1 + 1 : ℝ) = (j.1 + 1 : ℝ) :=
    (div_left_inj' hden).mp hij
  have hval : i.1 = j.1 := by
    exact_mod_cast (show (i.1 : ℝ) = j.1 by linarith)
  exact hval

theorem balancedReversalPacket_nodup (r : ℕ) :
    (balancedReversalPacket r).Nodup := by
  unfold balancedReversalPacket
  exact ((Finset.univ : Finset (Fin r)).nodup.map
    (balancedReversalActivity_injective r))

@[simp]
theorem balancedReversalPacket_card (r : ℕ) :
    (balancedReversalPacket r).card = r := by
  simp [balancedReversalPacket]

@[simp]
theorem balancedInteriorPacket_card (c r : ℕ) :
    (balancedInteriorPacket c r).card = c + r + 1 := by
  simp [balancedInteriorPacket, balancedReversalPacket]
  omega

theorem balancedInteriorPacket_positive (c r : ℕ) :
    ∀ x ∈ balancedInteriorPacket c r, 0 < x := by
  intro x hx
  rw [balancedInteriorPacket, Multiset.mem_add] at hx
  rcases hx with hx | hx
  · rw [Multiset.mem_add] at hx
    rcases hx with hx | hx
    · exact (Multiset.mem_replicate.mp hx).2 ▸ by norm_num
    · exact (Multiset.mem_singleton.mp hx) ▸ by norm_num
  · rw [balancedReversalPacket, Multiset.mem_map] at hx
    obtain ⟨i, _, rfl⟩ := hx
    exact balancedReversalActivity_pos r i

theorem balancedReversalPacket_count_half (r : ℕ) :
    (balancedReversalPacket r).count (1 / 2 : ℝ) = 0 := by
  rw [Multiset.count_eq_zero]
  intro hmem
  rw [balancedReversalPacket, Multiset.mem_map] at hmem
  obtain ⟨i, _, hi⟩ := hmem
  linarith [balancedReversalActivity_lt_half r i]

theorem balancedReversalPacket_count_one (r : ℕ) :
    (balancedReversalPacket r).count (1 : ℝ) = 0 := by
  rw [Multiset.count_eq_zero]
  intro hmem
  rw [balancedReversalPacket, Multiset.mem_map] at hmem
  obtain ⟨i, _, hi⟩ := hmem
  linarith [balancedReversalActivity_lt_half r i]

@[simp]
theorem balancedInteriorPacket_count_half (c r : ℕ) :
    (balancedInteriorPacket c r).count (1 / 2 : ℝ) = c := by
  rw [balancedInteriorPacket, Multiset.count_add, Multiset.count_add,
    balancedReversalPacket_count_half]
  norm_num

@[simp]
theorem balancedInteriorPacket_count_one (c r : ℕ) :
    (balancedInteriorPacket c r).count (1 : ℝ) = 1 := by
  have hreplicate :
      (Multiset.replicate c (1 / 2 : ℝ)).count 1 = 0 := by
    rw [Multiset.count_replicate]
    norm_num
  rw [balancedInteriorPacket, Multiset.count_add, Multiset.count_add,
    hreplicate, balancedReversalPacket_count_one]
  norm_num

theorem balancedInteriorPacket_count_reversal
    (c r : ℕ) (i : Fin r) :
    (balancedInteriorPacket c r).count (balancedReversalActivity r i) = 1 := by
  have hhalf : balancedReversalActivity r i ≠ (1 / 2 : ℝ) :=
    ne_of_lt (balancedReversalActivity_lt_half r i)
  have hone : balancedReversalActivity r i ≠ (1 : ℝ) := by
    linarith [balancedReversalActivity_lt_half r i]
  have hmem : balancedReversalActivity r i ∈ balancedReversalPacket r := by
    rw [balancedReversalPacket, Multiset.mem_map]
    exact ⟨i, by simp, rfl⟩
  have hcount :
      (balancedReversalPacket r).count (balancedReversalActivity r i) = 1 :=
    Multiset.count_eq_one_of_mem (balancedReversalPacket_nodup r) hmem
  have hreplicate :
      (Multiset.replicate c (1 / 2 : ℝ)).count
        (balancedReversalActivity r i) = 0 := by
    have hne : (1 / 2 : ℝ) ≠ balancedReversalActivity r i :=
      Ne.symm hhalf
    rw [Multiset.count_replicate, if_neg hne]
  rw [balancedInteriorPacket, Multiset.count_add, Multiset.count_add,
    hreplicate, hcount]
  simp [hone]

/-- The balanced sharp activity polynomial.  Its extra root at activity one
is exactly the equal-zero-weight-mass condition. -/
noncomputable def balancedInteriorPolynomial (c r : ℕ) : ℝ[X] :=
  sharpContactPolynomial (balancedInteriorPacket c r)

/-- Exact slice and root multiplicities of the balanced constructor. -/
theorem balancedInteriorPolynomial_exact (c r : ℕ) :
    activitySliceCount (balancedInteriorPolynomial c r) = c + r + 2 ∧
    (balancedInteriorPolynomial c r).roots.count (1 / 2 : ℝ) = c ∧
    (balancedInteriorPolynomial c r).roots.count (1 : ℝ) = 1 ∧
    (∀ i : Fin r,
      (balancedInteriorPolynomial c r).roots.count
        (balancedReversalActivity r i) = 1) := by
  have hexact := sharpContactPolynomial_exact
    (balancedInteriorPacket_positive c r)
  have hroots := hexact.2.2
  constructor
  · dsimp [balancedInteriorPolynomial]
    rw [hexact.1, balancedInteriorPacket_card]
  · constructor
    · rw [balancedInteriorPolynomial, hroots, Multiset.count_add,
        balancedInteriorPacket_count_half]
      norm_num
    · constructor
      · rw [balancedInteriorPolynomial, hroots, Multiset.count_add,
          balancedInteriorPacket_count_one]
        norm_num
      · intro i
        rw [balancedInteriorPolynomial, hroots, Multiset.count_add,
          balancedInteriorPacket_count_reversal]
        have hpos := balancedReversalActivity_pos r i
        simp [ne_of_gt hpos]

/-- Positive-coefficient alternative partition mass at one activity. -/
noncomputable def positiveCoefficientMass
    (p : ℝ[X]) (activity : ℝ) : ℝ :=
  p.sum fun exponent coefficient ↦ max coefficient 0 * activity ^ exponent

/-- Sign-reversed negative-coefficient alternative partition mass. -/
noncomputable def negativeCoefficientMass
    (p : ℝ[X]) (activity : ℝ) : ℝ :=
  p.sum fun exponent coefficient ↦
    max (-coefficient) 0 * activity ^ exponent

theorem max_sub_max_neg_eq_self (coefficient : ℝ) :
    max coefficient 0 - max (-coefficient) 0 = coefficient := by
  by_cases h : 0 ≤ coefficient
  · rw [max_eq_left h, max_eq_right]
    · linarith
    · linarith
  · have hneg : coefficient ≤ 0 := le_of_not_ge h
    rw [max_eq_right hneg, max_eq_left]
    · simp
    · linarith

/-- Exact signed-ledger reconstruction at every activity. -/
theorem positiveCoefficientMass_sub_negativeCoefficientMass
    (p : ℝ[X]) (activity : ℝ) :
    positiveCoefficientMass p activity -
        negativeCoefficientMass p activity = p.eval activity := by
  rw [positiveCoefficientMass, negativeCoefficientMass,
    Polynomial.sum_def, Polynomial.sum_def, ← Finset.sum_sub_distrib,
    Polynomial.eval_eq_sum, Polynomial.sum_def]
  apply Finset.sum_congr rfl
  intro exponent _
  rw [← sub_mul, max_sub_max_neg_eq_self]

theorem positiveCoefficientMass_nonnegative
    (p : ℝ[X]) {activity : ℝ} (hactivity : 0 ≤ activity) :
    0 ≤ positiveCoefficientMass p activity := by
  rw [positiveCoefficientMass, Polynomial.sum_def]
  positivity

theorem negativeCoefficientMass_nonnegative
    (p : ℝ[X]) {activity : ℝ} (hactivity : 0 ≤ activity) :
    0 ≤ negativeCoefficientMass p activity := by
  rw [negativeCoefficientMass, Polynomial.sum_def]
  positivity

theorem balancedInteriorPolynomial_eval_one (c r : ℕ) :
    (balancedInteriorPolynomial c r).eval 1 = 0 := by
  have hroots := (balancedInteriorPolynomial_exact c r).2.2.1
  have hmem : (1 : ℝ) ∈ (balancedInteriorPolynomial c r).roots :=
    Multiset.count_pos.mp (by omega)
  exact (Polynomial.mem_roots
    (sharpContactPolynomial_ne_zero (balancedInteriorPacket c r))).mp hmem

/-- The balance root forces equal total alternative mass at zero weight. -/
theorem balancedInterior_equal_zeroWeight_mass (c r : ℕ) :
    positiveCoefficientMass (balancedInteriorPolynomial c r) 1 =
      negativeCoefficientMass (balancedInteriorPolynomial c r) 1 := by
  have hdifference := positiveCoefficientMass_sub_negativeCoefficientMass
    (balancedInteriorPolynomial c r) 1
  rw [balancedInteriorPolynomial_eval_one] at hdifference
  linarith

/-- Exact MaxEnt translation: the positive normalizer preserves every zero
and sign of the activity polynomial in the named-probability difference. -/
theorem balancedInterior_probability_translation (c r : ℕ)
    {activity : ℝ} (hactivity : 0 ≤ activity) :
    let positiveMass := positiveCoefficientMass
      (balancedInteriorPolynomial c r) activity
    let negativeMass := negativeCoefficientMass
      (balancedInteriorPolynomial c r) activity
    namedCandidateProbability negativeMass -
          namedCandidateProbability positiveMass =
        (balancedInteriorPolynomial c r).eval activity /
          ((1 + positiveMass) * (1 + negativeMass)) ∧
      0 < (1 + positiveMass) * (1 + negativeMass) ∧
      (namedCandidateProbability negativeMass -
            namedCandidateProbability positiveMass = 0 ↔
        (balancedInteriorPolynomial c r).eval activity = 0) ∧
      (0 < namedCandidateProbability negativeMass -
            namedCandidateProbability positiveMass ↔
        0 < (balancedInteriorPolynomial c r).eval activity) := by
  dsimp only
  have hpositive := positiveCoefficientMass_nonnegative
    (balancedInteriorPolynomial c r) hactivity
  have hnegative := negativeCoefficientMass_nonnegative
    (balancedInteriorPolynomial c r) hactivity
  have horientation := max_g8_probability_orientation hpositive hnegative
  have hdifference := positiveCoefficientMass_sub_negativeCoefficientMass
    (balancedInteriorPolynomial c r) activity
  rw [hdifference] at horientation
  exact horientation

/-- Activity on the positive ray whose integer row scale is `s`. -/
noncomputable def balancedInteriorActivity (s : ℕ) (time : ℝ) : ℝ :=
  Real.exp (-(s : ℝ) * time)

/-- The strict-interior audit time corresponding to activity one half. -/
noncomputable def balancedInteriorAuditTime (s : ℕ) : ℝ :=
  Real.log 2 / s

theorem balancedInteriorActivity_pos (s : ℕ) (time : ℝ) :
    0 < balancedInteriorActivity s time := by
  exact Real.exp_pos _

theorem balancedInteriorActivity_at_audit
    {s : ℕ} (hs : 0 < s) :
    balancedInteriorActivity s (balancedInteriorAuditTime s) = 1 / 2 := by
  unfold balancedInteriorActivity balancedInteriorAuditTime
  have hsreal : (s : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hs)
  have harg : -(s : ℝ) * (Real.log 2 / s) = -Real.log 2 := by
    field_simp
  rw [harg, Real.exp_neg,
    Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  norm_num

/-- The balanced polynomial pulled back to the declared weight ray. -/
noncomputable def balancedInteriorResponse
    (c r s : ℕ) (time : ℝ) : ℝ :=
  (balancedInteriorPolynomial c r).eval (balancedInteriorActivity s time)

theorem balancedInteriorResponse_at_audit
    (c r : ℕ) {s : ℕ} (hc : 0 < c) (hs : 0 < s) :
    balancedInteriorResponse c r s (balancedInteriorAuditTime s) = 0 := by
  rw [balancedInteriorResponse, balancedInteriorActivity_at_audit hs]
  have hroots := (balancedInteriorPolynomial_exact c r).2.1
  have hmem : (1 / 2 : ℝ) ∈ (balancedInteriorPolynomial c r).roots :=
    Multiset.count_pos.mp (by omega)
  exact (Polynomial.mem_roots
    (sharpContactPolynomial_ne_zero (balancedInteriorPacket c r))).mp hmem

/-- Every retained alternative slice has positive exponent.  Hence scaling by
positive `s` gives a positive projected violation against the named zero row. -/
theorem balancedInterior_support_exponent_pos
    (c r : ℕ) {exponent : ℕ}
    (hexponent : exponent ∈ (balancedInteriorPolynomial c r).support) :
    0 < exponent := by
  by_contra hnot
  have hzero : exponent = 0 := Nat.eq_zero_of_not_pos hnot
  subst exponent
  exact (Polynomial.mem_support_iff.mp hexponent)
    (sharpContactPolynomial_coeff_zero (balancedInteriorPacket c r))

/-- Projected violation of an activity exponent under row scale `s`. -/
def balancedProjectedViolation (s exponent : ℕ) : ℕ := s * exponent

theorem balancedProjectedViolation_pos
    (c r : ℕ) {s exponent : ℕ} (hs : 0 < s)
    (hexponent : exponent ∈ (balancedInteriorPolynomial c r).support) :
    0 < balancedProjectedViolation s exponent := by
  exact Nat.mul_pos hs
    (balancedInterior_support_exponent_pos c r hexponent)

/-- **MAX-G8.BOUNDARY.03**, full balanced strict-interior branch.  The
constructor has `c + r + 2` slices, audit multiplicity `c`, one balance root,
`r` distinct simple later roots, equal zero-weight alternative mass, the exact
strict-interior audit activity, and only positive nonnamed violation rows. -/
theorem max_g8_boundary_03_balancedInterior
    (c r s : ℕ) (hc : 0 < c) (hs : 0 < s) :
    activitySliceCount (balancedInteriorPolynomial c r) = c + r + 2 ∧
    (balancedInteriorPolynomial c r).roots.count (1 / 2 : ℝ) = c ∧
    (balancedInteriorPolynomial c r).roots.count (1 : ℝ) = 1 ∧
    (∀ i : Fin r,
      (balancedInteriorPolynomial c r).roots.count
        (balancedReversalActivity r i) = 1) ∧
    positiveCoefficientMass (balancedInteriorPolynomial c r) 1 =
      negativeCoefficientMass (balancedInteriorPolynomial c r) 1 ∧
    balancedInteriorActivity s (balancedInteriorAuditTime s) = 1 / 2 ∧
    balancedInteriorResponse c r s (balancedInteriorAuditTime s) = 0 ∧
    (∀ exponent ∈ (balancedInteriorPolynomial c r).support,
      0 < balancedProjectedViolation s exponent) := by
  have hexact := balancedInteriorPolynomial_exact c r
  refine ⟨hexact.1, hexact.2.1, hexact.2.2.1, hexact.2.2.2,
    balancedInterior_equal_zeroWeight_mass c r,
    balancedInteriorActivity_at_audit hs,
    balancedInteriorResponse_at_audit c r hc hs, ?_⟩
  intro exponent hexponent
  exact balancedProjectedViolation_pos c r hs hexponent

/-! ## Rolle reduction and the general `q - 1` theorem -/

/-- Remove the lowest exponential rate by multiplication with its inverse
exponential.  The lowest slice becomes constant. -/
noncomputable def normalizedExponentialResponse {q : ℕ}
    (data : CollectedDistinctExponentialResponse (q + 1)) : ℝ → ℝ :=
  finiteExponentialResponse
    (fun i ↦ data.exponent 0 - data.exponent i) data.coefficient

/-- The derivative ledger after the constant lowest slice is removed. -/
noncomputable def exponentialDerivativeTail {q : ℕ}
    (data : CollectedDistinctExponentialResponse (q + 1)) (hq : 0 < q) :
    CollectedDistinctExponentialResponse q where
  exponent := fun i ↦ data.exponent i.succ - data.exponent 0
  coefficient := fun i ↦
    (data.exponent 0 - data.exponent i.succ) * data.coefficient i.succ
  q_pos := hq
  exponent_strictMono := by
    intro i j hij
    have hmono := data.exponent_strictMono
      (Fin.succ_lt_succ_iff.mpr hij)
    linarith
  coefficient_ne_zero := by
    intro i
    apply mul_ne_zero
    · apply sub_ne_zero.mpr
      intro heq
      have hindex : (0 : Fin (q + 1)) = i.succ :=
        data.exponent_strictMono.injective heq
      have hval := congrArg Fin.val hindex
      simp at hval
    · exact data.coefficient_ne_zero i.succ

/-- Exact inverse-exponential normalization identity. -/
theorem normalizedExponentialResponse_eq_mul {q : ℕ}
    (data : CollectedDistinctExponentialResponse (q + 1)) :
    normalizedExponentialResponse data =
      fun time ↦ Real.exp (data.exponent 0 * time) * data.response time := by
  funext time
  rw [normalizedExponentialResponse,
    CollectedDistinctExponentialResponse.response,
    finiteExponentialResponse, finiteExponentialResponse,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  calc
    data.coefficient i *
          Real.exp ((data.exponent 0 - data.exponent i) * time) =
    data.coefficient i *
          (Real.exp (data.exponent 0 * time) *
            Real.exp (-data.exponent i * time)) := by
              rw [← Real.exp_add]
              congr 2
              ring
    _ = Real.exp (data.exponent 0 * time) *
          (data.coefficient i * Real.exp (-data.exponent i * time)) := by
            ring

/-- Differentiating the normalized response removes exactly one slice and
produces the collected derivative-tail response. -/
theorem deriv_normalizedExponentialResponse_eq_tail {q : ℕ}
    (data : CollectedDistinctExponentialResponse (q + 1)) (hq : 0 < q) :
    deriv (normalizedExponentialResponse data) =
      (exponentialDerivativeTail data hq).response := by
  funext time
  rw [← iteratedDeriv_one, normalizedExponentialResponse,
    iteratedDeriv_finiteExponentialResponse]
  rw [CollectedDistinctExponentialResponse.response,
    finiteExponentialResponse, Fin.sum_univ_succ]
  simp [exponentialDerivativeTail]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The normalized response itself as a collected ordered response. -/
noncomputable def normalizedExponentialData {q : ℕ}
    (data : CollectedDistinctExponentialResponse (q + 1)) :
    CollectedDistinctExponentialResponse (q + 1) where
  exponent := fun i ↦ data.exponent i - data.exponent 0
  coefficient := data.coefficient
  q_pos := data.q_pos
  exponent_strictMono := by
    intro i j hij
    have hmono := data.exponent_strictMono hij
    linarith
  coefficient_ne_zero := data.coefficient_ne_zero

theorem normalizedExponentialData_response {q : ℕ}
    (data : CollectedDistinctExponentialResponse (q + 1)) :
    (normalizedExponentialData data).response =
      normalizedExponentialResponse data := by
  funext time
  rw [CollectedDistinctExponentialResponse.response,
    normalizedExponentialResponse, finiteExponentialResponse]
  apply Finset.sum_congr rfl
  intro i _
  simp only [normalizedExponentialData]
  rw [show -(data.exponent i - data.exponent 0) * time =
      (data.exponent 0 - data.exponent i) * time by ring]

theorem normalizedExponentialResponse_ne_zero {q : ℕ}
    (data : CollectedDistinctExponentialResponse (q + 1)) :
    normalizedExponentialResponse data ≠ 0 := by
  rw [← normalizedExponentialData_response]
  exact (normalizedExponentialData data).response_ne_zero

/-- Analytic extension across both endpoints of the declared interval. -/
def realAnalyticOnClosedInterval
    (response : ℝ → ℝ) (left right : ℝ) : Prop :=
  ∀ point ∈ Set.Icc left right, AnalyticAt ℝ response point

/-- Explicit Lean contract for `FOUND-ANALYTIC-ROLLE-MULTIPLICITY-001`.
It owns only the standard multiplicity-counting Rolle step: a nonzero analytic
function's zero packet is bounded by one plus a derivative zero packet on the
same interval.  No project theorem is added to Lean's trusted base. -/
def FoundAnalyticRolleMultiplicity001 : Prop :=
  ∀ (response : ℝ → ℝ) (packet : Multiset ℝ) (left right : ℝ),
    left < right →
    realAnalyticOnClosedInterval response left right →
    response ≠ 0 →
    packetInsideOpenInterval packet left right →
    supportsZeroMultiplicity response packet →
    ∃ derivativePacket : Multiset ℝ,
      packetInsideOpenInterval derivativePacket left right ∧
      supportsZeroMultiplicity (deriv response) derivativePacket ∧
      packet.card ≤ derivativePacket.card + 1

theorem normalizedExponentialResponse_realAnalyticOnClosedInterval {q : ℕ}
    (data : CollectedDistinctExponentialResponse (q + 1))
    (left right : ℝ) :
    realAnalyticOnClosedInterval
      (normalizedExponentialResponse data) left right := by
  intro point _
  unfold normalizedExponentialResponse finiteExponentialResponse
  fun_prop

/-- Multiplication by the positive inverse exponential preserves every
registered local zero multiplicity. -/
theorem supportsZeroMultiplicity_normalizedExponentialResponse {q : ℕ}
    (data : CollectedDistinctExponentialResponse (q + 1))
    {packet : Multiset ℝ}
    (hzeros : supportsZeroMultiplicity data.response packet) :
    supportsZeroMultiplicity (normalizedExponentialResponse data) packet := by
  intro point order horder
  let denominator : ℝ → ℝ :=
    fun time ↦ Real.exp (data.exponent 0 * time)
  have hdenominator : ContDiff ℝ ⊤ denominator := by
    dsimp [denominator]
    fun_prop
  have hresponse : ContDiff ℝ ⊤ data.response := by
    unfold CollectedDistinctExponentialResponse.response
      finiteExponentialResponse
    fun_prop
  have hjet : responseJetZeroThrough data.response point order := by
    intro degree hdegree
    exact hzeros point degree (lt_of_le_of_lt hdegree horder)
  have hproduct := (responseJetZeroThrough_mul_iff_right
    denominator data.response point order hdenominator hresponse
    (Real.exp_ne_zero _)).2 hjet
  have heq :
      normalizedExponentialResponse data = denominator * data.response := by
    rw [normalizedExponentialResponse_eq_mul]
    rfl
  rw [← heq] at hproduct
  exact hproduct order le_rfl

/-- The project-specific Chebyshev induction.  It removes the lowest slice,
differentiates the normalized response, invokes only the explicit Rolle
foundation step, and recursively spends one slice per zero multiplicity. -/
theorem exponentialResponse_zeroMultiplicity_bound
    (hfoundation : FoundAnalyticRolleMultiplicity001) :
    ∀ {q : ℕ} (data : CollectedDistinctExponentialResponse q)
      (packet : Multiset ℝ) (left right : ℝ),
      left < right →
      packetInsideOpenInterval packet left right →
      supportsZeroMultiplicity data.response packet →
      packet.card ≤ q - 1 := by
  intro q
  induction q with
  | zero =>
      intro data
      exact (Nat.not_lt_zero _ data.q_pos).elim
  | succ q inductionHypothesis =>
      intro data packet left right hinterval hinside hzeros
      by_cases hqzero : q = 0
      · subst q
        have hpacketEmpty : packet = 0 := by
          have hcardzero : packet.card = 0 := by
            by_contra hcard
            have hpositive : 0 < packet.card := Nat.pos_of_ne_zero hcard
            obtain ⟨point, hpoint⟩ :=
              Multiset.card_pos_iff_exists_mem.mp hpositive
            have hzero := hzeros point 0 (Multiset.count_pos.mpr hpoint)
            have hvalue : data.coefficient 0 *
                Real.exp (-data.exponent 0 * point) = 0 := by
              simpa [CollectedDistinctExponentialResponse.response,
                finiteExponentialResponse] using hzero
            have hcoefficient : data.coefficient 0 = 0 := by
              exact (mul_eq_zero.mp hvalue).resolve_right (Real.exp_ne_zero _)
            exact data.coefficient_ne_zero 0 hcoefficient
          exact Multiset.card_eq_zero.mp hcardzero
        simp [hpacketEmpty]
      · have hqpos : 0 < q := Nat.pos_of_ne_zero hqzero
        have hnormalizedZeros :=
          supportsZeroMultiplicity_normalizedExponentialResponse data hzeros
        obtain ⟨derivativePacket, hderivativeInside,
            hderivativeZeros, hrolle⟩ :=
          hfoundation (normalizedExponentialResponse data) packet left right
            hinterval
            (normalizedExponentialResponse_realAnalyticOnClosedInterval
              data left right)
            (normalizedExponentialResponse_ne_zero data)
            hinside hnormalizedZeros
        have htailZeros : supportsZeroMultiplicity
            (exponentialDerivativeTail data hqpos).response
            derivativePacket := by
          rw [← deriv_normalizedExponentialResponse_eq_tail data hqpos]
          exact hderivativeZeros
        have htailBound := inductionHypothesis
          (exponentialDerivativeTail data hqpos) derivativePacket left right
          hinterval hderivativeInside htailZeros
        omega

/-- **MAX-G8.CHEBYSHEV.04**, arbitrary distinct-real-exponent branch.  The
complete `q - 1` zero-multiplicity bound is derived relative only to the
registered Rolle foundation contract. -/
theorem max_g8_chebyshev_04_general
    (hfoundation : FoundAnalyticRolleMultiplicity001)
    {q : ℕ} (data : CollectedDistinctExponentialResponse q)
    (packet : Multiset ℝ) (left right : ℝ)
    (hinterval : left < right)
    (hinside : packetInsideOpenInterval packet left right)
    (hzeros : supportsZeroMultiplicity data.response packet) :
    packet.card ≤ q - 1 := by
  exact exponentialResponse_zeroMultiplicity_bound hfoundation data packet
    left right hinterval hinside hzeros

/-- **MAX-G8.CAPACITY.02**, arbitrary distinct-real-exponent branch.  Exact
contact multiplicities and disjoint additional strict reversals consume the
same `q - 1` budget. -/
theorem max_g8_capacity_02_general
    (hfoundation : FoundAnalyticRolleMultiplicity001)
    {q : ℕ} (data : CollectedDistinctExponentialResponse q)
    (contacts reversals : Finset ℝ) (multiplicity : ℝ → ℕ)
    (left right : ℝ)
    (hinterval : left < right)
    (hdisjoint : Disjoint contacts reversals)
    (hcontactsInside : ∀ x ∈ contacts, x ∈ Set.Ioo left right)
    (hreversalsInside : ∀ x ∈ reversals, x ∈ Set.Ioo left right)
    (hcontacts : ∀ x ∈ contacts,
      responseContactMultiplicityAt data.response x (multiplicity x))
    (hreversals : ∀ x ∈ reversals,
      strictResponseReversalAt data.response x) :
    (∑ x ∈ contacts, multiplicity x) + reversals.card ≤ q - 1 := by
  rw [← card_registeredContactPacket]
  exact max_g8_chebyshev_04_general hfoundation data _ left right hinterval
    (registeredContactPacket_insideOpenInterval contacts reversals multiplicity
      left right hcontactsInside hreversalsInside)
    (registeredContactPacket_supportsZeroMultiplicity data.response
      contacts reversals multiplicity hdisjoint hcontacts hreversals)

end PhonologicalCalculus.MaxEnt
