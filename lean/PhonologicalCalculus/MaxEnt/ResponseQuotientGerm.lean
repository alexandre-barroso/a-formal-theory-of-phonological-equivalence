import PhonologicalCalculus.MaxEnt.FixedMassResponseComplete
import Mathlib.Tactic

/-!
# Exact quotient-germ transport

A MaxEnt response difference is obtained by dividing a cross-numerator by a
strictly positive normalizing denominator.  This module proves at an arbitrary
base point that multiplication by a smooth function with nonzero base value
neither creates nor removes any finite vanishing jet.
-/

namespace PhonologicalCalculus.MaxEnt

/-- Vanishing of every true derivative through a declared finite order at an
arbitrary base point. -/
def responseJetZeroThrough
    (response : ℝ → ℝ) (base : ℝ) (order : ℕ) : Prop :=
  ∀ degree, degree ≤ order → iteratedDeriv degree response base = 0

/-- A smooth nonvanishing denominator preserves every finite response jet.
This is the arbitrary-base analytic version of the polynomial coefficient
transport in `MAX-G7.CONTACT.02`. -/
theorem responseJetZeroThrough_mul_iff_right
    (denominator response : ℝ → ℝ) (base : ℝ) (order : ℕ)
    (hdenominator : ContDiff ℝ ⊤ denominator)
    (hresponse : ContDiff ℝ ⊤ response)
    (hbase : denominator base ≠ 0) :
    responseJetZeroThrough (denominator * response) base order ↔
      responseJetZeroThrough response base order := by
  constructor
  · intro hproduct degree hdegree
    induction degree using Nat.strong_induction_on with
    | h degree inductionHypothesis =>
        have hproductDegree := hproduct degree hdegree
        rw [iteratedDeriv_mul
          (hdenominator.contDiffAt.of_le (by simp))
          (hresponse.contDiffAt.of_le (by simp))] at hproductDegree
        by_cases hzero : degree = 0
        · subst degree
          simpa [hbase] using hproductDegree
        · have hdegreePositive : 0 < degree := Nat.pos_of_ne_zero hzero
          have hcollapse :
              ∑ i ∈ Finset.range (degree + 1),
                  degree.choose i * iteratedDeriv i denominator base *
                    iteratedDeriv (degree - i) response base =
                denominator base * iteratedDeriv degree response base := by
            rw [Finset.sum_eq_single 0]
            · simp
            · intro i hi hi0
              have hiPositive : 0 < i := Nat.pos_of_ne_zero hi0
              have hsubLt : degree - i < degree :=
                Nat.sub_lt hdegreePositive hiPositive
              have hsubLeOrder : degree - i ≤ order :=
                (Nat.sub_le degree i).trans hdegree
              rw [inductionHypothesis (degree - i) hsubLt hsubLeOrder]
              simp
            · simp
          rw [hcollapse] at hproductDegree
          exact (mul_eq_zero.mp hproductDegree).resolve_left hbase
  · intro hzero degree hdegree
    rw [iteratedDeriv_mul
      (hdenominator.contDiffAt.of_le (by simp))
      (hresponse.contDiffAt.of_le (by simp))]
    apply Finset.sum_eq_zero
    intro i hi
    have hsubLeOrder : degree - i ≤ order :=
      (Nat.sub_le degree i).trans hdegree
    rw [hzero (degree - i) hsubLeOrder]
    simp

/-- Exact numerator-to-response transport when the registered response is a
smooth quotient represented by `numerator = denominator * response`. -/
theorem max_g7_contact_02_actualGerm
    (denominator numerator response : ℝ → ℝ)
    (base : ℝ) (order : ℕ)
    (hdenominator : ContDiff ℝ ⊤ denominator)
    (hresponse : ContDiff ℝ ⊤ response)
    (hbase : denominator base ≠ 0)
    (hfactor : numerator = denominator * response) :
    responseJetZeroThrough numerator base order ↔
      responseJetZeroThrough response base order := by
  rw [hfactor]
  exact responseJetZeroThrough_mul_iff_right
    denominator response base order hdenominator hresponse hbase

end PhonologicalCalculus.MaxEnt
