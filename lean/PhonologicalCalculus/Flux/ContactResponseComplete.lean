import PhonologicalCalculus.Flux.ContactAsymptoticComplete
import PhonologicalCalculus.Flux.ContactSpectrumComplete

/-!
# Complete declared contact-response package

This module joins the two independently checked components of `FLUX-D4`.
The constructive gauge theorem realizes every positive odd analytic contact
order.  Under the prospectively declared normalized little-o remainder and a
positive Lambert witness branch, the scalar theorem then derives the exact
coefficient, logarithmic response exponent, and ratio-one Lambert
representative.  The remainder is an explicit assumption of the registered
contract; it is not concealed as a consequence of an undeclared KKT model.
-/

namespace PhonologicalCalculus.Flux

open Filter
open scoped Topology

/-- The response exponent attached to the `r`th constructive odd contact. -/
def oddContactResponseExponent (r : ℕ) (p : ℝ) : ℝ :=
  responseExponent (2 * r + 1) p

theorem oddContactResponseExponent_pos
    {p : ℝ} (hp : 1 < p) (r : ℕ) :
    0 < oddContactResponseExponent r p := by
  unfold oddContactResponseExponent responseExponent
  have hmin : 0 < min 1 (p - 1) := lt_min one_pos (sub_pos.mpr hp)
  exact mul_pos (by positivity) hmin

/-- **FLUX-D4.NORMALFORM.03 and FLUX-D4.PERTURBATION.04.**  For a fixed
constructive odd-contact member, the registered normalized remainder entails
all three asymptotic response answers.  The same member simultaneously
satisfies the exact analytic gauge conditions and equation `(D4.6)`. -/
theorem flux_d4_complete_declared_response
    {lambda p C : ℝ} {t w : ℝ → ℝ}
    (hlambda : lambda ≠ 0) (hp : 1 < p) (hC : 0 < C) (r : ℕ)
    (htPos : ∀ᶠ epsilon in 𝓝[>] (0 : ℝ), 0 < t epsilon)
    (htZero : Tendsto t (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hRemainder : Tendsto
      (contactNormalizedRemainder (oddContactResponseExponent r p) C t)
      (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hwPos : ∀ᶠ epsilon in 𝓝[>] (0 : ℝ), 0 < w epsilon)
    (hLambert : ∀ᶠ epsilon in 𝓝[>] (0 : ℝ),
      LambertWitness
        (oddContactResponseExponent r p * C / epsilon) (w epsilon)) :
    (oddContactGauge lambda r 0 = 0 ∧
      ShiftEquivariant (oddContactGauge lambda r) lambda ∧
      StrictMono (oddContactGauge lambda r) ∧
      deriv (oddContactGauge lambda r) = raisedCosineMarginal lambda r ∧
      analyticOrderAt
          (fun z => oddContactGauge lambda r z - oddContactGauge lambda r 0) 0 =
        (2 * r + 1 : ℕ)) ∧
    Tendsto
        (contactRecoveredCoefficient (oddContactResponseExponent r p) t)
        (𝓝[>] (0 : ℝ)) (𝓝 C) ∧
    Tendsto
        (fun epsilon => Real.log (t epsilon) / Real.log epsilon)
        (𝓝[>] (0 : ℝ))
        (𝓝 (1 / oddContactResponseExponent r p)) ∧
    Tendsto
        (fun epsilon =>
          t epsilon /
            lambertNormalT epsilon (oddContactResponseExponent r p) C
              (w epsilon))
        (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have hGamma : 0 < oddContactResponseExponent r p :=
    oddContactResponseExponent_pos hp r
  have hgauge := flux_d4_constructive_odd_gauge hlambda r
  have hscalar := flux_d4_scalar_contact_response hGamma hC htPos htZero hRemainder
  have hlambert := contact_remainder_implies_lambert_equivalence
    hGamma hC htPos htZero hRemainder hwPos hLambert
  exact ⟨hgauge, hscalar.1, hscalar.2, hlambert⟩

end PhonologicalCalculus.Flux
