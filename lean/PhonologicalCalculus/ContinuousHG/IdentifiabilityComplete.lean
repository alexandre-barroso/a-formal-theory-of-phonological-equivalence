import PhonologicalCalculus.ContinuousHG.PhaseProfileOptimizerBridge
import PhonologicalCalculus.ContinuousHG.TripleIdentifiability

/-!
# Complete query-relative parameter identifiability

This module separates global family admission from local recovery.  A global
admission predicate requires every active pair to satisfy the same indexed
powered-gap law.  A strictly decreasing, positive, strictly log-concave triple
then determines one and only one exponent-ratio pair satisfying its two
consecutive gap equations.  Common positive scaling remains an exact gauge.
-/

namespace PhonologicalCalculus.ContinuousHG

/-- Global admission to one constant-exponent, constant-ratio active phase. -/
def PoweredGapFamilyAdmission
    (p rho : ℝ) (decrease : ℕ → ℝ) (K : ℕ) : Prop :=
  1 < p ∧ 0 < rho ∧
    ∀ i j : ℕ, i < j → j < K →
      (decrease i) ^ (p - 1) - (decrease j) ^ (p - 1) =
        ((j - i : ℕ) : ℝ) / (p * rho)

/-- Every admitted active pair recovers the same harmony ratio. -/
theorem poweredGapFamilyAdmission_pair_recovers_ratio
    {p rho : ℝ} {decrease : ℕ → ℝ} {K i j : ℕ}
    (hadmit : PoweredGapFamilyAdmission p rho decrease K)
    (hij : i < j) (hjK : j < K) :
    rho = ((j - i : ℕ) : ℝ) /
      (p * ((decrease i) ^ (p - 1) - (decrease j) ^ (p - 1))) := by
  rcases hadmit with ⟨hp, hrho, hall⟩
  apply powered_gap_recovers_ratio
    (lt_trans zero_lt_one hp) hrho (by exact_mod_cast Nat.sub_pos_of_lt hij)
  exact hall i j hij hjK

/-- Exact two-equation local identification contract for three consecutive
positive decreases. -/
def TripleExponentRatioSystem (a b c p rho : ℝ) : Prop :=
  1 < p ∧ 0 < rho ∧
    a ^ (p - 1) - b ^ (p - 1) = 1 / (p * rho) ∧
    b ^ (p - 1) - c ^ (p - 1) = 1 / (p * rho)

/-- A positive strictly decreasing log-concave triple determines a unique
penalty exponent and a unique positive harmony ratio. -/
theorem logConcaveTriple_existsUnique_exponentRatio
    {a b c : ℝ} (hc : 0 < c) (hcb : c < b) (hba : b < a)
    (hLogConcave : a * c < b ^ 2) :
    ∃! parameter : ℝ × ℝ,
      TripleExponentRatioSystem a b c parameter.1 parameter.2 := by
  have hb : 0 < b := lt_trans hc hcb
  have ha : 0 < a := lt_trans hb hba
  obtain ⟨p, hpSystem, hpUnique⟩ :=
    logConcaveTriple_existsUnique_exponentAboveOne hc hcb hba hLogConcave
  let s : ℝ := p - 1
  have hs : 0 < s := sub_pos.mpr hpSystem.1
  have hgap : 0 < a ^ s - b ^ s := by
    exact sub_pos.mpr (Real.rpow_lt_rpow hb.le hba hs)
  let rho : ℝ := 1 / (p * (a ^ s - b ^ s))
  have hpPositive : 0 < p := lt_trans zero_lt_one hpSystem.1
  have rhoPositive : 0 < rho := by
    dsimp [rho]
    positivity
  have firstGap : a ^ (p - 1) - b ^ (p - 1) = 1 / (p * rho) := by
    dsimp [rho, s] at hgap ⊢
    field_simp [ne_of_gt hpPositive, ne_of_gt hgap]
  have tripleBalance :
      a ^ s + c ^ s = 2 * b ^ s := by
    have hbpow : 0 < b ^ s := Real.rpow_pos_of_pos hb s
    have ratioA : (a / b) ^ s = a ^ s / b ^ s :=
      Real.div_rpow ha.le hb.le s
    have ratioC : (c / b) ^ s = c ^ s / b ^ s :=
      Real.div_rpow hc.le hb.le s
    have equation : (a / b) ^ s + (c / b) ^ s = 2 := by
      simpa [s] using hpSystem.2
    rw [ratioA, ratioC] at equation
    field_simp [ne_of_gt hbpow] at equation
    linarith
  have secondGap : b ^ (p - 1) - c ^ (p - 1) = 1 / (p * rho) := by
    have balance : a ^ (p - 1) + c ^ (p - 1) = 2 * b ^ (p - 1) := by
      simpa [s] using tripleBalance
    rw [← firstGap]
    linarith
  refine ⟨(p, rho), ⟨hpSystem.1, rhoPositive, firstGap, secondGap⟩, ?_⟩
  rintro ⟨otherP, otherRho⟩ hother
  rcases hother with ⟨hOtherP, hOtherRho, hOtherFirst, hOtherSecond⟩
  have otherBpow : 0 < b ^ (otherP - 1) :=
    Real.rpow_pos_of_pos hb _
  have otherBalance :
      a ^ (otherP - 1) + c ^ (otherP - 1) =
        2 * b ^ (otherP - 1) := by
    linarith
  have otherRatioEquation :
      (a / b) ^ (otherP - 1) + (c / b) ^ (otherP - 1) = 2 := by
    rw [Real.div_rpow ha.le hb.le, Real.div_rpow hc.le hb.le]
    field_simp [ne_of_gt otherBpow]
    linarith
  have pIdentity : otherP = p :=
    hpUnique otherP ⟨hOtherP, otherRatioEquation⟩
  subst otherP
  have denominatorNonzero : p * (a ^ (p - 1) - b ^ (p - 1)) ≠ 0 := by
    have gapPositive : 0 < a ^ (p - 1) - b ^ (p - 1) := by
      simpa [s] using hgap
    exact mul_ne_zero (ne_of_gt hpPositive) (ne_of_gt gapPositive)
  have rhoIdentity : otherRho = rho := by
    have fromOther : otherRho = 1 /
        (p * (a ^ (p - 1) - b ^ (p - 1))) := by
      simpa using powered_gap_recovers_ratio
        hpPositive hOtherRho (by norm_num : (0 : ℝ) < 1) hOtherFirst
    have targetIdentity : rho = 1 /
        (p * (a ^ (p - 1) - b ^ (p - 1))) := by
      dsimp [rho, s]
    exact fromOther.trans targetIdentity.symm
  subst otherRho
  rfl

/-- A positive, decreasing, strictly log-concave *consecutive* triple from an
admitted family identifies the admitted exponent and ratio themselves.  This
is the bridge that prevents an unrelated locally identifiable triple from
being mistaken for evidence about the globally admitted path. -/
theorem poweredGapFamilyAdmission_consecutive_triple_identifies
    {p rho : ℝ} {decrease : ℕ → ℝ} {K t : ℕ}
    (hadmit : PoweredGapFamilyAdmission p rho decrease K)
    (htK : t + 2 < K)
    (hc : 0 < decrease (t + 2))
    (hcb : decrease (t + 2) < decrease (t + 1))
    (hba : decrease (t + 1) < decrease t)
    (hLogConcave : decrease t * decrease (t + 2) < decrease (t + 1) ^ 2) :
    TripleExponentRatioSystem
        (decrease t) (decrease (t + 1)) (decrease (t + 2)) p rho ∧
      ∀ parameter : ℝ × ℝ,
        TripleExponentRatioSystem
            (decrease t) (decrease (t + 1)) (decrease (t + 2))
            parameter.1 parameter.2 →
          parameter = (p, rho) := by
  rcases hadmit with ⟨hp, hrho, hall⟩
  have firstEquation := hall t (t + 1) (by omega) (by omega)
  have secondEquation := hall (t + 1) (t + 2) (by omega) htK
  have admittedSystem :
      TripleExponentRatioSystem
        (decrease t) (decrease (t + 1)) (decrease (t + 2)) p rho := by
    exact ⟨hp, hrho, by simpa using firstEquation,
      by simpa using secondEquation⟩
  obtain ⟨identified, hidentified, hunique⟩ :=
    logConcaveTriple_existsUnique_exponentRatio hc hcb hba hLogConcave
  refine ⟨admittedSystem, ?_⟩
  intro parameter hparameter
  exact (hunique parameter hparameter).trans
    (hunique (p, rho) admittedSystem).symm

/-- Integrated identifiability theorem: global admission makes every active
pair ratio-consistent; an admitted log-concave triple uniquely identifies the
local exponent-ratio pair; common scale remains free. -/
theorem chg_b11_complete_query_relative_identifiability
    {p rho lambda h m : ℝ} {decrease : ℕ → ℝ} {K i j t : ℕ}
    (hadmit : PoweredGapFamilyAdmission p rho decrease K)
    (hij : i < j) (hjK : j < K)
    (htK : t + 2 < K)
    (hc : 0 < decrease (t + 2))
    (hcb : decrease (t + 2) < decrease (t + 1))
    (hba : decrease (t + 1) < decrease t)
    (hLogConcave : decrease t * decrease (t + 2) < (decrease (t + 1)) ^ 2)
    (hlambda : 0 < lambda) (hm : 0 < m) :
    rho = ((j - i : ℕ) : ℝ) /
        (p * ((decrease i) ^ (p - 1) - (decrease j) ^ (p - 1))) ∧
      TripleExponentRatioSystem
        (decrease t) (decrease (t + 1)) (decrease (t + 2)) p rho ∧
      (∀ parameter : ℝ × ℝ,
        TripleExponentRatioSystem
          (decrease t) (decrease (t + 1)) (decrease (t + 2))
          parameter.1 parameter.2 → parameter = (p, rho)) ∧
      (lambda * h) / (lambda * m) = h / m := by
  rcases hadmit with ⟨hp, hrho, hall⟩
  have restoredAdmission : PoweredGapFamilyAdmission p rho decrease K :=
    ⟨hp, hrho, hall⟩
  have htFirst : t < t + 1 := by omega
  have htSecond : t + 1 < t + 2 := by omega
  have hFirstIn : t + 1 < K := by omega
  have hSecondIn : t + 2 < K := htK
  have firstEquation :
      decrease t ^ (p - 1) - decrease (t + 1) ^ (p - 1) =
        1 / (p * rho) := by
    simpa using hall t (t + 1) htFirst hFirstIn
  have secondEquation :
      decrease (t + 1) ^ (p - 1) - decrease (t + 2) ^ (p - 1) =
        1 / (p * rho) := by
    simpa using hall (t + 1) (t + 2) htSecond hSecondIn
  have admittedSystem : TripleExponentRatioSystem
      (decrease t) (decrease (t + 1)) (decrease (t + 2)) p rho :=
    ⟨hp, hrho, firstEquation, secondEquation⟩
  obtain ⟨canonical, canonicalSystem, canonicalUnique⟩ :=
    logConcaveTriple_existsUnique_exponentRatio hc hcb hba hLogConcave
  have admittedEqualsCanonical : (p, rho) = canonical :=
    canonicalUnique (p, rho) admittedSystem
  refine ⟨poweredGapFamilyAdmission_pair_recovers_ratio
      restoredAdmission hij hjK,
    admittedSystem, ?_, common_positive_scale_ratio hlambda hm⟩
  intro parameter parameterSystem
  have parameterEqualsCanonical : parameter = canonical :=
    canonicalUnique parameter parameterSystem
  exact parameterEqualsCanonical.trans admittedEqualsCanonical.symm

end PhonologicalCalculus.ContinuousHG
