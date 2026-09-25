import PhonologicalCalculus.ContinuousHG.PhaseComparativeStatics
import PhonologicalCalculus.ContinuousHG.GeneralPersistenceAsymptotic

namespace PhonologicalCalculus.ContinuousHG

open Filter Finset Set

theorem normalizedPhaseProfile_boundary_le_next
    {q tau : ℝ} {K i : ℕ}
    (hq : 0 < q) (hK : 0 < K) (htau : tau ∈ Ico (0 : ℝ) 1) :
    normalizedPhaseProfile q 0 K i ≤
      normalizedPhaseProfile q tau (K + 1) i := by
  have htendsto := normalizedPhaseProfile_phase_paste_tendsto hq hK i
  have heventually : ∀ᶠ offset : ℝ in nhdsWithin 1 (Iio 1),
      normalizedPhaseProfile q offset (K + 1) i ≤
        normalizedPhaseProfile q tau (K + 1) i := by
    have offsetAbove : ∀ᶠ offset : ℝ in nhds (1 : ℝ), tau < offset :=
      eventually_gt_nhds htau.2
    filter_upwards [offsetAbove.filter_mono inf_le_left,
      self_mem_nhdsWithin] with offset hoffset hbelow
    exact normalizedPhaseProfile_antitone_offset hq hoffset.le hbelow
  exact le_of_tendsto htendsto heventually

theorem normalizedPhaseProfile_zero_mono_support_add
    {q : ℝ} (hq : 0 < q) {K : ℕ} (hK : 0 < K) (R i : ℕ) :
    normalizedPhaseProfile q 0 K i ≤
      normalizedPhaseProfile q 0 (K + R) i := by
  induction R with
  | zero => simp
  | succ R ih =>
      calc
        normalizedPhaseProfile q 0 K i ≤
            normalizedPhaseProfile q 0 (K + R) i := ih
        _ ≤ normalizedPhaseProfile q 0 ((K + R) + 1) i :=
          normalizedPhaseProfile_boundary_le_next hq
            (Nat.add_pos_left hK R) ⟨le_rfl, zero_lt_one⟩
        _ = normalizedPhaseProfile q 0 (K + (R + 1)) i := by
          simp only [Nat.add_assoc]

theorem normalizedPhaseProfile_mono_of_support_lt
    {q tauEarly tauLate : ℝ} {K L i : ℕ}
    (hq : 0 < q) (hK : 0 < K) (hKL : K < L)
    (htauEarly : tauEarly ∈ Ico (0 : ℝ) 1)
    (htauLate : tauLate ∈ Ico (0 : ℝ) 1) :
    normalizedPhaseProfile q tauEarly K i ≤
      normalizedPhaseProfile q tauLate L i := by
  have earlyToEndpoint :
      normalizedPhaseProfile q tauEarly K i ≤
        normalizedPhaseProfile q 0 K i :=
    normalizedPhaseProfile_antitone_offset hq htauEarly.1 htauEarly.2
  let R := L - K - 1
  have supportIdentity : K + R + 1 = L := by
    dsimp [R]
    omega
  have endpointGrowth :
      normalizedPhaseProfile q 0 K i ≤
        normalizedPhaseProfile q 0 (K + R) i :=
    normalizedPhaseProfile_zero_mono_support_add hq hK R i
  have finalBoundary :
      normalizedPhaseProfile q 0 (K + R) i ≤
        normalizedPhaseProfile q tauLate ((K + R) + 1) i :=
    normalizedPhaseProfile_boundary_le_next hq
      (Nat.add_pos_left hK R) htauLate
  calc
    normalizedPhaseProfile q tauEarly K i ≤
        normalizedPhaseProfile q 0 K i := earlyToEndpoint
    _ ≤ normalizedPhaseProfile q 0 (K + R) i := endpointGrowth
    _ ≤ normalizedPhaseProfile q tauLate ((K + R) + 1) i := finalBoundary
    _ = normalizedPhaseProfile q tauLate L i := by rw [supportIdentity]

theorem normalizedPhaseProfile_global_mono_ratio
    {p rhoOne rhoTwo tauOne tauTwo : ℝ} {K L i : ℕ}
    (hp : 1 < p) (hrhoOne : 0 < rhoOne) (_hrhoTwo : 0 < rhoTwo)
    (hrho : rhoOne ≤ rhoTwo)
    (hcellOne : GeneralPowerRatioPhaseCell p rhoOne K)
    (hcellTwo : GeneralPowerRatioPhaseCell p rhoTwo L)
    (htauOne : tauOne ∈ Ico (0 : ℝ) 1)
    (htauTwo : tauTwo ∈ Ico (0 : ℝ) 1)
    (hphaseOne : shiftedPowerSum (powerShiftExponent p) tauOne K =
      (p * rhoOne) ^ powerShiftExponent p)
    (hphaseTwo : shiftedPowerSum (powerShiftExponent p) tauTwo L =
      (p * rhoTwo) ^ powerShiftExponent p) :
    normalizedPhaseProfile (powerShiftExponent p) tauOne K i ≤
      normalizedPhaseProfile (powerShiftExponent p) tauTwo L i := by
  have hKL : K ≤ L :=
    generalPowerRatioPhaseCell_mono hcellOne hcellTwo hrho
  rcases hKL.eq_or_lt with rfl | hKL
  · exact normalizedPhaseProfile_mono_ratio_of_phase hp hrhoOne hrho
      htauOne htauTwo hphaseOne hphaseTwo
  · exact normalizedPhaseProfile_mono_of_support_lt
      (powerShiftExponent_positive hp) hcellOne.2.2.1 hKL
      htauOne htauTwo

theorem generalPower_boundary_optimizer_profile_global_mono_ratio
    {p rhoOne rhoTwo : ℝ} {K L : ℕ}
    (hp : 1 < p) (hrhoOne : 0 < rhoOne) (hrhoTwo : 0 < rhoTwo)
    (hrho : rhoOne ≤ rhoTwo)
    (hcellOne : GeneralPowerFirstZeroCell rhoOne 1 p K)
    (hcellTwo : GeneralPowerFirstZeroCell rhoTwo 1 p L) :
    ∃ etaOne etaTwo : ℝ,
      0 ≤ etaOne ∧ etaOne < 1 ∧
      0 ≤ etaTwo ∧ etaTwo < 1 ∧
      powerPathMass rhoOne 1 p etaOne K = 1 ∧
      powerPathMass rhoTwo 1 p etaTwo L = 1 ∧
      IsUniqueMinimizerOn (SolidSimplex : (Fin K → ℝ) → Prop)
        (powerReducedObjective rhoOne 1 p (powerPathWeight K))
        (powerPathDecrease rhoOne 1 p etaOne K) ∧
      IsUniqueMinimizerOn (SolidSimplex : (Fin L → ℝ) → Prop)
        (powerReducedObjective rhoTwo 1 p (powerPathWeight L))
        (powerPathDecrease rhoTwo 1 p etaTwo L) ∧
      ∀ i : ℕ,
        powerProfileFromDecreases
            (powerPathDecrease rhoOne 1 p etaOne K) i ≤
          powerProfileFromDecreases
            (powerPathDecrease rhoTwo 1 p etaTwo L) i := by
  obtain ⟨etaOne, hetaOne, hetaOneBelow, hmassOne,
      huniqueOne, _hsupportOne, _hextensionsOne⟩ :=
    generalPower_all_horizon_finite_persistence hcellOne
  obtain ⟨etaTwo, hetaTwo, hetaTwoBelow, hmassTwo,
      huniqueTwo, _hsupportTwo, _hextensionsTwo⟩ :=
    generalPower_all_horizon_finite_persistence hcellTwo
  have ratioCellOne : GeneralPowerRatioPhaseCell p rhoOne K := by
    simpa using (generalPowerFirstZeroCell_iff_ratioPhase
      hrhoOne one_pos).1 hcellOne
  have ratioCellTwo : GeneralPowerRatioPhaseCell p rhoTwo L := by
    simpa using (generalPowerFirstZeroCell_iff_ratioPhase
      hrhoTwo one_pos).1 hcellTwo
  have tauOneRange : etaOne ∈ Ico (0 : ℝ) 1 := ⟨hetaOne, hetaOneBelow⟩
  have tauTwoRange : etaTwo ∈ Ico (0 : ℝ) 1 := ⟨hetaTwo, hetaTwoBelow⟩
  have phaseOne : shiftedPowerSum (powerShiftExponent p) etaOne K =
      (p * rhoOne) ^ powerShiftExponent p := by
    simpa using (powerPathMass_one_iff_phaseEquation
      hrhoOne one_pos hp hetaOneBelow).1 hmassOne
  have phaseTwo : shiftedPowerSum (powerShiftExponent p) etaTwo L =
      (p * rhoTwo) ^ powerShiftExponent p := by
    simpa using (powerPathMass_one_iff_phaseEquation
      hrhoTwo one_pos hp hetaTwoBelow).1 hmassTwo
  refine ⟨etaOne, etaTwo, hetaOne, hetaOneBelow, hetaTwo, hetaTwoBelow,
    hmassOne, hmassTwo, huniqueOne, huniqueTwo, ?_⟩
  intro i
  rw [powerProfileFromDecreases_eq_normalizedPhaseProfile
      hrhoOne one_pos hp hetaOneBelow hmassOne,
    powerProfileFromDecreases_eq_normalizedPhaseProfile
      hrhoTwo one_pos hp hetaTwoBelow hmassTwo]
  simpa using normalizedPhaseProfile_global_mono_ratio hp hrhoOne hrhoTwo
    hrho ratioCellOne ratioCellTwo tauOneRange tauTwoRange phaseOne phaseTwo

def GeneralPowerStablePositiveHorizon
    (h m p : ℝ) (N : ℕ) : Prop :=
  0 < N ∧ ∃ eta : ℝ,
    0 ≤ eta ∧ powerPathMass h m p eta N = 1 ∧
    IsUniqueMinimizerOn (SolidSimplex : (Fin N → ℝ) → Prop)
      (powerReducedObjective h m p (powerPathWeight N))
      (powerPathDecrease h m p eta N) ∧
    ∀ R : ℕ,
      IsUniqueMinimizerOn
        (SolidSimplex : (Fin (N + R) → ℝ) → Prop)
        (powerReducedObjective h m p (powerPathWeight (N + R)))
        (powerPathDecrease h m p (eta + m * R) (N + R)) ∧
      ∀ i : ℕ,
        powerProfileFromDecreases
            (powerPathDecrease h m p (eta + m * R) (N + R)) i =
          powerProfileFromDecreases (powerPathDecrease h m p eta N) i

theorem not_generalPowerStablePositiveHorizon_zero (h m p : ℝ) :
    ¬ GeneralPowerStablePositiveHorizon h m p 0 := by
  simp [GeneralPowerStablePositiveHorizon]

theorem generalPowerFirstZeroCell_stablePositive
    {h m p : ℝ} {K : ℕ} (hcell : GeneralPowerFirstZeroCell h m p K) :
    GeneralPowerStablePositiveHorizon h m p K := by
  obtain ⟨eta, heta, _hetaBelow, hmass, hunique,
      _hsupport, hextensions⟩ :=
    generalPower_all_horizon_finite_persistence hcell
  rcases hcell with ⟨hK, hh, hm, hp, _hprevious, _hboundary⟩
  refine ⟨hK, eta, heta, hmass, hunique, ?_⟩
  intro R
  exact ⟨(hextensions R).1,
    fun i => generalPower_profile_extension_stable hh hm hp heta R i⟩

theorem generalPowerFirstZeroCell_least_stablePositive
    {h m p : ℝ} {K : ℕ} (hcell : GeneralPowerFirstZeroCell h m p K) :
    GeneralPowerStablePositiveHorizon h m p K ∧
      ∀ J : ℕ, 0 < J → J < K →
        ¬ GeneralPowerStablePositiveHorizon h m p J := by
  rcases hcell with ⟨hK, hh, hm, hp, hprevious, hboundary⟩
  have restoredCell : GeneralPowerFirstZeroCell h m p K :=
    ⟨hK, hh, hm, hp, hprevious, hboundary⟩
  refine ⟨generalPowerFirstZeroCell_stablePositive restoredCell, ?_⟩
  intro J _hJ hJK hstable
  rcases hstable with
    ⟨_hJPositive, eta, heta, hmass, _hunique, _hextensions⟩
  have multiplierBound :
      powerPathMass h m p eta J ≤ powerPathMass h m p 0 J := by
    unfold powerPathMass
    exact powerKKTMass_antitone_multiplier (powerPathWeight J)
      hh hp heta
  have horizonBound :
      powerPathMass h m p 0 J ≤
        powerPathMass h m p 0 (K - 1) := by
    rw [powerPathMass_zero_eq_shiftedSum J hh hm hp,
      powerPathMass_zero_eq_shiftedSum (K - 1) hh hm hp]
    exact powerPathShiftedSum_monotone hh hm hp (by omega)
  linarith

theorem generalPowerFirstZeroCell_all_later_stablePositive
    {h m p : ℝ} {K : ℕ} (hcell : GeneralPowerFirstZeroCell h m p K)
    (R : ℕ) :
    GeneralPowerStablePositiveHorizon h m p (K + R) := by
  obtain ⟨eta, heta, _hetaBelow, hmass, _hunique,
      _hsupport, _hextensions⟩ :=
    generalPower_all_horizon_finite_persistence hcell
  rcases hcell with ⟨hK, hh, hm, hp, _hprevious, _hboundary⟩
  let etaR := eta + m * (R : ℝ)
  have hetaR : 0 ≤ etaR := by
    dsimp [etaR]
    positivity
  have hmassR : powerPathMass h m p etaR (K + R) = 1 := by
    dsimp [etaR]
    rw [powerPathMass_extension R hh hm hp heta, hmass]
  refine ⟨Nat.add_pos_left hK R, etaR, hetaR, hmassR,
    generalPower_extension_stable_unique_optimizer
      hh hm hp heta hmass R, ?_⟩
  intro S
  refine ⟨?_, fun i =>
    generalPower_profile_extension_stable hh hm hp hetaR S i⟩
  exact generalPower_extension_stable_unique_optimizer
    hh hm hp hetaR hmassR S

theorem generalPowerFirstZeroCell_minimal_extension_package
    {h m p : ℝ} {K : ℕ} (hcell : GeneralPowerFirstZeroCell h m p K) :
    GeneralPowerStablePositiveHorizon h m p K ∧
      (∀ J : ℕ, 0 < J → J < K →
        ¬ GeneralPowerStablePositiveHorizon h m p J) ∧
      ∃ eta : ℝ,
        0 ≤ eta ∧ eta < m ∧ powerPathMass h m p eta K = 1 ∧
        IsUniqueMinimizerOn (SolidSimplex : (Fin K → ℝ) → Prop)
          (powerReducedObjective h m p (powerPathWeight K))
          (powerPathDecrease h m p eta K) ∧
        ∀ R : ℕ,
          IsUniqueMinimizerOn
            (SolidSimplex : (Fin (K + R) → ℝ) → Prop)
            (powerReducedObjective h m p (powerPathWeight (K + R)))
            (powerPathDecrease h m p (eta + m * R) (K + R)) ∧
          ∀ i : ℕ,
            powerProfileFromDecreases
                (powerPathDecrease h m p (eta + m * R) (K + R)) i =
              powerProfileFromDecreases
                (powerPathDecrease h m p eta K) i := by
  have least := generalPowerFirstZeroCell_least_stablePositive hcell
  obtain ⟨eta, heta, hetaBelow, hmass, hunique, _hsupport, hextensions⟩ :=
    generalPower_all_horizon_finite_persistence hcell
  rcases hcell with ⟨_hK, hh, hm, hp, _hprevious, _hboundary⟩
  refine ⟨least.1, least.2, eta, heta, hetaBelow, hmass, hunique, ?_⟩
  intro R
  exact ⟨(hextensions R).1,
    fun i => generalPower_profile_extension_stable hh hm hp heta R i⟩

theorem exists_powerPath_active_unique_optimizer
    {rho p : ℝ} {N : ℕ}
    (hrho : 0 < rho) (hp : 1 < p)
    (hthreshold : 1 ≤ powerPathMass rho 1 p 0 N) :
    ∃ eta : ℝ,
      0 ≤ eta ∧ eta ≤ (N : ℝ) ∧
      powerPathMass rho 1 p eta N = 1 ∧
      IsUniqueMinimizerOn (SolidSimplex : (Fin N → ℝ) → Prop)
        (powerReducedObjective rho 1 p (powerPathWeight N))
        (powerPathDecrease rho 1 p eta N) := by
  have upperNonnegative : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  have clips : ∀ i : Fin N,
      (1 : ℝ) * powerPathWeight N i ≤ (N : ℝ) := by
    intro i
    simpa using powerPathWeight_le_horizon i
  obtain ⟨eta, heta, hetaUpper, hmass⟩ :=
    exists_powerKKT_multiplier (powerPathWeight N) hrho hp
      upperNonnegative clips (by simpa [powerPathMass] using hthreshold)
  refine ⟨eta, heta, hetaUpper, ?_, ?_⟩
  · simpa [powerPathMass] using hmass
  · change IsUniqueMinimizerOn
      (SolidSimplex : (Fin N → ℝ) → Prop)
      (powerReducedObjective rho 1 p (powerPathWeight N))
      (powerKKTDecrease rho 1 p eta (powerPathWeight N))
    exact powerKKTDecrease_unique_minimizer
      (powerPathWeight N) hrho hp heta hmass

theorem exists_powerPath_unique_optimizer
    {rho p : ℝ} (N : ℕ) (hrho : 0 < rho) (hp : 1 < p) :
    ∃ winner : Fin N → ℝ,
      IsUniqueMinimizerOn (SolidSimplex : (Fin N → ℝ) → Prop)
        (powerReducedObjective rho 1 p (powerPathWeight N)) winner := by
  by_cases hslack : powerPathMass rho 1 p 0 N ≤ 1
  · refine ⟨powerPathDecrease rho 1 p 0 N, ?_⟩
    change IsUniqueMinimizerOn
      (SolidSimplex : (Fin N → ℝ) → Prop)
      (powerReducedObjective rho 1 p (powerPathWeight N))
      (powerKKTDecrease rho 1 p 0 (powerPathWeight N))
    exact powerKKTDecrease_zero_unique_minimizer
      (powerPathWeight N) hrho hp (by simpa [powerPathMass] using hslack)
  · have hthreshold : 1 ≤ powerPathMass rho 1 p 0 N :=
      (lt_of_not_ge hslack).le
    obtain ⟨eta, _heta, _hetaUpper, _hmass, hunique⟩ :=
      exists_powerPath_active_unique_optimizer hrho hp hthreshold
    exact ⟨powerPathDecrease rho 1 p eta N, hunique⟩

theorem powerPathMinimumValue_concave_all_phases
    {rhoOne rhoTwo theta p : ℝ} (N : ℕ)
    (hrhoOne : 0 < rhoOne) (hrhoTwo : 0 < rhoTwo) (hp : 1 < p)
    (_hN : 0 < N) (hthetaZero : 0 ≤ theta) (hthetaOne : theta ≤ 1) :
    ∃ winnerOne winnerTwo winnerMiddle : Fin N → ℝ,
      IsUniqueMinimizerOn (SolidSimplex : (Fin N → ℝ) → Prop)
        (powerReducedObjective rhoOne 1 p (powerPathWeight N)) winnerOne ∧
      IsUniqueMinimizerOn (SolidSimplex : (Fin N → ℝ) → Prop)
        (powerReducedObjective rhoTwo 1 p (powerPathWeight N)) winnerTwo ∧
      IsUniqueMinimizerOn (SolidSimplex : (Fin N → ℝ) → Prop)
        (powerReducedObjective
          (theta * rhoOne + (1 - theta) * rhoTwo) 1 p
          (powerPathWeight N)) winnerMiddle ∧
      theta * powerReducedObjective rhoOne 1 p (powerPathWeight N) winnerOne +
        (1 - theta) *
          powerReducedObjective rhoTwo 1 p (powerPathWeight N) winnerTwo ≤
        powerReducedObjective
          (theta * rhoOne + (1 - theta) * rhoTwo) 1 p
          (powerPathWeight N) winnerMiddle := by
  have hrhoMiddle :
      0 < theta * rhoOne + (1 - theta) * rhoTwo := by
    have hthetaUpper : 0 ≤ 1 - theta := sub_nonneg.mpr hthetaOne
    rcases eq_or_lt_of_le hthetaZero with rfl | hthetaPositive
    · simpa using mul_pos (by linarith : 0 < 1 - (0 : ℝ)) hrhoTwo
    · exact add_pos_of_pos_of_nonneg
        (mul_pos hthetaPositive hrhoOne)
        (mul_nonneg hthetaUpper hrhoTwo.le)
  obtain ⟨winnerOne, huniqueOne⟩ :=
    exists_powerPath_unique_optimizer N hrhoOne hp
  obtain ⟨winnerTwo, huniqueTwo⟩ :=
    exists_powerPath_unique_optimizer N hrhoTwo hp
  obtain ⟨winnerMiddle, huniqueMiddle⟩ :=
    exists_powerPath_unique_optimizer N hrhoMiddle hp
  exact ⟨winnerOne, winnerTwo, winnerMiddle,
    huniqueOne, huniqueTwo, huniqueMiddle,
    powerMinimumValue_concave_in_ratio hthetaZero hthetaOne
      huniqueOne huniqueTwo huniqueMiddle⟩

theorem powerPathMinimumValue_concave_in_ratio
    {rhoOne rhoTwo theta p : ℝ} {N : ℕ}
    (hrhoOne : 0 < rhoOne) (hrhoTwo : 0 < rhoTwo) (hp : 1 < p)
    (hthetaZero : 0 ≤ theta) (hthetaOne : theta ≤ 1)
    (hthresholdOne : 1 ≤ powerPathMass rhoOne 1 p 0 N)
    (hthresholdTwo : 1 ≤ powerPathMass rhoTwo 1 p 0 N)
    (hthresholdMiddle :
      1 ≤ powerPathMass
        (theta * rhoOne + (1 - theta) * rhoTwo) 1 p 0 N) :
    ∃ etaOne etaTwo etaMiddle : ℝ,
      0 ≤ etaOne ∧ 0 ≤ etaTwo ∧ 0 ≤ etaMiddle ∧
      powerPathMass rhoOne 1 p etaOne N = 1 ∧
      powerPathMass rhoTwo 1 p etaTwo N = 1 ∧
      powerPathMass
        (theta * rhoOne + (1 - theta) * rhoTwo) 1 p etaMiddle N = 1 ∧
      IsUniqueMinimizerOn (SolidSimplex : (Fin N → ℝ) → Prop)
        (powerReducedObjective rhoOne 1 p (powerPathWeight N))
        (powerPathDecrease rhoOne 1 p etaOne N) ∧
      IsUniqueMinimizerOn (SolidSimplex : (Fin N → ℝ) → Prop)
        (powerReducedObjective rhoTwo 1 p (powerPathWeight N))
        (powerPathDecrease rhoTwo 1 p etaTwo N) ∧
      IsUniqueMinimizerOn (SolidSimplex : (Fin N → ℝ) → Prop)
        (powerReducedObjective
          (theta * rhoOne + (1 - theta) * rhoTwo) 1 p
          (powerPathWeight N))
        (powerPathDecrease
          (theta * rhoOne + (1 - theta) * rhoTwo) 1 p etaMiddle N) ∧
      theta * powerReducedObjective rhoOne 1 p (powerPathWeight N)
          (powerPathDecrease rhoOne 1 p etaOne N) +
        (1 - theta) * powerReducedObjective rhoTwo 1 p (powerPathWeight N)
          (powerPathDecrease rhoTwo 1 p etaTwo N) ≤
        powerReducedObjective
          (theta * rhoOne + (1 - theta) * rhoTwo) 1 p
          (powerPathWeight N)
          (powerPathDecrease
            (theta * rhoOne + (1 - theta) * rhoTwo) 1 p etaMiddle N) := by
  have hrhoMiddle :
      0 < theta * rhoOne + (1 - theta) * rhoTwo := by
    have hthetaUpper : 0 ≤ 1 - theta := sub_nonneg.mpr hthetaOne
    have hsum : 0 < theta * rhoOne + (1 - theta) * rhoTwo := by
      rcases eq_or_lt_of_le hthetaZero with rfl | hthetaPositive
      · simpa using mul_pos (by linarith : 0 < 1 - (0 : ℝ)) hrhoTwo
      · exact add_pos_of_pos_of_nonneg
          (mul_pos hthetaPositive hrhoOne)
          (mul_nonneg hthetaUpper hrhoTwo.le)
    exact hsum
  obtain ⟨etaOne, hetaOne, _hetaOneUpper, hmassOne, huniqueOne⟩ :=
    exists_powerPath_active_unique_optimizer hrhoOne hp hthresholdOne
  obtain ⟨etaTwo, hetaTwo, _hetaTwoUpper, hmassTwo, huniqueTwo⟩ :=
    exists_powerPath_active_unique_optimizer hrhoTwo hp hthresholdTwo
  obtain ⟨etaMiddle, hetaMiddle, _hetaMiddleUpper,
      hmassMiddle, huniqueMiddle⟩ :=
    exists_powerPath_active_unique_optimizer hrhoMiddle hp hthresholdMiddle
  refine ⟨etaOne, etaTwo, etaMiddle, hetaOne, hetaTwo, hetaMiddle,
    hmassOne, hmassTwo, hmassMiddle, huniqueOne, huniqueTwo,
    huniqueMiddle, ?_⟩
  exact powerMinimumValue_concave_in_ratio hthetaZero hthetaOne
    huniqueOne huniqueTwo huniqueMiddle

          
theorem chg_b10_complete_global_comparative_statics :
    (∀ (p rhoOne rhoTwo : ℝ) (K L : ℕ),
      1 < p → 0 < rhoOne → 0 < rhoTwo → rhoOne ≤ rhoTwo →
      GeneralPowerFirstZeroCell rhoOne 1 p K →
      GeneralPowerFirstZeroCell rhoTwo 1 p L →
      ∃ etaOne etaTwo : ℝ,
        0 ≤ etaOne ∧ etaOne < 1 ∧
        0 ≤ etaTwo ∧ etaTwo < 1 ∧
        powerPathMass rhoOne 1 p etaOne K = 1 ∧
        powerPathMass rhoTwo 1 p etaTwo L = 1 ∧
        IsUniqueMinimizerOn (SolidSimplex : (Fin K → ℝ) → Prop)
          (powerReducedObjective rhoOne 1 p (powerPathWeight K))
          (powerPathDecrease rhoOne 1 p etaOne K) ∧
        IsUniqueMinimizerOn (SolidSimplex : (Fin L → ℝ) → Prop)
          (powerReducedObjective rhoTwo 1 p (powerPathWeight L))
          (powerPathDecrease rhoTwo 1 p etaTwo L) ∧
        ∀ i : ℕ,
          powerProfileFromDecreases
              (powerPathDecrease rhoOne 1 p etaOne K) i ≤
            powerProfileFromDecreases
              (powerPathDecrease rhoTwo 1 p etaTwo L) i) ∧
    (∀ (h m p : ℝ) (K : ℕ), GeneralPowerFirstZeroCell h m p K →
      GeneralPowerStablePositiveHorizon h m p K ∧
      (∀ J : ℕ, 0 < J → J < K →
        ¬ GeneralPowerStablePositiveHorizon h m p J) ∧
      ∃ eta : ℝ,
        0 ≤ eta ∧ eta < m ∧ powerPathMass h m p eta K = 1 ∧
        IsUniqueMinimizerOn (SolidSimplex : (Fin K → ℝ) → Prop)
          (powerReducedObjective h m p (powerPathWeight K))
          (powerPathDecrease h m p eta K) ∧
        ∀ R : ℕ,
          IsUniqueMinimizerOn
            (SolidSimplex : (Fin (K + R) → ℝ) → Prop)
            (powerReducedObjective h m p (powerPathWeight (K + R)))
            (powerPathDecrease h m p (eta + m * R) (K + R)) ∧
          ∀ i : ℕ,
            powerProfileFromDecreases
                (powerPathDecrease h m p (eta + m * R) (K + R)) i =
              powerProfileFromDecreases
                (powerPathDecrease h m p eta K) i) ∧
    (∀ (rhoOne rhoTwo theta p : ℝ) (N : ℕ),
      0 < rhoOne → 0 < rhoTwo → 1 < p → 0 < N →
      0 ≤ theta → theta ≤ 1 →
      ∃ winnerOne winnerTwo winnerMiddle : Fin N → ℝ,
        IsUniqueMinimizerOn (SolidSimplex : (Fin N → ℝ) → Prop)
          (powerReducedObjective rhoOne 1 p (powerPathWeight N))
          winnerOne ∧
        IsUniqueMinimizerOn (SolidSimplex : (Fin N → ℝ) → Prop)
          (powerReducedObjective rhoTwo 1 p (powerPathWeight N))
          winnerTwo ∧
        IsUniqueMinimizerOn (SolidSimplex : (Fin N → ℝ) → Prop)
          (powerReducedObjective
            (theta * rhoOne + (1 - theta) * rhoTwo) 1 p
            (powerPathWeight N))
          winnerMiddle ∧
        theta * powerReducedObjective rhoOne 1 p (powerPathWeight N)
            winnerOne +
          (1 - theta) * powerReducedObjective rhoTwo 1 p (powerPathWeight N)
            winnerTwo ≤
          powerReducedObjective
            (theta * rhoOne + (1 - theta) * rhoTwo) 1 p
            (powerPathWeight N) winnerMiddle) ∧
    (∀ (q : ℝ) (K i : ℕ), 0 < q → 0 < K →
      Tendsto (fun tau : ℝ => normalizedPhaseProfile q tau (K + 1) i)
        (nhdsWithin 1 (Iio 1))
        (nhds (normalizedPhaseProfile q 0 K i))) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p rhoOne rhoTwo K L hp hrhoOne hrhoTwo hrho
      hcellOne hcellTwo
    exact generalPower_boundary_optimizer_profile_global_mono_ratio
      hp hrhoOne hrhoTwo hrho hcellOne hcellTwo
  · intro h m p K hcell
    exact generalPowerFirstZeroCell_minimal_extension_package hcell
  · intro rhoOne rhoTwo theta p N hrhoOne hrhoTwo hp hN
      hthetaZero hthetaOne
    exact powerPathMinimumValue_concave_all_phases N
      hrhoOne hrhoTwo hp hN hthetaZero hthetaOne
  · intro q K i hq hK
    exact normalizedPhaseProfile_phase_paste_tendsto hq hK i

end PhonologicalCalculus.ContinuousHG
