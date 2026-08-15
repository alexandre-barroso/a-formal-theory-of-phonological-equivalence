import PhonologicalCalculus.ContinuousHG.Quadratic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Sequences
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-!
# Lattice convergence and exact identity

This module formalizes the compact argmin-convergence result used by
`CHG-B12`.  Approximation of a unique continuum optimizer is kept distinct
from exact candidate identity and from eventual preservation of a query that
is locally constant at the optimizer.
-/

namespace PhonologicalCalculus.ContinuousHG

open Filter Set Topology

/-- A point is the unique minimizer of an objective on a carrier. -/
def IsUniqueCompactMinimizerOn {α : Type*} (carrier : Set α)
    (objective : α → ℝ) (optimizer : α) : Prop :=
  optimizer ∈ carrier ∧
    (∀ x ∈ carrier, objective optimizer ≤ objective x) ∧
    ∀ x ∈ carrier, objective x = objective optimizer → x = optimizer

/-- Exact minimizers on increasingly fine subsets of a compact carrier
converge to the unique continuum minimizer whenever each subset contains a
comparison point converging to that minimizer. -/
theorem compact_lattice_minimizers_converge
    {α : Type*} [PseudoMetricSpace α]
    {carrier : Set α} {objective : α → ℝ} {optimizer : α}
    {comparison latticeMinimizer : ℕ → α}
    (hcompact : IsCompact carrier)
    (hcontinuous : Continuous objective)
    (hunique : IsUniqueCompactMinimizerOn carrier objective optimizer)
    (hcomparisonCarrier : ∀ n, comparison n ∈ carrier)
    (hlatticeCarrier : ∀ n, latticeMinimizer n ∈ carrier)
    (hcomparison : Tendsto comparison atTop (𝓝 optimizer))
    (hoptimal : ∀ n, comparison n ∈ carrier →
      objective (latticeMinimizer n) ≤ objective (comparison n)) :
    Tendsto latticeMinimizer atTop (𝓝 optimizer) := by
  refine tendsto_of_subseq_tendsto ?_
  intro subsequence hsubsequence
  obtain ⟨limit, hlimitCarrier, extraction, hextraction,
      hlimit⟩ := hcompact.tendsto_subseq
        (x := latticeMinimizer ∘ subsequence)
        (fun n => hlatticeCarrier (subsequence n))
  refine ⟨extraction, ?_⟩
  have hobjectiveLimit :
      Tendsto (fun n => objective
        (latticeMinimizer (subsequence (extraction n))))
        atTop (𝓝 (objective limit)) := by
    simpa [Function.comp_def] using hcontinuous.continuousAt.tendsto.comp hlimit
  have hindexLimit :
      Tendsto (fun n => subsequence (extraction n)) atTop atTop :=
    hsubsequence.comp hextraction.tendsto_atTop
  have hcomparisonLimit :
      Tendsto (fun n => objective
        (comparison (subsequence (extraction n))))
        atTop (𝓝 (objective optimizer)) :=
    hcontinuous.continuousAt.tendsto.comp (hcomparison.comp hindexLimit)
  have hlimitUpper : objective limit ≤ objective optimizer :=
    le_of_tendsto_of_tendsto' hobjectiveLimit hcomparisonLimit
      (fun n => hoptimal (subsequence (extraction n))
        (hcomparisonCarrier (subsequence (extraction n))))
  have hlimitLower : objective optimizer ≤ objective limit :=
    hunique.2.1 limit hlimitCarrier
  have hlimitEq : limit = optimizer :=
    hunique.2.2 limit hlimitCarrier (le_antisymm hlimitUpper hlimitLower)
  simpa [Function.comp_def, hlimitEq] using hlimit

/-- A continuum optimizer absent from every lattice cannot be the exact
identity of any corresponding lattice minimizer. -/
theorem absent_optimizer_ne_lattice_minimizer
    {α : Type*} {lattice : ℕ → Set α} {optimizer : α}
    {latticeMinimizer : ℕ → α}
    (habsent : ∀ n, optimizer ∉ lattice n)
    (hmember : ∀ n, latticeMinimizer n ∈ lattice n) :
    ∀ n, latticeMinimizer n ≠ optimizer := by
  intro n heq
  exact habsent n (heq ▸ hmember n)

/-- Convergence preserves any query that is constant on a neighborhood of
the limiting optimizer, eventually. -/
theorem locally_constant_query_eventually_preserved
    {α β : Type*} [TopologicalSpace α]
    {sequence : ℕ → α} {optimizer : α} {query : α → β}
    (hsequence : Tendsto sequence atTop (𝓝 optimizer))
    (hlocal : ∀ᶠ x in 𝓝 optimizer, query x = query optimizer) :
    ∀ᶠ n in atTop, query (sequence n) = query optimizer :=
  hsequence.eventually hlocal

/-! ### Concrete density of the uniform solid-simplex lattice -/

/-- Coordinatewise lower rounding to the uniform grid of denominator `n+1`.
The lower rounding is essential: it preserves the solid-simplex mass bound. -/
noncomputable def uniformSimplexFloorApprox {N : ℕ}
    (u : Fin N → ℝ) (n : ℕ) : Fin N → ℝ :=
  fun i => (Nat.floor (((n + 1 : ℕ) : ℝ) * u i) : ℝ) / (n + 1 : ℕ)

/-- The complete uniform grid of denominator `n+1` inside the finite solid
simplex.  Coordinates are nonnegative rational multiples of the common mesh
and their sum is at most one. -/
def UniformSimplexLattice {N : ℕ} (n : ℕ) : Set (Fin N → ℝ) :=
  {d | SolidSimplex d ∧ ∀ i, ∃ k : ℕ,
    k ≤ n + 1 ∧ d i = (k : ℝ) / (n + 1 : ℕ)}

/-- Each complete uniform solid-simplex lattice is a finite set. -/
theorem UniformSimplexLattice.finite {N : ℕ} (n : ℕ) :
    (UniformSimplexLattice (N := N) n).Finite := by
  let realization : (Fin N → Fin (n + 2)) → (Fin N → ℝ) :=
    fun k i => (k i : ℕ) / (n + 1 : ℕ)
  apply Set.finite_range realization |>.subset
  intro d hd
  choose k hkBound hkValue using hd.2
  let code : Fin N → Fin (n + 2) := fun i =>
    ⟨k i, Nat.lt_succ_iff.mpr (hkBound i)⟩
  refine ⟨code, ?_⟩
  funext i
  exact (hkValue i).symm

/-- Every complete uniform solid-simplex lattice contains the zero vector. -/
theorem UniformSimplexLattice.nonempty {N : ℕ} (n : ℕ) :
    (UniformSimplexLattice (N := N) n).Nonempty := by
  refine ⟨0, ⟨?_, ?_⟩⟩
  · constructor
    · intro i
      simp
    · simp
  · intro i
    exact ⟨0, Nat.zero_le _, by simp⟩

/-- A continuous real objective attains a minimum on each complete uniform
solid-simplex lattice. -/
theorem exists_uniformSimplexLattice_minimizer {N : ℕ}
    (objective : (Fin N → ℝ) → ℝ) (hcontinuous : Continuous objective)
    (n : ℕ) :
    ∃ d ∈ UniformSimplexLattice (N := N) n,
      ∀ y ∈ UniformSimplexLattice (N := N) n, objective d ≤ objective y := by
  exact (UniformSimplexLattice.finite (N := N) n).isCompact.exists_isMinOn
    (UniformSimplexLattice.nonempty (N := N) n) hcontinuous.continuousOn

/-- A canonical exact minimizer selected from the nonempty finite uniform
solid-simplex lattice. -/
noncomputable def exactUniformSimplexLatticeMinimizer {N : ℕ}
    (objective : (Fin N → ℝ) → ℝ) (hcontinuous : Continuous objective)
    (n : ℕ) : Fin N → ℝ :=
  Classical.choose (exists_uniformSimplexLattice_minimizer objective hcontinuous n)

/-- The canonical selected lattice minimizer belongs to its grid and is
globally optimal on that complete finite grid. -/
theorem exactUniformSimplexLatticeMinimizer_spec {N : ℕ}
    (objective : (Fin N → ℝ) → ℝ) (hcontinuous : Continuous objective)
    (n : ℕ) :
    exactUniformSimplexLatticeMinimizer objective hcontinuous n ∈
        UniformSimplexLattice (N := N) n ∧
      ∀ y ∈ UniformSimplexLattice (N := N) n,
        objective (exactUniformSimplexLatticeMinimizer objective hcontinuous n) ≤
          objective y := by
  exact ⟨(Classical.choose_spec
    (exists_uniformSimplexLattice_minimizer objective hcontinuous n)).1,
    (Classical.choose_spec
      (exists_uniformSimplexLattice_minimizer objective hcontinuous n)).2⟩

/-- The finite solid simplex is closed in the product topology. -/
theorem isClosed_solidSimplex (N : ℕ) :
    IsClosed ({d : Fin N → ℝ | SolidSimplex d} : Set (Fin N → ℝ)) := by
  have hnonnegative :
      IsClosed {d : Fin N → ℝ | ∀ i, 0 ≤ d i} := by
    simpa only [Set.setOf_forall] using
      (isClosed_iInter fun i : Fin N =>
        isClosed_le continuous_const (continuous_apply i))
  have hmass :
      IsClosed {d : Fin N → ℝ | (∑ i, d i) ≤ 1} :=
    isClosed_le (by fun_prop) continuous_const
  simpa only [SolidSimplex, Set.setOf_and] using hnonnegative.inter hmass

/-- The finite solid simplex is compact.  This discharges the compactness
premise used by the lattice-convergence argument inside the project theorem. -/
theorem isCompact_solidSimplex (N : ℕ) :
    IsCompact ({d : Fin N → ℝ | SolidSimplex d} : Set (Fin N → ℝ)) := by
  apply IsCompact.of_isClosed_subset (isCompact_Icc :
    IsCompact (Set.Icc (0 : Fin N → ℝ) 1)) (isClosed_solidSimplex N)
  intro d hd
  refine ⟨hd.1, ?_⟩
  intro i
  exact (Finset.single_le_sum (fun j _ => hd.1 j)
    (Finset.mem_univ i)).trans hd.2

/-- Lower coordinatewise rounding maps every solid-simplex point into the
complete uniform lattice at every positive denominator. -/
theorem uniformSimplexFloorApprox_mem {N : ℕ} (u : Fin N → ℝ)
    (hu : SolidSimplex u) (n : ℕ) :
    uniformSimplexFloorApprox u n ∈ UniformSimplexLattice n := by
  have hDpos : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  have hpoint : ∀ i, 0 ≤ uniformSimplexFloorApprox u n i := by
    intro i
    exact div_nonneg (Nat.cast_nonneg _) hDpos.le
  have hcoord : ∀ i, uniformSimplexFloorApprox u n i ≤ u i := by
    intro i
    unfold uniformSimplexFloorApprox
    rw [div_le_iff₀ hDpos]
    simpa [mul_comm] using
      Nat.floor_le (mul_nonneg hDpos.le (hu.1 i))
  have hsum : (∑ i, uniformSimplexFloorApprox u n i) ≤ 1 := by
    exact (Finset.sum_le_sum fun i _ => hcoord i).trans hu.2
  refine ⟨⟨hpoint, hsum⟩, ?_⟩
  intro i
  refine ⟨Nat.floor (((n + 1 : ℕ) : ℝ) * u i), ?_, rfl⟩
  exact Nat.floor_le_of_le (by
    have huiSum : u i ≤ ∑ j, u j :=
      Finset.single_le_sum (fun j _ => hu.1 j) (Finset.mem_univ i)
    have hui : u i ≤ 1 := huiSum.trans hu.2
    nlinarith)

/-- Every coordinate of the canonical lower-rounding sequence converges to
the original solid-simplex coordinate, with error bounded by the common mesh. -/
theorem uniformSimplexFloorApprox_coordinate_tendsto {N : ℕ}
    (u : Fin N → ℝ) (hu : SolidSimplex u) (i : Fin N) :
    Tendsto (fun n => uniformSimplexFloorApprox u n i) atTop (𝓝 (u i)) := by
  apply tendsto_iff_dist_tendsto_zero.2
  have hbound : ∀ n,
      dist (uniformSimplexFloorApprox u n i) (u i) ≤
        (1 : ℝ) / (n + 1 : ℕ) := by
    intro n
    have hDpos : (0 : ℝ) < (n + 1 : ℕ) := by positivity
    have hfloorle : uniformSimplexFloorApprox u n i ≤ u i := by
      unfold uniformSimplexFloorApprox
      rw [div_le_iff₀ hDpos]
      simpa [mul_comm] using
        Nat.floor_le (mul_nonneg hDpos.le (hu.1 i))
    have hfloorerr :
        ((n + 1 : ℕ) : ℝ) * u i -
            (Nat.floor (((n + 1 : ℕ) : ℝ) * u i) : ℝ) < 1 :=
      Nat.self_sub_floor_lt_one _
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hfloorle)]
    unfold uniformSimplexFloorApprox
    rw [neg_sub]
    change u i -
      (Nat.floor (((n + 1 : ℕ) : ℝ) * u i) : ℝ) / (n + 1 : ℕ) ≤
        (1 : ℝ) / (n + 1 : ℕ)
    rw [show u i -
          (Nat.floor (((n + 1 : ℕ) : ℝ) * u i) : ℝ) / (n + 1 : ℕ) =
        (((n + 1 : ℕ) : ℝ) * u i -
          (Nat.floor (((n + 1 : ℕ) : ℝ) * u i) : ℝ)) / (n + 1 : ℕ) by
      field_simp [ne_of_gt hDpos]]
    apply (div_le_div_iff_of_pos_right hDpos).2
    exact hfloorerr.le
  exact squeeze_zero (fun n => dist_nonneg)
    hbound (by
      simpa [Nat.cast_add, Nat.cast_one] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))

/-- The complete uniform solid-simplex lattices are concretely dense: the
canonical lower-rounding sequence converges in the finite product topology. -/
theorem uniformSimplexFloorApprox_tendsto {N : ℕ}
    (u : Fin N → ℝ) (hu : SolidSimplex u) :
    Tendsto (uniformSimplexFloorApprox u) atTop (𝓝 u) := by
  rw [tendsto_pi_nhds]
  intro i
  exact uniformSimplexFloorApprox_coordinate_tendsto u hu i

/-- Exact minimizers on the complete uniform solid-simplex lattices converge
to the unique continuum minimizer.  Unlike the generic compactness theorem,
this result derives the required comparison sequence from the declared grid. -/
theorem uniformSimplexLattice_minimizers_converge
    {N : ℕ} {objective : (Fin N → ℝ) → ℝ} {optimizer : Fin N → ℝ}
    {latticeMinimizer : ℕ → Fin N → ℝ}
    (hcontinuous : Continuous objective)
    (hunique : IsUniqueCompactMinimizerOn
      ({d : Fin N → ℝ | SolidSimplex d} : Set (Fin N → ℝ))
      objective optimizer)
    (hlattice : ∀ n, latticeMinimizer n ∈ UniformSimplexLattice n)
    (hoptimal : ∀ n d, d ∈ UniformSimplexLattice n →
      objective (latticeMinimizer n) ≤ objective d) :
    Tendsto latticeMinimizer atTop (𝓝 optimizer) := by
  apply compact_lattice_minimizers_converge (isCompact_solidSimplex N)
    hcontinuous hunique
    (comparison := uniformSimplexFloorApprox optimizer)
  · intro n
    exact (uniformSimplexFloorApprox_mem optimizer hunique.1 n).1
  · intro n
    exact (hlattice n).1
  · exact uniformSimplexFloorApprox_tendsto optimizer hunique.1
  · intro n _
    exact hoptimal n _ (uniformSimplexFloorApprox_mem optimizer hunique.1 n)

/-- The canonically selected exact minimizer on each complete uniform lattice
converges to the unique continuum minimizer; no external minimizer sequence or
existence premise remains. -/
theorem exactUniformSimplexLatticeMinimizer_tendsto
    {N : ℕ} {objective : (Fin N → ℝ) → ℝ} {optimizer : Fin N → ℝ}
    (hcontinuous : Continuous objective)
    (hunique : IsUniqueCompactMinimizerOn
      ({d : Fin N → ℝ | SolidSimplex d} : Set (Fin N → ℝ))
      objective optimizer) :
    Tendsto (exactUniformSimplexLatticeMinimizer objective hcontinuous)
      atTop (𝓝 optimizer) := by
  apply uniformSimplexLattice_minimizers_converge hcontinuous hunique
  · intro n
    exact (exactUniformSimplexLatticeMinimizer_spec objective hcontinuous n).1
  · intro n d hd
    exact (exactUniformSimplexLatticeMinimizer_spec objective hcontinuous n).2 d hd

/-- Concrete `CHG-B12` closure for the complete uniform lattices: optimizer
convergence, persistent failure of exact identity when the continuum optimizer
is absent from every grid, and eventual preservation of every locally constant
query. -/
theorem chg_b12_uniformSimplexLattice_convergence_without_identity
    {N : ℕ} {β : Type*}
    {objective : (Fin N → ℝ) → ℝ} {optimizer : Fin N → ℝ}
    {latticeMinimizer : ℕ → Fin N → ℝ} {query : (Fin N → ℝ) → β}
    (hcontinuous : Continuous objective)
    (hunique : IsUniqueCompactMinimizerOn
      ({d : Fin N → ℝ | SolidSimplex d} : Set (Fin N → ℝ))
      objective optimizer)
    (hlattice : ∀ n, latticeMinimizer n ∈ UniformSimplexLattice n)
    (hoptimal : ∀ n d, d ∈ UniformSimplexLattice n →
      objective (latticeMinimizer n) ≤ objective d)
    (habsent : ∀ n, optimizer ∉ UniformSimplexLattice n)
    (hlocal : ∀ᶠ x in 𝓝 optimizer, query x = query optimizer) :
    Tendsto latticeMinimizer atTop (𝓝 optimizer) ∧
      (∀ n, latticeMinimizer n ≠ optimizer) ∧
      ∀ᶠ n in atTop, query (latticeMinimizer n) = query optimizer := by
  have hconvergence := uniformSimplexLattice_minimizers_converge
    hcontinuous hunique hlattice hoptimal
  exact ⟨hconvergence,
    absent_optimizer_ne_lattice_minimizer habsent (fun n => hlattice n),
    locally_constant_query_eventually_preserved hconvergence hlocal⟩

/-- Fully internal selected-minimizer form of `CHG-B12`.  Finite-lattice
existence, density, compactness, convergence, nonidentity, and local-query
stability are all discharged in Lean from the declared hypotheses. -/
theorem chg_b12_exactUniformSimplexLattice_selectedMinimizers
    {N : ℕ} {β : Type*}
    {objective : (Fin N → ℝ) → ℝ} {optimizer : Fin N → ℝ}
    {query : (Fin N → ℝ) → β}
    (hcontinuous : Continuous objective)
    (hunique : IsUniqueCompactMinimizerOn
      ({d : Fin N → ℝ | SolidSimplex d} : Set (Fin N → ℝ))
      objective optimizer)
    (habsent : ∀ n, optimizer ∉ UniformSimplexLattice (N := N) n)
    (hlocal : ∀ᶠ x in 𝓝 optimizer, query x = query optimizer) :
    Tendsto (exactUniformSimplexLatticeMinimizer objective hcontinuous)
        atTop (𝓝 optimizer) ∧
      (∀ n, exactUniformSimplexLatticeMinimizer objective hcontinuous n ≠
        optimizer) ∧
      ∀ᶠ n in atTop,
        query (exactUniformSimplexLatticeMinimizer objective hcontinuous n) =
          query optimizer := by
  have hconvergence := exactUniformSimplexLatticeMinimizer_tendsto
    hcontinuous hunique
  have hmember : ∀ n,
      exactUniformSimplexLatticeMinimizer objective hcontinuous n ∈
        UniformSimplexLattice (N := N) n := fun n =>
    (exactUniformSimplexLatticeMinimizer_spec objective hcontinuous n).1
  exact ⟨hconvergence,
    absent_optimizer_ne_lattice_minimizer habsent hmember,
    locally_constant_query_eventually_preserved hconvergence hlocal⟩

/-- The six registered nearest decimal-lattice representatives for the
quadratic optimizer `41/42`. -/
def chgB12DecimalTargets : List ℚ :=
  [1, 49 / 50, 122 / 125, 4881 / 5000, 97619 / 100000,
    97619 / 100000]

/-- Exact replay of the registered decimal sequence, its final error bound,
and the absence of exact identity in the six displayed grids. -/
theorem chg_b12_decimal_sequence :
    chgB12DecimalTargets =
      [1, 49 / 50, 122 / 125, 4881 / 5000, 97619 / 100000,
        97619 / 100000] ∧
    |(97619 / 100000 : ℚ) - 41 / 42| < 1 / 1000000 ∧
    (41 / 42 : ℚ) ∉ chgB12DecimalTargets := by
  norm_num [chgB12DecimalTargets, abs_of_nonpos, abs_of_nonneg]

/-- The rational optimizer `41/42` is absent from every terminating decimal
lattice, independently of grid precision. -/
theorem fortyOne_over_fortyTwo_not_terminating_decimal (k n : ℕ) :
    (k : ℚ) / (10 : ℚ) ^ n ≠ 41 / 42 := by
  intro heq
  have hnat : 42 * k = 41 * 10 ^ n := by
    field_simp at heq
    have hnat' : k * 42 = 10 ^ n * 41 := by exact_mod_cast heq
    simpa [mul_comm] using hnat'
  have hzmod :
      ((42 * k : ℕ) : ZMod 3) = ((41 * 10 ^ n : ℕ) : ZMod 3) := by
    exact congrArg (fun value : ℕ => (value : ZMod 3)) hnat
  have h42 : (42 : ZMod 3) = 0 := by decide
  have h41 : (41 : ZMod 3) = 2 := by decide
  have h10 : (10 : ZMod 3) = 1 := by decide
  push_cast at hzmod
  rw [h42, h41, h10, one_pow, zero_mul, mul_one] at hzmod
  exact (by decide : (0 : ZMod 3) ≠ 2) hzmod

/-- A rational point on the grid with positive integer denominator `D`. -/
def rationalGridPoint (D : ℕ) (numerator : ℤ) : ℚ :=
  numerator / D

/-- A grid point is nearest when no integer numerator gives a smaller
absolute error. -/
def IsNearestRationalGridPoint (D : ℕ) (target : ℚ)
    (numerator : ℤ) : Prop :=
  ∀ alternative : ℤ,
    |target - rationalGridPoint D numerator| ≤
      |target - rationalGridPoint D alternative|

/-- Midpoint inequalities prove a nearest point on any positive uniform
rational grid. -/
theorem nearest_rationalGridPoint_of_midpoints
    {D : ℕ} (hD : 0 < D) {target : ℚ} {numerator : ℤ}
    (hlower : 2 * (numerator : ℚ) - 1 ≤ 2 * D * target)
    (hupper : 2 * D * target ≤ 2 * (numerator : ℚ) + 1) :
    IsNearestRationalGridPoint D target numerator := by
  intro alternative
  by_cases heq : alternative = numerator
  · subst alternative
    rfl
  have hDq : (0 : ℚ) < D := by exact_mod_cast hD
  rcases lt_or_gt_of_ne heq with hless | hgreater
  · have halternative : (alternative : ℚ) ≤ (numerator : ℚ) - 1 := by
      exact_mod_cast (Int.le_sub_one_iff.mpr hless)
    have hright :
        0 ≤ target - rationalGridPoint D alternative := by
      unfold rationalGridPoint
      apply sub_nonneg.mpr
      rw [div_le_iff₀ hDq]
      nlinarith
    rw [abs_of_nonneg hright]
    by_cases htarget : target ≤ rationalGridPoint D numerator
    · rw [abs_of_nonpos (sub_nonpos.mpr htarget)]
      unfold rationalGridPoint at htarget ⊢
      field_simp [ne_of_gt hDq] at htarget ⊢
      nlinarith
    · have htarget' : rationalGridPoint D numerator ≤ target :=
        le_of_not_ge htarget
      rw [abs_of_nonneg (sub_nonneg.mpr htarget')]
      unfold rationalGridPoint at htarget' ⊢
      field_simp [ne_of_gt hDq] at htarget' ⊢
      nlinarith
  · have halternative : (numerator : ℚ) + 1 ≤ (alternative : ℚ) := by
      exact_mod_cast (Int.add_one_le_iff.mpr hgreater)
    have hright :
        target - rationalGridPoint D alternative ≤ 0 := by
      unfold rationalGridPoint
      apply sub_nonpos.mpr
      rw [le_div_iff₀ hDq]
      nlinarith
    rw [abs_of_nonpos hright]
    by_cases htarget : target ≤ rationalGridPoint D numerator
    · rw [abs_of_nonpos (sub_nonpos.mpr htarget)]
      unfold rationalGridPoint at htarget ⊢
      field_simp [ne_of_gt hDq] at htarget ⊢
      nlinarith
    · have htarget' : rationalGridPoint D numerator ≤ target :=
        le_of_not_ge htarget
      rw [abs_of_nonneg (sub_nonneg.mpr htarget')]
      unfold rationalGridPoint at htarget' ⊢
      field_simp [ne_of_gt hDq] at htarget' ⊢
      nlinarith

/-- Each registered decimal representative is an exact nearest point to
`41/42` on its stated decimal lattice. -/
theorem chg_b12_decimal_targets_are_nearest :
    IsNearestRationalGridPoint 10 (41 / 42) 10 ∧
    IsNearestRationalGridPoint 100 (41 / 42) 98 ∧
    IsNearestRationalGridPoint 1000 (41 / 42) 976 ∧
    IsNearestRationalGridPoint 10000 (41 / 42) 9762 ∧
    IsNearestRationalGridPoint 100000 (41 / 42) 97619 ∧
    IsNearestRationalGridPoint 1000000 (41 / 42) 976190 := by
  constructor
  · apply nearest_rationalGridPoint_of_midpoints <;> norm_num
  constructor
  · apply nearest_rationalGridPoint_of_midpoints <;> norm_num
  constructor
  · apply nearest_rationalGridPoint_of_midpoints <;> norm_num
  constructor
  · apply nearest_rationalGridPoint_of_midpoints <;> norm_num
  constructor <;>
    apply nearest_rationalGridPoint_of_midpoints <;> norm_num

/-- Registered universal content of `CHG-B12`: convergence, persistent
nonidentity when the optimizer is absent, and eventual stability of every
locally constant query. -/
theorem chg_b12_lattice_convergence_without_identity
    {α β : Type*} [PseudoMetricSpace α]
    {carrier : Set α} {objective : α → ℝ} {optimizer : α}
    {lattice : ℕ → Set α}
    {comparison latticeMinimizer : ℕ → α} {query : α → β}
    (hcompact : IsCompact carrier)
    (hcontinuous : Continuous objective)
    (hunique : IsUniqueCompactMinimizerOn carrier objective optimizer)
    (hcomparisonCarrier : ∀ n, comparison n ∈ carrier)
    (hlatticeCarrier : ∀ n, latticeMinimizer n ∈ carrier)
    (hcomparison : Tendsto comparison atTop (𝓝 optimizer))
    (hoptimal : ∀ n, comparison n ∈ carrier →
      objective (latticeMinimizer n) ≤ objective (comparison n))
    (habsent : ∀ n, optimizer ∉ lattice n)
    (hmember : ∀ n, latticeMinimizer n ∈ lattice n)
    (hlocal : ∀ᶠ x in 𝓝 optimizer, query x = query optimizer) :
    Tendsto latticeMinimizer atTop (𝓝 optimizer) ∧
      (∀ n, latticeMinimizer n ≠ optimizer) ∧
      ∀ᶠ n in atTop, query (latticeMinimizer n) = query optimizer := by
  have hconvergence := compact_lattice_minimizers_converge hcompact
    hcontinuous hunique hcomparisonCarrier hlatticeCarrier hcomparison hoptimal
  exact ⟨hconvergence,
    absent_optimizer_ne_lattice_minimizer habsent hmember,
    locally_constant_query_eventually_preserved hconvergence hlocal⟩

end PhonologicalCalculus.ContinuousHG
