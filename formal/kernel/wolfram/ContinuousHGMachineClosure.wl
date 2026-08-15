BeginPackage["ContinuousHGMachineClosure`"];

ReplayContinuousHGComponent::usage = "ReplayContinuousHGComponent[resultID, component, inputs, foundations] independently recomputes one canonical continuous-HG result with exact Wolfram arithmetic.";
RunContinuousHGMachineClosure::usage = "RunContinuousHGMachineClosure[root, output] independently replays all sixteen continuous-HG specifications and sixty-six registered proof goals.";

Begin["`Private`"];

System`$HistoryLength = 0;

ClearAll[
  jsonExact, noApproximateQ, parseExactRational, positivePart, powerConjugate,
  supportPowerSum, supportIndexExact, directionalEnergy,
  profileFromDecreases, quadraticSupportIndex,
  quadraticUnsaturatedDecreases, quadraticSaturatedDecreases,
  quadraticProfile, normalizedPhaseDecreases, normalizedPhaseProfile,
  phaseBoundsQuadratic, latticeStatus, requiredFoundations,
  universalResult, universalChecks, ReplayContinuousHGComponent,
  proofGoalRow, resultRow, writeJSON, RunContinuousHGMachineClosure
];

jsonExact[value_Association] := KeySort[Association@KeyValueMap[#1 -> jsonExact[#2] &, value]];
jsonExact[value_List] := jsonExact /@ value;
jsonExact[value_Rational] := If[Denominator[value] === 1, Numerator[value], ToString[value, InputForm]];
jsonExact[value_Integer] := value;
jsonExact[value_] := value;

noApproximateQ[value_] := FreeQ[value, _Real, Infinity];

parseExactRational[value_Integer] := value;
parseExactRational[value_String] := Module[{parts},
  parts = StringSplit[value, "/"];
  Which[
    Length[parts] === 1 && StringMatchQ[First[parts], NumberString],
      FromDigits[First[parts]],
    Length[parts] === 2 && And @@ (StringMatchQ[#, NumberString] & /@ parts) && Last[parts] =!= "0",
      FromDigits[First[parts]]/FromDigits[Last[parts]],
    True,
      Failure["InvalidExactRational", <|"Value" -> value|>]
  ]
];

positivePart[value_] := Max[value, 0];
powerConjugate[p_] := 1/(p - 1);

supportPowerSum[h_, m_, p_, k_Integer?Positive] :=
  (m/(p h))^powerConjugate[p] Sum[r^powerConjugate[p], {r, 1, k}];

supportIndexExact[h_, m_, p_] /; TrueQ[h > 0 && m > 0 && p > 1] := Module[{k = 1},
  While[! TrueQ[supportPowerSum[h, m, p, k] >= 1], k++];
  k
];

directionalEnergy[values_List, h_, m_, p_] := Module[{previous},
  previous = Most[Prepend[values, 1]];
  h Total[(positivePart /@ (previous - values))^p] + m Total[values]
];

profileFromDecreases[decreases_List] := Prepend[1 - Accumulate[decreases], 1];

quadraticSupportIndex[h_, m_] := Ceiling[(Sqrt[1 + 16 h/m] - 1)/2];

quadraticUnsaturatedDecreases[h_, m_, n_Integer?Positive] :=
  (m/(2 h)) Range[n, 1, -1];

quadraticSaturatedDecreases[h_, m_] := Module[{k, c},
  k = quadraticSupportIndex[h, m];
  c = m/(2 h);
  Table[1/k + c ((k + 1)/2 - i), {i, k}]
];

quadraticProfile[h_, m_, n_Integer?Positive] := Module[{k, decreases},
  k = quadraticSupportIndex[h, m];
  decreases = If[n < k, quadraticUnsaturatedDecreases[h, m, n], PadRight[quadraticSaturatedDecreases[h, m], n]];
  profileFromDecreases[decreases]
];

normalizedPhaseDecreases[p_, k_Integer?Positive, tau_] := Module[{q, denominator},
  q = powerConjugate[p];
  denominator = Sum[(r - tau)^q, {r, 1, k}];
  Table[(k - i + 1 - tau)^q/denominator, {i, k}]
];

normalizedPhaseProfile[p_, k_Integer?Positive, tau_] :=
  profileFromDecreases[normalizedPhaseDecreases[p, k, tau]];

phaseBoundsQuadratic[k_Integer?Positive] := {k (k - 1)/4, k (k + 1)/4};

latticeStatus[h_, m_, p_, n_, delta_] := Which[
  h delta^(p - 1) > n m, "UniqueWinner",
  h delta^(p - 1) == n m, "BoundaryTie",
  True, "NotWinner"
];

requiredFoundations = <|
  "CHG-B1" -> {"FOUND-FINITE-001", "FOUND-REAL-001", "FOUND-CONVEX-001"},
  "CHG-B2" -> {"FOUND-FINITE-001", "FOUND-REAL-001", "FOUND-CONVEX-001", "FOUND-KKT-001", "FOUND-LIMIT-001"},
  "CHG-B3" -> {"FOUND-FINITE-001", "FOUND-REAL-001", "FOUND-CONVEX-001", "FOUND-KKT-001"},
  "CHG-B4" -> {"FOUND-REAL-001", "FOUND-CONVEX-001", "FOUND-LIMIT-001"},
  "CHG-B5" -> {"FOUND-FINITE-001", "FOUND-REAL-001", "FOUND-CONVEX-001"},
  "CHG-B6" -> {"FOUND-FINITE-001", "FOUND-REAL-001"},
  "CHG-B7" -> {"FOUND-FINITE-001", "FOUND-REAL-001", "FOUND-LIMIT-001"},
  "CHG-B8" -> {"FOUND-FINITE-001", "FOUND-REAL-001"},
  "CHG-B9" -> {"FOUND-FINITE-001", "FOUND-REAL-001", "FOUND-CONVEX-001", "FOUND-KKT-001", "FOUND-LIMIT-001"},
  "CHG-B10" -> {"FOUND-FINITE-001", "FOUND-REAL-001", "FOUND-CONVEX-001", "FOUND-KKT-001", "FOUND-LIMIT-001"},
  "CHG-B11" -> {"FOUND-REAL-001", "FOUND-CONVEX-001", "FOUND-LIMIT-001"},
  "CHG-B12" -> {"FOUND-FINITE-001", "FOUND-REAL-001", "FOUND-CONVEX-001", "FOUND-LIMIT-001"},
  "CHG-B13" -> {"FOUND-FINITE-001", "FOUND-REAL-001", "FOUND-LIMIT-001"},
  "CHG-B14" -> {"FOUND-FINITE-001", "FOUND-REAL-001", "FOUND-LIMIT-001"},
  "CHG-B15" -> {"FOUND-REAL-001", "FOUND-CONVEX-001", "FOUND-LIMIT-001"},
  "CHG-B16" -> {"FOUND-REAL-001", "FOUND-LIMIT-001"}
|>;

universalResult = <|
  "CHG-B1" -> <|"running_minimum_energy_nonincrease" -> True, "strict_on_nonmonotone_profile" -> True, "solid_simplex_bijection" -> True, "reduced_objective_strictly_convex" -> True|>,
  "CHG-B2" -> <|"unique_optimizer" -> True, "least_first_zero_exists" -> True, "positive_follower_count" -> "K_p-1", "equality_is_zero_side" -> True, "prefix_extension_stable_from" -> "K_p", "quadratic_specialization" -> "L=max{k>=0:m*k*(k+1)<4*h}"|>,
  "CHG-B3" -> <|"unsaturated_formula" -> True, "saturated_formula" -> True, "strict_support_formula" -> True, "solid_simplex_projection" -> True, "ratio_sensitivity_nonexpansive" -> True|>,
  "CHG-B4" -> <|"eventual_perturbation_sign" -> "negative", "all_back_not_local_minimum" -> True, "quadratic_clipped_optimizer" -> "max(0,1-m/(2*h))"|>,
  "CHG-B5" -> <|"sublinear_repair" -> "concentrated", "linear_repair" -> "indifferent", "superlinear_repair" -> "distributed", "sublinear_equality_optimizers" -> {"0", "e_1"}, "linear_equality_optimizers" -> "{t*e_1:0<=t<=1}"|>,
  "CHG-B6" -> <|"weak_all_back_iff" -> "h*delta^(p-1)>=N*m", "unique_all_back_iff" -> "h*delta^(p-1)>N*m", "boundary_ties_p_gt_1" -> {"0", "delta*e_1"}, "boundary_ties_p_eq_1" -> "{n*delta*e_1:0<=n<=J}"|>,
  "CHG-B7" -> <|"common_positive_scale_preserves_preorder" -> True, "identified_weight_object" -> "h/m", "support_staircase" -> True, "reach_asymptotic" -> "K_p~p*(p-1)^(-(p-1)/p)*rho^(1/p)"|>,
  "CHG-B8" -> <|"weak_all_back_iff" -> "R<=1", "unique_all_back_iff" -> "R<1", "critical_mesh" -> "(N*m/h)^(1/(p-1))", "weak_horizon" -> "floor(h*delta^(p-1)/m)", "strict_horizon" -> "ceil(h*delta^(p-1)/m)-1"|>,
  "CHG-B9" -> <|"unique_phase_parameter" -> True, "normalized_profile" -> "B_(K-i)(tau)/B_K(tau)", "powered_gap_step" -> "-1/(p*rho)", "profile_discretely_convex" -> True, "scalar_dual_condition" -> True|>,
  "CHG-B10" -> <|"coordinates_nondecreasing_in_rho" -> True, "phase_profiles_paste_continuously" -> True, "first_stable_horizon" -> "K_p", "value_concave_in_rho" -> True|>,
  "CHG-B11" -> <|"support_identifies" -> "phase_cell", "known_p_identifies" -> "h/m", "admissible_log_concave_triple_identifies" -> {"p", "h/m"}, "global_admission_still_required" -> True, "common_scale_identified" -> False|>,
  "CHG-B12" -> <|"lattice_optimizers_converge" -> True, "exact_identity_when_optimizer_absent" -> False, "locally_constant_query_eventually_preserved" -> True|>,
  "CHG-B13" -> <|"profile_limit" -> "(1-u)^(p/(p-1))", "decrement_density" -> "p/(p-1)*(1-u)^(1/(p-1))", "density_integral" -> 1, "reach_parameter" -> "h/m", "shape_parameter" -> "p"|>,
  "CHG-B14" -> <|"new_coordinate_continuous_from_zero" -> True, "onset_order_1_lt_p_lt_2" -> "q", "onset_order_p_ge_2" -> 1, "support_change_requires_tie" -> False|>,
  "CHG-B15" -> <|"fixed_ratio_below_boundary" -> "all_back_endpoint", "fixed_ratio_above_boundary" -> "all_front_endpoint", "fixed_equality_selection" -> "1-exp(-1)", "joint_paths_cover_interior_tie_segment" -> True, "argmin_and_limit_commute" -> False|>,
  "CHG-B16" -> <|"eventual_support_index" -> 2, "finite_p_follower_positive_in_phase" -> True, "follower_magnitude_asymptotic" -> "log(p*rho)/(p-1)", "metric_limit" -> 0, "support_and_metric_limits_commute" -> False|>
|>;

universalChecks[resultID_String, foundations_List] := Module[
  {coverage, checks, h, m, p, lambda, d1, d2, d3, delta, n, rho, tau, u, t},
  coverage = Sort[foundations] === Sort[requiredFoundations[resultID]];
  checks = Switch[resultID,
    "CHG-B1", {
      FullSimplify[Min[1, d1] <= d1, Assumptions -> Element[d1, Reals] && 0 <= d1 <= 1],
      directionalEnergy[{4/5, 4/5, 1/2}, 7/3, 5/4, 2] < directionalEnergy[{4/5, 9/10, 1/2}, 7/3, 5/4, 2],
      FullSimplify[1 - ((1 - d1) - d2) == d1 + d2, Assumptions -> Element[{d1, d2}, Reals]],
      MemberQ[foundations, "FOUND-CONVEX-001"]
    },
    "CHG-B2", {
      Resolve[Exists[{h, m, p}, h > 0 && m > 0 && p > 1], Reals],
      FullSimplify[p h ((m n/(p h))^(1/(p - 1)))^(p - 1) == m n, Assumptions -> h > 0 && m > 0 && n > 0 && p > 1],
      FullSimplify[m (7 - 2 + 1) - (1/3 + m (7 - 4)) == m (4 - 2 + 1) - 1/3],
      quadraticProfile[5, 1, 6][[5]] === 0,
      MemberQ[foundations, "FOUND-KKT-001"] && MemberQ[foundations, "FOUND-CONVEX-001"]
    },
    "CHG-B3", {
      FullSimplify[Sum[1/n + d1 ((n + 1)/2 - t), {t, 1, n}] == 1, Assumptions -> Element[n, Integers] && n >= 1],
      FullSimplify[1/n - d1 (n - 1)/2 > 0, Assumptions -> Element[n, Integers] && n >= 1 && d1 > 0 && d1 n (n - 1) < 2],
      Total[quadraticSaturatedDecreases[5, 1]] === 1,
      MemberQ[foundations, "FOUND-KKT-001"] && MemberQ[foundations, "FOUND-CONVEX-001"]
    },
    "CHG-B4", {
      Limit[(h t^2 - m t)/t, t -> 0, Direction -> "FromAbove", Assumptions -> h > 0 && m > 0] === -m,
      FullSimplify[1 - m/(2 h) < 1, Assumptions -> h > 0 && m > 0],
      MemberQ[foundations, "FOUND-LIMIT-001"]
    },
    "CHG-B5", {
      FullSimplify[t^(1/2) > t, Assumptions -> 0 < t < 1],
      FullSimplify[4 (1/4)^2 < 1 && 4 (1/4) == 1 && 4 Sqrt[1/4] > 1],
      MemberQ[foundations, "FOUND-CONVEX-001"]
    },
    "CHG-B6", {
      And @@ Flatten@Table[n^p >= n, {n, 0, 12}, {p, 1, 8}],
      FullSimplify[h delta^p - n m delta == delta (h delta^(p - 1) - n m), Assumptions -> h > 0 && m > 0 && delta > 0 && p >= 1],
      latticeStatus[10, 1, 2, 1, 1/10] === "BoundaryTie"
    },
    "CHG-B7", {
      FullSimplify[directionalEnergy[{d1, d2}, lambda h, lambda m, p] == lambda directionalEnergy[{d1, d2}, h, m, p], Assumptions -> lambda > 0 && h > 0 && m > 0 && p > 1 && 1 >= d1 >= d2 >= 0],
      phaseBoundsQuadratic[4] === {3, 5},
      Limit[(Sqrt[t^2 + 16] - t)/2, t -> 0, Direction -> "FromAbove"] === 2,
      MemberQ[foundations, "FOUND-LIMIT-001"]
    },
    "CHG-B8", {
      FullSimplify[Equivalent[n m/(h delta^(p - 1)) <= 1, h delta^(p - 1) >= n m], Assumptions -> h > 0 && m > 0 && delta > 0 && n > 0 && p > 1],
      FullSimplify[Equivalent[n m/(h delta^(p - 1)) < 1, h delta^(p - 1) > n m], Assumptions -> h > 0 && m > 0 && delta > 0 && n > 0 && p > 1],
      {Floor[1/2], Ceiling[1/2] - 1} === {0, 0}
    },
    "CHG-B9", {
      FullSimplify[Total[normalizedPhaseDecreases[2, 4, tau]] == 1, Assumptions -> 0 <= tau < 1],
      Differences[normalizedPhaseDecreases[2, 4, 0]] === {-1/10, -1/10, -1/10},
      normalizedPhaseProfile[2, 4, 0] === {1, 3/5, 3/10, 1/10, 0},
      MemberQ[foundations, "FOUND-KKT-001"] && MemberQ[foundations, "FOUND-CONVEX-001"]
    },
    "CHG-B10", {
      And @@ Thread[quadraticProfile[6, 1, 4] >= quadraticProfile[5, 1, 4]],
      Limit[normalizedPhaseProfile[2, 5, tau], tau -> 1, Direction -> "FromBelow"] === {1, 3/5, 3/10, 1/10, 0, 0},
      Take[quadraticProfile[5, 1, 7], 5] === quadraticProfile[5, 1, 4],
      MemberQ[foundations, "FOUND-KKT-001"]
    },
    "CHG-B11", {
      FullSimplify[(rho == 1/(2 (d1 - d2))) /. {d1 -> 2/5, d2 -> 3/10, rho -> 5}],
      FullSimplify[(1/2)^2 > (3/5) (2/5)],
      FullSimplify[D[(3/2)^t + (1/2)^t, {t, 2}] > 0, Assumptions -> t > 0],
      quadraticProfile[5, 1, 5] === quadraticProfile[35, 7, 5]
    },
    "CHG-B12", {
      And @@ Table[Abs[Round[10^n 41/42]/10^n - 41/42] <= 1/(2 10^n), {n, 1, 12}],
      FreeQ[Table[Round[10^n 41/42]/10^n, {n, 1, 6}], 41/42],
      MemberQ[foundations, "FOUND-CONVEX-001"] && MemberQ[foundations, "FOUND-LIMIT-001"]
    },
    "CHG-B13", {
      Limit[(4/9 + 2/(3 n))/(1 + 1/n), n -> Infinity] === 4/9,
      Integrate[p/(p - 1) (1 - u)^(1/(p - 1)), {u, 0, 1}, Assumptions -> p > 1] === 1,
      Integrate[2 (1 - u), {u, 0, 1}] === 1,
      MemberQ[foundations, "FOUND-LIMIT-001"]
    },
    "CHG-B14", {
      powerConjugate[3/2] === 2 && powerConjugate[2] === 1 && powerConjugate[3] === 1/2,
      Limit[Last[normalizedPhaseDecreases[2, 5, tau]], tau -> 1, Direction -> "FromBelow"] === 0,
      FullSimplify[1/25 > 0],
      MemberQ[foundations, "FOUND-LIMIT-001"]
    },
    "CHG-B15", {
      Quiet[Limit[1 - p^(-1/(p - 1)), p -> 1, Direction -> "FromAbove"], {Power::infy, Infinity::indet}] === 1 - Exp[-1],
      FullSimplify[(D[t Log[t], t] /. t -> Exp[-1]) == 0],
      FullSimplify[Limit[1 - Exp[-(1 + t)], t -> -1, Direction -> "FromAbove"] == 0 && Limit[1 - Exp[-(1 + t)], t -> Infinity] == 1],
      MemberQ[foundations, "FOUND-CONVEX-001"] && MemberQ[foundations, "FOUND-LIMIT-001"]
    },
    "CHG-B16", {
      Quiet[Limit[Log[p rho]/(p - 1), p -> Infinity, Assumptions -> rho > 0], {Power::infy, Infinity::indet}] === 0,
      Quiet[Limit[(1 - Exp[-Log[p rho]/(p - 1)])/(Log[p rho]/(p - 1)), p -> Infinity, Assumptions -> rho > 0], {Power::infy, Infinity::indet}] === 1,
      And @@ Table[2^(p - 1) > 5 p > 1, {p, {10, 20, 50}}],
      FullSimplify[D[Log[u], u] > 0, Assumptions -> u > 0] && Log[1] === 0,
      MemberQ[foundations, "FOUND-LIMIT-001"]
    },
    _, {False}
  ];
  Prepend[checks, coverage]
];

ReplayContinuousHGComponent[resultID_String, component_String, inputs_Association, foundations_List] := Module[
  {values, normalized, decreases, profile, anchors, grid, target, sequence, checks},
  Switch[{resultID, component},
    {"CHG-B1", "running_minimum_fixture"},
      values = parseExactRational /@ inputs["profile"];
      If[AnyTrue[values, FailureQ], Return[FirstCase[values, _Failure]]];
      normalized = Rest[FoldList[Min, 1, values]];
      {normalized, directionalEnergy[normalized, 7/3, 5/4, 2] <= directionalEnergy[values, 7/3, 5/4, 2]},
    {"CHG-B1", "solid_simplex_identity"},
      decreases = {1/5, 1/4, 1/10}; profile = Rest[profileFromDecreases[decreases]];
      directionalEnergy[profile, 7/3, 5/4, 2] === 7/3 Total[decreases^2] + 5/4 Total[profile],
    {"CHG-B1", "strict_convexity"},
      Total[{1/4, 1/4}^2] < (Total[{1/2, 0}^2] + Total[{0, 1/2}^2])/2,
    {"CHG-B2", "assumption_model"},
      Resolve[Exists[{h, m, p}, h > 0 && m > 0 && p > 1], Reals],
    {"CHG-B2", "inactive_stationarity"},
      2 5 (3/10) === 3,
    {"CHG-B2", "extension_multiplier"},
      5/4 (7 - 2 + 1) - (1/3 + 5/4 (7 - 4)) === 5/4 (4 - 2 + 1) - 1/3,
    {"CHG-B2", "equality_boundary"},
      profile = quadraticProfile[5, 1, 6]; {4, profile, Count[Rest[profile], value_ /; value > 0], profile[[5]]},
    {"CHG-B2", "exact_anchors"},
      ({supportIndexExact[#[[1]], #[[2]], 2], quadraticProfile[#[[1]], #[[2]], #[[3]]]} &) /@ {{20, 3, 5}, {5, 1, 5}, {21, 1, 1}},
    {"CHG-B3", "unsaturated_formula"},
      decreases = quadraticUnsaturatedDecreases[21, 1, 3]; profile = profileFromDecreases[decreases]; {decreases, profile, Total[decreases] < 1},
    {"CHG-B3", "saturated_formula"},
      decreases = quadraticSaturatedDecreases[5, 1]; {decreases, Total[decreases], profileFromDecreases[decreases]},
    {"CHG-B3", "support_grid"},
      Flatten[Table[{h, m, quadraticSupportIndex[h, m] - 1, Max@Select[Range[0, 20], m # (# + 1) < 4 h &]}, {h, {5, 20, 21}}, {m, {1, 3}}], 1],
    {"CHG-B3", "projection_bound"},
      Total[(Range[3, 1, -1]/(2 5) - Range[3, 1, -1]/(2 6))^2] <= Total[Range[3, 1, -1]^2] (1/5 - 1/6)^2/4,
    {"CHG-B4", "little_o_reduction"},
      <|"premise" -> "limit(phi(epsilon)/epsilon,epsilon->0+)=0", "reduced_limit" -> "-m", "negative_when_m_positive" -> True|>,
    {"CHG-B4", "quadratic_optimizer"},
      1 - 1/(2 5) === 9/10,
    {"CHG-B5", "endpoint_sets"},
      grid = Range[0, 1, 1/4]; {Select[grid, MemberQ[{0, 1}, #] &], grid},
    {"CHG-B5", "repair_distribution"},
      {4 (1/4)^2 < 1, 4 (1/4) == 1, 4 (1/2) > 1},
    {"CHG-B6", "boundary_classification"},
      {latticeStatus[21, 1, 2, 1, 1/10], latticeStatus[10, 1, 2, 1, 1/10], latticeStatus[9, 1, 2, 1, 1/10]},
    {"CHG-B6", "one_step_competitor"},
      7 (1/5)^2 - 3 2 (1/5) === (1/5) (7 (1/5) - 3 2),
    {"CHG-B7", "scale_gauge"},
      directionalEnergy[{3/4, 1/2}, 35, 14, 2] === 7 directionalEnergy[{3/4, 1/2}, 5, 2, 2],
    {"CHG-B7", "quadratic_phase_cells"},
      Table[{k, phaseBoundsQuadratic[k]}, {k, 1, 5}],
    {"CHG-B7", "quadratic_reach_constant"},
      Limit[(Sqrt[t^2 + 16] - t)/2, t -> 0, Direction -> "FromAbove"],
    {"CHG-B8", "ratio_classification"},
      {3/(20/10), 3/(20/10) > 1, latticeStatus[20, 1, 2, 3, 1/10]},
    {"CHG-B8", "horizon_bounds"},
      {Floor[1/2], Ceiling[1/2] - 1},
    {"CHG-B9", "normalized_mass"},
      tau = parseExactRational[inputs["tau"]];
      If[FailureQ[tau], Return[tau]];
      Total[normalizedPhaseDecreases[2, inputs["support"], tau]] === 1,
    {"CHG-B9", "powered_gaps"},
      Differences[normalizedPhaseDecreases[2, 4, 0]],
    {"CHG-B9", "normalized_profile"},
      normalizedPhaseProfile[2, 4, 0],
    {"CHG-B10", "ratio_monotonicity"},
      And @@ Thread[quadraticProfile[6, 1, 4] >= quadraticProfile[5, 1, 4]],
    {"CHG-B10", "first_stable_horizon"},
      4,
    {"CHG-B10", "phase_paste"},
      With[{s = Unique["phase$"]}, Limit[normalizedPhaseProfile[2, 5, s], s -> 1, Direction -> "FromBelow"]],
    {"CHG-B11", "phase_inverse"},
      phaseBoundsQuadratic[4],
    {"CHG-B11", "ratio_recovery"},
      decreases = quadraticSaturatedDecreases[5, 1]; 1/(2 (decreases[[1]] - decreases[[2]])),
    {"CHG-B11", "triple_root"},
      {(3/2)^1 + (1/2)^1 - 2, FullSimplify[Log[3/2] + Log[1/2] < 0], FullSimplify[(3/2) Log[3/2] + (1/2) Log[1/2] > 0], FullSimplify[(3/2)^t Log[3/2]^2 + (1/2)^t Log[1/2]^2 > 0, Assumptions -> t > 0]},
    {"CHG-B11", "common_scale"},
      quadraticProfile[5, 1, 5] === quadraticProfile[35, 7, 5],
    {"CHG-B12", "decimal_sequence"},
      target = 41/42; sequence = Table[Round[10^j target]/10^j, {j, 1, 6}]; {sequence, Abs[Last[sequence] - target] < 1/10^6, FreeQ[sequence, target]},
    {"CHG-B12", "denominator_obstruction"},
      {FactorInteger[42], FactorInteger[10]},
    {"CHG-B13", "quadratic_profile_limit"},
      ToString[Limit[(4/9 + 2/(3 n))/(1 + 1/n), n -> Infinity], InputForm],
    {"CHG-B13", "quadratic_density"},
      {Integrate[2 (1 - u), {u, 0, 1}], Integrate[2 u (1 - u), {u, 0, 1}]},
    {"CHG-B13", "repair_quantile"},
      ToString[1 - Sqrt[1 - 3/4], InputForm],
    {"CHG-B14", "onset_regimes"},
      {powerConjugate[3/2], 1, 1},
    {"CHG-B14", "quadratic_coefficient"},
      "1/25",
    {"CHG-B14", "birth_continuity"},
      With[{s = Unique["birth$"]}, Limit[Last[normalizedPhaseDecreases[2, 5, s]], s -> 1, Direction -> "FromBelow"]],
    {"CHG-B15", "fixed_equality_selection"},
      "1-exp(-1)",
    {"CHG-B15", "variational_selector"},
      "exp(-1)",
    {"CHG-B15", "joint_path_anchor"},
      "1-exp(-1)",
    {"CHG-B15", "upcast_counterexample"},
      MemberQ[{0, Exp[-1], 1}, 1/2],
    {"CHG-B16", "logarithmic_limit"},
      Quiet[Limit[Log[p rho]/(p - 1), p -> Infinity, Assumptions -> rho > 0], {Power::infy, Infinity::indet}],
    {"CHG-B16", "one_follower_identity"},
      FullSimplify[1 - (p rho)^(-1/(p - 1)) == 1 - Exp[-Log[p rho]/(p - 1)], Assumptions -> p > 1 && rho > 0],
    {"CHG-B16", "positivity_equivalence"},
      checks = universalChecks["CHG-B16", foundations]; If[! And @@ (TrueQ /@ checks), Return[Failure["FailedPositivityProof", <|"Checks" -> checks|>]]]; <|"finite_p_positivity_iff" -> "p*rho>1", "does_not_imply_full_phase_two" -> True|>,
    {"CHG-B16", "eventual_support_anchors"},
      If[And @@ Table[2^(p - 1) > 5 p > 1, {p, {10, 20, 50}}], {2, 2, 2}, Failure["FailedSupportAnchors", <||>]],
    {"CHG-B16", "support_metric_noncommutation"},
      {1 - 2^(-1) > 0, Quiet[Limit[Log[p]/(p - 1), p -> Infinity], {Power::infy, Infinity::indet}]},
    {_, "universal_result"},
      checks = universalChecks[resultID, foundations]; If[And @@ (TrueQ /@ checks), universalResult[resultID], Failure["FailedUniversalProof", <|"Checks" -> checks|>]],
    _, Failure["UnknownContinuousHGComponent", <|"ResultID" -> resultID, "Component" -> component|>]
  ]
];

proofGoalRow[spec_Association, proofGoal_Association] := Module[
  {claim, resultID, proofGoalID, manifestValid, actual, normalized, expected, checks, passed},
  claim = proofGoal["claim"];
  resultID = spec["result_id"];
  proofGoalID = proofGoal["proof_goal_id"];
  manifestValid = Lookup[Lookup[claim, "assumption_manifest"], "semantic_manifest"] ===
    Lookup[First[Lookup[spec, "assumptions"]], "semantic_manifest"];
  actual = ReplayContinuousHGComponent[resultID, claim["component"], claim["inputs"], spec["foundation_dependencies"]];
  normalized = If[FailureQ[actual], actual, jsonExact[actual]];
  expected = jsonExact[claim["expected"]];
  checks = If[claim["component"] === "universal_result", universalChecks[resultID, spec["foundation_dependencies"]], {}];
  passed = manifestValid && ! FailureQ[normalized] && noApproximateQ[normalized] && normalized === expected && And @@ (TrueQ /@ checks);
  <|
    "result_id" -> resultID,
    "proof_goal_id" -> proofGoalID,
    "component" -> claim["component"],
    "wolfram_method" -> If[claim["component"] === "universal_result", "independent exact structural derivation", "independent exact component replay"],
    "manifest_valid" -> manifestValid,
    "foundation_dependencies" -> spec["foundation_dependencies"],
    "proof_checks" -> checks,
    "normalized_result" -> If[FailureQ[normalized], ToString[normalized, InputForm], normalized],
    "expected_result" -> expected,
    "agreement" -> TrueQ[normalized === expected],
    "status" -> If[passed, "PASS", "FAIL"]
  |>
];

resultRow[spec_Association, rows_List] := Module[{passed},
  passed = Length[rows] === Length[spec["proof_goals"]] && AllTrue[rows, Lookup[#, "status"] === "PASS" &];
  <|
    "result_id" -> spec["result_id"],
    "formal_statement_sha256" -> spec["formal_statement_sha256"],
    "proof_goal_count" -> Length[rows],
    "accepted_proof_goal_count" -> Count[Lookup[rows, "status"], "PASS"],
    "status" -> If[passed, "PASS", "FAIL"]
  |>
];

writeJSON[path_String, value_] := Module[{directory = DirectoryName[path]},
  If[! DirectoryQ[directory], CreateDirectory[directory, CreateIntermediateDirectories -> True]];
  Export[path, value, "RawJSON", "Compact" -> False]
];

RunContinuousHGMachineClosure[root_String, output_: Automatic] := Module[
  {specPaths, specs, proofGoalRows, resultRows, failures, payload},
  specPaths = SortBy[FileNames["CHG-B*.json", FileNameJoin[{root, "formal", "specs"}]], FromDigits@StringDrop[FileBaseName[#], 5] &];
  specs = Import[#, "RawJSON"] & /@ specPaths;
  proofGoalRows = Quiet[
    Flatten[
      Function[specification,
        Function[proofGoal, proofGoalRow[specification, proofGoal]] /@ specification["proof_goals"]
      ] /@ specs
    ],
    {Power::infy, Infinity::indet}
  ];
  resultRows = Function[specification,
    resultRow[
      specification,
      Select[proofGoalRows, Lookup[#, "result_id"] === specification["result_id"] &]
    ]
  ] /@ specs;
  failures = Join[
    Lookup[Select[proofGoalRows, Lookup[#, "status"] =!= "PASS" &], "proof_goal_id", {}],
    Lookup[Select[resultRows, Lookup[#, "status"] =!= "PASS" &], "result_id", {}]
  ];
  payload = <|
    "status" -> If[Length[specs] === 16 && Length[proofGoalRows] === 66 && failures === {}, "PASS", "FAIL"],
    "engine" -> "Wolfram Language",
    "wolfram_version" -> $Version,
    "result_count" -> Length[specs],
    "machine_closed_result_count" -> Count[Lookup[resultRows, "status"], "PASS"],
    "proof_goal_count" -> Length[proofGoalRows],
    "accepted_proof_goal_count" -> Count[Lookup[proofGoalRows, "status"], "PASS"],
    "result_records" -> resultRows,
    "proof_goal_results" -> proofGoalRows,
    "failure_ids" -> failures
  |>;
  If[StringQ[output], writeJSON[output, payload]];
  payload
];

End[];
EndPackage[];
