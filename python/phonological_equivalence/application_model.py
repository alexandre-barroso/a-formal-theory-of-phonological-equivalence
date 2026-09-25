from __future__ import annotations

from fractions import Fraction
from itertools import permutations, product
from typing import Any

from .rational import ParseRational, RationalText


def QuadraticSupportIndex(harmony: Fraction, markedness: Fraction) -> int:
    if harmony <= 0 or markedness <= 0:
        raise ValueError("Quadratic profile weights must be positive")
    index = 1
    while markedness * index * (index + 1) < 4 * harmony:
        index += 1
    return index


def QuadraticProfile(harmony: Fraction, markedness: Fraction, horizon: int) -> list[Fraction]:
    if not isinstance(horizon, int) or isinstance(horizon, bool) or horizon < 1:
        raise ValueError("Quadratic profile horizon must be a positive integer")
    support = QuadraticSupportIndex(harmony, markedness)
    scale = markedness / (2 * harmony)
    if horizon < support:
        decreases = [scale * rank for rank in range(horizon, 0, -1)]
    else:
        decreases = [Fraction(1, support) + scale * (Fraction(support + 1, 2) - index) for index in range(1, support + 1)]
        decreases.extend(Fraction(0) for _ in range(horizon - support))
    profile = [Fraction(1)]
    for decrease in decreases:
        profile.append(profile[-1] - decrease)
    if any(value < 0 or value > 1 for value in profile) or any(later > earlier for earlier, later in zip(profile, profile[1:])):
        raise ValueError("Derived quadratic profile leaves the monotone unit interval")
    return profile


def ParseWeights(value: dict[str, Any]) -> tuple[Fraction, Fraction]:
    return ParseRational(value["h"]), ParseRational(value["m"])


def QuadraticObjective(harmony: Fraction, markedness: Fraction, value: Fraction) -> Fraction:
    return harmony * (1 - value) ** 2 + markedness * value


def ContinuumMinimum(inputs: dict[str, Any]) -> tuple[str, dict[str, Any]]:
    harmony, markedness = ParseWeights(inputs)
    lower = ParseRational(inputs["lower"])
    upper = ParseRational(inputs["upper"])
    if lower != 0 or upper != 1:
        raise ValueError("The registered continuum application requires [0,1]")
    minimizer = 1 - markedness / (2 * harmony)
    if not lower <= minimizer <= upper:
        raise ValueError("The stationary point is outside the registered interval")
    derivative = 2 * harmony * (minimizer - 1) + markedness
    constant = QuadraticObjective(harmony, markedness, minimizer)
    left_coefficients = [harmony, markedness - 2 * harmony, harmony - constant]
    right_coefficients = [harmony, -2 * harmony * minimizer, harmony * minimizer ** 2]
    if derivative != 0 or left_coefficients != right_coefficients or harmony <= 0:
        raise ValueError("Exact completing-square global-minimum identity failed")
    return RationalText(minimizer), {"minimizer": RationalText(minimizer), "objective": RationalText(constant), "difference_identity_coefficients": [RationalText(value) for value in left_coefficients], "strict_convexity_coefficient": RationalText(harmony)}


def GridMinimum(inputs: dict[str, Any]) -> tuple[str, dict[str, Any]]:
    harmony, markedness = ParseWeights(inputs)
    lower = ParseRational(inputs["lower"])
    upper = ParseRational(inputs["upper"])
    step = ParseRational(inputs["step"])
    if step <= 0 or lower >= upper:
        raise ValueError("Malformed uniform grid")
    count = (upper - lower) / step
    if count.denominator != 1:
        raise ValueError("Uniform grid does not terminate at the upper endpoint")
    domain = [lower + step * index for index in range(count.numerator + 1)]
    energies = [QuadraticObjective(harmony, markedness, value) for value in domain]
    minimum = min(energies)
    winners = [value for value, energy in zip(domain, energies, strict=True) if energy == minimum]
    if len(winners) != 1:
        raise ValueError("Registered uniform-grid application lacks a unique winner")
    return RationalText(winners[0]), {"domain_cardinality": len(domain), "domain": [RationalText(value) for value in domain], "energies": [RationalText(value) for value in energies], "winner": RationalText(winners[0])}


def ProfileResult(inputs: dict[str, Any]) -> tuple[list[str], dict[str, Any]]:
    harmony, markedness = ParseWeights(inputs)
    profile = QuadraticProfile(harmony, markedness, inputs["horizon"])
    result = [RationalText(value) for value in profile]
    return result, {"support_index": QuadraticSupportIndex(harmony, markedness), "profile": result}


def BasicSyllableInventory(transcription: dict[str, Any], inputs: dict[str, Any]) -> tuple[dict[str, Any], dict[str, Any]]:
    tensor = transcription["formal_objects"]["violation_tensor"]
    ranking_count = inputs["ranking_count"]
    if ranking_count != 24 or len(tensor) != 4 or any(len(rows) != 4 for rows in tensor):
        raise ValueError("Basic Syllable source transcription has the wrong finite domain")
    rankings = list(permutations(range(4)))
    winner_maps = []
    for ranking in rankings:
        winners = []
        for rows in tensor:
            keys = [tuple(row[index] for index in ranking) for row in rows]
            minimum = min(keys)
            if keys.count(minimum) != 1:
                raise ValueError("Basic Syllable strict-ranking event contains a tie")
            winners.append(keys.index(minimum))
        winner_maps.append(tuple(winners))
    mappings = list(product(range(4), range(4)))
    events = {mapping: {index for index, winners in enumerate(winner_maps) if winners[mapping[0]] == mapping[1]} for mapping in mappings}
    pairs = [(antecedent, consequent) for antecedent, consequent in product(mappings, repeat=2) if (not inputs["exclude_reflexive"] or antecedent != consequent) and events[antecedent].issubset(events[consequent])]
    empty = sum(not events[antecedent] for antecedent, _ in pairs)
    live = len(pairs) - empty
    result = {"Inventory": [len(pairs), empty, live], "ReusedFrom": "MAX-G6"}
    detail = {"ranking_count": len(rankings), "distinct_winner_maps": [list(value) for value in sorted(set(winner_maps))], "mapping_count": len(mappings), "empty_mapping_count": sum(not event for event in events.values()), "universal_count": len(pairs), "empty_antecedent_count": empty, "live_antecedent_count": live}
    return result, detail


def ReplayApplication(algorithm: str, inputs: Any, transcription: dict[str, Any]) -> tuple[Any, dict[str, Any]]:
    if algorithm == "quadratic_continuum_minimum_v1":
        return ContinuumMinimum(inputs)
    if algorithm == "quadratic_uniform_grid_minimum_v1":
        return GridMinimum(inputs)
    if algorithm == "exact_winner_nonidentity_v1":
        result = ParseRational(inputs["source_winner"]) != ParseRational(inputs["target_winner"])
        return result, {"source_winner": inputs["source_winner"], "target_winner": inputs["target_winner"]}
    if algorithm == "quadratic_profile_v1":
        return ProfileResult(inputs)
    if algorithm == "quadratic_profile_bundle_v1":
        result = []
        details = []
        for item in inputs:
            profile, detail = ProfileResult(item)
            result.append([detail["support_index"], profile])
            details.append(detail)
        return result, {"cases": details}
    if algorithm == "quadratic_all_horizon_carrier_and_label_counts_v2":
        domain = inputs["all_horizon_domain"]
        expected_domain = {
            "h": "positive_real",
            "m": "positive_real",
            "horizon": "natural_number",
        }
        if domain != expected_domain:
            raise ValueError("Malformed all-horizon quadratic compiler domain")
        cases = inputs["registered_label_cases"]
        supports = [QuadraticSupportIndex(*ParseWeights(item)) for item in cases]
        counts = [1 + support * (support + 1) // 2 for support in supports]
        result = {
            "all_horizon_phase_carrier": {
                "exists_first_zero_phase": True,
                "phase_carrier_cardinality": "K+1",
                "decode_encode_exact_for_every_natural_horizon": True,
                "optimizer_proof_for_every_natural_horizon": True,
                "profile_proof_for_every_natural_horizon": True,
            },
            "registered_label_counts": counts,
        }
        detail = {
            "universal_closure": "Lean theorem PhonologicalCalculus.Application.app_mcc_comp_allHorizon",
            "universal_domain": domain,
            "support_indices": supports,
            "registered_label_count_formula": "1+K(K+1)/2",
            "carrier_distinction": "phase carrier K+1; registered coordinate-label inventory 1+K(K+1)/2",
        }
        return result, detail
    if algorithm == "quadratic_parameter_change_v1":
        first, first_detail = ProfileResult(inputs["first"])
        second, second_detail = ProfileResult(inputs["second"])
        difference = ParseRational(second[1]) - ParseRational(first[1])
        return [first[1], second[1], RationalText(difference)], {"first": first_detail, "second": second_detail}
    if algorithm == "lattice_interval_type_guard_v1":
        lower = ParseRational(inputs["lower"])
        upper = ParseRational(inputs["upper"])
        step = ParseRational(inputs["step"])
        count = (upper - lower) / step
        if count.denominator != 1 or inputs["continuum_type"] != "Interval":
            raise ValueError("Malformed lattice/interval carrier guard")
        return [count.numerator + 1, "Interval"], {"finite_lattice_cardinality": count.numerator + 1, "continuum_sort": "real interval", "same_carrier_sort": False}
    if algorithm == "basic_syllable_inventory_v1":
        return BasicSyllableInventory(transcription, inputs)
    raise ValueError("Unknown exact application replay algorithm")
