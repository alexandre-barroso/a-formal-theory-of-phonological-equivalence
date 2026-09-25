import csv
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from phonological_requirements import certificate, paths

REPO = paths.REPO

def read_catalogue(name):
    with (REPO / "data" / "dissertation" / name).open(newline="", encoding="utf-8") as stream:
        return list(csv.DictReader(stream, delimiter="\t"))


CATALOGUE = read_catalogue("statements.tsv")
LABELS = tuple((r["label"], r["kind"], r["number"], r["source"], r["title"]) for r in CATALOGUE)
SECTIONS = {r["label"]: (r["source"], r["title"]) for r in read_catalogue("sections.tsv")}

CODES = {
    "CALC-F1": ("thm:calc-f1",), "CALC-R": ("sec:calc-regressions",),
    "FIN-A1": ("thm:rep-fin-a1",), "FIN-A2": ("thm:rep-fin-a2",), "FIN-A3": ("thm:rep-fin-a3",), "FIN-A4": ("thm:rep-fin-a4",),
    "FIN-A5": ("thm:rep-fin-a5",), "FIN-A6": ("thm:rep-fin-a6",), "FIN-A7": ("thm:rep-fin-a7",),
    "MAX-G1": ("thm:max-g1",), "MAX-G2": ("thm:max-g2",), "MAX-G3": ("thm:max-g3",), "MAX-G4": ("thm:max-g4-cells", "thm:max-g4-selector"),
    "MAX-G5": ("thm:max-g5",), "MAX-G6": ("thm:max-g6",), "MAX-G7": ("thm:max-g7",), "MAX-G8": ("thm:max-g8",), "MAX-G9": ("thm:max-g9",),
    "ETR-INV": ("sec:app-maxent-g3",),
    "CHG-B1": ("prop:chg-b1",), "CHG-B2": ("thm:chg-b2",), "CHG-B3": ("cor:chg-b3",), "CHG-B4": ("sec:chg-endpoint-exponent",),
    "CHG-B5": ("prop:chg-b5",), "CHG-B7": ("sec:chg-phases",), "CHG-B9": ("sec:chg-profile-inverse",), "CHG-B10": ("sec:chg-profile-inverse",),
    "CHG-B11": ("sec:chg-profile-inverse",), "CHG-B12": ("sec:chg-convergence",), "CHG-B13": ("sec:chg-scaling",), "CHG-B14": ("sec:chg-scaling",),
    "CHG-B15": ("sec:chg-exponent-limits",), "CHG-B16": ("sec:chg-exponent-limits",),
    "CTX-C1": ("sec:chg-context",), "CTX-C2": ("sec:chg-context",),
    "FLUX-D1": ("prop:flux-d1",), "FLUX-D2": ("prop:flux-two-load-collapse", "prop:flux-star-collapse"), "FLUX-D3": ("sec:flux-ledger",),
    "FLUX-D4": ("prop:flux-odd-contact", "prop:flux-contact-response"), "FLUX-D5": ("sec:flux-tomography",),
    "SUP-E1": ("sec:support-endpoint",), "SUP-E2": ("sec:support-projectivity",), "SUP-E3": ("sec:support-matched",), "SUP-E4": ("sec:support-matched",),
    "SEL-F1": ("thm:app-sel-f1", "thm:apph-sel-f1"), "SEL-F2": ("thm:apph-sel-f2",),
    "APP-MCC-GRID": ("sec:applications-mccollum-grid",), "APP-MCC-LENGTH": ("sec:applications-mccollum-length", "prop:app-mcc-phases"),
    "APP-MCC-COMP": ("sec:applications-mccollum-length",), "APP-BASIC": ("sec:applications-basic-syllable", "thm:max-g6"),
}

OPACITY_MODULES = {
    "Attenuation/Typology": ("prop:opacity-interaction-regions",),
    "Attenuation/MutualCounterfeeding.lean": ("prop:opacity-interaction-regions",),
    "Attenuation/Lardil.lean": ("prop:opacity-interaction-regions",),
    "Attenuation/LardilCycle.lean": ("prop:int-mutual-scalar-limit",),
    "Attenuation/SerialComparison.lean": ("prop:int-mutual-scalar-limit",),
    "Attenuation/SharingObstruction.lean": ("prop:int-mutual-scalar-limit",),
    "Attenuation/InteractionObstruction.lean": ("prop:int-mutual-scalar-limit",),
    "Attenuation/FreeWeights": ("prop:opacity-lambda-region",),
    "Attenuation": ("prop:int-lambda",),
    "Lithuanian": ("thm:opacity-lt-region", "prop:int-lambda"),
    "Gua/Deletion/Baseline.lean": ("thm:opacity-current-bound", "prop:int-lambda"),
    "Gua/Deletion/Bindings.lean": ("thm:opacity-deletion-bound", "prop:int-winner-locality"),
    "Gua/Deletion": ("thm:opacity-deletion-bound",),
    "Gua": ("thm:opacity-gua-selection",),
}

DOSSIERS = {
    "F01-1": ("1 local alternation and neutralization", "laryngeal_neutralization"),
    "F01-2": ("1 local alternation and neutralization", "gapped_inventory"),
    "F02-1": ("2 harmony and assimilation", "productive_enlargement"),
    "F02-2": ("2 harmony and assimilation", "nonmyopic_harmony"),
    "F03-1": ("3 blocking, transparency, and dissimilation", "antigemination"),
    "F03-2": ("3 blocking, transparency, and dissimilation", "ocp_repairs"),
    "F04-1": ("4 epenthesis, deletion, coalescence, metathesis", "apocope_counterfeeding"),
    "F04-2": ("4 epenthesis, deletion, coalescence, metathesis", "transient_environments"),
    "F05-1": ("5 syllabification and phonotactics", "contact_scale"),
    "F05-2": ("5 syllabification and phonotactics", "compensatory_lengthening"),
    "F06-1": ("6 stress and metrical organization", "accent_encoding"),
    "F06-2": ("6 stress and metrical organization", "morphological_accent"),
    "F07-1": ("7 tone and autosegmental association", "floating_tone_tie"),
    "F07-2": ("7 tone and autosegmental association", "phonation_tone"),
    "F08-1": ("8 morphologically conditioned phonology and cyclic domains", "cophonologies"),
    "F08-2": ("8 morphologically conditioned phonology and cyclic domains", "stratal_syncope"),
    "F09-1": ("9 phrase-level phonology", "tone_sandhi"),
    "F09-2": ("9 phrase-level phonology", "juncture_coalescence"),
    "F10-1": ("10 opaque and transparent process interaction", "interaction_typology"),
    "F10-2": ("10 opaque and transparent process interaction", "self_destructive_feeding"),
    "F11-1": ("11 copying, reduplicative correspondence, and positional faithfulness", "agreement_by_correspondence"),
    "F11-2": ("11 copying, reduplicative correspondence, and positional faithfulness", "reduplication_template"),
    "F12-1": ("12 variation and graded consequences", "variation_laws"),
    "F12-2": ("12 variation and graded consequences", "schwa_attenuation"),
}
DOSSIER_EXTRA = {
    "F03-2": ("python/phonological_requirements/ocp_region.py",
              "wolfram/phonological_requirements/ocp_region.wls",
              "results/requirements/certificates/ocp_region.json",
              "python/phonological_requirements/ocp_graph_region.py",
              "wolfram/phonological_requirements/ocp_graph_region.wls",
              "lean/phonological_equivalence/PhonologicalCalculus/Application/OCPGraphRegion.lean",
              "results/requirements/certificates/ocp_graph_region.json"),
    "F05-2": ("python/phonological_requirements/compensatory_lengthening_region.py",
              "wolfram/phonological_requirements/compensatory_lengthening_region.wls",
              "results/requirements/certificates/compensatory_lengthening_region.json"),
    "F07-1": ("python/phonological_requirements/poko_comparison.py",
              "wolfram/phonological_requirements/poko_comparison.wls",
              "results/requirements/certificates/poko_comparison.json"),
    "F06-1": ("wolfram/phonological_requirements/accent_encoding_regions.wl",),
    "F06-2": ("python/phonological_requirements/morphological_accent_native.py",
              "wolfram/phonological_requirements/morphological_accent_orientation.wl",
              "wolfram/phonological_requirements/morphological_accent_typology.wl"),
    "F04-2": ("wolfram/phonological_requirements/transient_environments_region.wl",),
    "F10-1": ("python/phonological_requirements/cell_refinement.py", "python/phonological_requirements/interaction_cells.py",
              "wolfram/phonological_requirements/interaction_typology_regions.wl", "wolfram/phonological_requirements/modes_check.wls"),
    "F12-2": ("wolfram/phonological_requirements/schwa_law_check.wls",),
    "F02-1": ("python/phonological_opacity/reproduce.py", "python/phonological_requirements/attenuation_region.py"),
}

R = "python/phonological_requirements/"
V = "python/verification/"
E = "python/phonological_equivalence/"
G = "python/phonological_grounding/"
O = "python/phonological_opacity/"
WE = "wolfram/phonological_equivalence/"
WG = "wolfram/phonological_grounding/"
WO = "wolfram/phonological_opacity/"
WR = "wolfram/phonological_requirements/"
FINITE = (E + "finite_model.py", V + "factcheck_queries_carriers.py", V + "stress_finite_carriers.py")
GROUND = (G + "query_discovery/kernel.py", G + "reproduce.py", V + "stress_grounding.py")
MAXENT = (E + "maxent.py", E + "polynomial.py", V + "factcheck_maxent_normalizers.py", V + "stress_maxent.py")
CHG = (E + "continuous_hg.py", V + "factcheck_continuous_hg.py", V + "factcheck_persistence_phases.py", V + "stress_continuous_hg.py")
FLUX = (E + "flux.py", E + "contextual_model.py", V + "factcheck_context_support.py")
SEL = (E + "support_selection.py", V + "factcheck_selected_output.py")
OPACITY = (O + "reproduce.py", O + "gua/check_selection.py", V + "factcheck_opacity_products.py", V + "stress_opacity.py")
DECL = (G + "reproduce.py", "results/declaration_language/INDEX.json")

PYTHON = {
    "eq:app-fin-factor-kernel": FINITE,
    "eq:intro-orders": (E + "order_comparison.py", V + "factcheck_opening_comparisons.py"),
    "eq:intro-conservativity": (E + "order_comparison.py", V + "factcheck_opening_comparisons.py"),
    "prop:opacity-russian-contrasts": (R + "russian_displayed.py", R + "russian_design.py", R + "russian_secondary.py"),
    "prop:int-huaian-odds": (R + "huaian_joint.py", R + "huaian_secondary.py", R + "huaian_observations.py", R + "huaian_comparison.py", R + "huaian_fit.py", R + "huaian_acoustics.py", R + "huaian_original_counts.py"),
    "prop:opacity-interaction-regions": (R + "interaction_regions.py", R + "lardil_region.py"),
    "prop:int-mutual-scalar-limit": (R + "interaction_regions.py", R + "lardil_region.py", R + "serial_comparison.py", R + "attenuation_region.py"),
    "prop:calc-discovery": (G + "query_discovery/discovery.py", V + "stress_grounding.py", V + "stress_finite_carriers.py"),
    "thm:calc-f1": FINITE,
    "thm:rep-fin-a1": FINITE, "thm:rep-fin-a2": FINITE, "thm:rep-fin-a3": FINITE,
    "thm:rep-fin-a4": FINITE + GROUND, "thm:rep-licensed": FINITE + GROUND, "thm:rep-fin-a5": FINITE + GROUND,
    "thm:rep-fin-a6": FINITE + GROUND, "thm:rep-fin-a7": FINITE,
    "def:rep-structure": (R + "wellformedness_audit.py", R + "generator_operations.py"),
    "def:rep-generator": (R + "generator_operations.py", R + "productive_enlargement.py", R + "created_position_quotient.py"),
    "thm:rep-wellformed": (R + "wellformedness_audit.py", R + "registered_export.py"),
    "thm:maxent-quotient": (R + "created_position_quotient.py",),
    "thm:maxent-temperature": (R + "created_position_quotient.py", V + "stress_maxent.py"),
    "thm:max-g1": MAXENT, "thm:max-g2": MAXENT, "thm:max-g3": MAXENT + (E + "expressions.py",),
    "thm:max-g4-cells": MAXENT, "thm:max-g4-selector": MAXENT, "thm:max-g5": MAXENT,
    "thm:max-g6": MAXENT + (V + "factcheck_basic_syllable.py",), "thm:max-g7": MAXENT,
    "thm:max-g8": MAXENT, "thm:max-g9": MAXENT,
    "prop:maxent-schwa-law": (R + "schwa_attenuation.py", V + "stress_requirements.py"),
    "prop:chg-b1": CHG, "thm:chg-b2": CHG, "cor:chg-b3": CHG, "prop:chg-b5": CHG,
    "thm:chg-nonnegative-sites": (R + "heterogeneous_sites.py", R + "heterogeneous_boundary.py", R + "heterogeneous_fibers.py", V + "stress_continuous_hg.py"),
    "thm:chg-obstruction": (R + "heterogeneous_sites.py", R + "heterogeneous_obstruction.py", V + "stress_continuous_hg.py"),
    "prop:flux-d1": FLUX, "prop:flux-two-load-collapse": FLUX, "prop:flux-star-collapse": FLUX,
    "prop:flux-odd-contact": FLUX, "prop:flux-contact-response": FLUX,
    "prop:app-mcc-phases": (E + "application_model.py", V + "factcheck_mccollum.py"),
    "thm:app-sel-f1": SEL, "prop:app-pater-scaling": (E + "application_model.py", V + "factcheck_maxent_mass_scaling.py"),
    "thm:opacity-labels-cells": (R + "cell_scope.py", R + "interaction_cells.py", R + "cell_refinement.py"),
    "thm:opacity-current-general": (R + "cell_scope.py",),
    "prop:opacity-two-contrasts": (R + "cell_scope.py",),
    "thm:opacity-gauge": (R + "attenuation_gauge.py", V + "stress_requirements.py", V + "stress_opacity.py"),
    "cor:opacity-lambda-identification": (R + "cell_scope.py", R + "attenuation_gauge.py"),
    "lem:opacity-entry-bridge": (V + "factcheck_requirements_bridge.py", R + "examples/entry_calc.py"),
    "thm:opacity-modes": (R + "interaction_typology.py", V + "stress_requirements.py"),
    "thm:opacity-gua-selection": OPACITY,
    "thm:opacity-productive": (R + "productive_enlargement.py", R + "products.py"),
    "thm:opacity-current-bound": OPACITY,
    "thm:opacity-deletion-bound": (O + "gua/check_deletion.py",) + OPACITY,
    "thm:opacity-lt-region": (O + "lithuanian/check.py", G + "declaration_language/lith_region.py", V + "stress_opacity.py"),
    "prop:opacity-lambda-region": (R + "attenuation_region.py", V + "factcheck_attenuation.py", R + "productive_region.py", R + "productive_region_appendix.py", R + "productive_region_subject.py"),
    "thm:int-grounding": GROUND, "thm:int-discovery": (G + "query_discovery/discovery.py",) + GROUND,
    "prop:int-lambda": (V + "factcheck_attenuation.py", V + "stress_opacity.py", R + "examples/frontier_lambda_grain.py"),
    "thm:int-definedness": (R + "definedness.py", R + "discharge_persistence.py", R + "formula_certificates.py") + DECL,
    "thm:int-third-party": (R + "definedness.py", R + "discharge_persistence.py",), "cor:int-excluded-family": (R + "discharge_persistence.py",),
    "thm:int-bridge": (R + "correspondence_regimes.py",),
    "thm:int-resolver-law": (R + "resolver_transfer.py", "results/declaration_language/resolver_variants.json"),
    "prop:int-individuation": (R + "individuation_ablations.py", "results/declaration_language/obligation_indexing.json"),
    "thm:int-indexation": (R + "individuation_ablations.py", V + "stress_requirements.py"),
    "def:int-footprint": (R + "footprint_soundness.py",),
    "prop:int-narrow-footprint": (R + "footprint_soundness.py",), "thm:int-footprint-sound": (R + "footprint_soundness.py", R + "footprint_support.py"),
    "thm:int-noninterference": (R + "noninterference.py", R + "product_composition.py", R + "word_projection.py"),
    "thm:int-cycles": (R + "interaction_graph.py", G + "transient_cycle_bounds.py", V + "stress_requirements.py"),
    "prop:int-antilithuanian": (R + "discharge_persistence.py",),
    "thm:int-inert": (R + "transient_environments.py", G + "transient_cycle_bounds.py"), "thm:int-transient": (R + "transient_environments.py", G + "transient_cycle_bounds.py"),
    "prop:int-arapaho": (R + "transient_environments.py",),
    "prop:int-winner-locality": (R + "resolver_transfer.py", G + "declaration_language/winner_locality.py",
                                 "results/declaration_language/winner_locality.json"),
    "prop:int-locality": (R + "footprint_soundness.py", R + "alignment_automaton.py"),
    "thm:int-regular": (R + "alignment_automaton.py", R + "weighted_cost.py", R + "irrational_selection.py", R + "cross_input_variation.py"),
    "thm:int-bounded-feeding": (R + "alignment_automaton.py", V + "stress_requirements.py"),
    "prop:int-covering": (R + "alignment_automaton.py", V + "stress_requirements.py"),
    "thm:int-majority": (R + "alignment_automaton.py",),
    "thm:int-identification": (R + "identification_sample.py", R + "learning_invariance.py", R + "learning_tail.py"),
    "thm:int-specialisation": (R + "core_specialisation.py", R + "registered_export.py", R + "formula_certificates.py"),
    "def:apph-positive-ray": SEL, "lem:apph-halfspace-inclusion": SEL, "thm:apph-sel-f1": SEL,
    "thm:apph-open-gap": SEL, "cor:apph-full-support-gap": SEL, "thm:apph-sel-f2": SEL,
    "lem:appg-first-step": OPACITY,
    "thm:apph-refinement": GROUND, "thm:apph-unarisation": GROUND, "prop:apph-frame": GROUND,
    "prop:apph-tone": (G + "query_discovery/gua_licence.py",) + GROUND,
    "prop:appi-rejects": (R + "wellformedness_audit.py",),
    "thm:appi-adequacy": (V + "factcheck_requirements_bridge.py", G + "declaration_language/adequacy.py",
                          "results/declaration_language/adequacy_gua.json", "results/declaration_language/adequacy_lithuanian.json"),
    "thm:appi-no-s": (R + "definedness.py", R + "discharge_persistence.py",) + DECL,
    "thm:appi-footprint": (R + "footprint_soundness.py", R + "footprint_support.py"),
    "thm:appi-noninterference": (R + "noninterference.py", R + "product_composition.py", R + "word_projection.py"),
    "prop:appi-record": (G + "declaration_language/record.py", "results/declaration_language/record_ablation.json"),
    "prop:appi-individuation": (R + "individuation_ablations.py", G + "declaration_language/indexing.py"),
    "thm:appi-zero": (R + "discharge_persistence.py",) + DECL,
    "prop:appj-nonrobust": (G + "predictions/sharedactivity.py", G + "predictions/separation_length.py", G + "reproduce.py"),
    "prop:appk-locality": (R + "footprint_soundness.py", R + "alignment_automaton.py"),
    "thm:appk-regular": (R + "alignment_automaton.py", R + "weighted_cost.py", R + "irrational_selection.py", R + "cross_input_variation.py"),
    "prop:appk-feeding": (R + "alignment_automaton.py", V + "stress_requirements.py"),
}

WOLFRAM = {
    "eq:intro-orders": (WE + "OpeningComparisons.wls",),
    "eq:intro-conservativity": (WE + "OpeningComparisons.wls",),
    "prop:opacity-russian-contrasts": (WR + "russian_displayed.wls",),
    "prop:int-huaian-odds": (WR + "huaian_joint.wls",),
    "thm:int-regular": (WR + "weighted_cost.wls", WR + "irrational_selection.wls", WR + "cross_input_variation.wls"),
    "thm:appk-regular": (WR + "weighted_cost.wls", WR + "irrational_selection.wls", WR + "cross_input_variation.wls"),
    "cor:opacity-lambda-identification": (WR + "cell_scope.wls",),
    "prop:opacity-two-contrasts": (WR + "cell_scope.wls",),
    "thm:opacity-current-general": (WR + "cell_scope.wls",),
    "thm:opacity-labels-cells": (WR + "cell_scope.wls",),
    "thm:int-third-party": (WR + "definedness.wls",),
    "thm:appi-no-s": (WR + "definedness.wls",),
    "thm:int-footprint-sound": (WR + "footprint_support.wls",),
    "thm:appi-footprint": (WR + "footprint_support.wls",),
    "thm:int-noninterference": (WR + "product_composition.wls", WR + "word_projection.wls"),
    "thm:appi-noninterference": (WR + "product_composition.wls", WR + "word_projection.wls"),
    "prop:opacity-interaction-regions": (WR + "interaction_regions.wls", WR + "lardil_region.wls"),
    "prop:int-mutual-scalar-limit": (WR + "interaction_regions.wls", WR + "lardil_region.wls", WR + "serial_comparison.wls", WR + "attenuation_region.wls"),
    "thm:calc-f1": (WG + "QueryDiscoveryCheck.wls",),
    "thm:rep-licensed": (WG + "QueryDiscoveryCheck.wls", WG + "BatterySpec.wl"),
    "thm:rep-fin-a4": (WG + "QueryDiscoveryCheck.wls",), "thm:rep-fin-a5": (WG + "QueryDiscoveryCheck.wls",),
    "thm:maxent-quotient": (WR + "quotient_temperature_check.wls",), "thm:maxent-temperature": (WR + "quotient_temperature_check.wls",),
    "thm:max-g1": (WE + "MaxEntG1G5.wl",), "thm:max-g2": (WE + "MaxEntG1G5.wl",), "thm:max-g3": (WE + "MaxEntG1G5.wl",),
    "thm:max-g4-cells": (WE + "MaxEntG1G5.wl",), "thm:max-g4-selector": (WE + "MaxEntG1G5.wl",), "thm:max-g5": (WE + "MaxEntG1G5.wl",),
    "thm:max-g6": (WE + "MaxEntG6G9.wl", WE + "factcheck_basic_syllable.wls"), "thm:max-g7": (WE + "MaxEntG6G9.wl",),
    "thm:max-g8": (WE + "MaxEntG6G9.wl", WE + "factcheck_capacity.wls"), "thm:max-g9": (WE + "MaxEntG6G9.wl",),
    "prop:maxent-schwa-law": (WR + "schwa_law_check.wls", WR + "schwa_attenuation_fit.wls",),
    "prop:opacity-lambda-region": (WR + "attenuation_region.wls", WR + "productive_region.wl", WR + "productive_region_appendix.wls", WR + "productive_region_subject.wls"),
    "thm:chg-nonnegative-sites": (WR + "heterogeneous_sites_check.wls", WR + "heterogeneous_boundary.wls", WR + "heterogeneous_fibers.wls"), "thm:chg-obstruction": (WR + "heterogeneous_sites_check.wls", WR + "heterogeneous_obstruction.wls"),
    "thm:opacity-modes": (WR + "interaction_typology_regions.wl", WR + "interaction_typology_systems.wl", WR + "modes_check.wls"),
    "thm:opacity-gua-selection": (WO + "gua/check_selection.wl", WO + "fragments/regression.wls"),
    "thm:opacity-deletion-bound": (WO + "gua/check_deletion.wl",),
    "thm:opacity-lt-region": (WO + "lithuanian/check.wl", WG + "LithuanianRegion.wls"),
    "prop:int-lambda": (WO + "fragments/LambdaInterval.wls",),
    "thm:int-grounding": (WG + "QueryDiscoveryCheck.wls", WG + "BatterySpec.wl", WG + "GuaLicenceSpec.wl"),
    "thm:int-discovery": (WG + "QueryDiscoveryCheck.wls",),
    "thm:int-definedness": (WR + "definedness.wls", WG + "DeclarationLanguageCheck.wls", WG + "LCore.wl", WG + "LSchemasSpec.wl", WR + "formula_certificates.wls"),
    "thm:int-specialisation": (WR + "formula_certificates.wls",),
    "thm:int-cycles": (WG + "TransientCycleBounds.wls",),
    "thm:int-identification": (WR + "learning_invariance.wls", WR + "learning_tail.wls"),
    "thm:int-inert": (WR + "transient_environments_region.wl", WG + "TransientCycleBounds.wls"), "thm:int-transient": (WR + "transient_environments_region.wl", WG + "TransientCycleBounds.wls"),
    "prop:int-arapaho": (WR + "transient_environments_region.wl",),
    "thm:int-bounded-feeding": (WR + "feeding_chain_check.wls",), "prop:appk-feeding": (WR + "feeding_chain_check.wls",),
    "prop:int-covering": (WR + "covering_count_check.wls",),
    "thm:appi-adequacy": (WG + "DeclarationLanguageCheck.wls",), "thm:appi-zero": (WG + "DeclarationLanguageCheck.wls",),
    "prop:appj-nonrobust": (WG + "PredictionBattery.wls",),
    "prop:apph-tone": (WG + "GuaLicenceSpec.wl",),
}

PROJECTS = {
    "lean/phonological_equivalence": "PhonologicalCalculus",
    "lean/phonological_opacity": "PhonologicalOpacity",
    "lean/phonological_grounding": "PhonologicalGrounding",
    "lean/phonological_requirements": "PhonologicalRequirements",
}
SOURCE_LABELS = json.loads((REPO / "data" / "dissertation" / "lean_source_labels.json").read_text(encoding="utf-8"))


def source_labels(path):
    return SOURCE_LABELS.get(path.relative_to(REPO).as_posix(), [])


def lean_index():
    refs = {}
    for proj, ns in PROJECTS.items():
        root = REPO / proj / ns
        for f in sorted(root.rglob("*.lean")):
            rel = str(f.relative_to(REPO))
            targets = set()
            for t in source_labels(f):
                if t in CODES:
                    targets.update(CODES[t])
                else:
                    targets.add(t)
            if ns == "PhonologicalOpacity":
                inner = str(f.relative_to(root))
                for prefix, labels in OPACITY_MODULES.items():
                    if inner == prefix or inner.startswith(prefix + "/"):
                        targets.update(labels)
                        break
            for t in targets:
                refs.setdefault(t, []).append(rel)
    return refs


EXPLICIT_LEAN = {
    "eq:app-fin-factor-kernel": ["lean/phonological_equivalence/PhonologicalCalculus/Finite/QueryFactorization.lean"],
    "sec:uyghur-grammar": ["lean/phonological_equivalence/PhonologicalCalculus/Application/UyghurJoint.lean"],
    "sec:uyghur-joint-restriction": ["lean/phonological_equivalence/PhonologicalCalculus/Application/UyghurJoint.lean",
                                  "lean/phonological_equivalence/PhonologicalCalculus/Application/UyghurPredictions.lean"],
    "sec:support-endpoint": ["lean/phonological_equivalence/PhonologicalCalculus/Support/EndpointLocalBridge.lean"],
}


def main():
    refs = lean_index()
    for label, artifacts in EXPLICIT_LEAN.items():
        for artifact in artifacts:
            if not (REPO / artifact).is_file():
                raise FileNotFoundError(artifact)
        refs.setdefault(label, []).extend(artifacts)
    known = {l[0] for l in LABELS} | set(SECTIONS) | set(DOSSIERS)
    problems = []
    for t, files in refs.items():
        if t not in known and not t.startswith("eq:"):
            problems.append(f"Lean source index names an unknown target {t} in {files[0]}")
    for table in (PYTHON, WOLFRAM):
        for label, arts in table.items():
            if label not in known:
                problems.append(f"artifact table names an unknown label {label}")
            for a in arts:
                if not (REPO / a).exists():
                    problems.append(f"missing artifact {a} ({label})")
    rows = []
    for label, kind, number, source, title in LABELS:
        lean = sorted(set(refs.get(label, [])))
        py = list(PYTHON.get(label, ()))
        wl = list(WOLFRAM.get(label, ()))
        if not (lean or py or wl):
            problems.append(f"no artifact for {label}")
        rows.append({"label": label, "kind": kind, "number": number, "source": source, "title": title,
                     "lean_modules": lean, "python_artifacts": py, "wolfram_scripts": wl,
                     "locator": next(r for r in CATALOGUE if r["label"] == label)})
    sections = []
    for label, (source, title) in SECTIONS.items():
        sections.append({"label": label, "source": source, "title": title, "lean_modules": sorted(set(refs.get(label, [])))})
    dossiers = []
    for did, (family, runner) in DOSSIERS.items():
        arts = [R + runner + ".py", "results/requirements/certificates/" + runner + ".json"] + list(DOSSIER_EXTRA.get(did, ()))
        for a in arts:
            if not (REPO / a).exists():
                problems.append(f"missing dossier artifact {a} ({did})")
        dossiers.append({"dossier": did, "family": family, "artifacts": arts, "lean_modules": sorted(set(refs.get(did, [])))})
    totals = {
        "labels": len(rows),
        "with_lean": sum(1 for r in rows if r["lean_modules"]),
        "with_python": sum(1 for r in rows if r["python_artifacts"]),
        "with_wolfram": sum(1 for r in rows if r["wolfram_scripts"]),
        "by_kind": {k: sum(1 for r in rows if r["kind"] == k) for k in sorted({r["kind"] for r in rows})},
        "lean_modules_referencing_a_label": len({f for t, fs in refs.items() for f in fs}),
        "dossiers": len(dossiers),
    }
    certificate.write("coverage.json", {"totals": totals, "labels": rows, "sections": sections, "dossiers": dossiers,
                       "unlabelled_environments": read_catalogue("unlabelled_environments.tsv"),
                       "scope": "Artifact and locator index; existence of a module is not by itself a semantic correspondence certificate. Definitions, direct theorems, applications and computations have distinct roles."},
                      REPO / "results")
    for p in problems:
        print("PROBLEM:", p)
    print(json.dumps(totals))
    return 1 if problems else 0


if __name__ == "__main__":
    raise SystemExit(main())
