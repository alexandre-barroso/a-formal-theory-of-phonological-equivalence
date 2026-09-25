import PhonologicalRequirements.Kleene
import PhonologicalRequirements.Terms
import PhonologicalRequirements.Discharge
import PhonologicalRequirements.Definedness
import PhonologicalRequirements.Contribution
import PhonologicalRequirements.Reduction
import PhonologicalRequirements.Transient
import PhonologicalRequirements.Prosody
import PhonologicalRequirements.Rep
import PhonologicalRequirements.Discipline
import PhonologicalRequirements.Footprint
import PhonologicalRequirements.FootprintSupport
import PhonologicalRequirements.Compose
import PhonologicalRequirements.Interaction
import PhonologicalRequirements.Cells
import PhonologicalRequirements.Modes
import PhonologicalRequirements.Feeding
import PhonologicalRequirements.Indexation
import PhonologicalRequirements.Schwa
import PhonologicalRequirements.Majority
import PhonologicalRequirements.Covering
import PhonologicalRequirements.Quotient
import PhonologicalRequirements.Splice
import PhonologicalRequirements.Barrier
import PhonologicalRequirements.Registered
import PhonologicalRequirements.RegisteredFormulae

namespace PhonologicalRequirements

#print axioms K.and_uu_of_uu
#print axioms K.not_uu_iff
#print axioms eval_defined_of_accesses
#print axioms pressure_zero_of_strict
#print axioms exists_total
#print axioms exists_not_strict
#print axioms contrib_a_one
#print axioms contrib_a_zero_gauge
#print axioms transfer_gap
#print axioms excluded_of_many_created
#print axioms reduction_fails_at_zero
#print axioms contrib_inert
#print axioms contrib_retained_destroyed
#print axioms dot_le_of_dominates
#print axioms dot_lt_of_dominates
#print axioms arapaho_transient_excluded
#print axioms arapaho_needs_positive_attenuation
#print axioms arapaho_control_needs_attenuation_below_one
#print axioms closesCell_of_refines
#print axioms refines_trans
#print axioms closesCell_not_symm
#print axioms Rep.WF_setReal
#print axioms Rep.WF_link
#print axioms Rep.WF_unlink
#print axioms Rep.WF_insertAt
#print axioms Rep.WF_renameMade
#print axioms Rep.canon_rename
#print axioms Rep.WF_swapAt
#print axioms Rep.WF_fuse
#print axioms Rep.WF_splitAt
#print axioms Footprint.scan_congr
#print axioms Footprint.resolveDyn_congr
#print axioms Footprint.resolveIn_congr
#print axioms Footprint.readers_congr
#print axioms Compose.reach_prod
#print axioms Compose.argmin_prod
#print axioms Compose.noninterference
#print axioms Interaction.separable_argmin
#print axioms Interaction.all_apply_not_min
#print axioms Discipline.wellTyped_iff
#print axioms Discipline.guaA_rejected
#print axioms Discipline.guaA_three_grounds
#print axioms Discipline.guaA_rules12
#print axioms Discipline.guaA_typed_accepted
#print axioms Discipline.lithR_accepted
#print axioms Discipline.lithS_rejected
#print axioms Discipline.lithS_grounds
#print axioms Discipline.factorizations

#print axioms eval_congr
#print axioms discharge_only_by_relata
#print axioms exists_form_violated
#print axioms exists_form_pressure
#print axioms antilithuanian
#print axioms Cells.overapplication_iff
#print axioms Cells.underapplication_iff
#print axioms Cells.current_general
#print axioms Cells.tolerate_iff
#print axioms Cells.lost_context_separated_by_a
#print axioms Cells.uniform_reparametrisation
#print axioms Cells.attenuation_enters_one_cell
#print axioms Modes.counterbleeding_iff
#print axioms Modes.counterbleeding_never
#print axioms Modes.bleeding_iff
#print axioms Modes.mutual_both_apply_iff
#print axioms Modes.feeds_iff
#print axioms Modes.feeding_needs_positive_attenuation
#print axioms Modes.counterfeeding_needs_attenuation_below_one
#print axioms Feeding.runs_to_end_iff
#print axioms Feeding.stops_after_first
#print axioms Indexation.saturated_count
#print axioms Indexation.partial_repair_worse
#print axioms Schwa.word_effect_ccc
#print axioms Schwa.clitic_effect_ccc
#print axioms Schwa.common_ratio
#print axioms Majority.edits_bounded
#print axioms Majority.boundary_bound
#print axioms Majority.majority_not_selected
#print axioms Covering.cost_eq
#print axioms Covering.length_bound
#print axioms Covering.cost_lower
#print axioms Covering.minimum_iff
#print axioms Covering.alternating_stats
#print axioms Covering.length_identity
#print axioms Covering.even_minimiser_unique
#print axioms Covering.odd_minimiser_seam
#print axioms Covering.tie_counts_bounded
#print axioms Barrier.reach_strict
#print axioms Barrier.no_path_to_target
#print axioms Covering.alternating_of_covered_nodouble
#print axioms Covering.alternating_unique
#print axioms Covering.odd_positions_deleted
#print axioms Footprint.narrow_footprint_unsound
#print axioms Quotient.score_zero_iff_pair
#print axioms Quotient.score_pos_of_present_created
#print axioms Quotient.placements_length
#print axioms Quotient.mem_placements
#print axioms Quotient.placements_nodup
#print axioms Quotient.score_zero_count
#print axioms Quotient.quotient_minimum
#print axioms Splice.window_splice_left
#print axioms Splice.window_splice_right
#print axioms Splice.splice_bound
#print axioms Registered.registered_sets
#print axioms Registered.registered_declarations
#print axioms Registered.registered_well_typed

#print axioms FormulaCertificate.assignments_complete
#print axioms FormulaCertificate.permitted_lookup
#print axioms FormulaCertificate.eval_mem_possible
#print axioms FormulaCertificate.abstract_certificate_sound
#print axioms FormulaCertificate.permittedCheck_sound
#print axioms FormulaCertificate.strict_certificate_sound
#print axioms FormulaCertificate.checked_positive_sound
#print axioms FormulaCertificate.checked_counterexample_sound
#print axioms FormulaCertificate.zero_pressure_iff
#print axioms FormulaCertificate.unresolved_can_be_defined
#print axioms FormulaCertificate.strict_does_not_imply_undefined
#print axioms FormulaCertificate.resolves_missing_not_strict
#print axioms RegisteredFormulae.case0_checked
#print axioms RegisteredFormulae.case1_checked
#print axioms RegisteredFormulae.case2_checked
#print axioms RegisteredFormulae.case3_checked
#print axioms RegisteredFormulae.case4_checked
#print axioms RegisteredFormulae.case5_checked
#print axioms RegisteredFormulae.case6_checked
#print axioms RegisteredFormulae.case7_checked
#print axioms RegisteredFormulae.case8_checked
#print axioms RegisteredFormulae.case9_checked
#print axioms RegisteredFormulae.case10_checked
#print axioms RegisteredFormulae.case11_checked
#print axioms RegisteredFormulae.case12_checked
#print axioms RegisteredFormulae.case13_checked
#print axioms RegisteredFormulae.case14_checked
#print axioms RegisteredFormulae.case15_checked
#print axioms RegisteredFormulae.case16_checked
#print axioms RegisteredFormulae.case17_checked
#print axioms RegisteredFormulae.case18_checked
#print axioms RegisteredFormulae.case19_checked
#print axioms RegisteredFormulae.case20_checked
#print axioms RegisteredFormulae.case21_checked
#print axioms RegisteredFormulae.case22_checked
#print axioms RegisteredFormulae.case23_checked
#print axioms RegisteredFormulae.case24_checked
#print axioms RegisteredFormulae.case25_checked
#print axioms RegisteredFormulae.case26_checked
#print axioms RegisteredFormulae.case27_checked
#print axioms RegisteredFormulae.case28_checked
#print axioms RegisteredFormulae.case29_checked
#print axioms RegisteredFormulae.case30_checked
#print axioms RegisteredFormulae.case31_checked
#print axioms RegisteredFormulae.case32_checked
#print axioms RegisteredFormulae.case33_checked
#print axioms RegisteredFormulae.case34_checked
#print axioms RegisteredFormulae.case35_checked
#print axioms RegisteredFormulae.case36_checked
#print axioms RegisteredFormulae.case37_checked
#print axioms RegisteredFormulae.case38_checked
#print axioms RegisteredFormulae.case39_checked
#print axioms RegisteredFormulae.case40_checked
#print axioms RegisteredFormulae.case41_checked
#print axioms RegisteredFormulae.case42_checked
#print axioms RegisteredFormulae.case43_checked
#print axioms RegisteredFormulae.case44_checked
#print axioms RegisteredFormulae.case45_checked
#print axioms RegisteredFormulae.case46_checked
#print axioms RegisteredFormulae.case47_checked
#print axioms RegisteredFormulae.case48_checked
#print axioms RegisteredFormulae.case49_checked
#print axioms RegisteredFormulae.case50_checked
#print axioms RegisteredFormulae.case51_checked
#print axioms RegisteredFormulae.case52_checked
#print axioms RegisteredFormulae.case53_checked
#print axioms RegisteredFormulae.case54_checked
#print axioms RegisteredFormulae.case55_checked
#print axioms RegisteredFormulae.case56_checked
#print axioms RegisteredFormulae.case57_checked
#print axioms RegisteredFormulae.case58_checked
#print axioms RegisteredFormulae.case59_checked
#print axioms RegisteredFormulae.case60_checked
#print axioms RegisteredFormulae.case61_checked
#print axioms RegisteredFormulae.case62_checked
#print axioms RegisteredFormulae.case63_checked
#print axioms RegisteredFormulae.case64_checked
#print axioms RegisteredFormulae.case65_checked
#print axioms RegisteredFormulae.case66_checked
#print axioms RegisteredFormulae.case67_checked
#print axioms RegisteredFormulae.case68_checked
#print axioms RegisteredFormulae.case69_checked
#print axioms RegisteredFormulae.case70_checked
#print axioms RegisteredFormulae.case71_checked
#print axioms RegisteredFormulae.case72_checked
#print axioms RegisteredFormulae.case73_checked
#print axioms RegisteredFormulae.case74_checked
#print axioms RegisteredFormulae.case75_checked
#print axioms RegisteredFormulae.case76_checked
#print axioms RegisteredFormulae.case77_checked
#print axioms RegisteredFormulae.case78_checked
#print axioms RegisteredFormulae.case79_checked
#print axioms RegisteredFormulae.case80_checked
#print axioms RegisteredFormulae.case81_checked
#print axioms RegisteredFormulae.case82_checked
#print axioms RegisteredFormulae.case83_checked
#print axioms RegisteredFormulae.case84_checked
#print axioms RegisteredFormulae.case85_checked
#print axioms RegisteredFormulae.case86_checked
#print axioms RegisteredFormulae.case87_checked
#print axioms RegisteredFormulae.case88_checked
#print axioms RegisteredFormulae.case89_checked
#print axioms RegisteredFormulae.case90_checked
#print axioms RegisteredFormulae.case91_checked
#print axioms RegisteredFormulae.case92_checked
#print axioms RegisteredFormulae.case93_checked
#print axioms RegisteredFormulae.case94_checked
#print axioms RegisteredFormulae.case95_checked
#print axioms RegisteredFormulae.case96_checked
#print axioms RegisteredFormulae.case97_checked
#print axioms RegisteredFormulae.case98_checked
#print axioms RegisteredFormulae.case99_checked
#print axioms RegisteredFormulae.case100_checked
#print axioms RegisteredFormulae.case101_checked
#print axioms RegisteredFormulae.case102_checked
#print axioms RegisteredFormulae.case103_checked
#print axioms RegisteredFormulae.case104_checked
#print axioms RegisteredFormulae.case105_checked
#print axioms RegisteredFormulae.case106_checked
#print axioms RegisteredFormulae.case107_checked
#print axioms RegisteredFormulae.case108_checked
#print axioms RegisteredFormulae.case109_checked
#print axioms RegisteredFormulae.case110_checked
#print axioms RegisteredFormulae.case111_checked
#print axioms RegisteredFormulae.case112_checked
#print axioms RegisteredFormulae.case113_checked
#print axioms RegisteredFormulae.case114_checked
#print axioms RegisteredFormulae.case115_checked
#print axioms RegisteredFormulae.case116_checked
#print axioms RegisteredFormulae.case117_checked
#print axioms RegisteredFormulae.case118_checked
#print axioms RegisteredFormulae.case119_checked
#print axioms RegisteredFormulae.case120_checked
#print axioms RegisteredFormulae.case121_checked
#print axioms RegisteredFormulae.case122_checked
#print axioms RegisteredFormulae.case123_checked
#print axioms RegisteredFormulae.case124_checked
#print axioms RegisteredFormulae.case125_checked
#print axioms RegisteredFormulae.case126_checked
#print axioms RegisteredFormulae.case127_checked
#print axioms RegisteredFormulae.case128_checked
#print axioms RegisteredFormulae.case129_checked
#print axioms RegisteredFormulae.case130_checked
#print axioms RegisteredFormulae.case131_checked
#print axioms RegisteredFormulae.case132_checked
#print axioms RegisteredFormulae.case133_checked
#print axioms RegisteredFormulae.case134_checked
#print axioms RegisteredFormulae.case135_checked
#print axioms RegisteredFormulae.case136_checked
#print axioms RegisteredFormulae.case137_checked
#print axioms RegisteredFormulae.case138_checked
#print axioms RegisteredFormulae.case139_checked
#print axioms RegisteredFormulae.case140_checked
#print axioms RegisteredFormulae.case141_checked
#print axioms RegisteredFormulae.case142_checked
#print axioms RegisteredFormulae.case143_checked
#print axioms RegisteredFormulae.case144_checked
#print axioms RegisteredFormulae.case145_checked
#print axioms RegisteredFormulae.case146_checked
#print axioms RegisteredFormulae.case147_checked
#print axioms RegisteredFormulae.case148_checked
#print axioms RegisteredFormulae.case149_checked
#print axioms RegisteredFormulae.case150_checked
#print axioms RegisteredFormulae.case151_checked
#print axioms RegisteredFormulae.case152_checked
#print axioms RegisteredFormulae.case153_checked
#print axioms RegisteredFormulae.case154_checked
#print axioms RegisteredFormulae.case155_checked
#print axioms RegisteredFormulae.case156_checked
#print axioms RegisteredFormulae.case157_checked
#print axioms RegisteredFormulae.case158_checked
#print axioms RegisteredFormulae.case159_checked
#print axioms RegisteredFormulae.case160_checked
#print axioms RegisteredFormulae.case161_checked
#print axioms RegisteredFormulae.case162_checked
#print axioms RegisteredFormulae.case163_checked
#print axioms RegisteredFormulae.case164_checked
#print axioms RegisteredFormulae.case165_checked
#print axioms RegisteredFormulae.case166_checked
#print axioms RegisteredFormulae.case167_checked
#print axioms RegisteredFormulae.case168_checked
#print axioms RegisteredFormulae.case169_checked
#print axioms RegisteredFormulae.case170_checked
#print axioms RegisteredFormulae.case171_checked
#print axioms RegisteredFormulae.case172_checked
#print axioms RegisteredFormulae.case173_checked
#print axioms RegisteredFormulae.case174_checked
#print axioms RegisteredFormulae.case175_checked
#print axioms RegisteredFormulae.case176_checked
#print axioms RegisteredFormulae.case177_checked
#print axioms RegisteredFormulae.case178_checked
#print axioms RegisteredFormulae.case179_checked
#print axioms RegisteredFormulae.case180_checked
#print axioms RegisteredFormulae.case181_checked
#print axioms RegisteredFormulae.cases_count
#print axioms RegisteredFormulae.cases_checked

#print axioms FootprintSupport.scan_congr
#print axioms FootprintSupport.scan_mem
#print axioms FootprintSupport.inadmissible_tail
#print axioms FootprintSupport.prefix_suffices
#print axioms FootprintSupport.prefix_congr
#print axioms FootprintSupport.scoped_congr
#print axioms FootprintSupport.readers_congr
#print axioms FootprintSupport.filter_congr
#print axioms FootprintSupport.positional_congr
#print axioms FootprintSupport.full_support_ext
#print axioms FootprintSupport.fixed_frame_reader_congr
#print axioms FootprintSupport.simultaneous_readers_congr
#print axioms FootprintSupport.external_region_irrelevant

#print axioms Definedness.undef_strict_subject_strict
#print axioms Definedness.undef_strict_not_defined
#print axioms Definedness.true_or_missing
#print axioms Definedness.false_and_missing
#print axioms Definedness.true_or_subject_strict
#print axioms Definedness.strict_can_be_defined
#print axioms Definedness.subject_strict_not_undef_strict
#print axioms Definedness.missing_strict_excludes_pressure_one
#print axioms Definedness.exists_conjunction_not_strict

end PhonologicalRequirements
