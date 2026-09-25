import PhonologicalOpacity.Attenuation.Productive.Baseline.ProductiveTheory
namespace ProductiveGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partOR38_1_4 : check uOR38 (4) (-2) outOR38 ["a","tʃ","∅","s","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_6 : check uOR38 (4) (-2) outOR38 ["a","tʃ","∅","s","a","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_7 : check uOR38 (4) (-2) outOR38 ["a","tʃ","∅","s","a","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_8 : check uOR38 (4) (-2) outOR38 ["a","tʃ","∅","s","a","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_9 : check uOR38 (4) (-2) outOR38 ["a","tʃ","∅","s","a","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_10 : check uOR38 (4) (-2) outOR38 ["a","tʃ","∅","s","a","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_11 : check uOR38 (4) (-2) outOR38 ["a","tʃ","∅","s","a","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_12 : check uOR38 (4) (-2) outOR38 ["a","tʃ","∅","s","a","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_13 : check uOR38 (4) (-2) outOR38 ["a","tʃ","∅","s","a","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_14 : check uOR38 (4) (-2) outOR38 ["a","tʃ","∅","s","a","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_15 : check uOR38 (4) (-2) outOR38 ["a","tʃ","∅","s","a","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_16 : check uOR38 (4) (-2) outOR38 ["a","tʃ","∅","s","a","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_17 : check uOR38 (4) (-2) outOR38 ["a","tʃ","∅","s","a","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_18 : check uOR38 (4) (-2) outOR38 ["a","tʃ","∅","s","a","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_5 : check uOR38 (4) (-2) outOR38 ["a","tʃ","∅","s","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_6
  · exact partOR38_1_7
  · exact partOR38_1_8
  · exact partOR38_1_9
  · exact partOR38_1_10
  · exact partOR38_1_11
  · exact partOR38_1_12
  · exact partOR38_1_13
  · exact partOR38_1_14
  · exact partOR38_1_15
  · exact partOR38_1_16
  · exact partOR38_1_17
  · exact partOR38_1_18
theorem partOR38_1_19 : check uOR38 (4) (-2) outOR38 ["a","tʃ","∅","s","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_21 : check uOR38 (4) (-2) outOR38 ["a","tʃ","∅","s","ɛ","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_22 : check uOR38 (4) (-2) outOR38 ["a","tʃ","∅","s","ɛ","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_23 : check uOR38 (4) (-2) outOR38 ["a","tʃ","∅","s","ɛ","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_24 : check uOR38 (4) (-2) outOR38 ["a","tʃ","∅","s","ɛ","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_25 : check uOR38 (4) (-2) outOR38 ["a","tʃ","∅","s","ɛ","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_26 : check uOR38 (4) (-2) outOR38 ["a","tʃ","∅","s","ɛ","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_27 : check uOR38 (4) (-2) outOR38 ["a","tʃ","∅","s","ɛ","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_28 : check uOR38 (4) (-2) outOR38 ["a","tʃ","∅","s","ɛ","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_29 : check uOR38 (4) (-2) outOR38 ["a","tʃ","∅","s","ɛ","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_30 : check uOR38 (4) (-2) outOR38 ["a","tʃ","∅","s","ɛ","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_31 : check uOR38 (4) (-2) outOR38 ["a","tʃ","∅","s","ɛ","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_32 : check uOR38 (4) (-2) outOR38 ["a","tʃ","∅","s","ɛ","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_33 : check uOR38 (4) (-2) outOR38 ["a","tʃ","∅","s","ɛ","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_20 : check uOR38 (4) (-2) outOR38 ["a","tʃ","∅","s","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_21
  · exact partOR38_1_22
  · exact partOR38_1_23
  · exact partOR38_1_24
  · exact partOR38_1_25
  · exact partOR38_1_26
  · exact partOR38_1_27
  · exact partOR38_1_28
  · exact partOR38_1_29
  · exact partOR38_1_30
  · exact partOR38_1_31
  · exact partOR38_1_32
  · exact partOR38_1_33
theorem partOR38_1_34 : check uOR38 (4) (-2) outOR38 ["a","tʃ","∅","s","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_36 : check uOR38 (4) (-2) outOR38 ["a","tʃ","∅","s","ɪ","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_37 : check uOR38 (4) (-2) outOR38 ["a","tʃ","∅","s","ɪ","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_38 : check uOR38 (4) (-2) outOR38 ["a","tʃ","∅","s","ɪ","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_39 : check uOR38 (4) (-2) outOR38 ["a","tʃ","∅","s","ɪ","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_40 : check uOR38 (4) (-2) outOR38 ["a","tʃ","∅","s","ɪ","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_41 : check uOR38 (4) (-2) outOR38 ["a","tʃ","∅","s","ɪ","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_42 : check uOR38 (4) (-2) outOR38 ["a","tʃ","∅","s","ɪ","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_43 : check uOR38 (4) (-2) outOR38 ["a","tʃ","∅","s","ɪ","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_44 : check uOR38 (4) (-2) outOR38 ["a","tʃ","∅","s","ɪ","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_45 : check uOR38 (4) (-2) outOR38 ["a","tʃ","∅","s","ɪ","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_46 : check uOR38 (4) (-2) outOR38 ["a","tʃ","∅","s","ɪ","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_47 : check uOR38 (4) (-2) outOR38 ["a","tʃ","∅","s","ɪ","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_48 : check uOR38 (4) (-2) outOR38 ["a","tʃ","∅","s","ɪ","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_35 : check uOR38 (4) (-2) outOR38 ["a","tʃ","∅","s","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_36
  · exact partOR38_1_37
  · exact partOR38_1_38
  · exact partOR38_1_39
  · exact partOR38_1_40
  · exact partOR38_1_41
  · exact partOR38_1_42
  · exact partOR38_1_43
  · exact partOR38_1_44
  · exact partOR38_1_45
  · exact partOR38_1_46
  · exact partOR38_1_47
  · exact partOR38_1_48
theorem partOR38_1_49 : check uOR38 (4) (-2) outOR38 ["a","tʃ","∅","s","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_51 : check uOR38 (4) (-2) outOR38 ["a","tʃ","∅","s","ɔ","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_52 : check uOR38 (4) (-2) outOR38 ["a","tʃ","∅","s","ɔ","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_53 : check uOR38 (4) (-2) outOR38 ["a","tʃ","∅","s","ɔ","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_54 : check uOR38 (4) (-2) outOR38 ["a","tʃ","∅","s","ɔ","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_55 : check uOR38 (4) (-2) outOR38 ["a","tʃ","∅","s","ɔ","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_56 : check uOR38 (4) (-2) outOR38 ["a","tʃ","∅","s","ɔ","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_57 : check uOR38 (4) (-2) outOR38 ["a","tʃ","∅","s","ɔ","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_58 : check uOR38 (4) (-2) outOR38 ["a","tʃ","∅","s","ɔ","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_59 : check uOR38 (4) (-2) outOR38 ["a","tʃ","∅","s","ɔ","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_60 : check uOR38 (4) (-2) outOR38 ["a","tʃ","∅","s","ɔ","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_61 : check uOR38 (4) (-2) outOR38 ["a","tʃ","∅","s","ɔ","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_62 : check uOR38 (4) (-2) outOR38 ["a","tʃ","∅","s","ɔ","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_63 : check uOR38 (4) (-2) outOR38 ["a","tʃ","∅","s","ɔ","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_50 : check uOR38 (4) (-2) outOR38 ["a","tʃ","∅","s","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_51
  · exact partOR38_1_52
  · exact partOR38_1_53
  · exact partOR38_1_54
  · exact partOR38_1_55
  · exact partOR38_1_56
  · exact partOR38_1_57
  · exact partOR38_1_58
  · exact partOR38_1_59
  · exact partOR38_1_60
  · exact partOR38_1_61
  · exact partOR38_1_62
  · exact partOR38_1_63
theorem partOR38_1_64 : check uOR38 (4) (-2) outOR38 ["a","tʃ","∅","s","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_66 : check uOR38 (4) (-2) outOR38 ["a","tʃ","∅","s","ʊ","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_67 : check uOR38 (4) (-2) outOR38 ["a","tʃ","∅","s","ʊ","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_68 : check uOR38 (4) (-2) outOR38 ["a","tʃ","∅","s","ʊ","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_69 : check uOR38 (4) (-2) outOR38 ["a","tʃ","∅","s","ʊ","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_70 : check uOR38 (4) (-2) outOR38 ["a","tʃ","∅","s","ʊ","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_71 : check uOR38 (4) (-2) outOR38 ["a","tʃ","∅","s","ʊ","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_72 : check uOR38 (4) (-2) outOR38 ["a","tʃ","∅","s","ʊ","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_73 : check uOR38 (4) (-2) outOR38 ["a","tʃ","∅","s","ʊ","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_74 : check uOR38 (4) (-2) outOR38 ["a","tʃ","∅","s","ʊ","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_75 : check uOR38 (4) (-2) outOR38 ["a","tʃ","∅","s","ʊ","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_76 : check uOR38 (4) (-2) outOR38 ["a","tʃ","∅","s","ʊ","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_77 : check uOR38 (4) (-2) outOR38 ["a","tʃ","∅","s","ʊ","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_78 : check uOR38 (4) (-2) outOR38 ["a","tʃ","∅","s","ʊ","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_65 : check uOR38 (4) (-2) outOR38 ["a","tʃ","∅","s","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_66
  · exact partOR38_1_67
  · exact partOR38_1_68
  · exact partOR38_1_69
  · exact partOR38_1_70
  · exact partOR38_1_71
  · exact partOR38_1_72
  · exact partOR38_1_73
  · exact partOR38_1_74
  · exact partOR38_1_75
  · exact partOR38_1_76
  · exact partOR38_1_77
  · exact partOR38_1_78
theorem partOR38_1_79 : check uOR38 (4) (-2) outOR38 ["a","tʃ","∅","s","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_80 : check uOR38 (4) (-2) outOR38 ["a","tʃ","∅","s","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_81 : check uOR38 (4) (-2) outOR38 ["a","tʃ","∅","s","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_3 : check uOR38 (4) (-2) outOR38 ["a","tʃ","∅","s"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_4
  · exact partOR38_1_5
  · exact partOR38_1_19
  · exact partOR38_1_20
  · exact partOR38_1_34
  · exact partOR38_1_35
  · exact partOR38_1_49
  · exact partOR38_1_50
  · exact partOR38_1_64
  · exact partOR38_1_65
  · exact partOR38_1_79
  · exact partOR38_1_80
  · exact partOR38_1_81
theorem partOR38_1_2 : check uOR38 (4) (-2) outOR38 ["a","tʃ","∅"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="s" := by simpa using hx
  subst x
  exact partOR38_1_3
end ProductiveGua
