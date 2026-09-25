import PhonologicalOpacity.Attenuation.Productive.Subject.CertificateParts.C21b_11_000
namespace ProductiveSubjectGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partC21b_11_84 : check uC21b (3) (-4) outC21b ["j","ʊ","s","ʊ","i"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_11_85 : check uC21b (3) (-4) outC21b ["j","ʊ","s","ʊ","ɔ"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_11_86 : check uC21b (3) (-4) outC21b ["j","ʊ","s","ʊ","o"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_11_87 : check uC21b (3) (-4) outC21b ["j","ʊ","s","ʊ","ʊ"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_11_88 : check uC21b (3) (-4) outC21b ["j","ʊ","s","ʊ","u"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_11_89 : check uC21b (3) (-4) outC21b ["j","ʊ","s","ʊ","j"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_11_90 : check uC21b (3) (-4) outC21b ["j","ʊ","s","ʊ","w"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_11_77 : check uC21b (3) (-4) outC21b ["j","ʊ","s","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partC21b_11_78
  · exact partC21b_11_79
  · exact partC21b_11_80
  · exact partC21b_11_81
  · exact partC21b_11_82
  · exact partC21b_11_83
  · exact partC21b_11_84
  · exact partC21b_11_85
  · exact partC21b_11_86
  · exact partC21b_11_87
  · exact partC21b_11_88
  · exact partC21b_11_89
  · exact partC21b_11_90
theorem partC21b_11_91 : check uC21b (3) (-4) outC21b ["j","ʊ","s","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_11_92 : check uC21b (3) (-4) outC21b ["j","ʊ","s","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_11_93 : check uC21b (3) (-4) outC21b ["j","ʊ","s","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_11_67 : check uC21b (3) (-4) outC21b ["j","ʊ","s"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partC21b_11_68
  · exact partC21b_11_69
  · exact partC21b_11_70
  · exact partC21b_11_71
  · exact partC21b_11_72
  · exact partC21b_11_73
  · exact partC21b_11_74
  · exact partC21b_11_75
  · exact partC21b_11_76
  · exact partC21b_11_77
  · exact partC21b_11_91
  · exact partC21b_11_92
  · exact partC21b_11_93
theorem partC21b_11_66 : check uC21b (3) (-4) outC21b ["j","ʊ"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="s" := by simpa using hx
  subst x
  exact partC21b_11_67
theorem partC21b_11_96 : check uC21b (3) (-4) outC21b ["j","u","s","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_11_97 : check uC21b (3) (-4) outC21b ["j","u","s","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_11_98 : check uC21b (3) (-4) outC21b ["j","u","s","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_11_99 : check uC21b (3) (-4) outC21b ["j","u","s","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_11_100 : check uC21b (3) (-4) outC21b ["j","u","s","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_11_101 : check uC21b (3) (-4) outC21b ["j","u","s","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_11_102 : check uC21b (3) (-4) outC21b ["j","u","s","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_11_103 : check uC21b (3) (-4) outC21b ["j","u","s","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_11_104 : check uC21b (3) (-4) outC21b ["j","u","s","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_11_105 : check uC21b (3) (-4) outC21b ["j","u","s","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_11_106 : check uC21b (3) (-4) outC21b ["j","u","s","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_11_107 : check uC21b (3) (-4) outC21b ["j","u","s","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_11_108 : check uC21b (3) (-4) outC21b ["j","u","s","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_11_95 : check uC21b (3) (-4) outC21b ["j","u","s"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partC21b_11_96
  · exact partC21b_11_97
  · exact partC21b_11_98
  · exact partC21b_11_99
  · exact partC21b_11_100
  · exact partC21b_11_101
  · exact partC21b_11_102
  · exact partC21b_11_103
  · exact partC21b_11_104
  · exact partC21b_11_105
  · exact partC21b_11_106
  · exact partC21b_11_107
  · exact partC21b_11_108
theorem partC21b_11_94 : check uC21b (3) (-4) outC21b ["j","u"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="s" := by simpa using hx
  subst x
  exact partC21b_11_95
theorem partC21b_11_109 : check uC21b (3) (-4) outC21b ["j","j"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_11_110 : check uC21b (3) (-4) outC21b ["j","w"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem checkedC21b_11 : check uC21b (3) (-4) outC21b ["j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partC21b_11_1
  · exact partC21b_11_2
  · exact partC21b_11_17
  · exact partC21b_11_18
  · exact partC21b_11_33
  · exact partC21b_11_34
  · exact partC21b_11_49
  · exact partC21b_11_50
  · exact partC21b_11_65
  · exact partC21b_11_66
  · exact partC21b_11_94
  · exact partC21b_11_109
  · exact partC21b_11_110
end ProductiveSubjectGua
