import PhonologicalOpacity.Attenuation.Productive.Subject.CertificateParts.OR38_0_000
namespace ProductiveSubjectGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partOR38_0_85 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","a","s","ʊ","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_86 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","a","s","ʊ","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_87 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","a","s","ʊ","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_88 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","a","s","ʊ","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_89 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","a","s","ʊ","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_90 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","a","s","ʊ","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_91 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","a","s","ʊ","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_92 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","a","s","ʊ","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_93 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","a","s","ʊ","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_80 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","a","s","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_0_81
  · exact partOR38_0_82
  · exact partOR38_0_83
  · exact partOR38_0_84
  · exact partOR38_0_85
  · exact partOR38_0_86
  · exact partOR38_0_87
  · exact partOR38_0_88
  · exact partOR38_0_89
  · exact partOR38_0_90
  · exact partOR38_0_91
  · exact partOR38_0_92
  · exact partOR38_0_93
theorem partOR38_0_94 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","a","s","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_95 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","a","s","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_96 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","a","s","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_18 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","a","s"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_0_19
  · exact partOR38_0_20
  · exact partOR38_0_34
  · exact partOR38_0_35
  · exact partOR38_0_49
  · exact partOR38_0_50
  · exact partOR38_0_64
  · exact partOR38_0_65
  · exact partOR38_0_79
  · exact partOR38_0_80
  · exact partOR38_0_94
  · exact partOR38_0_95
  · exact partOR38_0_96
theorem partOR38_0_17 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","a"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="s" := by simpa using hx
  subst x
  exact partOR38_0_18
theorem partOR38_0_99 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɜ","s","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_100 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɜ","s","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_101 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɜ","s","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_102 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɜ","s","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_103 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɜ","s","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_104 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɜ","s","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_105 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɜ","s","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_106 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɜ","s","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_107 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɜ","s","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_108 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɜ","s","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_109 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɜ","s","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_110 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɜ","s","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_111 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɜ","s","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_98 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɜ","s"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_0_99
  · exact partOR38_0_100
  · exact partOR38_0_101
  · exact partOR38_0_102
  · exact partOR38_0_103
  · exact partOR38_0_104
  · exact partOR38_0_105
  · exact partOR38_0_106
  · exact partOR38_0_107
  · exact partOR38_0_108
  · exact partOR38_0_109
  · exact partOR38_0_110
  · exact partOR38_0_111
theorem partOR38_0_97 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɜ"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="s" := by simpa using hx
  subst x
  exact partOR38_0_98
theorem partOR38_0_114 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɛ","s","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_116 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɛ","s","a","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_117 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɛ","s","a","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_118 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɛ","s","a","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_119 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɛ","s","a","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_120 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɛ","s","a","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_121 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɛ","s","a","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_122 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɛ","s","a","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_123 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɛ","s","a","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_124 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɛ","s","a","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_125 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɛ","s","a","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_126 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɛ","s","a","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_127 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɛ","s","a","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_128 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɛ","s","a","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_115 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɛ","s","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_0_116
  · exact partOR38_0_117
  · exact partOR38_0_118
  · exact partOR38_0_119
  · exact partOR38_0_120
  · exact partOR38_0_121
  · exact partOR38_0_122
  · exact partOR38_0_123
  · exact partOR38_0_124
  · exact partOR38_0_125
  · exact partOR38_0_126
  · exact partOR38_0_127
  · exact partOR38_0_128
theorem partOR38_0_129 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɛ","s","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_131 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɛ","s","ɛ","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_132 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɛ","s","ɛ","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_133 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɛ","s","ɛ","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_134 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɛ","s","ɛ","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_135 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɛ","s","ɛ","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_136 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɛ","s","ɛ","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_137 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɛ","s","ɛ","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_138 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɛ","s","ɛ","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_139 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɛ","s","ɛ","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_140 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɛ","s","ɛ","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_141 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɛ","s","ɛ","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_142 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɛ","s","ɛ","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_143 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɛ","s","ɛ","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_130 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɛ","s","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_0_131
  · exact partOR38_0_132
  · exact partOR38_0_133
  · exact partOR38_0_134
  · exact partOR38_0_135
  · exact partOR38_0_136
  · exact partOR38_0_137
  · exact partOR38_0_138
  · exact partOR38_0_139
  · exact partOR38_0_140
  · exact partOR38_0_141
  · exact partOR38_0_142
  · exact partOR38_0_143
theorem partOR38_0_144 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɛ","s","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_146 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɛ","s","ɪ","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_147 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɛ","s","ɪ","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_148 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɛ","s","ɪ","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_149 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɛ","s","ɪ","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_150 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɛ","s","ɪ","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_151 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɛ","s","ɪ","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_152 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɛ","s","ɪ","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_153 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɛ","s","ɪ","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_154 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɛ","s","ɪ","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_155 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɛ","s","ɪ","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_156 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɛ","s","ɪ","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_157 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɛ","s","ɪ","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_158 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɛ","s","ɪ","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_145 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɛ","s","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_0_146
  · exact partOR38_0_147
  · exact partOR38_0_148
  · exact partOR38_0_149
  · exact partOR38_0_150
  · exact partOR38_0_151
  · exact partOR38_0_152
  · exact partOR38_0_153
  · exact partOR38_0_154
  · exact partOR38_0_155
  · exact partOR38_0_156
  · exact partOR38_0_157
  · exact partOR38_0_158
theorem partOR38_0_159 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɛ","s","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_161 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɛ","s","ɔ","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_162 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɛ","s","ɔ","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_163 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɛ","s","ɔ","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_164 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɛ","s","ɔ","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
end ProductiveSubjectGua
