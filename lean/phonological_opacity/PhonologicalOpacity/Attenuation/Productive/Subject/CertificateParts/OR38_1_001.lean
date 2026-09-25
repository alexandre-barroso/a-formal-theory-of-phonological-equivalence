import PhonologicalOpacity.Attenuation.Productive.Subject.CertificateParts.OR38_1_000
namespace ProductiveSubjectGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partOR38_1_85 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","∅","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_86 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","∅","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_87 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","∅","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_88 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","∅","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_89 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","∅","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_90 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","∅","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_91 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","∅","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_92 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","∅","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_93 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","∅","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_94 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","∅","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_95 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","∅","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_96 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","∅","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_97 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","∅","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_84 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_85
  · exact partOR38_1_86
  · exact partOR38_1_87
  · exact partOR38_1_88
  · exact partOR38_1_89
  · exact partOR38_1_90
  · exact partOR38_1_91
  · exact partOR38_1_92
  · exact partOR38_1_93
  · exact partOR38_1_94
  · exact partOR38_1_95
  · exact partOR38_1_96
  · exact partOR38_1_97
theorem partOR38_1_99 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","a","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_100 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","a","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_101 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","a","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_102 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","a","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_103 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","a","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_104 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","a","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_105 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","a","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_106 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","a","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_107 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","a","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_108 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","a","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_109 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","a","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_110 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","a","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_111 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","a","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_98 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_99
  · exact partOR38_1_100
  · exact partOR38_1_101
  · exact partOR38_1_102
  · exact partOR38_1_103
  · exact partOR38_1_104
  · exact partOR38_1_105
  · exact partOR38_1_106
  · exact partOR38_1_107
  · exact partOR38_1_108
  · exact partOR38_1_109
  · exact partOR38_1_110
  · exact partOR38_1_111
theorem partOR38_1_113 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","ɜ","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_114 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","ɜ","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_115 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","ɜ","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_116 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","ɜ","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_117 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","ɜ","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_118 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","ɜ","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_119 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","ɜ","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_120 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","ɜ","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_121 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","ɜ","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_122 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","ɜ","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_123 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","ɜ","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_124 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","ɜ","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_125 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","ɜ","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_112 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_113
  · exact partOR38_1_114
  · exact partOR38_1_115
  · exact partOR38_1_116
  · exact partOR38_1_117
  · exact partOR38_1_118
  · exact partOR38_1_119
  · exact partOR38_1_120
  · exact partOR38_1_121
  · exact partOR38_1_122
  · exact partOR38_1_123
  · exact partOR38_1_124
  · exact partOR38_1_125
theorem partOR38_1_127 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","ɛ","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_128 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","ɛ","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_129 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","ɛ","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_130 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","ɛ","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_131 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","ɛ","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_132 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","ɛ","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_133 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","ɛ","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_134 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","ɛ","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_135 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","ɛ","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_136 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","ɛ","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_137 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","ɛ","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_138 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","ɛ","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_139 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","ɛ","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_126 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_127
  · exact partOR38_1_128
  · exact partOR38_1_129
  · exact partOR38_1_130
  · exact partOR38_1_131
  · exact partOR38_1_132
  · exact partOR38_1_133
  · exact partOR38_1_134
  · exact partOR38_1_135
  · exact partOR38_1_136
  · exact partOR38_1_137
  · exact partOR38_1_138
  · exact partOR38_1_139
theorem partOR38_1_141 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","e","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_142 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","e","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_143 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","e","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_144 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","e","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_145 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","e","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_146 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","e","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_147 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","e","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_148 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","e","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_149 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","e","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_150 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","e","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_151 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","e","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_152 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","e","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_153 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","e","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_140 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_141
  · exact partOR38_1_142
  · exact partOR38_1_143
  · exact partOR38_1_144
  · exact partOR38_1_145
  · exact partOR38_1_146
  · exact partOR38_1_147
  · exact partOR38_1_148
  · exact partOR38_1_149
  · exact partOR38_1_150
  · exact partOR38_1_151
  · exact partOR38_1_152
  · exact partOR38_1_153
theorem partOR38_1_155 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","ɪ","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_156 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","ɪ","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_157 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","ɪ","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_158 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","ɪ","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_159 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","ɪ","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_160 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","ɪ","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_161 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","ɪ","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_162 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","ɪ","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_163 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","ɪ","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_164 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","ɪ","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
end ProductiveSubjectGua
