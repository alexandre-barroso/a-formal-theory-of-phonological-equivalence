import PhonologicalOpacity.Attenuation.Productive.Baseline.CertificateParts.N7_1_000
namespace ProductiveGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partN7_1_70 : check uN7 (1) (0) outN7 ["a","tʃ","ɛ","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partN7_1_71
  · exact partN7_1_72
  · exact partN7_1_73
  · exact partN7_1_74
  · exact partN7_1_75
  · exact partN7_1_76
  · exact partN7_1_77
  · exact partN7_1_78
  · exact partN7_1_79
  · exact partN7_1_80
  · exact partN7_1_81
  · exact partN7_1_82
  · exact partN7_1_83
theorem partN7_1_44 : check uN7 (1) (0) outN7 ["a","tʃ","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partN7_1_45
  · exact partN7_1_46
  · exact partN7_1_47
  · exact partN7_1_48
  · exact partN7_1_49
  · exact partN7_1_50
  · exact partN7_1_51
  · exact partN7_1_52
  · exact partN7_1_53
  · exact partN7_1_54
  · exact partN7_1_55
  · exact partN7_1_56
  · exact partN7_1_70
theorem partN7_1_84 : check uN7 (1) (0) outN7 ["a","tʃ","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_86 : check uN7 (1) (0) outN7 ["a","tʃ","ɪ","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_87 : check uN7 (1) (0) outN7 ["a","tʃ","ɪ","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_88 : check uN7 (1) (0) outN7 ["a","tʃ","ɪ","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_89 : check uN7 (1) (0) outN7 ["a","tʃ","ɪ","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_90 : check uN7 (1) (0) outN7 ["a","tʃ","ɪ","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_91 : check uN7 (1) (0) outN7 ["a","tʃ","ɪ","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_92 : check uN7 (1) (0) outN7 ["a","tʃ","ɪ","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_93 : check uN7 (1) (0) outN7 ["a","tʃ","ɪ","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_94 : check uN7 (1) (0) outN7 ["a","tʃ","ɪ","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_95 : check uN7 (1) (0) outN7 ["a","tʃ","ɪ","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_96 : check uN7 (1) (0) outN7 ["a","tʃ","ɪ","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_98 : check uN7 (1) (0) outN7 ["a","tʃ","ɪ","j","∅"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_99 : check uN7 (1) (0) outN7 ["a","tʃ","ɪ","j","a"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_100 : check uN7 (1) (0) outN7 ["a","tʃ","ɪ","j","ɜ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_101 : check uN7 (1) (0) outN7 ["a","tʃ","ɪ","j","ɛ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_102 : check uN7 (1) (0) outN7 ["a","tʃ","ɪ","j","e"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_103 : check uN7 (1) (0) outN7 ["a","tʃ","ɪ","j","ɪ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_104 : check uN7 (1) (0) outN7 ["a","tʃ","ɪ","j","i"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_105 : check uN7 (1) (0) outN7 ["a","tʃ","ɪ","j","ɔ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_106 : check uN7 (1) (0) outN7 ["a","tʃ","ɪ","j","o"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_107 : check uN7 (1) (0) outN7 ["a","tʃ","ɪ","j","ʊ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_108 : check uN7 (1) (0) outN7 ["a","tʃ","ɪ","j","u"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_109 : check uN7 (1) (0) outN7 ["a","tʃ","ɪ","j","j"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_110 : check uN7 (1) (0) outN7 ["a","tʃ","ɪ","j","w"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_97 : check uN7 (1) (0) outN7 ["a","tʃ","ɪ","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partN7_1_98
  · exact partN7_1_99
  · exact partN7_1_100
  · exact partN7_1_101
  · exact partN7_1_102
  · exact partN7_1_103
  · exact partN7_1_104
  · exact partN7_1_105
  · exact partN7_1_106
  · exact partN7_1_107
  · exact partN7_1_108
  · exact partN7_1_109
  · exact partN7_1_110
theorem partN7_1_112 : check uN7 (1) (0) outN7 ["a","tʃ","ɪ","w","∅"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_113 : check uN7 (1) (0) outN7 ["a","tʃ","ɪ","w","a"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_114 : check uN7 (1) (0) outN7 ["a","tʃ","ɪ","w","ɜ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_115 : check uN7 (1) (0) outN7 ["a","tʃ","ɪ","w","ɛ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_116 : check uN7 (1) (0) outN7 ["a","tʃ","ɪ","w","e"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_117 : check uN7 (1) (0) outN7 ["a","tʃ","ɪ","w","ɪ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_118 : check uN7 (1) (0) outN7 ["a","tʃ","ɪ","w","i"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_119 : check uN7 (1) (0) outN7 ["a","tʃ","ɪ","w","ɔ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_120 : check uN7 (1) (0) outN7 ["a","tʃ","ɪ","w","o"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_121 : check uN7 (1) (0) outN7 ["a","tʃ","ɪ","w","ʊ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_122 : check uN7 (1) (0) outN7 ["a","tʃ","ɪ","w","u"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_123 : check uN7 (1) (0) outN7 ["a","tʃ","ɪ","w","j"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_124 : check uN7 (1) (0) outN7 ["a","tʃ","ɪ","w","w"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_111 : check uN7 (1) (0) outN7 ["a","tʃ","ɪ","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partN7_1_112
  · exact partN7_1_113
  · exact partN7_1_114
  · exact partN7_1_115
  · exact partN7_1_116
  · exact partN7_1_117
  · exact partN7_1_118
  · exact partN7_1_119
  · exact partN7_1_120
  · exact partN7_1_121
  · exact partN7_1_122
  · exact partN7_1_123
  · exact partN7_1_124
theorem partN7_1_85 : check uN7 (1) (0) outN7 ["a","tʃ","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partN7_1_86
  · exact partN7_1_87
  · exact partN7_1_88
  · exact partN7_1_89
  · exact partN7_1_90
  · exact partN7_1_91
  · exact partN7_1_92
  · exact partN7_1_93
  · exact partN7_1_94
  · exact partN7_1_95
  · exact partN7_1_96
  · exact partN7_1_97
  · exact partN7_1_111
theorem partN7_1_125 : check uN7 (1) (0) outN7 ["a","tʃ","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_127 : check uN7 (1) (0) outN7 ["a","tʃ","ɔ","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_128 : check uN7 (1) (0) outN7 ["a","tʃ","ɔ","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_129 : check uN7 (1) (0) outN7 ["a","tʃ","ɔ","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_130 : check uN7 (1) (0) outN7 ["a","tʃ","ɔ","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_131 : check uN7 (1) (0) outN7 ["a","tʃ","ɔ","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_132 : check uN7 (1) (0) outN7 ["a","tʃ","ɔ","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_133 : check uN7 (1) (0) outN7 ["a","tʃ","ɔ","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_134 : check uN7 (1) (0) outN7 ["a","tʃ","ɔ","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_135 : check uN7 (1) (0) outN7 ["a","tʃ","ɔ","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_136 : check uN7 (1) (0) outN7 ["a","tʃ","ɔ","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_137 : check uN7 (1) (0) outN7 ["a","tʃ","ɔ","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_139 : check uN7 (1) (0) outN7 ["a","tʃ","ɔ","j","∅"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_140 : check uN7 (1) (0) outN7 ["a","tʃ","ɔ","j","a"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_141 : check uN7 (1) (0) outN7 ["a","tʃ","ɔ","j","ɜ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_142 : check uN7 (1) (0) outN7 ["a","tʃ","ɔ","j","ɛ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_143 : check uN7 (1) (0) outN7 ["a","tʃ","ɔ","j","e"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_144 : check uN7 (1) (0) outN7 ["a","tʃ","ɔ","j","ɪ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_145 : check uN7 (1) (0) outN7 ["a","tʃ","ɔ","j","i"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_146 : check uN7 (1) (0) outN7 ["a","tʃ","ɔ","j","ɔ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_147 : check uN7 (1) (0) outN7 ["a","tʃ","ɔ","j","o"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_148 : check uN7 (1) (0) outN7 ["a","tʃ","ɔ","j","ʊ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_149 : check uN7 (1) (0) outN7 ["a","tʃ","ɔ","j","u"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_150 : check uN7 (1) (0) outN7 ["a","tʃ","ɔ","j","j"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_151 : check uN7 (1) (0) outN7 ["a","tʃ","ɔ","j","w"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_138 : check uN7 (1) (0) outN7 ["a","tʃ","ɔ","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partN7_1_139
  · exact partN7_1_140
  · exact partN7_1_141
  · exact partN7_1_142
  · exact partN7_1_143
  · exact partN7_1_144
  · exact partN7_1_145
  · exact partN7_1_146
  · exact partN7_1_147
  · exact partN7_1_148
  · exact partN7_1_149
  · exact partN7_1_150
  · exact partN7_1_151
theorem partN7_1_153 : check uN7 (1) (0) outN7 ["a","tʃ","ɔ","w","∅"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_154 : check uN7 (1) (0) outN7 ["a","tʃ","ɔ","w","a"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_155 : check uN7 (1) (0) outN7 ["a","tʃ","ɔ","w","ɜ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_156 : check uN7 (1) (0) outN7 ["a","tʃ","ɔ","w","ɛ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_157 : check uN7 (1) (0) outN7 ["a","tʃ","ɔ","w","e"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_158 : check uN7 (1) (0) outN7 ["a","tʃ","ɔ","w","ɪ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_159 : check uN7 (1) (0) outN7 ["a","tʃ","ɔ","w","i"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_160 : check uN7 (1) (0) outN7 ["a","tʃ","ɔ","w","ɔ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_161 : check uN7 (1) (0) outN7 ["a","tʃ","ɔ","w","o"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_162 : check uN7 (1) (0) outN7 ["a","tʃ","ɔ","w","ʊ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_163 : check uN7 (1) (0) outN7 ["a","tʃ","ɔ","w","u"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
end ProductiveGua
