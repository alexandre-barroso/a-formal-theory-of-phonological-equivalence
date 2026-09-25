import PhonologicalOpacity.Attenuation.Productive.Subject.CertificateParts.G37c_7_063
namespace ProductiveSubjectGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partG37c_7_5127 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","e","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5128 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","e","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5129 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","e","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5130 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","e","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5131 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","e","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5132 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","e","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5133 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","e","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5134 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","e","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5135 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","e","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5136 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","e","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5137 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","e","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5124 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","e","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_5125
  · exact partG37c_7_5126
  · exact partG37c_7_5127
  · exact partG37c_7_5128
  · exact partG37c_7_5129
  · exact partG37c_7_5130
  · exact partG37c_7_5131
  · exact partG37c_7_5132
  · exact partG37c_7_5133
  · exact partG37c_7_5134
  · exact partG37c_7_5135
  · exact partG37c_7_5136
  · exact partG37c_7_5137
theorem partG37c_7_5123 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","e","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_5124
theorem partG37c_7_5138 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","e","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5139 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","e","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5140 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","e","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5141 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","e","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5142 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","e","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5143 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","e","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5116 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_5117
  · exact partG37c_7_5118
  · exact partG37c_7_5119
  · exact partG37c_7_5120
  · exact partG37c_7_5121
  · exact partG37c_7_5122
  · exact partG37c_7_5123
  · exact partG37c_7_5138
  · exact partG37c_7_5139
  · exact partG37c_7_5140
  · exact partG37c_7_5141
  · exact partG37c_7_5142
  · exact partG37c_7_5143
theorem partG37c_7_5147 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɪ","∅","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5148 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɪ","∅","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5149 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɪ","∅","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5150 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɪ","∅","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5151 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɪ","∅","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5152 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɪ","∅","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5153 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɪ","∅","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5154 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɪ","∅","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5155 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɪ","∅","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5156 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɪ","∅","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5157 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɪ","∅","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5158 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɪ","∅","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5159 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɪ","∅","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5146 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɪ","∅","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_5147
  · exact partG37c_7_5148
  · exact partG37c_7_5149
  · exact partG37c_7_5150
  · exact partG37c_7_5151
  · exact partG37c_7_5152
  · exact partG37c_7_5153
  · exact partG37c_7_5154
  · exact partG37c_7_5155
  · exact partG37c_7_5156
  · exact partG37c_7_5157
  · exact partG37c_7_5158
  · exact partG37c_7_5159
theorem partG37c_7_5145 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɪ","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_5146
theorem partG37c_7_5160 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɪ","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5161 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɪ","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5162 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɪ","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5163 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɪ","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5164 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɪ","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5167 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɪ","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5168 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɪ","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5169 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɪ","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5170 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɪ","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5171 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɪ","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5172 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɪ","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5173 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɪ","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5174 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɪ","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5175 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɪ","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5176 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɪ","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5177 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɪ","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5178 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɪ","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5179 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɪ","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5166 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɪ","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_5167
  · exact partG37c_7_5168
  · exact partG37c_7_5169
  · exact partG37c_7_5170
  · exact partG37c_7_5171
  · exact partG37c_7_5172
  · exact partG37c_7_5173
  · exact partG37c_7_5174
  · exact partG37c_7_5175
  · exact partG37c_7_5176
  · exact partG37c_7_5177
  · exact partG37c_7_5178
  · exact partG37c_7_5179
theorem partG37c_7_5165 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɪ","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_5166
theorem partG37c_7_5180 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɪ","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5181 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɪ","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5182 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɪ","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5183 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɪ","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5186 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɪ","j","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5187 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɪ","j","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5188 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɪ","j","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5189 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɪ","j","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5190 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɪ","j","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5191 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɪ","j","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5192 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɪ","j","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5193 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɪ","j","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5194 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɪ","j","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5195 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɪ","j","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5196 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɪ","j","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5197 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɪ","j","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5198 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɪ","j","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5185 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɪ","j","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_5186
  · exact partG37c_7_5187
  · exact partG37c_7_5188
  · exact partG37c_7_5189
  · exact partG37c_7_5190
  · exact partG37c_7_5191
  · exact partG37c_7_5192
  · exact partG37c_7_5193
  · exact partG37c_7_5194
  · exact partG37c_7_5195
  · exact partG37c_7_5196
  · exact partG37c_7_5197
  · exact partG37c_7_5198
theorem partG37c_7_5184 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɪ","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_5185
theorem partG37c_7_5199 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɪ","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5144 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_5145
  · exact partG37c_7_5160
  · exact partG37c_7_5161
  · exact partG37c_7_5162
  · exact partG37c_7_5163
  · exact partG37c_7_5164
  · exact partG37c_7_5165
  · exact partG37c_7_5180
  · exact partG37c_7_5181
  · exact partG37c_7_5182
  · exact partG37c_7_5183
  · exact partG37c_7_5184
  · exact partG37c_7_5199
theorem partG37c_7_5201 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","i","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5202 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","i","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5203 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","i","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5204 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","i","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
end ProductiveSubjectGua
