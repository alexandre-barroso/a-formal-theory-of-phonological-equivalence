import PhonologicalOpacity.Attenuation.Productive.Subject.CertificateParts.N7_1_001
namespace ProductiveSubjectGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partN7_1_164 : check uN7 (1) (0) outN7 ["a","tʃ","ɔ","w","j"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_165 : check uN7 (1) (0) outN7 ["a","tʃ","ɔ","w","w"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_152 : check uN7 (1) (0) outN7 ["a","tʃ","ɔ","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partN7_1_153
  · exact partN7_1_154
  · exact partN7_1_155
  · exact partN7_1_156
  · exact partN7_1_157
  · exact partN7_1_158
  · exact partN7_1_159
  · exact partN7_1_160
  · exact partN7_1_161
  · exact partN7_1_162
  · exact partN7_1_163
  · exact partN7_1_164
  · exact partN7_1_165
theorem partN7_1_126 : check uN7 (1) (0) outN7 ["a","tʃ","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partN7_1_127
  · exact partN7_1_128
  · exact partN7_1_129
  · exact partN7_1_130
  · exact partN7_1_131
  · exact partN7_1_132
  · exact partN7_1_133
  · exact partN7_1_134
  · exact partN7_1_135
  · exact partN7_1_136
  · exact partN7_1_137
  · exact partN7_1_138
  · exact partN7_1_152
theorem partN7_1_166 : check uN7 (1) (0) outN7 ["a","tʃ","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_168 : check uN7 (1) (0) outN7 ["a","tʃ","ʊ","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_169 : check uN7 (1) (0) outN7 ["a","tʃ","ʊ","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_170 : check uN7 (1) (0) outN7 ["a","tʃ","ʊ","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_171 : check uN7 (1) (0) outN7 ["a","tʃ","ʊ","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_172 : check uN7 (1) (0) outN7 ["a","tʃ","ʊ","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_173 : check uN7 (1) (0) outN7 ["a","tʃ","ʊ","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_174 : check uN7 (1) (0) outN7 ["a","tʃ","ʊ","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_175 : check uN7 (1) (0) outN7 ["a","tʃ","ʊ","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_176 : check uN7 (1) (0) outN7 ["a","tʃ","ʊ","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_177 : check uN7 (1) (0) outN7 ["a","tʃ","ʊ","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_178 : check uN7 (1) (0) outN7 ["a","tʃ","ʊ","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_180 : check uN7 (1) (0) outN7 ["a","tʃ","ʊ","j","∅"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_181 : check uN7 (1) (0) outN7 ["a","tʃ","ʊ","j","a"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_182 : check uN7 (1) (0) outN7 ["a","tʃ","ʊ","j","ɜ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_183 : check uN7 (1) (0) outN7 ["a","tʃ","ʊ","j","ɛ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_184 : check uN7 (1) (0) outN7 ["a","tʃ","ʊ","j","e"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_185 : check uN7 (1) (0) outN7 ["a","tʃ","ʊ","j","ɪ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_186 : check uN7 (1) (0) outN7 ["a","tʃ","ʊ","j","i"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_187 : check uN7 (1) (0) outN7 ["a","tʃ","ʊ","j","ɔ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_188 : check uN7 (1) (0) outN7 ["a","tʃ","ʊ","j","o"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_189 : check uN7 (1) (0) outN7 ["a","tʃ","ʊ","j","ʊ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_190 : check uN7 (1) (0) outN7 ["a","tʃ","ʊ","j","u"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_191 : check uN7 (1) (0) outN7 ["a","tʃ","ʊ","j","j"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_192 : check uN7 (1) (0) outN7 ["a","tʃ","ʊ","j","w"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_179 : check uN7 (1) (0) outN7 ["a","tʃ","ʊ","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partN7_1_180
  · exact partN7_1_181
  · exact partN7_1_182
  · exact partN7_1_183
  · exact partN7_1_184
  · exact partN7_1_185
  · exact partN7_1_186
  · exact partN7_1_187
  · exact partN7_1_188
  · exact partN7_1_189
  · exact partN7_1_190
  · exact partN7_1_191
  · exact partN7_1_192
theorem partN7_1_194 : check uN7 (1) (0) outN7 ["a","tʃ","ʊ","w","∅"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_195 : check uN7 (1) (0) outN7 ["a","tʃ","ʊ","w","a"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_196 : check uN7 (1) (0) outN7 ["a","tʃ","ʊ","w","ɜ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_197 : check uN7 (1) (0) outN7 ["a","tʃ","ʊ","w","ɛ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_198 : check uN7 (1) (0) outN7 ["a","tʃ","ʊ","w","e"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_199 : check uN7 (1) (0) outN7 ["a","tʃ","ʊ","w","ɪ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_200 : check uN7 (1) (0) outN7 ["a","tʃ","ʊ","w","i"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_201 : check uN7 (1) (0) outN7 ["a","tʃ","ʊ","w","ɔ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_202 : check uN7 (1) (0) outN7 ["a","tʃ","ʊ","w","o"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_203 : check uN7 (1) (0) outN7 ["a","tʃ","ʊ","w","ʊ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_204 : check uN7 (1) (0) outN7 ["a","tʃ","ʊ","w","u"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_205 : check uN7 (1) (0) outN7 ["a","tʃ","ʊ","w","j"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_206 : check uN7 (1) (0) outN7 ["a","tʃ","ʊ","w","w"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_193 : check uN7 (1) (0) outN7 ["a","tʃ","ʊ","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partN7_1_194
  · exact partN7_1_195
  · exact partN7_1_196
  · exact partN7_1_197
  · exact partN7_1_198
  · exact partN7_1_199
  · exact partN7_1_200
  · exact partN7_1_201
  · exact partN7_1_202
  · exact partN7_1_203
  · exact partN7_1_204
  · exact partN7_1_205
  · exact partN7_1_206
theorem partN7_1_167 : check uN7 (1) (0) outN7 ["a","tʃ","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partN7_1_168
  · exact partN7_1_169
  · exact partN7_1_170
  · exact partN7_1_171
  · exact partN7_1_172
  · exact partN7_1_173
  · exact partN7_1_174
  · exact partN7_1_175
  · exact partN7_1_176
  · exact partN7_1_177
  · exact partN7_1_178
  · exact partN7_1_179
  · exact partN7_1_193
theorem partN7_1_207 : check uN7 (1) (0) outN7 ["a","tʃ","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_208 : check uN7 (1) (0) outN7 ["a","tʃ","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_209 : check uN7 (1) (0) outN7 ["a","tʃ","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partN7_1_1 : check uN7 (1) (0) outN7 ["a","tʃ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partN7_1_2
  · exact partN7_1_3
  · exact partN7_1_43
  · exact partN7_1_44
  · exact partN7_1_84
  · exact partN7_1_85
  · exact partN7_1_125
  · exact partN7_1_126
  · exact partN7_1_166
  · exact partN7_1_167
  · exact partN7_1_207
  · exact partN7_1_208
  · exact partN7_1_209
theorem checkedN7_1 : check uN7 (1) (0) outN7 ["a"] [["tʃ"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="tʃ" := by simpa using hx
  subst x
  exact partN7_1_1
end ProductiveSubjectGua
