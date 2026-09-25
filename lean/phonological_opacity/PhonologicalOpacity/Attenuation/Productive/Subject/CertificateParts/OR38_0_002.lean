import PhonologicalOpacity.Attenuation.Productive.Subject.CertificateParts.OR38_0_001
namespace ProductiveSubjectGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partOR38_0_165 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɛ","s","ɔ","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_166 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɛ","s","ɔ","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_167 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɛ","s","ɔ","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_168 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɛ","s","ɔ","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_169 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɛ","s","ɔ","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_170 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɛ","s","ɔ","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_171 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɛ","s","ɔ","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_172 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɛ","s","ɔ","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_173 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɛ","s","ɔ","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_160 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɛ","s","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_0_161
  · exact partOR38_0_162
  · exact partOR38_0_163
  · exact partOR38_0_164
  · exact partOR38_0_165
  · exact partOR38_0_166
  · exact partOR38_0_167
  · exact partOR38_0_168
  · exact partOR38_0_169
  · exact partOR38_0_170
  · exact partOR38_0_171
  · exact partOR38_0_172
  · exact partOR38_0_173
theorem partOR38_0_174 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɛ","s","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_176 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɛ","s","ʊ","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_177 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɛ","s","ʊ","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_178 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɛ","s","ʊ","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_179 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɛ","s","ʊ","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_180 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɛ","s","ʊ","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_181 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɛ","s","ʊ","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_182 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɛ","s","ʊ","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_183 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɛ","s","ʊ","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_184 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɛ","s","ʊ","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_185 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɛ","s","ʊ","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_186 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɛ","s","ʊ","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_187 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɛ","s","ʊ","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_188 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɛ","s","ʊ","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_175 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɛ","s","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_0_176
  · exact partOR38_0_177
  · exact partOR38_0_178
  · exact partOR38_0_179
  · exact partOR38_0_180
  · exact partOR38_0_181
  · exact partOR38_0_182
  · exact partOR38_0_183
  · exact partOR38_0_184
  · exact partOR38_0_185
  · exact partOR38_0_186
  · exact partOR38_0_187
  · exact partOR38_0_188
theorem partOR38_0_189 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɛ","s","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_190 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɛ","s","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_191 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɛ","s","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_113 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɛ","s"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_0_114
  · exact partOR38_0_115
  · exact partOR38_0_129
  · exact partOR38_0_130
  · exact partOR38_0_144
  · exact partOR38_0_145
  · exact partOR38_0_159
  · exact partOR38_0_160
  · exact partOR38_0_174
  · exact partOR38_0_175
  · exact partOR38_0_189
  · exact partOR38_0_190
  · exact partOR38_0_191
theorem partOR38_0_112 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɛ"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="s" := by simpa using hx
  subst x
  exact partOR38_0_113
theorem partOR38_0_194 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","e","s","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_195 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","e","s","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_196 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","e","s","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_197 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","e","s","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_198 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","e","s","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_199 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","e","s","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_200 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","e","s","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_201 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","e","s","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_202 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","e","s","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_203 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","e","s","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_204 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","e","s","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_205 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","e","s","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_206 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","e","s","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_193 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","e","s"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_0_194
  · exact partOR38_0_195
  · exact partOR38_0_196
  · exact partOR38_0_197
  · exact partOR38_0_198
  · exact partOR38_0_199
  · exact partOR38_0_200
  · exact partOR38_0_201
  · exact partOR38_0_202
  · exact partOR38_0_203
  · exact partOR38_0_204
  · exact partOR38_0_205
  · exact partOR38_0_206
theorem partOR38_0_192 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","e"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="s" := by simpa using hx
  subst x
  exact partOR38_0_193
theorem partOR38_0_209 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɪ","s","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_211 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɪ","s","a","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_212 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɪ","s","a","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_213 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɪ","s","a","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_214 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɪ","s","a","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_215 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɪ","s","a","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_216 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɪ","s","a","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_217 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɪ","s","a","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_218 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɪ","s","a","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_219 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɪ","s","a","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_220 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɪ","s","a","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_221 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɪ","s","a","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_222 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɪ","s","a","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_223 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɪ","s","a","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_210 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɪ","s","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_0_211
  · exact partOR38_0_212
  · exact partOR38_0_213
  · exact partOR38_0_214
  · exact partOR38_0_215
  · exact partOR38_0_216
  · exact partOR38_0_217
  · exact partOR38_0_218
  · exact partOR38_0_219
  · exact partOR38_0_220
  · exact partOR38_0_221
  · exact partOR38_0_222
  · exact partOR38_0_223
theorem partOR38_0_224 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɪ","s","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_226 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɪ","s","ɛ","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_227 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɪ","s","ɛ","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_228 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɪ","s","ɛ","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_229 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɪ","s","ɛ","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_230 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɪ","s","ɛ","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_231 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɪ","s","ɛ","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_232 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɪ","s","ɛ","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_233 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɪ","s","ɛ","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_234 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɪ","s","ɛ","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_235 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɪ","s","ɛ","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_236 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɪ","s","ɛ","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_237 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɪ","s","ɛ","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_238 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɪ","s","ɛ","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_225 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɪ","s","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_0_226
  · exact partOR38_0_227
  · exact partOR38_0_228
  · exact partOR38_0_229
  · exact partOR38_0_230
  · exact partOR38_0_231
  · exact partOR38_0_232
  · exact partOR38_0_233
  · exact partOR38_0_234
  · exact partOR38_0_235
  · exact partOR38_0_236
  · exact partOR38_0_237
  · exact partOR38_0_238
theorem partOR38_0_239 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɪ","s","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_241 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɪ","s","ɪ","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_242 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɪ","s","ɪ","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_243 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɪ","s","ɪ","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_244 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɪ","s","ɪ","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
end ProductiveSubjectGua
