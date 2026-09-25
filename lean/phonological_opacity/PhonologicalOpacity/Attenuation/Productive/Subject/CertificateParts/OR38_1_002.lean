import PhonologicalOpacity.Attenuation.Productive.Subject.CertificateParts.OR38_1_001
namespace ProductiveSubjectGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partOR38_1_165 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","ɪ","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_166 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","ɪ","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_167 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","ɪ","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_154 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_155
  · exact partOR38_1_156
  · exact partOR38_1_157
  · exact partOR38_1_158
  · exact partOR38_1_159
  · exact partOR38_1_160
  · exact partOR38_1_161
  · exact partOR38_1_162
  · exact partOR38_1_163
  · exact partOR38_1_164
  · exact partOR38_1_165
  · exact partOR38_1_166
  · exact partOR38_1_167
theorem partOR38_1_169 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","i","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_170 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","i","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_171 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","i","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_172 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","i","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_173 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","i","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_174 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","i","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_175 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","i","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_176 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","i","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_177 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","i","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_178 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","i","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_179 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","i","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_180 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","i","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_181 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","i","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_168 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_169
  · exact partOR38_1_170
  · exact partOR38_1_171
  · exact partOR38_1_172
  · exact partOR38_1_173
  · exact partOR38_1_174
  · exact partOR38_1_175
  · exact partOR38_1_176
  · exact partOR38_1_177
  · exact partOR38_1_178
  · exact partOR38_1_179
  · exact partOR38_1_180
  · exact partOR38_1_181
theorem partOR38_1_183 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","ɔ","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_184 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","ɔ","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_185 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","ɔ","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_186 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","ɔ","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_187 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","ɔ","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_188 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","ɔ","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_189 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","ɔ","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_190 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","ɔ","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_191 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","ɔ","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_192 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","ɔ","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_193 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","ɔ","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_194 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","ɔ","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_195 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","ɔ","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_182 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_183
  · exact partOR38_1_184
  · exact partOR38_1_185
  · exact partOR38_1_186
  · exact partOR38_1_187
  · exact partOR38_1_188
  · exact partOR38_1_189
  · exact partOR38_1_190
  · exact partOR38_1_191
  · exact partOR38_1_192
  · exact partOR38_1_193
  · exact partOR38_1_194
  · exact partOR38_1_195
theorem partOR38_1_197 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","o","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_198 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","o","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_199 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","o","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_200 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","o","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_201 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","o","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_202 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","o","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_203 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","o","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_204 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","o","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_205 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","o","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_206 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","o","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_207 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","o","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_208 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","o","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_209 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","o","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_196 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_197
  · exact partOR38_1_198
  · exact partOR38_1_199
  · exact partOR38_1_200
  · exact partOR38_1_201
  · exact partOR38_1_202
  · exact partOR38_1_203
  · exact partOR38_1_204
  · exact partOR38_1_205
  · exact partOR38_1_206
  · exact partOR38_1_207
  · exact partOR38_1_208
  · exact partOR38_1_209
theorem partOR38_1_211 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","ʊ","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_212 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","ʊ","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_213 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","ʊ","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_214 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","ʊ","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_215 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","ʊ","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_216 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","ʊ","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_217 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","ʊ","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_218 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","ʊ","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_219 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","ʊ","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_220 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","ʊ","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_221 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","ʊ","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_222 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","ʊ","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_223 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","ʊ","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_210 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_211
  · exact partOR38_1_212
  · exact partOR38_1_213
  · exact partOR38_1_214
  · exact partOR38_1_215
  · exact partOR38_1_216
  · exact partOR38_1_217
  · exact partOR38_1_218
  · exact partOR38_1_219
  · exact partOR38_1_220
  · exact partOR38_1_221
  · exact partOR38_1_222
  · exact partOR38_1_223
theorem partOR38_1_225 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","u","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_226 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","u","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_227 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","u","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_228 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","u","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_229 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","u","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_230 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","u","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_231 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","u","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_232 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","u","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_233 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","u","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_234 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","u","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_235 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","u","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_236 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","u","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_237 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","u","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_224 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_225
  · exact partOR38_1_226
  · exact partOR38_1_227
  · exact partOR38_1_228
  · exact partOR38_1_229
  · exact partOR38_1_230
  · exact partOR38_1_231
  · exact partOR38_1_232
  · exact partOR38_1_233
  · exact partOR38_1_234
  · exact partOR38_1_235
  · exact partOR38_1_236
  · exact partOR38_1_237
theorem partOR38_1_239 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","j","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_240 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","j","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_241 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","j","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_242 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","j","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_243 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","j","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_244 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","j","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
end ProductiveSubjectGua
