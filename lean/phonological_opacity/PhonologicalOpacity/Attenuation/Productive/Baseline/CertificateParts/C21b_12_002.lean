import PhonologicalOpacity.Attenuation.Productive.Baseline.CertificateParts.C21b_12_001
namespace ProductiveGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partC21b_12_163 : check uC21b (3) (-4) outC21b ["w","o","s","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_164 : check uC21b (3) (-4) outC21b ["w","o","s","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_165 : check uC21b (3) (-4) outC21b ["w","o","s","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_166 : check uC21b (3) (-4) outC21b ["w","o","s","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_167 : check uC21b (3) (-4) outC21b ["w","o","s","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_168 : check uC21b (3) (-4) outC21b ["w","o","s","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_169 : check uC21b (3) (-4) outC21b ["w","o","s","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_170 : check uC21b (3) (-4) outC21b ["w","o","s","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_171 : check uC21b (3) (-4) outC21b ["w","o","s","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_172 : check uC21b (3) (-4) outC21b ["w","o","s","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_173 : check uC21b (3) (-4) outC21b ["w","o","s","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_160 : check uC21b (3) (-4) outC21b ["w","o","s"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partC21b_12_161
  · exact partC21b_12_162
  · exact partC21b_12_163
  · exact partC21b_12_164
  · exact partC21b_12_165
  · exact partC21b_12_166
  · exact partC21b_12_167
  · exact partC21b_12_168
  · exact partC21b_12_169
  · exact partC21b_12_170
  · exact partC21b_12_171
  · exact partC21b_12_172
  · exact partC21b_12_173
theorem partC21b_12_159 : check uC21b (3) (-4) outC21b ["w","o"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="s" := by simpa using hx
  subst x
  exact partC21b_12_160
theorem partC21b_12_176 : check uC21b (3) (-4) outC21b ["w","ʊ","s","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_178 : check uC21b (3) (-4) outC21b ["w","ʊ","s","a","∅"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_179 : check uC21b (3) (-4) outC21b ["w","ʊ","s","a","a"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_180 : check uC21b (3) (-4) outC21b ["w","ʊ","s","a","ɜ"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_181 : check uC21b (3) (-4) outC21b ["w","ʊ","s","a","ɛ"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_182 : check uC21b (3) (-4) outC21b ["w","ʊ","s","a","e"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_183 : check uC21b (3) (-4) outC21b ["w","ʊ","s","a","ɪ"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_184 : check uC21b (3) (-4) outC21b ["w","ʊ","s","a","i"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_185 : check uC21b (3) (-4) outC21b ["w","ʊ","s","a","ɔ"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_186 : check uC21b (3) (-4) outC21b ["w","ʊ","s","a","o"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_187 : check uC21b (3) (-4) outC21b ["w","ʊ","s","a","ʊ"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_188 : check uC21b (3) (-4) outC21b ["w","ʊ","s","a","u"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_189 : check uC21b (3) (-4) outC21b ["w","ʊ","s","a","j"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_190 : check uC21b (3) (-4) outC21b ["w","ʊ","s","a","w"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_177 : check uC21b (3) (-4) outC21b ["w","ʊ","s","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partC21b_12_178
  · exact partC21b_12_179
  · exact partC21b_12_180
  · exact partC21b_12_181
  · exact partC21b_12_182
  · exact partC21b_12_183
  · exact partC21b_12_184
  · exact partC21b_12_185
  · exact partC21b_12_186
  · exact partC21b_12_187
  · exact partC21b_12_188
  · exact partC21b_12_189
  · exact partC21b_12_190
theorem partC21b_12_191 : check uC21b (3) (-4) outC21b ["w","ʊ","s","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_193 : check uC21b (3) (-4) outC21b ["w","ʊ","s","ɛ","∅"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_194 : check uC21b (3) (-4) outC21b ["w","ʊ","s","ɛ","a"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_195 : check uC21b (3) (-4) outC21b ["w","ʊ","s","ɛ","ɜ"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_196 : check uC21b (3) (-4) outC21b ["w","ʊ","s","ɛ","ɛ"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_197 : check uC21b (3) (-4) outC21b ["w","ʊ","s","ɛ","e"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_198 : check uC21b (3) (-4) outC21b ["w","ʊ","s","ɛ","ɪ"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_199 : check uC21b (3) (-4) outC21b ["w","ʊ","s","ɛ","i"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_200 : check uC21b (3) (-4) outC21b ["w","ʊ","s","ɛ","ɔ"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_201 : check uC21b (3) (-4) outC21b ["w","ʊ","s","ɛ","o"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_202 : check uC21b (3) (-4) outC21b ["w","ʊ","s","ɛ","ʊ"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_203 : check uC21b (3) (-4) outC21b ["w","ʊ","s","ɛ","u"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_204 : check uC21b (3) (-4) outC21b ["w","ʊ","s","ɛ","j"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_205 : check uC21b (3) (-4) outC21b ["w","ʊ","s","ɛ","w"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_192 : check uC21b (3) (-4) outC21b ["w","ʊ","s","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partC21b_12_193
  · exact partC21b_12_194
  · exact partC21b_12_195
  · exact partC21b_12_196
  · exact partC21b_12_197
  · exact partC21b_12_198
  · exact partC21b_12_199
  · exact partC21b_12_200
  · exact partC21b_12_201
  · exact partC21b_12_202
  · exact partC21b_12_203
  · exact partC21b_12_204
  · exact partC21b_12_205
theorem partC21b_12_206 : check uC21b (3) (-4) outC21b ["w","ʊ","s","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_208 : check uC21b (3) (-4) outC21b ["w","ʊ","s","ɪ","∅"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_209 : check uC21b (3) (-4) outC21b ["w","ʊ","s","ɪ","a"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_210 : check uC21b (3) (-4) outC21b ["w","ʊ","s","ɪ","ɜ"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_211 : check uC21b (3) (-4) outC21b ["w","ʊ","s","ɪ","ɛ"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_212 : check uC21b (3) (-4) outC21b ["w","ʊ","s","ɪ","e"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_213 : check uC21b (3) (-4) outC21b ["w","ʊ","s","ɪ","ɪ"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_214 : check uC21b (3) (-4) outC21b ["w","ʊ","s","ɪ","i"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_215 : check uC21b (3) (-4) outC21b ["w","ʊ","s","ɪ","ɔ"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_216 : check uC21b (3) (-4) outC21b ["w","ʊ","s","ɪ","o"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_217 : check uC21b (3) (-4) outC21b ["w","ʊ","s","ɪ","ʊ"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_218 : check uC21b (3) (-4) outC21b ["w","ʊ","s","ɪ","u"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_219 : check uC21b (3) (-4) outC21b ["w","ʊ","s","ɪ","j"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_220 : check uC21b (3) (-4) outC21b ["w","ʊ","s","ɪ","w"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_207 : check uC21b (3) (-4) outC21b ["w","ʊ","s","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partC21b_12_208
  · exact partC21b_12_209
  · exact partC21b_12_210
  · exact partC21b_12_211
  · exact partC21b_12_212
  · exact partC21b_12_213
  · exact partC21b_12_214
  · exact partC21b_12_215
  · exact partC21b_12_216
  · exact partC21b_12_217
  · exact partC21b_12_218
  · exact partC21b_12_219
  · exact partC21b_12_220
theorem partC21b_12_221 : check uC21b (3) (-4) outC21b ["w","ʊ","s","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_223 : check uC21b (3) (-4) outC21b ["w","ʊ","s","ɔ","∅"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_224 : check uC21b (3) (-4) outC21b ["w","ʊ","s","ɔ","a"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_225 : check uC21b (3) (-4) outC21b ["w","ʊ","s","ɔ","ɜ"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_226 : check uC21b (3) (-4) outC21b ["w","ʊ","s","ɔ","ɛ"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_227 : check uC21b (3) (-4) outC21b ["w","ʊ","s","ɔ","e"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_228 : check uC21b (3) (-4) outC21b ["w","ʊ","s","ɔ","ɪ"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_229 : check uC21b (3) (-4) outC21b ["w","ʊ","s","ɔ","i"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_230 : check uC21b (3) (-4) outC21b ["w","ʊ","s","ɔ","ɔ"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_231 : check uC21b (3) (-4) outC21b ["w","ʊ","s","ɔ","o"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_232 : check uC21b (3) (-4) outC21b ["w","ʊ","s","ɔ","ʊ"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_233 : check uC21b (3) (-4) outC21b ["w","ʊ","s","ɔ","u"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_234 : check uC21b (3) (-4) outC21b ["w","ʊ","s","ɔ","j"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_235 : check uC21b (3) (-4) outC21b ["w","ʊ","s","ɔ","w"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_222 : check uC21b (3) (-4) outC21b ["w","ʊ","s","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partC21b_12_223
  · exact partC21b_12_224
  · exact partC21b_12_225
  · exact partC21b_12_226
  · exact partC21b_12_227
  · exact partC21b_12_228
  · exact partC21b_12_229
  · exact partC21b_12_230
  · exact partC21b_12_231
  · exact partC21b_12_232
  · exact partC21b_12_233
  · exact partC21b_12_234
  · exact partC21b_12_235
theorem partC21b_12_236 : check uC21b (3) (-4) outC21b ["w","ʊ","s","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_238 : check uC21b (3) (-4) outC21b ["w","ʊ","s","ʊ","∅"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_239 : check uC21b (3) (-4) outC21b ["w","ʊ","s","ʊ","a"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_240 : check uC21b (3) (-4) outC21b ["w","ʊ","s","ʊ","ɜ"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_241 : check uC21b (3) (-4) outC21b ["w","ʊ","s","ʊ","ɛ"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_242 : check uC21b (3) (-4) outC21b ["w","ʊ","s","ʊ","e"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_243 : check uC21b (3) (-4) outC21b ["w","ʊ","s","ʊ","ɪ"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
end ProductiveGua
