import PhonologicalOpacity.Attenuation.Productive.Baseline.FixedCertificateParts.FixedCertificateG34a_1_001
namespace ProductiveGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem fixedPartG34a_1_165 : fixedCheck uG34a (24) goalG34a ["a","h","e","t","i","ʊ"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_166 : fixedCheck uG34a (24) goalG34a ["a","h","e","t","i","u"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_167 : fixedCheck uG34a (24) goalG34a ["a","h","e","t","i","j"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_168 : fixedCheck uG34a (24) goalG34a ["a","h","e","t","i","w"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_140 : fixedCheck uG34a (24) goalG34a ["a","h","e","t","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply fixedCheck_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixedPartG34a_1_141
  · exact fixedPartG34a_1_142
  · exact fixedPartG34a_1_143
  · exact fixedPartG34a_1_144
  · exact fixedPartG34a_1_145
  · exact fixedPartG34a_1_146
  · exact fixedPartG34a_1_147
  · exact fixedPartG34a_1_148
  · exact fixedPartG34a_1_164
  · exact fixedPartG34a_1_165
  · exact fixedPartG34a_1_166
  · exact fixedPartG34a_1_167
  · exact fixedPartG34a_1_168
theorem fixedPartG34a_1_169 : fixedCheck uG34a (24) goalG34a ["a","h","e","t","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_171 : fixedCheck uG34a (24) goalG34a ["a","h","e","t","o","∅"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_172 : fixedCheck uG34a (24) goalG34a ["a","h","e","t","o","a"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_173 : fixedCheck uG34a (24) goalG34a ["a","h","e","t","o","ɜ"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_174 : fixedCheck uG34a (24) goalG34a ["a","h","e","t","o","ɛ"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_175 : fixedCheck uG34a (24) goalG34a ["a","h","e","t","o","e"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_176 : fixedCheck uG34a (24) goalG34a ["a","h","e","t","o","ɪ"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_177 : fixedCheck uG34a (24) goalG34a ["a","h","e","t","o","i"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_181 : fixedCheck uG34a (24) goalG34a ["a","h","e","t","o","ɔ","k","p","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_182 : fixedCheck uG34a (24) goalG34a ["a","h","e","t","o","ɔ","k","p","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_183 : fixedCheck uG34a (24) goalG34a ["a","h","e","t","o","ɔ","k","p","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_184 : fixedCheck uG34a (24) goalG34a ["a","h","e","t","o","ɔ","k","p","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_185 : fixedCheck uG34a (24) goalG34a ["a","h","e","t","o","ɔ","k","p","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_186 : fixedCheck uG34a (24) goalG34a ["a","h","e","t","o","ɔ","k","p","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_187 : fixedCheck uG34a (24) goalG34a ["a","h","e","t","o","ɔ","k","p","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_188 : fixedCheck uG34a (24) goalG34a ["a","h","e","t","o","ɔ","k","p","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_189 : fixedCheck uG34a (24) goalG34a ["a","h","e","t","o","ɔ","k","p","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_190 : fixedCheck uG34a (24) goalG34a ["a","h","e","t","o","ɔ","k","p","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_191 : fixedCheck uG34a (24) goalG34a ["a","h","e","t","o","ɔ","k","p","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_192 : fixedCheck uG34a (24) goalG34a ["a","h","e","t","o","ɔ","k","p","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_193 : fixedCheck uG34a (24) goalG34a ["a","h","e","t","o","ɔ","k","p","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_180 : fixedCheck uG34a (24) goalG34a ["a","h","e","t","o","ɔ","k","p"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply fixedCheck_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixedPartG34a_1_181
  · exact fixedPartG34a_1_182
  · exact fixedPartG34a_1_183
  · exact fixedPartG34a_1_184
  · exact fixedPartG34a_1_185
  · exact fixedPartG34a_1_186
  · exact fixedPartG34a_1_187
  · exact fixedPartG34a_1_188
  · exact fixedPartG34a_1_189
  · exact fixedPartG34a_1_190
  · exact fixedPartG34a_1_191
  · exact fixedPartG34a_1_192
  · exact fixedPartG34a_1_193
theorem fixedPartG34a_1_179 : fixedCheck uG34a (24) goalG34a ["a","h","e","t","o","ɔ","k"] [["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply fixedCheck_of_children
  intro x hx
  have he : x="p" := by simpa using hx
  subst x
  exact fixedPartG34a_1_180
theorem fixedPartG34a_1_178 : fixedCheck uG34a (24) goalG34a ["a","h","e","t","o","ɔ"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply fixedCheck_of_children
  intro x hx
  have he : x="k" := by simpa using hx
  subst x
  exact fixedPartG34a_1_179
theorem fixedPartG34a_1_194 : fixedCheck uG34a (24) goalG34a ["a","h","e","t","o","o"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_195 : fixedCheck uG34a (24) goalG34a ["a","h","e","t","o","ʊ"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_196 : fixedCheck uG34a (24) goalG34a ["a","h","e","t","o","u"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_197 : fixedCheck uG34a (24) goalG34a ["a","h","e","t","o","j"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_198 : fixedCheck uG34a (24) goalG34a ["a","h","e","t","o","w"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_170 : fixedCheck uG34a (24) goalG34a ["a","h","e","t","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply fixedCheck_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixedPartG34a_1_171
  · exact fixedPartG34a_1_172
  · exact fixedPartG34a_1_173
  · exact fixedPartG34a_1_174
  · exact fixedPartG34a_1_175
  · exact fixedPartG34a_1_176
  · exact fixedPartG34a_1_177
  · exact fixedPartG34a_1_178
  · exact fixedPartG34a_1_194
  · exact fixedPartG34a_1_195
  · exact fixedPartG34a_1_196
  · exact fixedPartG34a_1_197
  · exact fixedPartG34a_1_198
theorem fixedPartG34a_1_199 : fixedCheck uG34a (24) goalG34a ["a","h","e","t","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_201 : fixedCheck uG34a (24) goalG34a ["a","h","e","t","u","∅"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_202 : fixedCheck uG34a (24) goalG34a ["a","h","e","t","u","a"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_203 : fixedCheck uG34a (24) goalG34a ["a","h","e","t","u","ɜ"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_204 : fixedCheck uG34a (24) goalG34a ["a","h","e","t","u","ɛ"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_205 : fixedCheck uG34a (24) goalG34a ["a","h","e","t","u","e"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_206 : fixedCheck uG34a (24) goalG34a ["a","h","e","t","u","ɪ"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_207 : fixedCheck uG34a (24) goalG34a ["a","h","e","t","u","i"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_211 : fixedCheck uG34a (24) goalG34a ["a","h","e","t","u","ɔ","k","p","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_212 : fixedCheck uG34a (24) goalG34a ["a","h","e","t","u","ɔ","k","p","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_213 : fixedCheck uG34a (24) goalG34a ["a","h","e","t","u","ɔ","k","p","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_214 : fixedCheck uG34a (24) goalG34a ["a","h","e","t","u","ɔ","k","p","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_215 : fixedCheck uG34a (24) goalG34a ["a","h","e","t","u","ɔ","k","p","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_216 : fixedCheck uG34a (24) goalG34a ["a","h","e","t","u","ɔ","k","p","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_217 : fixedCheck uG34a (24) goalG34a ["a","h","e","t","u","ɔ","k","p","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_218 : fixedCheck uG34a (24) goalG34a ["a","h","e","t","u","ɔ","k","p","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_219 : fixedCheck uG34a (24) goalG34a ["a","h","e","t","u","ɔ","k","p","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_220 : fixedCheck uG34a (24) goalG34a ["a","h","e","t","u","ɔ","k","p","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_221 : fixedCheck uG34a (24) goalG34a ["a","h","e","t","u","ɔ","k","p","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_222 : fixedCheck uG34a (24) goalG34a ["a","h","e","t","u","ɔ","k","p","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_223 : fixedCheck uG34a (24) goalG34a ["a","h","e","t","u","ɔ","k","p","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_210 : fixedCheck uG34a (24) goalG34a ["a","h","e","t","u","ɔ","k","p"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply fixedCheck_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixedPartG34a_1_211
  · exact fixedPartG34a_1_212
  · exact fixedPartG34a_1_213
  · exact fixedPartG34a_1_214
  · exact fixedPartG34a_1_215
  · exact fixedPartG34a_1_216
  · exact fixedPartG34a_1_217
  · exact fixedPartG34a_1_218
  · exact fixedPartG34a_1_219
  · exact fixedPartG34a_1_220
  · exact fixedPartG34a_1_221
  · exact fixedPartG34a_1_222
  · exact fixedPartG34a_1_223
theorem fixedPartG34a_1_209 : fixedCheck uG34a (24) goalG34a ["a","h","e","t","u","ɔ","k"] [["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply fixedCheck_of_children
  intro x hx
  have he : x="p" := by simpa using hx
  subst x
  exact fixedPartG34a_1_210
theorem fixedPartG34a_1_208 : fixedCheck uG34a (24) goalG34a ["a","h","e","t","u","ɔ"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply fixedCheck_of_children
  intro x hx
  have he : x="k" := by simpa using hx
  subst x
  exact fixedPartG34a_1_209
theorem fixedPartG34a_1_224 : fixedCheck uG34a (24) goalG34a ["a","h","e","t","u","o"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_225 : fixedCheck uG34a (24) goalG34a ["a","h","e","t","u","ʊ"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_226 : fixedCheck uG34a (24) goalG34a ["a","h","e","t","u","u"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_227 : fixedCheck uG34a (24) goalG34a ["a","h","e","t","u","j"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_228 : fixedCheck uG34a (24) goalG34a ["a","h","e","t","u","w"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_200 : fixedCheck uG34a (24) goalG34a ["a","h","e","t","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply fixedCheck_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixedPartG34a_1_201
  · exact fixedPartG34a_1_202
  · exact fixedPartG34a_1_203
  · exact fixedPartG34a_1_204
  · exact fixedPartG34a_1_205
  · exact fixedPartG34a_1_206
  · exact fixedPartG34a_1_207
  · exact fixedPartG34a_1_208
  · exact fixedPartG34a_1_224
  · exact fixedPartG34a_1_225
  · exact fixedPartG34a_1_226
  · exact fixedPartG34a_1_227
  · exact fixedPartG34a_1_228
theorem fixedPartG34a_1_229 : fixedCheck uG34a (24) goalG34a ["a","h","e","t","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_230 : fixedCheck uG34a (24) goalG34a ["a","h","e","t","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_49 : fixedCheck uG34a (24) goalG34a ["a","h","e","t"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply fixedCheck_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixedPartG34a_1_50
  · exact fixedPartG34a_1_51
  · exact fixedPartG34a_1_52
  · exact fixedPartG34a_1_81
  · exact fixedPartG34a_1_110
  · exact fixedPartG34a_1_139
  · exact fixedPartG34a_1_140
  · exact fixedPartG34a_1_169
  · exact fixedPartG34a_1_170
  · exact fixedPartG34a_1_199
  · exact fixedPartG34a_1_200
  · exact fixedPartG34a_1_229
  · exact fixedPartG34a_1_230
theorem fixedPartG34a_1_48 : fixedCheck uG34a (24) goalG34a ["a","h","e"] [["t"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply fixedCheck_of_children
  intro x hx
  have he : x="t" := by simpa using hx
  subst x
  exact fixedPartG34a_1_49
theorem fixedPartG34a_1_231 : fixedCheck uG34a (24) goalG34a ["a","h","ɪ"] [["t"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_234 : fixedCheck uG34a (24) goalG34a ["a","h","i","t","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_235 : fixedCheck uG34a (24) goalG34a ["a","h","i","t","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_236 : fixedCheck uG34a (24) goalG34a ["a","h","i","t","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_237 : fixedCheck uG34a (24) goalG34a ["a","h","i","t","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_239 : fixedCheck uG34a (24) goalG34a ["a","h","i","t","e","∅"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_240 : fixedCheck uG34a (24) goalG34a ["a","h","i","t","e","a"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_241 : fixedCheck uG34a (24) goalG34a ["a","h","i","t","e","ɜ"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_242 : fixedCheck uG34a (24) goalG34a ["a","h","i","t","e","ɛ"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_243 : fixedCheck uG34a (24) goalG34a ["a","h","i","t","e","e"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_244 : fixedCheck uG34a (24) goalG34a ["a","h","i","t","e","ɪ"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
end ProductiveGua
