import PhonologicalOpacity.Attenuation.Productive.Baseline.CertificateParts.G37c_7_064
namespace ProductiveGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partG37c_7_5205 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","i","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5206 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","i","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5209 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","i","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5210 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","i","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5211 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","i","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5212 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","i","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5213 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","i","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5214 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","i","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5215 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","i","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5216 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","i","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5217 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","i","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5218 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","i","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5219 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","i","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5220 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","i","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5221 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","i","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5208 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","i","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_5209
  · exact partG37c_7_5210
  · exact partG37c_7_5211
  · exact partG37c_7_5212
  · exact partG37c_7_5213
  · exact partG37c_7_5214
  · exact partG37c_7_5215
  · exact partG37c_7_5216
  · exact partG37c_7_5217
  · exact partG37c_7_5218
  · exact partG37c_7_5219
  · exact partG37c_7_5220
  · exact partG37c_7_5221
theorem partG37c_7_5207 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","i","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_5208
theorem partG37c_7_5222 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","i","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5223 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","i","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5224 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","i","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5225 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","i","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5226 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","i","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5227 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","i","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5200 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_5201
  · exact partG37c_7_5202
  · exact partG37c_7_5203
  · exact partG37c_7_5204
  · exact partG37c_7_5205
  · exact partG37c_7_5206
  · exact partG37c_7_5207
  · exact partG37c_7_5222
  · exact partG37c_7_5223
  · exact partG37c_7_5224
  · exact partG37c_7_5225
  · exact partG37c_7_5226
  · exact partG37c_7_5227
theorem partG37c_7_5231 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɔ","∅","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5232 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɔ","∅","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5233 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɔ","∅","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5234 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɔ","∅","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5235 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɔ","∅","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5236 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɔ","∅","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5237 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɔ","∅","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5238 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɔ","∅","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5239 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɔ","∅","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5240 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɔ","∅","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5241 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɔ","∅","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5242 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɔ","∅","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5243 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɔ","∅","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5230 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɔ","∅","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_5231
  · exact partG37c_7_5232
  · exact partG37c_7_5233
  · exact partG37c_7_5234
  · exact partG37c_7_5235
  · exact partG37c_7_5236
  · exact partG37c_7_5237
  · exact partG37c_7_5238
  · exact partG37c_7_5239
  · exact partG37c_7_5240
  · exact partG37c_7_5241
  · exact partG37c_7_5242
  · exact partG37c_7_5243
theorem partG37c_7_5229 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɔ","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_5230
theorem partG37c_7_5244 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɔ","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5245 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɔ","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5246 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɔ","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5247 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɔ","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5248 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɔ","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5251 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɔ","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5252 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɔ","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5253 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɔ","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5254 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɔ","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5255 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɔ","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5256 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɔ","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5257 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɔ","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5258 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɔ","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5259 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɔ","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5260 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɔ","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5261 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɔ","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5262 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɔ","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5263 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɔ","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5250 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɔ","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_5251
  · exact partG37c_7_5252
  · exact partG37c_7_5253
  · exact partG37c_7_5254
  · exact partG37c_7_5255
  · exact partG37c_7_5256
  · exact partG37c_7_5257
  · exact partG37c_7_5258
  · exact partG37c_7_5259
  · exact partG37c_7_5260
  · exact partG37c_7_5261
  · exact partG37c_7_5262
  · exact partG37c_7_5263
theorem partG37c_7_5249 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɔ","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_5250
theorem partG37c_7_5264 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɔ","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5265 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɔ","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5266 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɔ","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5267 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɔ","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5270 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɔ","j","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5271 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɔ","j","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5272 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɔ","j","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5273 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɔ","j","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5274 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɔ","j","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5275 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɔ","j","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5276 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɔ","j","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5277 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɔ","j","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5278 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɔ","j","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5279 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɔ","j","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5280 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɔ","j","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5281 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɔ","j","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5282 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɔ","j","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5269 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɔ","j","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_5270
  · exact partG37c_7_5271
  · exact partG37c_7_5272
  · exact partG37c_7_5273
  · exact partG37c_7_5274
  · exact partG37c_7_5275
  · exact partG37c_7_5276
  · exact partG37c_7_5277
  · exact partG37c_7_5278
  · exact partG37c_7_5279
  · exact partG37c_7_5280
  · exact partG37c_7_5281
  · exact partG37c_7_5282
theorem partG37c_7_5268 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɔ","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_5269
theorem partG37c_7_5283 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɔ","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5228 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_5229
  · exact partG37c_7_5244
  · exact partG37c_7_5245
  · exact partG37c_7_5246
  · exact partG37c_7_5247
  · exact partG37c_7_5248
  · exact partG37c_7_5249
  · exact partG37c_7_5264
  · exact partG37c_7_5265
  · exact partG37c_7_5266
  · exact partG37c_7_5267
  · exact partG37c_7_5268
  · exact partG37c_7_5283
end ProductiveGua
