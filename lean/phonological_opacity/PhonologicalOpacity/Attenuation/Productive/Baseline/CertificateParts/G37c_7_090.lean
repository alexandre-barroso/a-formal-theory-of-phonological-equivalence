import PhonologicalOpacity.Attenuation.Productive.Baseline.CertificateParts.G37c_7_089
namespace ProductiveGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partG37c_7_7207 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","∅","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7208 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","∅","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7209 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","∅","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7210 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","∅","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7211 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","∅","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7212 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","∅","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7213 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","∅","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7214 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","∅","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7215 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","∅","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7216 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","∅","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7217 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","∅","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7204 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","∅","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_7205
  · exact partG37c_7_7206
  · exact partG37c_7_7207
  · exact partG37c_7_7208
  · exact partG37c_7_7209
  · exact partG37c_7_7210
  · exact partG37c_7_7211
  · exact partG37c_7_7212
  · exact partG37c_7_7213
  · exact partG37c_7_7214
  · exact partG37c_7_7215
  · exact partG37c_7_7216
  · exact partG37c_7_7217
theorem partG37c_7_7203 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","∅","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_7204
theorem partG37c_7_7218 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","∅","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7219 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","∅","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7220 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","∅","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7221 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","∅","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7222 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","∅","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7223 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","∅","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7196 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_7197
  · exact partG37c_7_7198
  · exact partG37c_7_7199
  · exact partG37c_7_7200
  · exact partG37c_7_7201
  · exact partG37c_7_7202
  · exact partG37c_7_7203
  · exact partG37c_7_7218
  · exact partG37c_7_7219
  · exact partG37c_7_7220
  · exact partG37c_7_7221
  · exact partG37c_7_7222
  · exact partG37c_7_7223
theorem partG37c_7_7227 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","a","∅","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7228 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","a","∅","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7229 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","a","∅","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7230 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","a","∅","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7231 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","a","∅","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7232 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","a","∅","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7233 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","a","∅","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7234 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","a","∅","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7235 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","a","∅","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7236 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","a","∅","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7237 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","a","∅","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7238 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","a","∅","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7239 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","a","∅","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7226 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","a","∅","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_7227
  · exact partG37c_7_7228
  · exact partG37c_7_7229
  · exact partG37c_7_7230
  · exact partG37c_7_7231
  · exact partG37c_7_7232
  · exact partG37c_7_7233
  · exact partG37c_7_7234
  · exact partG37c_7_7235
  · exact partG37c_7_7236
  · exact partG37c_7_7237
  · exact partG37c_7_7238
  · exact partG37c_7_7239
theorem partG37c_7_7225 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","a","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_7226
theorem partG37c_7_7240 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","a","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7241 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","a","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7242 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","a","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7243 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","a","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7244 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","a","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7247 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","a","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7248 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","a","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7249 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","a","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7250 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","a","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7251 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","a","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7252 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","a","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7253 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","a","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7254 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","a","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7255 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","a","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7256 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","a","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7257 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","a","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7258 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","a","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7259 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","a","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7246 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","a","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_7247
  · exact partG37c_7_7248
  · exact partG37c_7_7249
  · exact partG37c_7_7250
  · exact partG37c_7_7251
  · exact partG37c_7_7252
  · exact partG37c_7_7253
  · exact partG37c_7_7254
  · exact partG37c_7_7255
  · exact partG37c_7_7256
  · exact partG37c_7_7257
  · exact partG37c_7_7258
  · exact partG37c_7_7259
theorem partG37c_7_7245 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","a","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_7246
theorem partG37c_7_7260 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","a","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7261 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","a","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7262 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","a","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7263 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","a","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7266 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","a","j","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7267 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","a","j","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7268 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","a","j","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7269 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","a","j","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7270 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","a","j","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7271 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","a","j","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7272 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","a","j","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7273 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","a","j","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7274 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","a","j","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7275 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","a","j","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7276 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","a","j","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7277 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","a","j","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7278 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","a","j","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7265 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","a","j","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_7266
  · exact partG37c_7_7267
  · exact partG37c_7_7268
  · exact partG37c_7_7269
  · exact partG37c_7_7270
  · exact partG37c_7_7271
  · exact partG37c_7_7272
  · exact partG37c_7_7273
  · exact partG37c_7_7274
  · exact partG37c_7_7275
  · exact partG37c_7_7276
  · exact partG37c_7_7277
  · exact partG37c_7_7278
theorem partG37c_7_7264 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","a","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_7265
theorem partG37c_7_7279 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","a","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7224 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_7225
  · exact partG37c_7_7240
  · exact partG37c_7_7241
  · exact partG37c_7_7242
  · exact partG37c_7_7243
  · exact partG37c_7_7244
  · exact partG37c_7_7245
  · exact partG37c_7_7260
  · exact partG37c_7_7261
  · exact partG37c_7_7262
  · exact partG37c_7_7263
  · exact partG37c_7_7264
  · exact partG37c_7_7279
theorem partG37c_7_7281 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɜ","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7282 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɜ","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7283 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɜ","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7284 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɜ","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
end ProductiveGua
