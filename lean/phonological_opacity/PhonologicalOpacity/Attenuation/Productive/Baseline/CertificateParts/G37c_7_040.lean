import PhonologicalOpacity.Attenuation.Productive.Baseline.CertificateParts.G37c_7_039
namespace ProductiveGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partG37c_7_3205 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɛ","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3150 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_3151
  · exact partG37c_7_3166
  · exact partG37c_7_3167
  · exact partG37c_7_3168
  · exact partG37c_7_3169
  · exact partG37c_7_3170
  · exact partG37c_7_3171
  · exact partG37c_7_3186
  · exact partG37c_7_3187
  · exact partG37c_7_3188
  · exact partG37c_7_3189
  · exact partG37c_7_3190
  · exact partG37c_7_3205
theorem partG37c_7_3209 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","e","∅","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3210 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","e","∅","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3211 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","e","∅","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3212 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","e","∅","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3213 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","e","∅","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3214 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","e","∅","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3215 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","e","∅","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3216 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","e","∅","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3217 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","e","∅","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3218 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","e","∅","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3219 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","e","∅","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3220 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","e","∅","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3221 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","e","∅","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3208 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","e","∅","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_3209
  · exact partG37c_7_3210
  · exact partG37c_7_3211
  · exact partG37c_7_3212
  · exact partG37c_7_3213
  · exact partG37c_7_3214
  · exact partG37c_7_3215
  · exact partG37c_7_3216
  · exact partG37c_7_3217
  · exact partG37c_7_3218
  · exact partG37c_7_3219
  · exact partG37c_7_3220
  · exact partG37c_7_3221
theorem partG37c_7_3207 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","e","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_3208
theorem partG37c_7_3222 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","e","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3223 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","e","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3224 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","e","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3225 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","e","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3226 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","e","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3229 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","e","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3230 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","e","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3231 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","e","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3232 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","e","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3233 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","e","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3234 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","e","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3235 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","e","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3236 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","e","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3237 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","e","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3238 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","e","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3239 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","e","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3240 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","e","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3241 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","e","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3228 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","e","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_3229
  · exact partG37c_7_3230
  · exact partG37c_7_3231
  · exact partG37c_7_3232
  · exact partG37c_7_3233
  · exact partG37c_7_3234
  · exact partG37c_7_3235
  · exact partG37c_7_3236
  · exact partG37c_7_3237
  · exact partG37c_7_3238
  · exact partG37c_7_3239
  · exact partG37c_7_3240
  · exact partG37c_7_3241
theorem partG37c_7_3227 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","e","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_3228
theorem partG37c_7_3242 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","e","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3243 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","e","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3244 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","e","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3245 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","e","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3248 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","e","j","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3249 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","e","j","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3250 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","e","j","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3251 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","e","j","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3252 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","e","j","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3253 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","e","j","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3254 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","e","j","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3255 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","e","j","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3256 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","e","j","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3257 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","e","j","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3258 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","e","j","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3259 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","e","j","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3260 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","e","j","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3247 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","e","j","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_3248
  · exact partG37c_7_3249
  · exact partG37c_7_3250
  · exact partG37c_7_3251
  · exact partG37c_7_3252
  · exact partG37c_7_3253
  · exact partG37c_7_3254
  · exact partG37c_7_3255
  · exact partG37c_7_3256
  · exact partG37c_7_3257
  · exact partG37c_7_3258
  · exact partG37c_7_3259
  · exact partG37c_7_3260
theorem partG37c_7_3246 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","e","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_3247
theorem partG37c_7_3261 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","e","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3206 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_3207
  · exact partG37c_7_3222
  · exact partG37c_7_3223
  · exact partG37c_7_3224
  · exact partG37c_7_3225
  · exact partG37c_7_3226
  · exact partG37c_7_3227
  · exact partG37c_7_3242
  · exact partG37c_7_3243
  · exact partG37c_7_3244
  · exact partG37c_7_3245
  · exact partG37c_7_3246
  · exact partG37c_7_3261
theorem partG37c_7_3265 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɪ","∅","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3266 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɪ","∅","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3267 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɪ","∅","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3268 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɪ","∅","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3269 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɪ","∅","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3270 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɪ","∅","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3271 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɪ","∅","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3272 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɪ","∅","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3273 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɪ","∅","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3274 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɪ","∅","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3275 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɪ","∅","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3276 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɪ","∅","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3277 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɪ","∅","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3264 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɪ","∅","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_3265
  · exact partG37c_7_3266
  · exact partG37c_7_3267
  · exact partG37c_7_3268
  · exact partG37c_7_3269
  · exact partG37c_7_3270
  · exact partG37c_7_3271
  · exact partG37c_7_3272
  · exact partG37c_7_3273
  · exact partG37c_7_3274
  · exact partG37c_7_3275
  · exact partG37c_7_3276
  · exact partG37c_7_3277
theorem partG37c_7_3263 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɪ","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_3264
theorem partG37c_7_3278 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɪ","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3279 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɪ","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3280 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɪ","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3281 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɪ","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3282 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɪ","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3285 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɪ","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3286 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɪ","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
end ProductiveGua
