import PhonologicalOpacity.Attenuation.Productive.Baseline.CertificateParts.G37c_7_090
namespace ProductiveGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partG37c_7_7285 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɜ","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7286 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɜ","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7289 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɜ","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7290 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɜ","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7291 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɜ","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7292 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɜ","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7293 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɜ","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7294 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɜ","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7295 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɜ","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7296 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɜ","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7297 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɜ","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7298 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɜ","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7299 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɜ","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7300 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɜ","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7301 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɜ","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7288 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɜ","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_7289
  · exact partG37c_7_7290
  · exact partG37c_7_7291
  · exact partG37c_7_7292
  · exact partG37c_7_7293
  · exact partG37c_7_7294
  · exact partG37c_7_7295
  · exact partG37c_7_7296
  · exact partG37c_7_7297
  · exact partG37c_7_7298
  · exact partG37c_7_7299
  · exact partG37c_7_7300
  · exact partG37c_7_7301
theorem partG37c_7_7287 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɜ","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_7288
theorem partG37c_7_7302 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɜ","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7303 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɜ","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7304 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɜ","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7305 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɜ","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7306 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɜ","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7307 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɜ","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7280 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_7281
  · exact partG37c_7_7282
  · exact partG37c_7_7283
  · exact partG37c_7_7284
  · exact partG37c_7_7285
  · exact partG37c_7_7286
  · exact partG37c_7_7287
  · exact partG37c_7_7302
  · exact partG37c_7_7303
  · exact partG37c_7_7304
  · exact partG37c_7_7305
  · exact partG37c_7_7306
  · exact partG37c_7_7307
theorem partG37c_7_7311 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɛ","∅","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7312 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɛ","∅","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7313 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɛ","∅","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7314 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɛ","∅","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7315 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɛ","∅","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7316 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɛ","∅","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7317 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɛ","∅","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7318 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɛ","∅","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7319 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɛ","∅","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7320 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɛ","∅","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7321 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɛ","∅","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7322 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɛ","∅","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7323 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɛ","∅","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7310 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɛ","∅","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_7311
  · exact partG37c_7_7312
  · exact partG37c_7_7313
  · exact partG37c_7_7314
  · exact partG37c_7_7315
  · exact partG37c_7_7316
  · exact partG37c_7_7317
  · exact partG37c_7_7318
  · exact partG37c_7_7319
  · exact partG37c_7_7320
  · exact partG37c_7_7321
  · exact partG37c_7_7322
  · exact partG37c_7_7323
theorem partG37c_7_7309 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɛ","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_7310
theorem partG37c_7_7324 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɛ","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7325 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɛ","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7326 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɛ","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7327 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɛ","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7328 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɛ","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7331 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɛ","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7332 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɛ","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7333 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɛ","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7334 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɛ","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7335 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɛ","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7336 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɛ","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7337 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɛ","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7338 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɛ","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7339 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɛ","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7340 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɛ","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7341 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɛ","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7342 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɛ","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7343 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɛ","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7330 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɛ","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_7331
  · exact partG37c_7_7332
  · exact partG37c_7_7333
  · exact partG37c_7_7334
  · exact partG37c_7_7335
  · exact partG37c_7_7336
  · exact partG37c_7_7337
  · exact partG37c_7_7338
  · exact partG37c_7_7339
  · exact partG37c_7_7340
  · exact partG37c_7_7341
  · exact partG37c_7_7342
  · exact partG37c_7_7343
theorem partG37c_7_7329 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɛ","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_7330
theorem partG37c_7_7344 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɛ","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7345 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɛ","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7346 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɛ","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7347 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɛ","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7350 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɛ","j","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7351 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɛ","j","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7352 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɛ","j","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7353 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɛ","j","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7354 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɛ","j","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7355 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɛ","j","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7356 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɛ","j","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7357 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɛ","j","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7358 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɛ","j","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7359 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɛ","j","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7360 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɛ","j","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7361 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɛ","j","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7362 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɛ","j","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7349 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɛ","j","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_7350
  · exact partG37c_7_7351
  · exact partG37c_7_7352
  · exact partG37c_7_7353
  · exact partG37c_7_7354
  · exact partG37c_7_7355
  · exact partG37c_7_7356
  · exact partG37c_7_7357
  · exact partG37c_7_7358
  · exact partG37c_7_7359
  · exact partG37c_7_7360
  · exact partG37c_7_7361
  · exact partG37c_7_7362
theorem partG37c_7_7348 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɛ","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_7349
theorem partG37c_7_7363 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɛ","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7308 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_7309
  · exact partG37c_7_7324
  · exact partG37c_7_7325
  · exact partG37c_7_7326
  · exact partG37c_7_7327
  · exact partG37c_7_7328
  · exact partG37c_7_7329
  · exact partG37c_7_7344
  · exact partG37c_7_7345
  · exact partG37c_7_7346
  · exact partG37c_7_7347
  · exact partG37c_7_7348
  · exact partG37c_7_7363
end ProductiveGua
