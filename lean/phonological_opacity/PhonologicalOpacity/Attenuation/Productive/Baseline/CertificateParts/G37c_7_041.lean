import PhonologicalOpacity.Attenuation.Productive.Baseline.CertificateParts.G37c_7_040
namespace ProductiveGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partG37c_7_3287 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɪ","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3288 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɪ","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3289 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɪ","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3290 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɪ","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3291 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɪ","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3292 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɪ","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3293 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɪ","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3294 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɪ","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3295 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɪ","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3296 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɪ","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3297 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɪ","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3284 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɪ","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_3285
  · exact partG37c_7_3286
  · exact partG37c_7_3287
  · exact partG37c_7_3288
  · exact partG37c_7_3289
  · exact partG37c_7_3290
  · exact partG37c_7_3291
  · exact partG37c_7_3292
  · exact partG37c_7_3293
  · exact partG37c_7_3294
  · exact partG37c_7_3295
  · exact partG37c_7_3296
  · exact partG37c_7_3297
theorem partG37c_7_3283 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɪ","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_3284
theorem partG37c_7_3298 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɪ","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3299 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɪ","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3300 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɪ","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3301 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɪ","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3304 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɪ","j","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3305 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɪ","j","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3306 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɪ","j","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3307 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɪ","j","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3308 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɪ","j","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3309 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɪ","j","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3310 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɪ","j","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3311 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɪ","j","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3312 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɪ","j","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3313 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɪ","j","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3314 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɪ","j","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3315 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɪ","j","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3316 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɪ","j","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3303 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɪ","j","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_3304
  · exact partG37c_7_3305
  · exact partG37c_7_3306
  · exact partG37c_7_3307
  · exact partG37c_7_3308
  · exact partG37c_7_3309
  · exact partG37c_7_3310
  · exact partG37c_7_3311
  · exact partG37c_7_3312
  · exact partG37c_7_3313
  · exact partG37c_7_3314
  · exact partG37c_7_3315
  · exact partG37c_7_3316
theorem partG37c_7_3302 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɪ","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_3303
theorem partG37c_7_3317 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɪ","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3262 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_3263
  · exact partG37c_7_3278
  · exact partG37c_7_3279
  · exact partG37c_7_3280
  · exact partG37c_7_3281
  · exact partG37c_7_3282
  · exact partG37c_7_3283
  · exact partG37c_7_3298
  · exact partG37c_7_3299
  · exact partG37c_7_3300
  · exact partG37c_7_3301
  · exact partG37c_7_3302
  · exact partG37c_7_3317
theorem partG37c_7_3321 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","i","∅","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3322 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","i","∅","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3323 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","i","∅","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3324 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","i","∅","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3325 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","i","∅","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3326 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","i","∅","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3327 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","i","∅","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3328 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","i","∅","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3329 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","i","∅","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3330 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","i","∅","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3331 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","i","∅","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3332 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","i","∅","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3333 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","i","∅","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3320 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","i","∅","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_3321
  · exact partG37c_7_3322
  · exact partG37c_7_3323
  · exact partG37c_7_3324
  · exact partG37c_7_3325
  · exact partG37c_7_3326
  · exact partG37c_7_3327
  · exact partG37c_7_3328
  · exact partG37c_7_3329
  · exact partG37c_7_3330
  · exact partG37c_7_3331
  · exact partG37c_7_3332
  · exact partG37c_7_3333
theorem partG37c_7_3319 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","i","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_3320
theorem partG37c_7_3334 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","i","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3335 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","i","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3336 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","i","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3337 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","i","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3338 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","i","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3341 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","i","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3342 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","i","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3343 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","i","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3344 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","i","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3345 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","i","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3346 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","i","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3347 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","i","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3348 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","i","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3349 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","i","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3350 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","i","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3351 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","i","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3352 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","i","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3353 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","i","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3340 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","i","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_3341
  · exact partG37c_7_3342
  · exact partG37c_7_3343
  · exact partG37c_7_3344
  · exact partG37c_7_3345
  · exact partG37c_7_3346
  · exact partG37c_7_3347
  · exact partG37c_7_3348
  · exact partG37c_7_3349
  · exact partG37c_7_3350
  · exact partG37c_7_3351
  · exact partG37c_7_3352
  · exact partG37c_7_3353
theorem partG37c_7_3339 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","i","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_3340
theorem partG37c_7_3354 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","i","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3355 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","i","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3356 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","i","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3357 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","i","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3360 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","i","j","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3361 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","i","j","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3362 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","i","j","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3363 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","i","j","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3364 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","i","j","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3365 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","i","j","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3366 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","i","j","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
end ProductiveGua
