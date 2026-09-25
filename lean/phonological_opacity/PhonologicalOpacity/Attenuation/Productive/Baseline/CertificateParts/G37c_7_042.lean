import PhonologicalOpacity.Attenuation.Productive.Baseline.CertificateParts.G37c_7_041
namespace ProductiveGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partG37c_7_3367 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","i","j","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3368 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","i","j","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3369 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","i","j","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3370 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","i","j","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3371 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","i","j","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3372 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","i","j","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3359 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","i","j","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_3360
  · exact partG37c_7_3361
  · exact partG37c_7_3362
  · exact partG37c_7_3363
  · exact partG37c_7_3364
  · exact partG37c_7_3365
  · exact partG37c_7_3366
  · exact partG37c_7_3367
  · exact partG37c_7_3368
  · exact partG37c_7_3369
  · exact partG37c_7_3370
  · exact partG37c_7_3371
  · exact partG37c_7_3372
theorem partG37c_7_3358 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","i","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_3359
theorem partG37c_7_3373 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","i","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3318 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_3319
  · exact partG37c_7_3334
  · exact partG37c_7_3335
  · exact partG37c_7_3336
  · exact partG37c_7_3337
  · exact partG37c_7_3338
  · exact partG37c_7_3339
  · exact partG37c_7_3354
  · exact partG37c_7_3355
  · exact partG37c_7_3356
  · exact partG37c_7_3357
  · exact partG37c_7_3358
  · exact partG37c_7_3373
theorem partG37c_7_3377 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɔ","∅","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3378 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɔ","∅","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3379 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɔ","∅","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3380 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɔ","∅","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3381 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɔ","∅","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3382 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɔ","∅","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3383 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɔ","∅","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3384 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɔ","∅","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3385 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɔ","∅","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3386 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɔ","∅","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3387 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɔ","∅","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3388 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɔ","∅","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3389 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɔ","∅","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3376 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɔ","∅","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_3377
  · exact partG37c_7_3378
  · exact partG37c_7_3379
  · exact partG37c_7_3380
  · exact partG37c_7_3381
  · exact partG37c_7_3382
  · exact partG37c_7_3383
  · exact partG37c_7_3384
  · exact partG37c_7_3385
  · exact partG37c_7_3386
  · exact partG37c_7_3387
  · exact partG37c_7_3388
  · exact partG37c_7_3389
theorem partG37c_7_3375 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɔ","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_3376
theorem partG37c_7_3390 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɔ","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3391 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɔ","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3392 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɔ","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3393 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɔ","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3394 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɔ","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3397 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɔ","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3398 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɔ","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3399 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɔ","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3400 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɔ","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3401 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɔ","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3402 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɔ","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3403 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɔ","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3404 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɔ","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3405 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɔ","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3406 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɔ","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3407 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɔ","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3408 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɔ","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3409 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɔ","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3396 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɔ","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_3397
  · exact partG37c_7_3398
  · exact partG37c_7_3399
  · exact partG37c_7_3400
  · exact partG37c_7_3401
  · exact partG37c_7_3402
  · exact partG37c_7_3403
  · exact partG37c_7_3404
  · exact partG37c_7_3405
  · exact partG37c_7_3406
  · exact partG37c_7_3407
  · exact partG37c_7_3408
  · exact partG37c_7_3409
theorem partG37c_7_3395 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɔ","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_3396
theorem partG37c_7_3410 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɔ","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3411 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɔ","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3412 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɔ","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3413 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɔ","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3416 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɔ","j","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3417 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɔ","j","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3418 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɔ","j","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3419 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɔ","j","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3420 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɔ","j","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3421 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɔ","j","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3422 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɔ","j","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3423 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɔ","j","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3424 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɔ","j","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3425 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɔ","j","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3426 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɔ","j","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3427 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɔ","j","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3428 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɔ","j","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3415 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɔ","j","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_3416
  · exact partG37c_7_3417
  · exact partG37c_7_3418
  · exact partG37c_7_3419
  · exact partG37c_7_3420
  · exact partG37c_7_3421
  · exact partG37c_7_3422
  · exact partG37c_7_3423
  · exact partG37c_7_3424
  · exact partG37c_7_3425
  · exact partG37c_7_3426
  · exact partG37c_7_3427
  · exact partG37c_7_3428
theorem partG37c_7_3414 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɔ","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_3415
theorem partG37c_7_3429 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɔ","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3374 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_3375
  · exact partG37c_7_3390
  · exact partG37c_7_3391
  · exact partG37c_7_3392
  · exact partG37c_7_3393
  · exact partG37c_7_3394
  · exact partG37c_7_3395
  · exact partG37c_7_3410
  · exact partG37c_7_3411
  · exact partG37c_7_3412
  · exact partG37c_7_3413
  · exact partG37c_7_3414
  · exact partG37c_7_3429
theorem partG37c_7_3433 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","o","∅","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3434 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","o","∅","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3435 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","o","∅","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3436 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","o","∅","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3437 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","o","∅","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3438 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","o","∅","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3439 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","o","∅","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3440 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","o","∅","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3441 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","o","∅","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3442 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","o","∅","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3443 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","o","∅","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3444 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","o","∅","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3445 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","o","∅","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3432 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","o","∅","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_3433
  · exact partG37c_7_3434
  · exact partG37c_7_3435
  · exact partG37c_7_3436
  · exact partG37c_7_3437
  · exact partG37c_7_3438
  · exact partG37c_7_3439
  · exact partG37c_7_3440
  · exact partG37c_7_3441
  · exact partG37c_7_3442
  · exact partG37c_7_3443
  · exact partG37c_7_3444
  · exact partG37c_7_3445
end ProductiveGua
