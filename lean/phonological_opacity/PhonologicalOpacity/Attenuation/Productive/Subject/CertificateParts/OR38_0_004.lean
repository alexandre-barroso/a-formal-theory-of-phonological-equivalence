import PhonologicalOpacity.Attenuation.Productive.Subject.CertificateParts.OR38_0_003
namespace ProductiveSubjectGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partOR38_0_325 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɔ","s","ɛ","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_326 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɔ","s","ɛ","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_327 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɔ","s","ɛ","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_328 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɔ","s","ɛ","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_329 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɔ","s","ɛ","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_330 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɔ","s","ɛ","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_331 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɔ","s","ɛ","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_332 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɔ","s","ɛ","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_333 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɔ","s","ɛ","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_320 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɔ","s","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_0_321
  · exact partOR38_0_322
  · exact partOR38_0_323
  · exact partOR38_0_324
  · exact partOR38_0_325
  · exact partOR38_0_326
  · exact partOR38_0_327
  · exact partOR38_0_328
  · exact partOR38_0_329
  · exact partOR38_0_330
  · exact partOR38_0_331
  · exact partOR38_0_332
  · exact partOR38_0_333
theorem partOR38_0_334 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɔ","s","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_336 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɔ","s","ɪ","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_337 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɔ","s","ɪ","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_338 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɔ","s","ɪ","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_339 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɔ","s","ɪ","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_340 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɔ","s","ɪ","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_341 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɔ","s","ɪ","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_342 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɔ","s","ɪ","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_343 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɔ","s","ɪ","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_344 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɔ","s","ɪ","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_345 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɔ","s","ɪ","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_346 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɔ","s","ɪ","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_347 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɔ","s","ɪ","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_348 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɔ","s","ɪ","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_335 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɔ","s","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_0_336
  · exact partOR38_0_337
  · exact partOR38_0_338
  · exact partOR38_0_339
  · exact partOR38_0_340
  · exact partOR38_0_341
  · exact partOR38_0_342
  · exact partOR38_0_343
  · exact partOR38_0_344
  · exact partOR38_0_345
  · exact partOR38_0_346
  · exact partOR38_0_347
  · exact partOR38_0_348
theorem partOR38_0_349 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɔ","s","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_351 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɔ","s","ɔ","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_352 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɔ","s","ɔ","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_353 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɔ","s","ɔ","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_354 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɔ","s","ɔ","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_355 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɔ","s","ɔ","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_356 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɔ","s","ɔ","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_357 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɔ","s","ɔ","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_358 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɔ","s","ɔ","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_359 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɔ","s","ɔ","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_360 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɔ","s","ɔ","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_361 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɔ","s","ɔ","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_362 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɔ","s","ɔ","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_363 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɔ","s","ɔ","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_350 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɔ","s","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_0_351
  · exact partOR38_0_352
  · exact partOR38_0_353
  · exact partOR38_0_354
  · exact partOR38_0_355
  · exact partOR38_0_356
  · exact partOR38_0_357
  · exact partOR38_0_358
  · exact partOR38_0_359
  · exact partOR38_0_360
  · exact partOR38_0_361
  · exact partOR38_0_362
  · exact partOR38_0_363
theorem partOR38_0_364 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɔ","s","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_366 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɔ","s","ʊ","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_367 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɔ","s","ʊ","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_368 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɔ","s","ʊ","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_369 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɔ","s","ʊ","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_370 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɔ","s","ʊ","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_371 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɔ","s","ʊ","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_372 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɔ","s","ʊ","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_373 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɔ","s","ʊ","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_374 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɔ","s","ʊ","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_375 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɔ","s","ʊ","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_376 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɔ","s","ʊ","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_377 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɔ","s","ʊ","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_378 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɔ","s","ʊ","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_365 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɔ","s","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_0_366
  · exact partOR38_0_367
  · exact partOR38_0_368
  · exact partOR38_0_369
  · exact partOR38_0_370
  · exact partOR38_0_371
  · exact partOR38_0_372
  · exact partOR38_0_373
  · exact partOR38_0_374
  · exact partOR38_0_375
  · exact partOR38_0_376
  · exact partOR38_0_377
  · exact partOR38_0_378
theorem partOR38_0_379 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɔ","s","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_380 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɔ","s","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_381 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɔ","s","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_303 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɔ","s"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_0_304
  · exact partOR38_0_305
  · exact partOR38_0_319
  · exact partOR38_0_320
  · exact partOR38_0_334
  · exact partOR38_0_335
  · exact partOR38_0_349
  · exact partOR38_0_350
  · exact partOR38_0_364
  · exact partOR38_0_365
  · exact partOR38_0_379
  · exact partOR38_0_380
  · exact partOR38_0_381
theorem partOR38_0_302 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɔ"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="s" := by simpa using hx
  subst x
  exact partOR38_0_303
theorem partOR38_0_384 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","o","s","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_385 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","o","s","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_386 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","o","s","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_387 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","o","s","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_388 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","o","s","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_389 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","o","s","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_390 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","o","s","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_391 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","o","s","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_392 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","o","s","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_393 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","o","s","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_394 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","o","s","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_395 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","o","s","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_396 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","o","s","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_383 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","o","s"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_0_384
  · exact partOR38_0_385
  · exact partOR38_0_386
  · exact partOR38_0_387
  · exact partOR38_0_388
  · exact partOR38_0_389
  · exact partOR38_0_390
  · exact partOR38_0_391
  · exact partOR38_0_392
  · exact partOR38_0_393
  · exact partOR38_0_394
  · exact partOR38_0_395
  · exact partOR38_0_396
theorem partOR38_0_382 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","o"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="s" := by simpa using hx
  subst x
  exact partOR38_0_383
theorem partOR38_0_399 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ʊ","s","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_401 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ʊ","s","a","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_402 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ʊ","s","a","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_403 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ʊ","s","a","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_404 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ʊ","s","a","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
end ProductiveSubjectGua
