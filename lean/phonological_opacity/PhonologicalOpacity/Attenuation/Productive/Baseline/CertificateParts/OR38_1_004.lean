import PhonologicalOpacity.Attenuation.Productive.Baseline.CertificateParts.OR38_1_003
namespace ProductiveGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partOR38_1_325 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɜ","s","ɔ","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_326 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɜ","s","ɔ","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_327 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɜ","s","ɔ","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_314 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɜ","s","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_315
  · exact partOR38_1_316
  · exact partOR38_1_317
  · exact partOR38_1_318
  · exact partOR38_1_319
  · exact partOR38_1_320
  · exact partOR38_1_321
  · exact partOR38_1_322
  · exact partOR38_1_323
  · exact partOR38_1_324
  · exact partOR38_1_325
  · exact partOR38_1_326
  · exact partOR38_1_327
theorem partOR38_1_328 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɜ","s","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_330 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɜ","s","ʊ","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_331 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɜ","s","ʊ","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_332 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɜ","s","ʊ","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_333 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɜ","s","ʊ","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_334 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɜ","s","ʊ","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_335 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɜ","s","ʊ","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_336 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɜ","s","ʊ","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_337 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɜ","s","ʊ","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_338 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɜ","s","ʊ","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_339 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɜ","s","ʊ","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_340 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɜ","s","ʊ","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_341 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɜ","s","ʊ","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_342 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɜ","s","ʊ","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_329 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɜ","s","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_330
  · exact partOR38_1_331
  · exact partOR38_1_332
  · exact partOR38_1_333
  · exact partOR38_1_334
  · exact partOR38_1_335
  · exact partOR38_1_336
  · exact partOR38_1_337
  · exact partOR38_1_338
  · exact partOR38_1_339
  · exact partOR38_1_340
  · exact partOR38_1_341
  · exact partOR38_1_342
theorem partOR38_1_343 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɜ","s","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_344 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɜ","s","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_345 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɜ","s","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_267 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɜ","s"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_268
  · exact partOR38_1_269
  · exact partOR38_1_283
  · exact partOR38_1_284
  · exact partOR38_1_298
  · exact partOR38_1_299
  · exact partOR38_1_313
  · exact partOR38_1_314
  · exact partOR38_1_328
  · exact partOR38_1_329
  · exact partOR38_1_343
  · exact partOR38_1_344
  · exact partOR38_1_345
theorem partOR38_1_266 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɜ"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="s" := by simpa using hx
  subst x
  exact partOR38_1_267
theorem partOR38_1_349 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","∅","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_350 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","∅","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_351 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","∅","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_352 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","∅","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_353 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","∅","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_354 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","∅","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_355 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","∅","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_356 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","∅","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_357 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","∅","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_358 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","∅","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_359 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","∅","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_360 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","∅","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_361 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","∅","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_348 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_349
  · exact partOR38_1_350
  · exact partOR38_1_351
  · exact partOR38_1_352
  · exact partOR38_1_353
  · exact partOR38_1_354
  · exact partOR38_1_355
  · exact partOR38_1_356
  · exact partOR38_1_357
  · exact partOR38_1_358
  · exact partOR38_1_359
  · exact partOR38_1_360
  · exact partOR38_1_361
theorem partOR38_1_363 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","a","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_364 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","a","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_365 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","a","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_366 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","a","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_367 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","a","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_368 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","a","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_369 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","a","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_370 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","a","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_371 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","a","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_372 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","a","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_373 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","a","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_374 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","a","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_375 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","a","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_362 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_363
  · exact partOR38_1_364
  · exact partOR38_1_365
  · exact partOR38_1_366
  · exact partOR38_1_367
  · exact partOR38_1_368
  · exact partOR38_1_369
  · exact partOR38_1_370
  · exact partOR38_1_371
  · exact partOR38_1_372
  · exact partOR38_1_373
  · exact partOR38_1_374
  · exact partOR38_1_375
theorem partOR38_1_377 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","ɜ","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_378 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","ɜ","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_379 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","ɜ","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_380 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","ɜ","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_381 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","ɜ","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_382 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","ɜ","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_383 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","ɜ","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_384 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","ɜ","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_385 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","ɜ","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_386 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","ɜ","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_387 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","ɜ","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_388 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","ɜ","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_389 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","ɜ","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_376 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_377
  · exact partOR38_1_378
  · exact partOR38_1_379
  · exact partOR38_1_380
  · exact partOR38_1_381
  · exact partOR38_1_382
  · exact partOR38_1_383
  · exact partOR38_1_384
  · exact partOR38_1_385
  · exact partOR38_1_386
  · exact partOR38_1_387
  · exact partOR38_1_388
  · exact partOR38_1_389
theorem partOR38_1_391 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","ɛ","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_392 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","ɛ","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_393 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","ɛ","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_394 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","ɛ","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_395 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","ɛ","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_396 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","ɛ","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_397 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","ɛ","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_398 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","ɛ","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_399 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","ɛ","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_400 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","ɛ","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_401 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","ɛ","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_402 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","ɛ","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_403 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","ɛ","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_390 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_391
  · exact partOR38_1_392
  · exact partOR38_1_393
  · exact partOR38_1_394
  · exact partOR38_1_395
  · exact partOR38_1_396
  · exact partOR38_1_397
  · exact partOR38_1_398
  · exact partOR38_1_399
  · exact partOR38_1_400
  · exact partOR38_1_401
  · exact partOR38_1_402
  · exact partOR38_1_403
end ProductiveGua
