import PhonologicalOpacity.Attenuation.Productive.Baseline.CertificateParts.G34a_1_004
namespace ProductiveGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partG34a_1_405 : check uG34a (3) (-2) outG34a ["a","h","a","t","i","j"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_406 : check uG34a (3) (-2) outG34a ["a","h","a","t","i","w"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_363 : check uG34a (3) (-2) outG34a ["a","h","a","t","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG34a_1_364
  · exact partG34a_1_380
  · exact partG34a_1_381
  · exact partG34a_1_382
  · exact partG34a_1_383
  · exact partG34a_1_384
  · exact partG34a_1_385
  · exact partG34a_1_386
  · exact partG34a_1_402
  · exact partG34a_1_403
  · exact partG34a_1_404
  · exact partG34a_1_405
  · exact partG34a_1_406
theorem partG34a_1_408 : check uG34a (3) (-2) outG34a ["a","h","a","t","ɔ","∅"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_409 : check uG34a (3) (-2) outG34a ["a","h","a","t","ɔ","a"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_410 : check uG34a (3) (-2) outG34a ["a","h","a","t","ɔ","ɜ"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_411 : check uG34a (3) (-2) outG34a ["a","h","a","t","ɔ","ɛ"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_412 : check uG34a (3) (-2) outG34a ["a","h","a","t","ɔ","e"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_413 : check uG34a (3) (-2) outG34a ["a","h","a","t","ɔ","ɪ"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_414 : check uG34a (3) (-2) outG34a ["a","h","a","t","ɔ","i"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_418 : check uG34a (3) (-2) outG34a ["a","h","a","t","ɔ","ɔ","k","p","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_419 : check uG34a (3) (-2) outG34a ["a","h","a","t","ɔ","ɔ","k","p","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_420 : check uG34a (3) (-2) outG34a ["a","h","a","t","ɔ","ɔ","k","p","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_421 : check uG34a (3) (-2) outG34a ["a","h","a","t","ɔ","ɔ","k","p","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_422 : check uG34a (3) (-2) outG34a ["a","h","a","t","ɔ","ɔ","k","p","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_423 : check uG34a (3) (-2) outG34a ["a","h","a","t","ɔ","ɔ","k","p","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_424 : check uG34a (3) (-2) outG34a ["a","h","a","t","ɔ","ɔ","k","p","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_425 : check uG34a (3) (-2) outG34a ["a","h","a","t","ɔ","ɔ","k","p","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_426 : check uG34a (3) (-2) outG34a ["a","h","a","t","ɔ","ɔ","k","p","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_427 : check uG34a (3) (-2) outG34a ["a","h","a","t","ɔ","ɔ","k","p","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_428 : check uG34a (3) (-2) outG34a ["a","h","a","t","ɔ","ɔ","k","p","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_429 : check uG34a (3) (-2) outG34a ["a","h","a","t","ɔ","ɔ","k","p","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_430 : check uG34a (3) (-2) outG34a ["a","h","a","t","ɔ","ɔ","k","p","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_417 : check uG34a (3) (-2) outG34a ["a","h","a","t","ɔ","ɔ","k","p"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG34a_1_418
  · exact partG34a_1_419
  · exact partG34a_1_420
  · exact partG34a_1_421
  · exact partG34a_1_422
  · exact partG34a_1_423
  · exact partG34a_1_424
  · exact partG34a_1_425
  · exact partG34a_1_426
  · exact partG34a_1_427
  · exact partG34a_1_428
  · exact partG34a_1_429
  · exact partG34a_1_430
theorem partG34a_1_416 : check uG34a (3) (-2) outG34a ["a","h","a","t","ɔ","ɔ","k"] [["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="p" := by simpa using hx
  subst x
  exact partG34a_1_417
theorem partG34a_1_415 : check uG34a (3) (-2) outG34a ["a","h","a","t","ɔ","ɔ"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="k" := by simpa using hx
  subst x
  exact partG34a_1_416
theorem partG34a_1_431 : check uG34a (3) (-2) outG34a ["a","h","a","t","ɔ","o"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_432 : check uG34a (3) (-2) outG34a ["a","h","a","t","ɔ","ʊ"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_433 : check uG34a (3) (-2) outG34a ["a","h","a","t","ɔ","u"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_434 : check uG34a (3) (-2) outG34a ["a","h","a","t","ɔ","j"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_435 : check uG34a (3) (-2) outG34a ["a","h","a","t","ɔ","w"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_407 : check uG34a (3) (-2) outG34a ["a","h","a","t","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG34a_1_408
  · exact partG34a_1_409
  · exact partG34a_1_410
  · exact partG34a_1_411
  · exact partG34a_1_412
  · exact partG34a_1_413
  · exact partG34a_1_414
  · exact partG34a_1_415
  · exact partG34a_1_431
  · exact partG34a_1_432
  · exact partG34a_1_433
  · exact partG34a_1_434
  · exact partG34a_1_435
theorem partG34a_1_440 : check uG34a (3) (-2) outG34a ["a","h","a","t","o","∅","k","p","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_441 : check uG34a (3) (-2) outG34a ["a","h","a","t","o","∅","k","p","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_442 : check uG34a (3) (-2) outG34a ["a","h","a","t","o","∅","k","p","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_443 : check uG34a (3) (-2) outG34a ["a","h","a","t","o","∅","k","p","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_444 : check uG34a (3) (-2) outG34a ["a","h","a","t","o","∅","k","p","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_445 : check uG34a (3) (-2) outG34a ["a","h","a","t","o","∅","k","p","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_446 : check uG34a (3) (-2) outG34a ["a","h","a","t","o","∅","k","p","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_447 : check uG34a (3) (-2) outG34a ["a","h","a","t","o","∅","k","p","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_448 : check uG34a (3) (-2) outG34a ["a","h","a","t","o","∅","k","p","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_449 : check uG34a (3) (-2) outG34a ["a","h","a","t","o","∅","k","p","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_450 : check uG34a (3) (-2) outG34a ["a","h","a","t","o","∅","k","p","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_451 : check uG34a (3) (-2) outG34a ["a","h","a","t","o","∅","k","p","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_452 : check uG34a (3) (-2) outG34a ["a","h","a","t","o","∅","k","p","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_439 : check uG34a (3) (-2) outG34a ["a","h","a","t","o","∅","k","p"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG34a_1_440
  · exact partG34a_1_441
  · exact partG34a_1_442
  · exact partG34a_1_443
  · exact partG34a_1_444
  · exact partG34a_1_445
  · exact partG34a_1_446
  · exact partG34a_1_447
  · exact partG34a_1_448
  · exact partG34a_1_449
  · exact partG34a_1_450
  · exact partG34a_1_451
  · exact partG34a_1_452
theorem partG34a_1_438 : check uG34a (3) (-2) outG34a ["a","h","a","t","o","∅","k"] [["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="p" := by simpa using hx
  subst x
  exact partG34a_1_439
theorem partG34a_1_437 : check uG34a (3) (-2) outG34a ["a","h","a","t","o","∅"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="k" := by simpa using hx
  subst x
  exact partG34a_1_438
theorem partG34a_1_453 : check uG34a (3) (-2) outG34a ["a","h","a","t","o","a"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_454 : check uG34a (3) (-2) outG34a ["a","h","a","t","o","ɜ"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_455 : check uG34a (3) (-2) outG34a ["a","h","a","t","o","ɛ"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_456 : check uG34a (3) (-2) outG34a ["a","h","a","t","o","e"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_457 : check uG34a (3) (-2) outG34a ["a","h","a","t","o","ɪ"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_458 : check uG34a (3) (-2) outG34a ["a","h","a","t","o","i"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_462 : check uG34a (3) (-2) outG34a ["a","h","a","t","o","ɔ","k","p","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_463 : check uG34a (3) (-2) outG34a ["a","h","a","t","o","ɔ","k","p","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_464 : check uG34a (3) (-2) outG34a ["a","h","a","t","o","ɔ","k","p","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_465 : check uG34a (3) (-2) outG34a ["a","h","a","t","o","ɔ","k","p","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_466 : check uG34a (3) (-2) outG34a ["a","h","a","t","o","ɔ","k","p","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_467 : check uG34a (3) (-2) outG34a ["a","h","a","t","o","ɔ","k","p","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_468 : check uG34a (3) (-2) outG34a ["a","h","a","t","o","ɔ","k","p","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_469 : check uG34a (3) (-2) outG34a ["a","h","a","t","o","ɔ","k","p","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_470 : check uG34a (3) (-2) outG34a ["a","h","a","t","o","ɔ","k","p","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_471 : check uG34a (3) (-2) outG34a ["a","h","a","t","o","ɔ","k","p","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_472 : check uG34a (3) (-2) outG34a ["a","h","a","t","o","ɔ","k","p","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_473 : check uG34a (3) (-2) outG34a ["a","h","a","t","o","ɔ","k","p","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_474 : check uG34a (3) (-2) outG34a ["a","h","a","t","o","ɔ","k","p","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_461 : check uG34a (3) (-2) outG34a ["a","h","a","t","o","ɔ","k","p"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG34a_1_462
  · exact partG34a_1_463
  · exact partG34a_1_464
  · exact partG34a_1_465
  · exact partG34a_1_466
  · exact partG34a_1_467
  · exact partG34a_1_468
  · exact partG34a_1_469
  · exact partG34a_1_470
  · exact partG34a_1_471
  · exact partG34a_1_472
  · exact partG34a_1_473
  · exact partG34a_1_474
theorem partG34a_1_460 : check uG34a (3) (-2) outG34a ["a","h","a","t","o","ɔ","k"] [["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="p" := by simpa using hx
  subst x
  exact partG34a_1_461
theorem partG34a_1_459 : check uG34a (3) (-2) outG34a ["a","h","a","t","o","ɔ"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="k" := by simpa using hx
  subst x
  exact partG34a_1_460
theorem partG34a_1_475 : check uG34a (3) (-2) outG34a ["a","h","a","t","o","o"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_476 : check uG34a (3) (-2) outG34a ["a","h","a","t","o","ʊ"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_477 : check uG34a (3) (-2) outG34a ["a","h","a","t","o","u"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_478 : check uG34a (3) (-2) outG34a ["a","h","a","t","o","j"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_479 : check uG34a (3) (-2) outG34a ["a","h","a","t","o","w"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_436 : check uG34a (3) (-2) outG34a ["a","h","a","t","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG34a_1_437
  · exact partG34a_1_453
  · exact partG34a_1_454
  · exact partG34a_1_455
  · exact partG34a_1_456
  · exact partG34a_1_457
  · exact partG34a_1_458
  · exact partG34a_1_459
  · exact partG34a_1_475
  · exact partG34a_1_476
  · exact partG34a_1_477
  · exact partG34a_1_478
  · exact partG34a_1_479
theorem partG34a_1_481 : check uG34a (3) (-2) outG34a ["a","h","a","t","ʊ","∅"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_482 : check uG34a (3) (-2) outG34a ["a","h","a","t","ʊ","a"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_483 : check uG34a (3) (-2) outG34a ["a","h","a","t","ʊ","ɜ"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_484 : check uG34a (3) (-2) outG34a ["a","h","a","t","ʊ","ɛ"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
end ProductiveGua
