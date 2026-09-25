import PhonologicalOpacity.Attenuation.Productive.Subject.CertificateParts.OR38_0_004
namespace ProductiveSubjectGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partOR38_0_405 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ʊ","s","a","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_406 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ʊ","s","a","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_407 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ʊ","s","a","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_408 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ʊ","s","a","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_409 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ʊ","s","a","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_410 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ʊ","s","a","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_411 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ʊ","s","a","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_412 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ʊ","s","a","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_413 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ʊ","s","a","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_400 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ʊ","s","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_0_401
  · exact partOR38_0_402
  · exact partOR38_0_403
  · exact partOR38_0_404
  · exact partOR38_0_405
  · exact partOR38_0_406
  · exact partOR38_0_407
  · exact partOR38_0_408
  · exact partOR38_0_409
  · exact partOR38_0_410
  · exact partOR38_0_411
  · exact partOR38_0_412
  · exact partOR38_0_413
theorem partOR38_0_414 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ʊ","s","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_416 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ʊ","s","ɛ","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_417 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ʊ","s","ɛ","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_418 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ʊ","s","ɛ","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_419 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ʊ","s","ɛ","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_420 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ʊ","s","ɛ","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_421 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ʊ","s","ɛ","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_422 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ʊ","s","ɛ","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_423 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ʊ","s","ɛ","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_424 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ʊ","s","ɛ","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_425 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ʊ","s","ɛ","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_426 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ʊ","s","ɛ","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_427 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ʊ","s","ɛ","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_428 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ʊ","s","ɛ","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_415 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ʊ","s","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_0_416
  · exact partOR38_0_417
  · exact partOR38_0_418
  · exact partOR38_0_419
  · exact partOR38_0_420
  · exact partOR38_0_421
  · exact partOR38_0_422
  · exact partOR38_0_423
  · exact partOR38_0_424
  · exact partOR38_0_425
  · exact partOR38_0_426
  · exact partOR38_0_427
  · exact partOR38_0_428
theorem partOR38_0_429 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ʊ","s","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_431 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ʊ","s","ɪ","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_432 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ʊ","s","ɪ","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_433 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ʊ","s","ɪ","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_434 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ʊ","s","ɪ","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_435 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ʊ","s","ɪ","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_436 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ʊ","s","ɪ","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_437 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ʊ","s","ɪ","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_438 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ʊ","s","ɪ","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_439 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ʊ","s","ɪ","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_440 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ʊ","s","ɪ","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_441 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ʊ","s","ɪ","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_442 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ʊ","s","ɪ","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_443 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ʊ","s","ɪ","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_430 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ʊ","s","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_0_431
  · exact partOR38_0_432
  · exact partOR38_0_433
  · exact partOR38_0_434
  · exact partOR38_0_435
  · exact partOR38_0_436
  · exact partOR38_0_437
  · exact partOR38_0_438
  · exact partOR38_0_439
  · exact partOR38_0_440
  · exact partOR38_0_441
  · exact partOR38_0_442
  · exact partOR38_0_443
theorem partOR38_0_444 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ʊ","s","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_446 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ʊ","s","ɔ","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_447 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ʊ","s","ɔ","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_448 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ʊ","s","ɔ","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_449 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ʊ","s","ɔ","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_450 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ʊ","s","ɔ","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_451 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ʊ","s","ɔ","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_452 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ʊ","s","ɔ","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_453 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ʊ","s","ɔ","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_454 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ʊ","s","ɔ","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_455 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ʊ","s","ɔ","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_456 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ʊ","s","ɔ","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_457 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ʊ","s","ɔ","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_458 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ʊ","s","ɔ","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_445 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ʊ","s","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_0_446
  · exact partOR38_0_447
  · exact partOR38_0_448
  · exact partOR38_0_449
  · exact partOR38_0_450
  · exact partOR38_0_451
  · exact partOR38_0_452
  · exact partOR38_0_453
  · exact partOR38_0_454
  · exact partOR38_0_455
  · exact partOR38_0_456
  · exact partOR38_0_457
  · exact partOR38_0_458
theorem partOR38_0_459 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ʊ","s","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_461 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ʊ","s","ʊ","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_462 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ʊ","s","ʊ","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_463 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ʊ","s","ʊ","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_464 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ʊ","s","ʊ","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_465 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ʊ","s","ʊ","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_466 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ʊ","s","ʊ","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_467 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ʊ","s","ʊ","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_468 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ʊ","s","ʊ","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_469 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ʊ","s","ʊ","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_470 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ʊ","s","ʊ","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_471 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ʊ","s","ʊ","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_472 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ʊ","s","ʊ","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_473 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ʊ","s","ʊ","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_460 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ʊ","s","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_0_461
  · exact partOR38_0_462
  · exact partOR38_0_463
  · exact partOR38_0_464
  · exact partOR38_0_465
  · exact partOR38_0_466
  · exact partOR38_0_467
  · exact partOR38_0_468
  · exact partOR38_0_469
  · exact partOR38_0_470
  · exact partOR38_0_471
  · exact partOR38_0_472
  · exact partOR38_0_473
theorem partOR38_0_474 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ʊ","s","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_475 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ʊ","s","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_476 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ʊ","s","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_398 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ʊ","s"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_0_399
  · exact partOR38_0_400
  · exact partOR38_0_414
  · exact partOR38_0_415
  · exact partOR38_0_429
  · exact partOR38_0_430
  · exact partOR38_0_444
  · exact partOR38_0_445
  · exact partOR38_0_459
  · exact partOR38_0_460
  · exact partOR38_0_474
  · exact partOR38_0_475
  · exact partOR38_0_476
theorem partOR38_0_397 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ʊ"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="s" := by simpa using hx
  subst x
  exact partOR38_0_398
theorem partOR38_0_479 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","u","s","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_480 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","u","s","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_481 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","u","s","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_482 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","u","s","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_483 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","u","s","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
end ProductiveSubjectGua
