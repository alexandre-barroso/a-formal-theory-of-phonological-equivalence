import PhonologicalOpacity.Attenuation.Productive.Subject.CertificateParts.OR38_1_004
namespace ProductiveSubjectGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partOR38_1_405 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","e","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_406 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","e","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_407 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","e","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_408 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","e","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_409 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","e","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_410 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","e","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_411 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","e","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_412 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","e","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_413 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","e","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_414 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","e","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_415 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","e","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_416 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","e","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_417 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","e","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_404 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_405
  · exact partOR38_1_406
  · exact partOR38_1_407
  · exact partOR38_1_408
  · exact partOR38_1_409
  · exact partOR38_1_410
  · exact partOR38_1_411
  · exact partOR38_1_412
  · exact partOR38_1_413
  · exact partOR38_1_414
  · exact partOR38_1_415
  · exact partOR38_1_416
  · exact partOR38_1_417
theorem partOR38_1_419 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","ɪ","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_420 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","ɪ","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_421 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","ɪ","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_422 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","ɪ","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_423 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","ɪ","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_424 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","ɪ","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_425 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","ɪ","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_426 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","ɪ","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_427 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","ɪ","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_428 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","ɪ","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_429 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","ɪ","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_430 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","ɪ","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_431 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","ɪ","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_418 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_419
  · exact partOR38_1_420
  · exact partOR38_1_421
  · exact partOR38_1_422
  · exact partOR38_1_423
  · exact partOR38_1_424
  · exact partOR38_1_425
  · exact partOR38_1_426
  · exact partOR38_1_427
  · exact partOR38_1_428
  · exact partOR38_1_429
  · exact partOR38_1_430
  · exact partOR38_1_431
theorem partOR38_1_433 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","i","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_434 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","i","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_435 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","i","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_436 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","i","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_437 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","i","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_438 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","i","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_439 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","i","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_440 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","i","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_441 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","i","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_442 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","i","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_443 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","i","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_444 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","i","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_445 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","i","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_432 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_433
  · exact partOR38_1_434
  · exact partOR38_1_435
  · exact partOR38_1_436
  · exact partOR38_1_437
  · exact partOR38_1_438
  · exact partOR38_1_439
  · exact partOR38_1_440
  · exact partOR38_1_441
  · exact partOR38_1_442
  · exact partOR38_1_443
  · exact partOR38_1_444
  · exact partOR38_1_445
theorem partOR38_1_447 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","ɔ","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_448 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","ɔ","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_449 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","ɔ","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_450 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","ɔ","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_451 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","ɔ","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_452 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","ɔ","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_453 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","ɔ","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_454 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","ɔ","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_455 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","ɔ","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_456 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","ɔ","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_457 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","ɔ","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_458 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","ɔ","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_459 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","ɔ","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_446 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_447
  · exact partOR38_1_448
  · exact partOR38_1_449
  · exact partOR38_1_450
  · exact partOR38_1_451
  · exact partOR38_1_452
  · exact partOR38_1_453
  · exact partOR38_1_454
  · exact partOR38_1_455
  · exact partOR38_1_456
  · exact partOR38_1_457
  · exact partOR38_1_458
  · exact partOR38_1_459
theorem partOR38_1_461 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","o","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_462 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","o","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_463 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","o","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_464 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","o","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_465 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","o","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_466 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","o","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_467 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","o","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_468 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","o","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_469 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","o","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_470 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","o","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_471 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","o","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_472 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","o","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_473 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","o","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_460 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_461
  · exact partOR38_1_462
  · exact partOR38_1_463
  · exact partOR38_1_464
  · exact partOR38_1_465
  · exact partOR38_1_466
  · exact partOR38_1_467
  · exact partOR38_1_468
  · exact partOR38_1_469
  · exact partOR38_1_470
  · exact partOR38_1_471
  · exact partOR38_1_472
  · exact partOR38_1_473
theorem partOR38_1_475 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","ʊ","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_476 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","ʊ","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_477 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","ʊ","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_478 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","ʊ","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_479 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","ʊ","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_480 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","ʊ","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_481 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","ʊ","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_482 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","ʊ","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_483 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","ʊ","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_484 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","ʊ","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
end ProductiveSubjectGua
