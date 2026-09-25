import PhonologicalOpacity.Attenuation.Productive.Subject.CertificateParts.OR38_1_005
namespace ProductiveSubjectGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partOR38_1_485 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","ʊ","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_486 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","ʊ","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_487 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","ʊ","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_474 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_475
  · exact partOR38_1_476
  · exact partOR38_1_477
  · exact partOR38_1_478
  · exact partOR38_1_479
  · exact partOR38_1_480
  · exact partOR38_1_481
  · exact partOR38_1_482
  · exact partOR38_1_483
  · exact partOR38_1_484
  · exact partOR38_1_485
  · exact partOR38_1_486
  · exact partOR38_1_487
theorem partOR38_1_489 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","u","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_490 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","u","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_491 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","u","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_492 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","u","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_493 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","u","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_494 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","u","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_495 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","u","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_496 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","u","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_497 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","u","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_498 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","u","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_499 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","u","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_500 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","u","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_501 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","u","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_488 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_489
  · exact partOR38_1_490
  · exact partOR38_1_491
  · exact partOR38_1_492
  · exact partOR38_1_493
  · exact partOR38_1_494
  · exact partOR38_1_495
  · exact partOR38_1_496
  · exact partOR38_1_497
  · exact partOR38_1_498
  · exact partOR38_1_499
  · exact partOR38_1_500
  · exact partOR38_1_501
theorem partOR38_1_503 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","j","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_504 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","j","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_505 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","j","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_506 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","j","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_507 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","j","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_508 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","j","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_509 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","j","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_510 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","j","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_511 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","j","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_512 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","j","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_513 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","j","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_514 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","j","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_515 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","j","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_502 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_503
  · exact partOR38_1_504
  · exact partOR38_1_505
  · exact partOR38_1_506
  · exact partOR38_1_507
  · exact partOR38_1_508
  · exact partOR38_1_509
  · exact partOR38_1_510
  · exact partOR38_1_511
  · exact partOR38_1_512
  · exact partOR38_1_513
  · exact partOR38_1_514
  · exact partOR38_1_515
theorem partOR38_1_517 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","w","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_518 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","w","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_519 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","w","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_520 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","w","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_521 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","w","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_522 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","w","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_523 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","w","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_524 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","w","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_525 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","w","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_526 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","w","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_527 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","w","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_528 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","w","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_529 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","w","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_516 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_517
  · exact partOR38_1_518
  · exact partOR38_1_519
  · exact partOR38_1_520
  · exact partOR38_1_521
  · exact partOR38_1_522
  · exact partOR38_1_523
  · exact partOR38_1_524
  · exact partOR38_1_525
  · exact partOR38_1_526
  · exact partOR38_1_527
  · exact partOR38_1_528
  · exact partOR38_1_529
theorem partOR38_1_347 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ","s"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_348
  · exact partOR38_1_362
  · exact partOR38_1_376
  · exact partOR38_1_390
  · exact partOR38_1_404
  · exact partOR38_1_418
  · exact partOR38_1_432
  · exact partOR38_1_446
  · exact partOR38_1_460
  · exact partOR38_1_474
  · exact partOR38_1_488
  · exact partOR38_1_502
  · exact partOR38_1_516
theorem partOR38_1_346 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɛ"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="s" := by simpa using hx
  subst x
  exact partOR38_1_347
theorem partOR38_1_532 : check uOR38 (4) (-2) outOR38 ["a","tʃ","e","s","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_534 : check uOR38 (4) (-2) outOR38 ["a","tʃ","e","s","a","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_535 : check uOR38 (4) (-2) outOR38 ["a","tʃ","e","s","a","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_536 : check uOR38 (4) (-2) outOR38 ["a","tʃ","e","s","a","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_537 : check uOR38 (4) (-2) outOR38 ["a","tʃ","e","s","a","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_538 : check uOR38 (4) (-2) outOR38 ["a","tʃ","e","s","a","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_539 : check uOR38 (4) (-2) outOR38 ["a","tʃ","e","s","a","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_540 : check uOR38 (4) (-2) outOR38 ["a","tʃ","e","s","a","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_541 : check uOR38 (4) (-2) outOR38 ["a","tʃ","e","s","a","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_542 : check uOR38 (4) (-2) outOR38 ["a","tʃ","e","s","a","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_543 : check uOR38 (4) (-2) outOR38 ["a","tʃ","e","s","a","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_544 : check uOR38 (4) (-2) outOR38 ["a","tʃ","e","s","a","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_545 : check uOR38 (4) (-2) outOR38 ["a","tʃ","e","s","a","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_546 : check uOR38 (4) (-2) outOR38 ["a","tʃ","e","s","a","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_533 : check uOR38 (4) (-2) outOR38 ["a","tʃ","e","s","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_534
  · exact partOR38_1_535
  · exact partOR38_1_536
  · exact partOR38_1_537
  · exact partOR38_1_538
  · exact partOR38_1_539
  · exact partOR38_1_540
  · exact partOR38_1_541
  · exact partOR38_1_542
  · exact partOR38_1_543
  · exact partOR38_1_544
  · exact partOR38_1_545
  · exact partOR38_1_546
theorem partOR38_1_547 : check uOR38 (4) (-2) outOR38 ["a","tʃ","e","s","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_549 : check uOR38 (4) (-2) outOR38 ["a","tʃ","e","s","ɛ","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_550 : check uOR38 (4) (-2) outOR38 ["a","tʃ","e","s","ɛ","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_551 : check uOR38 (4) (-2) outOR38 ["a","tʃ","e","s","ɛ","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_552 : check uOR38 (4) (-2) outOR38 ["a","tʃ","e","s","ɛ","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_553 : check uOR38 (4) (-2) outOR38 ["a","tʃ","e","s","ɛ","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_554 : check uOR38 (4) (-2) outOR38 ["a","tʃ","e","s","ɛ","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_555 : check uOR38 (4) (-2) outOR38 ["a","tʃ","e","s","ɛ","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_556 : check uOR38 (4) (-2) outOR38 ["a","tʃ","e","s","ɛ","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_557 : check uOR38 (4) (-2) outOR38 ["a","tʃ","e","s","ɛ","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_558 : check uOR38 (4) (-2) outOR38 ["a","tʃ","e","s","ɛ","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_559 : check uOR38 (4) (-2) outOR38 ["a","tʃ","e","s","ɛ","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_560 : check uOR38 (4) (-2) outOR38 ["a","tʃ","e","s","ɛ","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_561 : check uOR38 (4) (-2) outOR38 ["a","tʃ","e","s","ɛ","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_548 : check uOR38 (4) (-2) outOR38 ["a","tʃ","e","s","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_549
  · exact partOR38_1_550
  · exact partOR38_1_551
  · exact partOR38_1_552
  · exact partOR38_1_553
  · exact partOR38_1_554
  · exact partOR38_1_555
  · exact partOR38_1_556
  · exact partOR38_1_557
  · exact partOR38_1_558
  · exact partOR38_1_559
  · exact partOR38_1_560
  · exact partOR38_1_561
theorem partOR38_1_562 : check uOR38 (4) (-2) outOR38 ["a","tʃ","e","s","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_564 : check uOR38 (4) (-2) outOR38 ["a","tʃ","e","s","ɪ","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
end ProductiveSubjectGua
