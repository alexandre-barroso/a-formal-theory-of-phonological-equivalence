import PhonologicalOpacity.Attenuation.Productive.Subject.CertificateParts.G37c_7_005
namespace ProductiveSubjectGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partG37c_7_485 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","w","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_486 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","w","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_489 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","w","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_490 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","w","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_491 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","w","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_492 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","w","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_493 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","w","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_494 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","w","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_495 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","w","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_496 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","w","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_497 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","w","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_498 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","w","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_499 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","w","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_500 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","w","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_501 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","w","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_488 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","w","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_489
  · exact partG37c_7_490
  · exact partG37c_7_491
  · exact partG37c_7_492
  · exact partG37c_7_493
  · exact partG37c_7_494
  · exact partG37c_7_495
  · exact partG37c_7_496
  · exact partG37c_7_497
  · exact partG37c_7_498
  · exact partG37c_7_499
  · exact partG37c_7_500
  · exact partG37c_7_501
theorem partG37c_7_487 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","w","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_488
theorem partG37c_7_502 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","w","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_503 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","w","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_504 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","w","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_505 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","w","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_506 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","w","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_507 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","w","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_480 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_481
  · exact partG37c_7_482
  · exact partG37c_7_483
  · exact partG37c_7_484
  · exact partG37c_7_485
  · exact partG37c_7_486
  · exact partG37c_7_487
  · exact partG37c_7_502
  · exact partG37c_7_503
  · exact partG37c_7_504
  · exact partG37c_7_505
  · exact partG37c_7_506
  · exact partG37c_7_507
theorem partG37c_7_3 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_4
  · exact partG37c_7_32
  · exact partG37c_7_88
  · exact partG37c_7_116
  · exact partG37c_7_172
  · exact partG37c_7_200
  · exact partG37c_7_256
  · exact partG37c_7_284
  · exact partG37c_7_340
  · exact partG37c_7_368
  · exact partG37c_7_424
  · exact partG37c_7_452
  · exact partG37c_7_480
theorem partG37c_7_2 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="s" := by simpa using hx
  subst x
  exact partG37c_7_3
theorem partG37c_7_513 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","∅","∅","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_514 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","∅","∅","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_515 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","∅","∅","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_516 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","∅","∅","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_517 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","∅","∅","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_518 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","∅","∅","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_519 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","∅","∅","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_520 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","∅","∅","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_521 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","∅","∅","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_522 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","∅","∅","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_523 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","∅","∅","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_524 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","∅","∅","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_525 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","∅","∅","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_512 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","∅","∅","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_513
  · exact partG37c_7_514
  · exact partG37c_7_515
  · exact partG37c_7_516
  · exact partG37c_7_517
  · exact partG37c_7_518
  · exact partG37c_7_519
  · exact partG37c_7_520
  · exact partG37c_7_521
  · exact partG37c_7_522
  · exact partG37c_7_523
  · exact partG37c_7_524
  · exact partG37c_7_525
theorem partG37c_7_511 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","∅","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_512
theorem partG37c_7_526 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","∅","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_527 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","∅","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_528 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","∅","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_529 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","∅","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_530 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","∅","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_533 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","∅","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_534 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","∅","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_535 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","∅","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_536 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","∅","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_537 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","∅","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_538 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","∅","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_539 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","∅","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_540 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","∅","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_541 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","∅","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_542 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","∅","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_543 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","∅","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_544 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","∅","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_545 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","∅","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_532 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","∅","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_533
  · exact partG37c_7_534
  · exact partG37c_7_535
  · exact partG37c_7_536
  · exact partG37c_7_537
  · exact partG37c_7_538
  · exact partG37c_7_539
  · exact partG37c_7_540
  · exact partG37c_7_541
  · exact partG37c_7_542
  · exact partG37c_7_543
  · exact partG37c_7_544
  · exact partG37c_7_545
theorem partG37c_7_531 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","∅","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_532
theorem partG37c_7_546 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","∅","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_547 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","∅","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_548 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","∅","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_549 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","∅","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_552 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","∅","j","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_553 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","∅","j","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_554 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","∅","j","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_555 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","∅","j","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_556 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","∅","j","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_557 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","∅","j","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_558 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","∅","j","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_559 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","∅","j","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_560 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","∅","j","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_561 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","∅","j","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_562 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","∅","j","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_563 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","∅","j","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_564 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","∅","j","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_551 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","∅","j","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_552
  · exact partG37c_7_553
  · exact partG37c_7_554
  · exact partG37c_7_555
  · exact partG37c_7_556
  · exact partG37c_7_557
  · exact partG37c_7_558
  · exact partG37c_7_559
  · exact partG37c_7_560
  · exact partG37c_7_561
  · exact partG37c_7_562
  · exact partG37c_7_563
  · exact partG37c_7_564
theorem partG37c_7_550 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","∅","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_551
end ProductiveSubjectGua
