import PhonologicalOpacity.Attenuation.Productive.Subject.CertificateParts.G37c_7_080
namespace ProductiveSubjectGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partG37c_7_6487 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","ɔ","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6488 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","ɔ","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6489 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","ɔ","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6490 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","ɔ","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6491 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","ɔ","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6492 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","ɔ","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6493 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","ɔ","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6494 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","ɔ","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6495 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","ɔ","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6496 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","ɔ","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6497 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","ɔ","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6498 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","ɔ","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6499 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","ɔ","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6486 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","ɔ","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_6487
  · exact partG37c_7_6488
  · exact partG37c_7_6489
  · exact partG37c_7_6490
  · exact partG37c_7_6491
  · exact partG37c_7_6492
  · exact partG37c_7_6493
  · exact partG37c_7_6494
  · exact partG37c_7_6495
  · exact partG37c_7_6496
  · exact partG37c_7_6497
  · exact partG37c_7_6498
  · exact partG37c_7_6499
theorem partG37c_7_6485 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","ɔ","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_6486
theorem partG37c_7_6500 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","ɔ","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6501 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","ɔ","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6502 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","ɔ","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6503 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","ɔ","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6506 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","ɔ","j","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6507 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","ɔ","j","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6508 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","ɔ","j","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6509 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","ɔ","j","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6510 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","ɔ","j","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6511 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","ɔ","j","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6512 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","ɔ","j","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6513 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","ɔ","j","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6514 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","ɔ","j","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6515 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","ɔ","j","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6516 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","ɔ","j","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6517 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","ɔ","j","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6518 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","ɔ","j","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6505 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","ɔ","j","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_6506
  · exact partG37c_7_6507
  · exact partG37c_7_6508
  · exact partG37c_7_6509
  · exact partG37c_7_6510
  · exact partG37c_7_6511
  · exact partG37c_7_6512
  · exact partG37c_7_6513
  · exact partG37c_7_6514
  · exact partG37c_7_6515
  · exact partG37c_7_6516
  · exact partG37c_7_6517
  · exact partG37c_7_6518
theorem partG37c_7_6504 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","ɔ","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_6505
theorem partG37c_7_6519 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","ɔ","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6464 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_6465
  · exact partG37c_7_6480
  · exact partG37c_7_6481
  · exact partG37c_7_6482
  · exact partG37c_7_6483
  · exact partG37c_7_6484
  · exact partG37c_7_6485
  · exact partG37c_7_6500
  · exact partG37c_7_6501
  · exact partG37c_7_6502
  · exact partG37c_7_6503
  · exact partG37c_7_6504
  · exact partG37c_7_6519
theorem partG37c_7_6521 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","o","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6522 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","o","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6523 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","o","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6524 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","o","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6525 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","o","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6526 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","o","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6529 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","o","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6530 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","o","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6531 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","o","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6532 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","o","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6533 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","o","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6534 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","o","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6535 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","o","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6536 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","o","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6537 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","o","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6538 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","o","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6539 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","o","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6540 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","o","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6541 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","o","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6528 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","o","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_6529
  · exact partG37c_7_6530
  · exact partG37c_7_6531
  · exact partG37c_7_6532
  · exact partG37c_7_6533
  · exact partG37c_7_6534
  · exact partG37c_7_6535
  · exact partG37c_7_6536
  · exact partG37c_7_6537
  · exact partG37c_7_6538
  · exact partG37c_7_6539
  · exact partG37c_7_6540
  · exact partG37c_7_6541
theorem partG37c_7_6527 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","o","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_6528
theorem partG37c_7_6542 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","o","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6543 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","o","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6544 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","o","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6545 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","o","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6546 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","o","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6547 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","o","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6520 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_6521
  · exact partG37c_7_6522
  · exact partG37c_7_6523
  · exact partG37c_7_6524
  · exact partG37c_7_6525
  · exact partG37c_7_6526
  · exact partG37c_7_6527
  · exact partG37c_7_6542
  · exact partG37c_7_6543
  · exact partG37c_7_6544
  · exact partG37c_7_6545
  · exact partG37c_7_6546
  · exact partG37c_7_6547
theorem partG37c_7_6551 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","ʊ","∅","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6552 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","ʊ","∅","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6553 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","ʊ","∅","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6554 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","ʊ","∅","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6555 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","ʊ","∅","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6556 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","ʊ","∅","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6557 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","ʊ","∅","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6558 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","ʊ","∅","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6559 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","ʊ","∅","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6560 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","ʊ","∅","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6561 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","ʊ","∅","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6562 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","ʊ","∅","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6563 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","ʊ","∅","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6550 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","ʊ","∅","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_6551
  · exact partG37c_7_6552
  · exact partG37c_7_6553
  · exact partG37c_7_6554
  · exact partG37c_7_6555
  · exact partG37c_7_6556
  · exact partG37c_7_6557
  · exact partG37c_7_6558
  · exact partG37c_7_6559
  · exact partG37c_7_6560
  · exact partG37c_7_6561
  · exact partG37c_7_6562
  · exact partG37c_7_6563
theorem partG37c_7_6549 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","ʊ","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_6550
theorem partG37c_7_6564 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","ʊ","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
end ProductiveSubjectGua
