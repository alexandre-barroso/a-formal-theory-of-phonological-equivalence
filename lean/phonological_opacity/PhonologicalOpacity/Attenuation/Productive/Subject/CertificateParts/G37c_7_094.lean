import PhonologicalOpacity.Attenuation.Productive.Subject.CertificateParts.G37c_7_093
namespace ProductiveSubjectGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partG37c_7_7527 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɔ","j","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7528 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɔ","j","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7529 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɔ","j","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7530 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɔ","j","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7517 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɔ","j","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_7518
  · exact partG37c_7_7519
  · exact partG37c_7_7520
  · exact partG37c_7_7521
  · exact partG37c_7_7522
  · exact partG37c_7_7523
  · exact partG37c_7_7524
  · exact partG37c_7_7525
  · exact partG37c_7_7526
  · exact partG37c_7_7527
  · exact partG37c_7_7528
  · exact partG37c_7_7529
  · exact partG37c_7_7530
theorem partG37c_7_7516 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɔ","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_7517
theorem partG37c_7_7531 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɔ","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7476 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_7477
  · exact partG37c_7_7492
  · exact partG37c_7_7493
  · exact partG37c_7_7494
  · exact partG37c_7_7495
  · exact partG37c_7_7496
  · exact partG37c_7_7497
  · exact partG37c_7_7512
  · exact partG37c_7_7513
  · exact partG37c_7_7514
  · exact partG37c_7_7515
  · exact partG37c_7_7516
  · exact partG37c_7_7531
theorem partG37c_7_7533 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","o","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7534 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","o","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7535 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","o","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7536 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","o","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7537 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","o","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7538 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","o","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7541 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","o","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7542 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","o","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7543 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","o","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7544 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","o","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7545 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","o","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7546 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","o","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7547 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","o","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7548 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","o","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7549 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","o","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7550 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","o","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7551 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","o","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7552 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","o","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7553 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","o","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7540 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","o","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_7541
  · exact partG37c_7_7542
  · exact partG37c_7_7543
  · exact partG37c_7_7544
  · exact partG37c_7_7545
  · exact partG37c_7_7546
  · exact partG37c_7_7547
  · exact partG37c_7_7548
  · exact partG37c_7_7549
  · exact partG37c_7_7550
  · exact partG37c_7_7551
  · exact partG37c_7_7552
  · exact partG37c_7_7553
theorem partG37c_7_7539 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","o","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_7540
theorem partG37c_7_7554 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","o","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7555 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","o","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7556 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","o","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7557 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","o","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7558 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","o","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7559 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","o","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7532 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_7533
  · exact partG37c_7_7534
  · exact partG37c_7_7535
  · exact partG37c_7_7536
  · exact partG37c_7_7537
  · exact partG37c_7_7538
  · exact partG37c_7_7539
  · exact partG37c_7_7554
  · exact partG37c_7_7555
  · exact partG37c_7_7556
  · exact partG37c_7_7557
  · exact partG37c_7_7558
  · exact partG37c_7_7559
theorem partG37c_7_7563 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ʊ","∅","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7564 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ʊ","∅","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7565 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ʊ","∅","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7566 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ʊ","∅","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7567 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ʊ","∅","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7568 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ʊ","∅","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7569 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ʊ","∅","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7570 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ʊ","∅","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7571 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ʊ","∅","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7572 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ʊ","∅","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7573 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ʊ","∅","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7574 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ʊ","∅","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7575 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ʊ","∅","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7562 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ʊ","∅","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_7563
  · exact partG37c_7_7564
  · exact partG37c_7_7565
  · exact partG37c_7_7566
  · exact partG37c_7_7567
  · exact partG37c_7_7568
  · exact partG37c_7_7569
  · exact partG37c_7_7570
  · exact partG37c_7_7571
  · exact partG37c_7_7572
  · exact partG37c_7_7573
  · exact partG37c_7_7574
  · exact partG37c_7_7575
theorem partG37c_7_7561 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ʊ","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_7562
theorem partG37c_7_7576 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ʊ","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7577 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ʊ","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7578 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ʊ","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7579 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ʊ","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7580 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ʊ","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7583 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ʊ","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7584 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ʊ","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7585 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ʊ","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7586 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ʊ","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7587 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ʊ","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7588 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ʊ","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7589 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ʊ","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7590 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ʊ","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7591 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ʊ","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7592 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ʊ","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7593 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ʊ","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7594 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ʊ","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7595 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ʊ","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7582 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ʊ","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_7583
  · exact partG37c_7_7584
  · exact partG37c_7_7585
  · exact partG37c_7_7586
  · exact partG37c_7_7587
  · exact partG37c_7_7588
  · exact partG37c_7_7589
  · exact partG37c_7_7590
  · exact partG37c_7_7591
  · exact partG37c_7_7592
  · exact partG37c_7_7593
  · exact partG37c_7_7594
  · exact partG37c_7_7595
theorem partG37c_7_7581 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ʊ","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_7582
theorem partG37c_7_7596 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ʊ","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7597 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ʊ","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7598 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ʊ","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7599 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ʊ","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7602 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ʊ","j","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7603 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ʊ","j","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7604 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ʊ","j","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7605 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ʊ","j","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7606 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ʊ","j","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
end ProductiveSubjectGua
