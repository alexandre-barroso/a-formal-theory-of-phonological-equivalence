import PhonologicalOpacity.Attenuation.Productive.Subject.CertificateParts.G37c_7_043
namespace ProductiveSubjectGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partG37c_7_3525 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ʊ","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3528 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ʊ","j","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3529 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ʊ","j","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3530 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ʊ","j","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3531 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ʊ","j","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3532 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ʊ","j","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3533 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ʊ","j","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3534 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ʊ","j","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3535 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ʊ","j","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3536 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ʊ","j","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3537 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ʊ","j","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3538 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ʊ","j","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3539 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ʊ","j","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3540 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ʊ","j","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3527 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ʊ","j","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_3528
  · exact partG37c_7_3529
  · exact partG37c_7_3530
  · exact partG37c_7_3531
  · exact partG37c_7_3532
  · exact partG37c_7_3533
  · exact partG37c_7_3534
  · exact partG37c_7_3535
  · exact partG37c_7_3536
  · exact partG37c_7_3537
  · exact partG37c_7_3538
  · exact partG37c_7_3539
  · exact partG37c_7_3540
theorem partG37c_7_3526 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ʊ","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_3527
theorem partG37c_7_3541 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ʊ","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3486 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_3487
  · exact partG37c_7_3502
  · exact partG37c_7_3503
  · exact partG37c_7_3504
  · exact partG37c_7_3505
  · exact partG37c_7_3506
  · exact partG37c_7_3507
  · exact partG37c_7_3522
  · exact partG37c_7_3523
  · exact partG37c_7_3524
  · exact partG37c_7_3525
  · exact partG37c_7_3526
  · exact partG37c_7_3541
theorem partG37c_7_3545 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","u","∅","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3546 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","u","∅","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3547 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","u","∅","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3548 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","u","∅","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3549 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","u","∅","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3550 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","u","∅","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3551 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","u","∅","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3552 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","u","∅","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3553 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","u","∅","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3554 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","u","∅","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3555 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","u","∅","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3556 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","u","∅","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3557 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","u","∅","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3544 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","u","∅","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_3545
  · exact partG37c_7_3546
  · exact partG37c_7_3547
  · exact partG37c_7_3548
  · exact partG37c_7_3549
  · exact partG37c_7_3550
  · exact partG37c_7_3551
  · exact partG37c_7_3552
  · exact partG37c_7_3553
  · exact partG37c_7_3554
  · exact partG37c_7_3555
  · exact partG37c_7_3556
  · exact partG37c_7_3557
theorem partG37c_7_3543 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","u","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_3544
theorem partG37c_7_3558 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","u","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3559 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","u","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3560 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","u","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3561 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","u","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3562 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","u","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3565 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","u","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3566 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","u","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3567 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","u","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3568 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","u","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3569 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","u","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3570 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","u","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3571 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","u","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3572 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","u","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3573 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","u","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3574 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","u","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3575 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","u","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3576 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","u","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3577 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","u","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3564 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","u","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_3565
  · exact partG37c_7_3566
  · exact partG37c_7_3567
  · exact partG37c_7_3568
  · exact partG37c_7_3569
  · exact partG37c_7_3570
  · exact partG37c_7_3571
  · exact partG37c_7_3572
  · exact partG37c_7_3573
  · exact partG37c_7_3574
  · exact partG37c_7_3575
  · exact partG37c_7_3576
  · exact partG37c_7_3577
theorem partG37c_7_3563 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","u","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_3564
theorem partG37c_7_3578 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","u","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3579 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","u","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3580 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","u","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3581 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","u","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3584 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","u","j","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3585 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","u","j","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3586 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","u","j","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3587 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","u","j","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3588 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","u","j","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3589 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","u","j","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3590 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","u","j","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3591 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","u","j","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3592 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","u","j","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3593 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","u","j","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3594 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","u","j","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3595 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","u","j","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3596 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","u","j","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3583 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","u","j","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_3584
  · exact partG37c_7_3585
  · exact partG37c_7_3586
  · exact partG37c_7_3587
  · exact partG37c_7_3588
  · exact partG37c_7_3589
  · exact partG37c_7_3590
  · exact partG37c_7_3591
  · exact partG37c_7_3592
  · exact partG37c_7_3593
  · exact partG37c_7_3594
  · exact partG37c_7_3595
  · exact partG37c_7_3596
theorem partG37c_7_3582 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","u","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_3583
theorem partG37c_7_3597 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","u","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3542 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_3543
  · exact partG37c_7_3558
  · exact partG37c_7_3559
  · exact partG37c_7_3560
  · exact partG37c_7_3561
  · exact partG37c_7_3562
  · exact partG37c_7_3563
  · exact partG37c_7_3578
  · exact partG37c_7_3579
  · exact partG37c_7_3580
  · exact partG37c_7_3581
  · exact partG37c_7_3582
  · exact partG37c_7_3597
theorem partG37c_7_3601 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","j","∅","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3602 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","j","∅","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3603 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","j","∅","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3604 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","j","∅","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3605 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","j","∅","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3606 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","j","∅","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
end ProductiveSubjectGua
