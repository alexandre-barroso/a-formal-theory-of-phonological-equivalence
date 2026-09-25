import PhonologicalOpacity.Attenuation.Productive.Subject.CertificateParts.OR38_1_006
namespace ProductiveSubjectGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partOR38_1_565 : check uOR38 (4) (-2) outOR38 ["a","tʃ","e","s","ɪ","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_566 : check uOR38 (4) (-2) outOR38 ["a","tʃ","e","s","ɪ","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_567 : check uOR38 (4) (-2) outOR38 ["a","tʃ","e","s","ɪ","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_568 : check uOR38 (4) (-2) outOR38 ["a","tʃ","e","s","ɪ","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_569 : check uOR38 (4) (-2) outOR38 ["a","tʃ","e","s","ɪ","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_570 : check uOR38 (4) (-2) outOR38 ["a","tʃ","e","s","ɪ","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_571 : check uOR38 (4) (-2) outOR38 ["a","tʃ","e","s","ɪ","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_572 : check uOR38 (4) (-2) outOR38 ["a","tʃ","e","s","ɪ","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_573 : check uOR38 (4) (-2) outOR38 ["a","tʃ","e","s","ɪ","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_574 : check uOR38 (4) (-2) outOR38 ["a","tʃ","e","s","ɪ","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_575 : check uOR38 (4) (-2) outOR38 ["a","tʃ","e","s","ɪ","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_576 : check uOR38 (4) (-2) outOR38 ["a","tʃ","e","s","ɪ","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_563 : check uOR38 (4) (-2) outOR38 ["a","tʃ","e","s","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_564
  · exact partOR38_1_565
  · exact partOR38_1_566
  · exact partOR38_1_567
  · exact partOR38_1_568
  · exact partOR38_1_569
  · exact partOR38_1_570
  · exact partOR38_1_571
  · exact partOR38_1_572
  · exact partOR38_1_573
  · exact partOR38_1_574
  · exact partOR38_1_575
  · exact partOR38_1_576
theorem partOR38_1_577 : check uOR38 (4) (-2) outOR38 ["a","tʃ","e","s","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_579 : check uOR38 (4) (-2) outOR38 ["a","tʃ","e","s","ɔ","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_580 : check uOR38 (4) (-2) outOR38 ["a","tʃ","e","s","ɔ","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_581 : check uOR38 (4) (-2) outOR38 ["a","tʃ","e","s","ɔ","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_582 : check uOR38 (4) (-2) outOR38 ["a","tʃ","e","s","ɔ","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_583 : check uOR38 (4) (-2) outOR38 ["a","tʃ","e","s","ɔ","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_584 : check uOR38 (4) (-2) outOR38 ["a","tʃ","e","s","ɔ","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_585 : check uOR38 (4) (-2) outOR38 ["a","tʃ","e","s","ɔ","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_586 : check uOR38 (4) (-2) outOR38 ["a","tʃ","e","s","ɔ","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_587 : check uOR38 (4) (-2) outOR38 ["a","tʃ","e","s","ɔ","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_588 : check uOR38 (4) (-2) outOR38 ["a","tʃ","e","s","ɔ","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_589 : check uOR38 (4) (-2) outOR38 ["a","tʃ","e","s","ɔ","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_590 : check uOR38 (4) (-2) outOR38 ["a","tʃ","e","s","ɔ","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_591 : check uOR38 (4) (-2) outOR38 ["a","tʃ","e","s","ɔ","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_578 : check uOR38 (4) (-2) outOR38 ["a","tʃ","e","s","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_579
  · exact partOR38_1_580
  · exact partOR38_1_581
  · exact partOR38_1_582
  · exact partOR38_1_583
  · exact partOR38_1_584
  · exact partOR38_1_585
  · exact partOR38_1_586
  · exact partOR38_1_587
  · exact partOR38_1_588
  · exact partOR38_1_589
  · exact partOR38_1_590
  · exact partOR38_1_591
theorem partOR38_1_592 : check uOR38 (4) (-2) outOR38 ["a","tʃ","e","s","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_594 : check uOR38 (4) (-2) outOR38 ["a","tʃ","e","s","ʊ","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_595 : check uOR38 (4) (-2) outOR38 ["a","tʃ","e","s","ʊ","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_596 : check uOR38 (4) (-2) outOR38 ["a","tʃ","e","s","ʊ","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_597 : check uOR38 (4) (-2) outOR38 ["a","tʃ","e","s","ʊ","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_598 : check uOR38 (4) (-2) outOR38 ["a","tʃ","e","s","ʊ","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_599 : check uOR38 (4) (-2) outOR38 ["a","tʃ","e","s","ʊ","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_600 : check uOR38 (4) (-2) outOR38 ["a","tʃ","e","s","ʊ","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_601 : check uOR38 (4) (-2) outOR38 ["a","tʃ","e","s","ʊ","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_602 : check uOR38 (4) (-2) outOR38 ["a","tʃ","e","s","ʊ","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_603 : check uOR38 (4) (-2) outOR38 ["a","tʃ","e","s","ʊ","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_604 : check uOR38 (4) (-2) outOR38 ["a","tʃ","e","s","ʊ","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_605 : check uOR38 (4) (-2) outOR38 ["a","tʃ","e","s","ʊ","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_606 : check uOR38 (4) (-2) outOR38 ["a","tʃ","e","s","ʊ","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_593 : check uOR38 (4) (-2) outOR38 ["a","tʃ","e","s","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_594
  · exact partOR38_1_595
  · exact partOR38_1_596
  · exact partOR38_1_597
  · exact partOR38_1_598
  · exact partOR38_1_599
  · exact partOR38_1_600
  · exact partOR38_1_601
  · exact partOR38_1_602
  · exact partOR38_1_603
  · exact partOR38_1_604
  · exact partOR38_1_605
  · exact partOR38_1_606
theorem partOR38_1_607 : check uOR38 (4) (-2) outOR38 ["a","tʃ","e","s","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_608 : check uOR38 (4) (-2) outOR38 ["a","tʃ","e","s","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_609 : check uOR38 (4) (-2) outOR38 ["a","tʃ","e","s","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_531 : check uOR38 (4) (-2) outOR38 ["a","tʃ","e","s"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_532
  · exact partOR38_1_533
  · exact partOR38_1_547
  · exact partOR38_1_548
  · exact partOR38_1_562
  · exact partOR38_1_563
  · exact partOR38_1_577
  · exact partOR38_1_578
  · exact partOR38_1_592
  · exact partOR38_1_593
  · exact partOR38_1_607
  · exact partOR38_1_608
  · exact partOR38_1_609
theorem partOR38_1_530 : check uOR38 (4) (-2) outOR38 ["a","tʃ","e"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="s" := by simpa using hx
  subst x
  exact partOR38_1_531
theorem partOR38_1_613 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","∅","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_614 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","∅","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_615 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","∅","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_616 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","∅","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_617 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","∅","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_618 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","∅","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_619 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","∅","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_620 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","∅","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_621 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","∅","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_622 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","∅","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_623 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","∅","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_624 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","∅","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_625 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","∅","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_612 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_613
  · exact partOR38_1_614
  · exact partOR38_1_615
  · exact partOR38_1_616
  · exact partOR38_1_617
  · exact partOR38_1_618
  · exact partOR38_1_619
  · exact partOR38_1_620
  · exact partOR38_1_621
  · exact partOR38_1_622
  · exact partOR38_1_623
  · exact partOR38_1_624
  · exact partOR38_1_625
theorem partOR38_1_627 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","a","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_628 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","a","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_629 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","a","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_630 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","a","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_631 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","a","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_632 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","a","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_633 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","a","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_634 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","a","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_635 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","a","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_636 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","a","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_637 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","a","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_638 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","a","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_639 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","a","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_626 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_627
  · exact partOR38_1_628
  · exact partOR38_1_629
  · exact partOR38_1_630
  · exact partOR38_1_631
  · exact partOR38_1_632
  · exact partOR38_1_633
  · exact partOR38_1_634
  · exact partOR38_1_635
  · exact partOR38_1_636
  · exact partOR38_1_637
  · exact partOR38_1_638
  · exact partOR38_1_639
theorem partOR38_1_641 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","ɜ","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_642 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","ɜ","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_643 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","ɜ","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_644 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","ɜ","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
end ProductiveSubjectGua
