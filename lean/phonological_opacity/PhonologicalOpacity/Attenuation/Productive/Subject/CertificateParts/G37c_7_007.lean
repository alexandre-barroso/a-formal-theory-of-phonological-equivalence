import PhonologicalOpacity.Attenuation.Productive.Subject.CertificateParts.G37c_7_006
namespace ProductiveSubjectGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partG37c_7_565 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","∅","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_510 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_511
  · exact partG37c_7_526
  · exact partG37c_7_527
  · exact partG37c_7_528
  · exact partG37c_7_529
  · exact partG37c_7_530
  · exact partG37c_7_531
  · exact partG37c_7_546
  · exact partG37c_7_547
  · exact partG37c_7_548
  · exact partG37c_7_549
  · exact partG37c_7_550
  · exact partG37c_7_565
theorem partG37c_7_569 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","a","∅","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_570 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","a","∅","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_571 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","a","∅","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_572 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","a","∅","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_573 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","a","∅","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_574 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","a","∅","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_575 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","a","∅","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_576 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","a","∅","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_577 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","a","∅","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_578 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","a","∅","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_579 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","a","∅","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_580 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","a","∅","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_581 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","a","∅","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_568 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","a","∅","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_569
  · exact partG37c_7_570
  · exact partG37c_7_571
  · exact partG37c_7_572
  · exact partG37c_7_573
  · exact partG37c_7_574
  · exact partG37c_7_575
  · exact partG37c_7_576
  · exact partG37c_7_577
  · exact partG37c_7_578
  · exact partG37c_7_579
  · exact partG37c_7_580
  · exact partG37c_7_581
theorem partG37c_7_567 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","a","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_568
theorem partG37c_7_582 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","a","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_583 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","a","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_584 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","a","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_585 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","a","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_586 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","a","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_589 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","a","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_590 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","a","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_591 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","a","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_592 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","a","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_593 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","a","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_594 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","a","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_595 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","a","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_596 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","a","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_597 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","a","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_598 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","a","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_599 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","a","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_600 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","a","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_601 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","a","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_588 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","a","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_589
  · exact partG37c_7_590
  · exact partG37c_7_591
  · exact partG37c_7_592
  · exact partG37c_7_593
  · exact partG37c_7_594
  · exact partG37c_7_595
  · exact partG37c_7_596
  · exact partG37c_7_597
  · exact partG37c_7_598
  · exact partG37c_7_599
  · exact partG37c_7_600
  · exact partG37c_7_601
theorem partG37c_7_587 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","a","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_588
theorem partG37c_7_602 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","a","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_603 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","a","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_604 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","a","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_605 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","a","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_608 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","a","j","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_609 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","a","j","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_610 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","a","j","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_611 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","a","j","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_612 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","a","j","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_613 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","a","j","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_614 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","a","j","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_615 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","a","j","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_616 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","a","j","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_617 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","a","j","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_618 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","a","j","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_619 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","a","j","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_620 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","a","j","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_607 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","a","j","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_608
  · exact partG37c_7_609
  · exact partG37c_7_610
  · exact partG37c_7_611
  · exact partG37c_7_612
  · exact partG37c_7_613
  · exact partG37c_7_614
  · exact partG37c_7_615
  · exact partG37c_7_616
  · exact partG37c_7_617
  · exact partG37c_7_618
  · exact partG37c_7_619
  · exact partG37c_7_620
theorem partG37c_7_606 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","a","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_607
theorem partG37c_7_621 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","a","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_566 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_567
  · exact partG37c_7_582
  · exact partG37c_7_583
  · exact partG37c_7_584
  · exact partG37c_7_585
  · exact partG37c_7_586
  · exact partG37c_7_587
  · exact partG37c_7_602
  · exact partG37c_7_603
  · exact partG37c_7_604
  · exact partG37c_7_605
  · exact partG37c_7_606
  · exact partG37c_7_621
theorem partG37c_7_625 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɜ","∅","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_626 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɜ","∅","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_627 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɜ","∅","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_628 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɜ","∅","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_629 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɜ","∅","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_630 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɜ","∅","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_631 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɜ","∅","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_632 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɜ","∅","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_633 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɜ","∅","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_634 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɜ","∅","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_635 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɜ","∅","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_636 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɜ","∅","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_637 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɜ","∅","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_624 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɜ","∅","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_625
  · exact partG37c_7_626
  · exact partG37c_7_627
  · exact partG37c_7_628
  · exact partG37c_7_629
  · exact partG37c_7_630
  · exact partG37c_7_631
  · exact partG37c_7_632
  · exact partG37c_7_633
  · exact partG37c_7_634
  · exact partG37c_7_635
  · exact partG37c_7_636
  · exact partG37c_7_637
theorem partG37c_7_623 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɜ","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_624
theorem partG37c_7_638 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɜ","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_639 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɜ","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_640 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɜ","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_641 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɜ","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_642 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɜ","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_645 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɜ","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_646 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɜ","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
end ProductiveSubjectGua
