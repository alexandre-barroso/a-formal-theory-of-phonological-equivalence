import PhonologicalOpacity.Attenuation.Productive.Baseline.CertificateParts.G37c_7_056
namespace ProductiveGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partG37c_7_4567 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","i","∅","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4568 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","i","∅","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4569 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","i","∅","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4556 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","i","∅","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_4557
  · exact partG37c_7_4558
  · exact partG37c_7_4559
  · exact partG37c_7_4560
  · exact partG37c_7_4561
  · exact partG37c_7_4562
  · exact partG37c_7_4563
  · exact partG37c_7_4564
  · exact partG37c_7_4565
  · exact partG37c_7_4566
  · exact partG37c_7_4567
  · exact partG37c_7_4568
  · exact partG37c_7_4569
theorem partG37c_7_4555 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","i","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_4556
theorem partG37c_7_4570 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","i","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4571 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","i","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4572 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","i","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4573 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","i","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4574 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","i","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4577 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","i","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4578 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","i","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4579 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","i","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4580 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","i","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4581 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","i","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4582 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","i","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4583 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","i","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4584 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","i","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4585 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","i","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4586 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","i","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4587 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","i","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4588 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","i","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4589 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","i","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4576 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","i","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_4577
  · exact partG37c_7_4578
  · exact partG37c_7_4579
  · exact partG37c_7_4580
  · exact partG37c_7_4581
  · exact partG37c_7_4582
  · exact partG37c_7_4583
  · exact partG37c_7_4584
  · exact partG37c_7_4585
  · exact partG37c_7_4586
  · exact partG37c_7_4587
  · exact partG37c_7_4588
  · exact partG37c_7_4589
theorem partG37c_7_4575 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","i","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_4576
theorem partG37c_7_4590 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","i","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4591 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","i","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4592 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","i","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4593 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","i","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4596 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","i","j","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4597 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","i","j","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4598 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","i","j","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4599 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","i","j","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4600 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","i","j","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4601 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","i","j","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4602 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","i","j","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4603 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","i","j","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4604 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","i","j","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4605 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","i","j","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4606 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","i","j","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4607 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","i","j","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4608 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","i","j","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4595 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","i","j","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_4596
  · exact partG37c_7_4597
  · exact partG37c_7_4598
  · exact partG37c_7_4599
  · exact partG37c_7_4600
  · exact partG37c_7_4601
  · exact partG37c_7_4602
  · exact partG37c_7_4603
  · exact partG37c_7_4604
  · exact partG37c_7_4605
  · exact partG37c_7_4606
  · exact partG37c_7_4607
  · exact partG37c_7_4608
theorem partG37c_7_4594 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","i","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_4595
theorem partG37c_7_4609 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","i","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4554 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_4555
  · exact partG37c_7_4570
  · exact partG37c_7_4571
  · exact partG37c_7_4572
  · exact partG37c_7_4573
  · exact partG37c_7_4574
  · exact partG37c_7_4575
  · exact partG37c_7_4590
  · exact partG37c_7_4591
  · exact partG37c_7_4592
  · exact partG37c_7_4593
  · exact partG37c_7_4594
  · exact partG37c_7_4609
theorem partG37c_7_4613 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɔ","∅","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4614 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɔ","∅","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4615 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɔ","∅","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4616 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɔ","∅","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4617 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɔ","∅","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4618 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɔ","∅","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4619 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɔ","∅","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4620 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɔ","∅","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4621 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɔ","∅","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4622 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɔ","∅","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4623 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɔ","∅","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4624 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɔ","∅","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4625 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɔ","∅","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4612 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɔ","∅","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_4613
  · exact partG37c_7_4614
  · exact partG37c_7_4615
  · exact partG37c_7_4616
  · exact partG37c_7_4617
  · exact partG37c_7_4618
  · exact partG37c_7_4619
  · exact partG37c_7_4620
  · exact partG37c_7_4621
  · exact partG37c_7_4622
  · exact partG37c_7_4623
  · exact partG37c_7_4624
  · exact partG37c_7_4625
theorem partG37c_7_4611 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɔ","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_4612
theorem partG37c_7_4626 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɔ","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4627 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɔ","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4628 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɔ","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4629 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɔ","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4630 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɔ","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4633 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɔ","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4634 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɔ","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4635 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɔ","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4636 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɔ","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4637 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɔ","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4638 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɔ","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4639 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɔ","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4640 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɔ","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4641 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɔ","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4642 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɔ","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4643 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɔ","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4644 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɔ","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4645 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɔ","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4632 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɔ","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_4633
  · exact partG37c_7_4634
  · exact partG37c_7_4635
  · exact partG37c_7_4636
  · exact partG37c_7_4637
  · exact partG37c_7_4638
  · exact partG37c_7_4639
  · exact partG37c_7_4640
  · exact partG37c_7_4641
  · exact partG37c_7_4642
  · exact partG37c_7_4643
  · exact partG37c_7_4644
  · exact partG37c_7_4645
end ProductiveGua
