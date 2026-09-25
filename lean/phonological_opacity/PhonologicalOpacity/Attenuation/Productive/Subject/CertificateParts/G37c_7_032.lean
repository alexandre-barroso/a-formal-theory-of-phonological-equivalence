import PhonologicalOpacity.Attenuation.Productive.Subject.CertificateParts.G37c_7_031
namespace ProductiveSubjectGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partG37c_7_2565 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ɜ","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2566 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ɜ","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2569 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ɜ","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2570 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ɜ","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2571 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ɜ","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2572 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ɜ","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2573 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ɜ","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2574 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ɜ","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2575 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ɜ","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2576 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ɜ","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2577 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ɜ","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2578 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ɜ","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2579 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ɜ","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2580 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ɜ","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2581 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ɜ","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2568 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ɜ","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_2569
  · exact partG37c_7_2570
  · exact partG37c_7_2571
  · exact partG37c_7_2572
  · exact partG37c_7_2573
  · exact partG37c_7_2574
  · exact partG37c_7_2575
  · exact partG37c_7_2576
  · exact partG37c_7_2577
  · exact partG37c_7_2578
  · exact partG37c_7_2579
  · exact partG37c_7_2580
  · exact partG37c_7_2581
theorem partG37c_7_2567 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ɜ","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_2568
theorem partG37c_7_2582 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ɜ","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2583 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ɜ","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2584 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ɜ","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2585 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ɜ","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2586 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ɜ","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2587 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ɜ","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2560 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_2561
  · exact partG37c_7_2562
  · exact partG37c_7_2563
  · exact partG37c_7_2564
  · exact partG37c_7_2565
  · exact partG37c_7_2566
  · exact partG37c_7_2567
  · exact partG37c_7_2582
  · exact partG37c_7_2583
  · exact partG37c_7_2584
  · exact partG37c_7_2585
  · exact partG37c_7_2586
  · exact partG37c_7_2587
theorem partG37c_7_2591 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ɛ","∅","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2592 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ɛ","∅","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2593 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ɛ","∅","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2594 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ɛ","∅","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2595 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ɛ","∅","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2596 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ɛ","∅","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2597 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ɛ","∅","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2598 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ɛ","∅","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2599 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ɛ","∅","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2600 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ɛ","∅","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2601 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ɛ","∅","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2602 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ɛ","∅","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2603 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ɛ","∅","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2590 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ɛ","∅","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_2591
  · exact partG37c_7_2592
  · exact partG37c_7_2593
  · exact partG37c_7_2594
  · exact partG37c_7_2595
  · exact partG37c_7_2596
  · exact partG37c_7_2597
  · exact partG37c_7_2598
  · exact partG37c_7_2599
  · exact partG37c_7_2600
  · exact partG37c_7_2601
  · exact partG37c_7_2602
  · exact partG37c_7_2603
theorem partG37c_7_2589 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ɛ","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_2590
theorem partG37c_7_2604 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ɛ","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2605 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ɛ","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2606 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ɛ","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2607 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ɛ","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2608 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ɛ","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2611 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ɛ","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2612 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ɛ","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2613 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ɛ","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2614 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ɛ","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2615 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ɛ","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2616 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ɛ","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2617 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ɛ","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2618 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ɛ","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2619 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ɛ","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2620 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ɛ","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2621 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ɛ","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2622 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ɛ","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2623 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ɛ","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2610 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ɛ","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_2611
  · exact partG37c_7_2612
  · exact partG37c_7_2613
  · exact partG37c_7_2614
  · exact partG37c_7_2615
  · exact partG37c_7_2616
  · exact partG37c_7_2617
  · exact partG37c_7_2618
  · exact partG37c_7_2619
  · exact partG37c_7_2620
  · exact partG37c_7_2621
  · exact partG37c_7_2622
  · exact partG37c_7_2623
theorem partG37c_7_2609 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ɛ","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_2610
theorem partG37c_7_2624 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ɛ","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2625 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ɛ","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2626 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ɛ","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2627 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ɛ","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2630 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ɛ","j","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2631 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ɛ","j","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2632 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ɛ","j","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2633 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ɛ","j","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2634 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ɛ","j","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2635 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ɛ","j","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2636 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ɛ","j","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2637 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ɛ","j","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2638 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ɛ","j","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2639 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ɛ","j","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2640 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ɛ","j","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2641 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ɛ","j","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2642 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ɛ","j","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2629 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ɛ","j","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_2630
  · exact partG37c_7_2631
  · exact partG37c_7_2632
  · exact partG37c_7_2633
  · exact partG37c_7_2634
  · exact partG37c_7_2635
  · exact partG37c_7_2636
  · exact partG37c_7_2637
  · exact partG37c_7_2638
  · exact partG37c_7_2639
  · exact partG37c_7_2640
  · exact partG37c_7_2641
  · exact partG37c_7_2642
theorem partG37c_7_2628 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ɛ","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_2629
theorem partG37c_7_2643 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ɛ","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2588 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_2589
  · exact partG37c_7_2604
  · exact partG37c_7_2605
  · exact partG37c_7_2606
  · exact partG37c_7_2607
  · exact partG37c_7_2608
  · exact partG37c_7_2609
  · exact partG37c_7_2624
  · exact partG37c_7_2625
  · exact partG37c_7_2626
  · exact partG37c_7_2627
  · exact partG37c_7_2628
  · exact partG37c_7_2643
end ProductiveSubjectGua
