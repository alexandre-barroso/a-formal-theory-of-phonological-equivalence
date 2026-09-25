import PhonologicalOpacity.Attenuation.Productive.Subject.CertificateParts.G34a_1_032
namespace ProductiveSubjectGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partG34a_1_2632 : check uG34a (3) (-2) outG34a ["a","h","ʊ","t","∅","ɔ","k"] [["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="p" := by simpa using hx
  subst x
  exact partG34a_1_2633
theorem partG34a_1_2631 : check uG34a (3) (-2) outG34a ["a","h","ʊ","t","∅","ɔ"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="k" := by simpa using hx
  subst x
  exact partG34a_1_2632
theorem partG34a_1_2647 : check uG34a (3) (-2) outG34a ["a","h","ʊ","t","∅","o"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_2648 : check uG34a (3) (-2) outG34a ["a","h","ʊ","t","∅","ʊ"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_2649 : check uG34a (3) (-2) outG34a ["a","h","ʊ","t","∅","u"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_2650 : check uG34a (3) (-2) outG34a ["a","h","ʊ","t","∅","j"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_2651 : check uG34a (3) (-2) outG34a ["a","h","ʊ","t","∅","w"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_2623 : check uG34a (3) (-2) outG34a ["a","h","ʊ","t","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG34a_1_2624
  · exact partG34a_1_2625
  · exact partG34a_1_2626
  · exact partG34a_1_2627
  · exact partG34a_1_2628
  · exact partG34a_1_2629
  · exact partG34a_1_2630
  · exact partG34a_1_2631
  · exact partG34a_1_2647
  · exact partG34a_1_2648
  · exact partG34a_1_2649
  · exact partG34a_1_2650
  · exact partG34a_1_2651
theorem partG34a_1_2653 : check uG34a (3) (-2) outG34a ["a","h","ʊ","t","a","∅"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_2654 : check uG34a (3) (-2) outG34a ["a","h","ʊ","t","a","a"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_2655 : check uG34a (3) (-2) outG34a ["a","h","ʊ","t","a","ɜ"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_2656 : check uG34a (3) (-2) outG34a ["a","h","ʊ","t","a","ɛ"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_2657 : check uG34a (3) (-2) outG34a ["a","h","ʊ","t","a","e"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_2658 : check uG34a (3) (-2) outG34a ["a","h","ʊ","t","a","ɪ"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_2659 : check uG34a (3) (-2) outG34a ["a","h","ʊ","t","a","i"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_2663 : check uG34a (3) (-2) outG34a ["a","h","ʊ","t","a","ɔ","k","p","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_2664 : check uG34a (3) (-2) outG34a ["a","h","ʊ","t","a","ɔ","k","p","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_2665 : check uG34a (3) (-2) outG34a ["a","h","ʊ","t","a","ɔ","k","p","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_2666 : check uG34a (3) (-2) outG34a ["a","h","ʊ","t","a","ɔ","k","p","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_2667 : check uG34a (3) (-2) outG34a ["a","h","ʊ","t","a","ɔ","k","p","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_2668 : check uG34a (3) (-2) outG34a ["a","h","ʊ","t","a","ɔ","k","p","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_2669 : check uG34a (3) (-2) outG34a ["a","h","ʊ","t","a","ɔ","k","p","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_2670 : check uG34a (3) (-2) outG34a ["a","h","ʊ","t","a","ɔ","k","p","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_2671 : check uG34a (3) (-2) outG34a ["a","h","ʊ","t","a","ɔ","k","p","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_2672 : check uG34a (3) (-2) outG34a ["a","h","ʊ","t","a","ɔ","k","p","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_2673 : check uG34a (3) (-2) outG34a ["a","h","ʊ","t","a","ɔ","k","p","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_2674 : check uG34a (3) (-2) outG34a ["a","h","ʊ","t","a","ɔ","k","p","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_2675 : check uG34a (3) (-2) outG34a ["a","h","ʊ","t","a","ɔ","k","p","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_2662 : check uG34a (3) (-2) outG34a ["a","h","ʊ","t","a","ɔ","k","p"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG34a_1_2663
  · exact partG34a_1_2664
  · exact partG34a_1_2665
  · exact partG34a_1_2666
  · exact partG34a_1_2667
  · exact partG34a_1_2668
  · exact partG34a_1_2669
  · exact partG34a_1_2670
  · exact partG34a_1_2671
  · exact partG34a_1_2672
  · exact partG34a_1_2673
  · exact partG34a_1_2674
  · exact partG34a_1_2675
theorem partG34a_1_2661 : check uG34a (3) (-2) outG34a ["a","h","ʊ","t","a","ɔ","k"] [["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="p" := by simpa using hx
  subst x
  exact partG34a_1_2662
theorem partG34a_1_2660 : check uG34a (3) (-2) outG34a ["a","h","ʊ","t","a","ɔ"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="k" := by simpa using hx
  subst x
  exact partG34a_1_2661
theorem partG34a_1_2676 : check uG34a (3) (-2) outG34a ["a","h","ʊ","t","a","o"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_2677 : check uG34a (3) (-2) outG34a ["a","h","ʊ","t","a","ʊ"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_2678 : check uG34a (3) (-2) outG34a ["a","h","ʊ","t","a","u"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_2679 : check uG34a (3) (-2) outG34a ["a","h","ʊ","t","a","j"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_2680 : check uG34a (3) (-2) outG34a ["a","h","ʊ","t","a","w"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_2652 : check uG34a (3) (-2) outG34a ["a","h","ʊ","t","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG34a_1_2653
  · exact partG34a_1_2654
  · exact partG34a_1_2655
  · exact partG34a_1_2656
  · exact partG34a_1_2657
  · exact partG34a_1_2658
  · exact partG34a_1_2659
  · exact partG34a_1_2660
  · exact partG34a_1_2676
  · exact partG34a_1_2677
  · exact partG34a_1_2678
  · exact partG34a_1_2679
  · exact partG34a_1_2680
theorem partG34a_1_2685 : check uG34a (3) (-2) outG34a ["a","h","ʊ","t","ɜ","∅","k","p","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_2686 : check uG34a (3) (-2) outG34a ["a","h","ʊ","t","ɜ","∅","k","p","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_2687 : check uG34a (3) (-2) outG34a ["a","h","ʊ","t","ɜ","∅","k","p","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_2688 : check uG34a (3) (-2) outG34a ["a","h","ʊ","t","ɜ","∅","k","p","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_2689 : check uG34a (3) (-2) outG34a ["a","h","ʊ","t","ɜ","∅","k","p","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_2690 : check uG34a (3) (-2) outG34a ["a","h","ʊ","t","ɜ","∅","k","p","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_2691 : check uG34a (3) (-2) outG34a ["a","h","ʊ","t","ɜ","∅","k","p","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_2692 : check uG34a (3) (-2) outG34a ["a","h","ʊ","t","ɜ","∅","k","p","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_2693 : check uG34a (3) (-2) outG34a ["a","h","ʊ","t","ɜ","∅","k","p","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_2694 : check uG34a (3) (-2) outG34a ["a","h","ʊ","t","ɜ","∅","k","p","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_2695 : check uG34a (3) (-2) outG34a ["a","h","ʊ","t","ɜ","∅","k","p","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_2696 : check uG34a (3) (-2) outG34a ["a","h","ʊ","t","ɜ","∅","k","p","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_2697 : check uG34a (3) (-2) outG34a ["a","h","ʊ","t","ɜ","∅","k","p","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_2684 : check uG34a (3) (-2) outG34a ["a","h","ʊ","t","ɜ","∅","k","p"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG34a_1_2685
  · exact partG34a_1_2686
  · exact partG34a_1_2687
  · exact partG34a_1_2688
  · exact partG34a_1_2689
  · exact partG34a_1_2690
  · exact partG34a_1_2691
  · exact partG34a_1_2692
  · exact partG34a_1_2693
  · exact partG34a_1_2694
  · exact partG34a_1_2695
  · exact partG34a_1_2696
  · exact partG34a_1_2697
theorem partG34a_1_2683 : check uG34a (3) (-2) outG34a ["a","h","ʊ","t","ɜ","∅","k"] [["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="p" := by simpa using hx
  subst x
  exact partG34a_1_2684
theorem partG34a_1_2682 : check uG34a (3) (-2) outG34a ["a","h","ʊ","t","ɜ","∅"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="k" := by simpa using hx
  subst x
  exact partG34a_1_2683
theorem partG34a_1_2698 : check uG34a (3) (-2) outG34a ["a","h","ʊ","t","ɜ","a"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_2699 : check uG34a (3) (-2) outG34a ["a","h","ʊ","t","ɜ","ɜ"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_2700 : check uG34a (3) (-2) outG34a ["a","h","ʊ","t","ɜ","ɛ"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_2701 : check uG34a (3) (-2) outG34a ["a","h","ʊ","t","ɜ","e"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_2702 : check uG34a (3) (-2) outG34a ["a","h","ʊ","t","ɜ","ɪ"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_2703 : check uG34a (3) (-2) outG34a ["a","h","ʊ","t","ɜ","i"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_2707 : check uG34a (3) (-2) outG34a ["a","h","ʊ","t","ɜ","ɔ","k","p","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_2708 : check uG34a (3) (-2) outG34a ["a","h","ʊ","t","ɜ","ɔ","k","p","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_2709 : check uG34a (3) (-2) outG34a ["a","h","ʊ","t","ɜ","ɔ","k","p","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_2710 : check uG34a (3) (-2) outG34a ["a","h","ʊ","t","ɜ","ɔ","k","p","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_2711 : check uG34a (3) (-2) outG34a ["a","h","ʊ","t","ɜ","ɔ","k","p","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_2712 : check uG34a (3) (-2) outG34a ["a","h","ʊ","t","ɜ","ɔ","k","p","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_2713 : check uG34a (3) (-2) outG34a ["a","h","ʊ","t","ɜ","ɔ","k","p","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_2714 : check uG34a (3) (-2) outG34a ["a","h","ʊ","t","ɜ","ɔ","k","p","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_2715 : check uG34a (3) (-2) outG34a ["a","h","ʊ","t","ɜ","ɔ","k","p","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_2716 : check uG34a (3) (-2) outG34a ["a","h","ʊ","t","ɜ","ɔ","k","p","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_2717 : check uG34a (3) (-2) outG34a ["a","h","ʊ","t","ɜ","ɔ","k","p","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_2718 : check uG34a (3) (-2) outG34a ["a","h","ʊ","t","ɜ","ɔ","k","p","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_2719 : check uG34a (3) (-2) outG34a ["a","h","ʊ","t","ɜ","ɔ","k","p","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_2706 : check uG34a (3) (-2) outG34a ["a","h","ʊ","t","ɜ","ɔ","k","p"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG34a_1_2707
  · exact partG34a_1_2708
  · exact partG34a_1_2709
  · exact partG34a_1_2710
  · exact partG34a_1_2711
  · exact partG34a_1_2712
  · exact partG34a_1_2713
  · exact partG34a_1_2714
  · exact partG34a_1_2715
  · exact partG34a_1_2716
  · exact partG34a_1_2717
  · exact partG34a_1_2718
  · exact partG34a_1_2719
theorem partG34a_1_2705 : check uG34a (3) (-2) outG34a ["a","h","ʊ","t","ɜ","ɔ","k"] [["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="p" := by simpa using hx
  subst x
  exact partG34a_1_2706
theorem partG34a_1_2704 : check uG34a (3) (-2) outG34a ["a","h","ʊ","t","ɜ","ɔ"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="k" := by simpa using hx
  subst x
  exact partG34a_1_2705
theorem partG34a_1_2720 : check uG34a (3) (-2) outG34a ["a","h","ʊ","t","ɜ","o"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_2721 : check uG34a (3) (-2) outG34a ["a","h","ʊ","t","ɜ","ʊ"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_2722 : check uG34a (3) (-2) outG34a ["a","h","ʊ","t","ɜ","u"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_2723 : check uG34a (3) (-2) outG34a ["a","h","ʊ","t","ɜ","j"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_2724 : check uG34a (3) (-2) outG34a ["a","h","ʊ","t","ɜ","w"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
end ProductiveSubjectGua
