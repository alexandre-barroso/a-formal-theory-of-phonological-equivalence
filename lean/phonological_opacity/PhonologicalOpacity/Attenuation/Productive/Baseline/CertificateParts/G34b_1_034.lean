import PhonologicalOpacity.Attenuation.Productive.Baseline.CertificateParts.G34b_1_033
namespace ProductiveGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partG34b_1_2727 : check uG34b (2) (0) outG34b ["a","f","ʊ","s","i","o","h","o"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2728 : check uG34b (2) (0) outG34b ["a","f","ʊ","s","i","o","h","ʊ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2729 : check uG34b (2) (0) outG34b ["a","f","ʊ","s","i","o","h","u"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2730 : check uG34b (2) (0) outG34b ["a","f","ʊ","s","i","o","h","j"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2731 : check uG34b (2) (0) outG34b ["a","f","ʊ","s","i","o","h","w"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2718 : check uG34b (2) (0) outG34b ["a","f","ʊ","s","i","o","h"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG34b_1_2719
  · exact partG34b_1_2720
  · exact partG34b_1_2721
  · exact partG34b_1_2722
  · exact partG34b_1_2723
  · exact partG34b_1_2724
  · exact partG34b_1_2725
  · exact partG34b_1_2726
  · exact partG34b_1_2727
  · exact partG34b_1_2728
  · exact partG34b_1_2729
  · exact partG34b_1_2730
  · exact partG34b_1_2731
theorem partG34b_1_2717 : check uG34b (2) (0) outG34b ["a","f","ʊ","s","i","o"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="h" := by simpa using hx
  subst x
  exact partG34b_1_2718
theorem partG34b_1_2732 : check uG34b (2) (0) outG34b ["a","f","ʊ","s","i","ʊ"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2733 : check uG34b (2) (0) outG34b ["a","f","ʊ","s","i","u"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2734 : check uG34b (2) (0) outG34b ["a","f","ʊ","s","i","j"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2735 : check uG34b (2) (0) outG34b ["a","f","ʊ","s","i","w"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2708 : check uG34b (2) (0) outG34b ["a","f","ʊ","s","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG34b_1_2709
  · exact partG34b_1_2710
  · exact partG34b_1_2711
  · exact partG34b_1_2712
  · exact partG34b_1_2713
  · exact partG34b_1_2714
  · exact partG34b_1_2715
  · exact partG34b_1_2716
  · exact partG34b_1_2717
  · exact partG34b_1_2732
  · exact partG34b_1_2733
  · exact partG34b_1_2734
  · exact partG34b_1_2735
theorem partG34b_1_2739 : check uG34b (2) (0) outG34b ["a","f","ʊ","s","ɔ","∅","h","∅"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2740 : check uG34b (2) (0) outG34b ["a","f","ʊ","s","ɔ","∅","h","a"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2741 : check uG34b (2) (0) outG34b ["a","f","ʊ","s","ɔ","∅","h","ɜ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2742 : check uG34b (2) (0) outG34b ["a","f","ʊ","s","ɔ","∅","h","ɛ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2743 : check uG34b (2) (0) outG34b ["a","f","ʊ","s","ɔ","∅","h","e"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2744 : check uG34b (2) (0) outG34b ["a","f","ʊ","s","ɔ","∅","h","ɪ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2745 : check uG34b (2) (0) outG34b ["a","f","ʊ","s","ɔ","∅","h","i"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2746 : check uG34b (2) (0) outG34b ["a","f","ʊ","s","ɔ","∅","h","ɔ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2747 : check uG34b (2) (0) outG34b ["a","f","ʊ","s","ɔ","∅","h","o"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2748 : check uG34b (2) (0) outG34b ["a","f","ʊ","s","ɔ","∅","h","ʊ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2749 : check uG34b (2) (0) outG34b ["a","f","ʊ","s","ɔ","∅","h","u"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2750 : check uG34b (2) (0) outG34b ["a","f","ʊ","s","ɔ","∅","h","j"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2751 : check uG34b (2) (0) outG34b ["a","f","ʊ","s","ɔ","∅","h","w"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2738 : check uG34b (2) (0) outG34b ["a","f","ʊ","s","ɔ","∅","h"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG34b_1_2739
  · exact partG34b_1_2740
  · exact partG34b_1_2741
  · exact partG34b_1_2742
  · exact partG34b_1_2743
  · exact partG34b_1_2744
  · exact partG34b_1_2745
  · exact partG34b_1_2746
  · exact partG34b_1_2747
  · exact partG34b_1_2748
  · exact partG34b_1_2749
  · exact partG34b_1_2750
  · exact partG34b_1_2751
theorem partG34b_1_2737 : check uG34b (2) (0) outG34b ["a","f","ʊ","s","ɔ","∅"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="h" := by simpa using hx
  subst x
  exact partG34b_1_2738
theorem partG34b_1_2752 : check uG34b (2) (0) outG34b ["a","f","ʊ","s","ɔ","a"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2753 : check uG34b (2) (0) outG34b ["a","f","ʊ","s","ɔ","ɜ"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2754 : check uG34b (2) (0) outG34b ["a","f","ʊ","s","ɔ","ɛ"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2755 : check uG34b (2) (0) outG34b ["a","f","ʊ","s","ɔ","e"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2756 : check uG34b (2) (0) outG34b ["a","f","ʊ","s","ɔ","ɪ"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2757 : check uG34b (2) (0) outG34b ["a","f","ʊ","s","ɔ","i"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2758 : check uG34b (2) (0) outG34b ["a","f","ʊ","s","ɔ","ɔ"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2761 : check uG34b (2) (0) outG34b ["a","f","ʊ","s","ɔ","o","h","∅"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2762 : check uG34b (2) (0) outG34b ["a","f","ʊ","s","ɔ","o","h","a"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2763 : check uG34b (2) (0) outG34b ["a","f","ʊ","s","ɔ","o","h","ɜ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2764 : check uG34b (2) (0) outG34b ["a","f","ʊ","s","ɔ","o","h","ɛ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2765 : check uG34b (2) (0) outG34b ["a","f","ʊ","s","ɔ","o","h","e"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2766 : check uG34b (2) (0) outG34b ["a","f","ʊ","s","ɔ","o","h","ɪ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2767 : check uG34b (2) (0) outG34b ["a","f","ʊ","s","ɔ","o","h","i"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2768 : check uG34b (2) (0) outG34b ["a","f","ʊ","s","ɔ","o","h","ɔ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2769 : check uG34b (2) (0) outG34b ["a","f","ʊ","s","ɔ","o","h","o"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2770 : check uG34b (2) (0) outG34b ["a","f","ʊ","s","ɔ","o","h","ʊ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2771 : check uG34b (2) (0) outG34b ["a","f","ʊ","s","ɔ","o","h","u"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2772 : check uG34b (2) (0) outG34b ["a","f","ʊ","s","ɔ","o","h","j"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2773 : check uG34b (2) (0) outG34b ["a","f","ʊ","s","ɔ","o","h","w"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2760 : check uG34b (2) (0) outG34b ["a","f","ʊ","s","ɔ","o","h"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG34b_1_2761
  · exact partG34b_1_2762
  · exact partG34b_1_2763
  · exact partG34b_1_2764
  · exact partG34b_1_2765
  · exact partG34b_1_2766
  · exact partG34b_1_2767
  · exact partG34b_1_2768
  · exact partG34b_1_2769
  · exact partG34b_1_2770
  · exact partG34b_1_2771
  · exact partG34b_1_2772
  · exact partG34b_1_2773
theorem partG34b_1_2759 : check uG34b (2) (0) outG34b ["a","f","ʊ","s","ɔ","o"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="h" := by simpa using hx
  subst x
  exact partG34b_1_2760
theorem partG34b_1_2774 : check uG34b (2) (0) outG34b ["a","f","ʊ","s","ɔ","ʊ"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2775 : check uG34b (2) (0) outG34b ["a","f","ʊ","s","ɔ","u"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2776 : check uG34b (2) (0) outG34b ["a","f","ʊ","s","ɔ","j"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2777 : check uG34b (2) (0) outG34b ["a","f","ʊ","s","ɔ","w"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2736 : check uG34b (2) (0) outG34b ["a","f","ʊ","s","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG34b_1_2737
  · exact partG34b_1_2752
  · exact partG34b_1_2753
  · exact partG34b_1_2754
  · exact partG34b_1_2755
  · exact partG34b_1_2756
  · exact partG34b_1_2757
  · exact partG34b_1_2758
  · exact partG34b_1_2759
  · exact partG34b_1_2774
  · exact partG34b_1_2775
  · exact partG34b_1_2776
  · exact partG34b_1_2777
theorem partG34b_1_2779 : check uG34b (2) (0) outG34b ["a","f","ʊ","s","o","∅"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2780 : check uG34b (2) (0) outG34b ["a","f","ʊ","s","o","a"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2781 : check uG34b (2) (0) outG34b ["a","f","ʊ","s","o","ɜ"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2782 : check uG34b (2) (0) outG34b ["a","f","ʊ","s","o","ɛ"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2783 : check uG34b (2) (0) outG34b ["a","f","ʊ","s","o","e"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2784 : check uG34b (2) (0) outG34b ["a","f","ʊ","s","o","ɪ"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2785 : check uG34b (2) (0) outG34b ["a","f","ʊ","s","o","i"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2786 : check uG34b (2) (0) outG34b ["a","f","ʊ","s","o","ɔ"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2789 : check uG34b (2) (0) outG34b ["a","f","ʊ","s","o","o","h","∅"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2790 : check uG34b (2) (0) outG34b ["a","f","ʊ","s","o","o","h","a"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2791 : check uG34b (2) (0) outG34b ["a","f","ʊ","s","o","o","h","ɜ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2792 : check uG34b (2) (0) outG34b ["a","f","ʊ","s","o","o","h","ɛ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2793 : check uG34b (2) (0) outG34b ["a","f","ʊ","s","o","o","h","e"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2794 : check uG34b (2) (0) outG34b ["a","f","ʊ","s","o","o","h","ɪ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2795 : check uG34b (2) (0) outG34b ["a","f","ʊ","s","o","o","h","i"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2796 : check uG34b (2) (0) outG34b ["a","f","ʊ","s","o","o","h","ɔ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2797 : check uG34b (2) (0) outG34b ["a","f","ʊ","s","o","o","h","o"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2798 : check uG34b (2) (0) outG34b ["a","f","ʊ","s","o","o","h","ʊ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2799 : check uG34b (2) (0) outG34b ["a","f","ʊ","s","o","o","h","u"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2800 : check uG34b (2) (0) outG34b ["a","f","ʊ","s","o","o","h","j"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2801 : check uG34b (2) (0) outG34b ["a","f","ʊ","s","o","o","h","w"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2788 : check uG34b (2) (0) outG34b ["a","f","ʊ","s","o","o","h"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG34b_1_2789
  · exact partG34b_1_2790
  · exact partG34b_1_2791
  · exact partG34b_1_2792
  · exact partG34b_1_2793
  · exact partG34b_1_2794
  · exact partG34b_1_2795
  · exact partG34b_1_2796
  · exact partG34b_1_2797
  · exact partG34b_1_2798
  · exact partG34b_1_2799
  · exact partG34b_1_2800
  · exact partG34b_1_2801
theorem partG34b_1_2787 : check uG34b (2) (0) outG34b ["a","f","ʊ","s","o","o"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="h" := by simpa using hx
  subst x
  exact partG34b_1_2788
theorem partG34b_1_2802 : check uG34b (2) (0) outG34b ["a","f","ʊ","s","o","ʊ"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2803 : check uG34b (2) (0) outG34b ["a","f","ʊ","s","o","u"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2804 : check uG34b (2) (0) outG34b ["a","f","ʊ","s","o","j"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
end ProductiveGua
