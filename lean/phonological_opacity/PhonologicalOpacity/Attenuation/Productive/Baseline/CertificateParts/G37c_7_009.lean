import PhonologicalOpacity.Attenuation.Productive.Baseline.CertificateParts.G37c_7_008
namespace ProductiveGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partG37c_7_727 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɛ","j","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_728 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɛ","j","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_729 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɛ","j","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_730 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɛ","j","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_731 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɛ","j","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_732 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɛ","j","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_719 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɛ","j","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_720
  · exact partG37c_7_721
  · exact partG37c_7_722
  · exact partG37c_7_723
  · exact partG37c_7_724
  · exact partG37c_7_725
  · exact partG37c_7_726
  · exact partG37c_7_727
  · exact partG37c_7_728
  · exact partG37c_7_729
  · exact partG37c_7_730
  · exact partG37c_7_731
  · exact partG37c_7_732
theorem partG37c_7_718 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɛ","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_719
theorem partG37c_7_733 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɛ","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_678 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_679
  · exact partG37c_7_694
  · exact partG37c_7_695
  · exact partG37c_7_696
  · exact partG37c_7_697
  · exact partG37c_7_698
  · exact partG37c_7_699
  · exact partG37c_7_714
  · exact partG37c_7_715
  · exact partG37c_7_716
  · exact partG37c_7_717
  · exact partG37c_7_718
  · exact partG37c_7_733
theorem partG37c_7_737 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","e","∅","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_738 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","e","∅","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_739 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","e","∅","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_740 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","e","∅","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_741 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","e","∅","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_742 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","e","∅","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_743 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","e","∅","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_744 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","e","∅","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_745 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","e","∅","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_746 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","e","∅","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_747 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","e","∅","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_748 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","e","∅","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_749 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","e","∅","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_736 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","e","∅","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_737
  · exact partG37c_7_738
  · exact partG37c_7_739
  · exact partG37c_7_740
  · exact partG37c_7_741
  · exact partG37c_7_742
  · exact partG37c_7_743
  · exact partG37c_7_744
  · exact partG37c_7_745
  · exact partG37c_7_746
  · exact partG37c_7_747
  · exact partG37c_7_748
  · exact partG37c_7_749
theorem partG37c_7_735 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","e","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_736
theorem partG37c_7_750 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","e","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_751 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","e","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_752 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","e","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_753 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","e","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_754 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","e","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_757 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","e","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_758 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","e","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_759 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","e","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_760 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","e","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_761 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","e","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_762 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","e","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_763 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","e","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_764 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","e","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_765 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","e","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_766 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","e","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_767 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","e","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_768 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","e","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_769 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","e","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_756 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","e","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_757
  · exact partG37c_7_758
  · exact partG37c_7_759
  · exact partG37c_7_760
  · exact partG37c_7_761
  · exact partG37c_7_762
  · exact partG37c_7_763
  · exact partG37c_7_764
  · exact partG37c_7_765
  · exact partG37c_7_766
  · exact partG37c_7_767
  · exact partG37c_7_768
  · exact partG37c_7_769
theorem partG37c_7_755 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","e","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_756
theorem partG37c_7_770 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","e","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_771 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","e","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_772 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","e","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_773 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","e","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_776 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","e","j","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_777 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","e","j","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_778 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","e","j","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_779 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","e","j","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_780 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","e","j","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_781 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","e","j","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_782 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","e","j","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_783 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","e","j","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_784 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","e","j","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_785 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","e","j","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_786 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","e","j","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_787 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","e","j","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_788 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","e","j","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_775 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","e","j","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_776
  · exact partG37c_7_777
  · exact partG37c_7_778
  · exact partG37c_7_779
  · exact partG37c_7_780
  · exact partG37c_7_781
  · exact partG37c_7_782
  · exact partG37c_7_783
  · exact partG37c_7_784
  · exact partG37c_7_785
  · exact partG37c_7_786
  · exact partG37c_7_787
  · exact partG37c_7_788
theorem partG37c_7_774 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","e","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_775
theorem partG37c_7_789 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","e","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_734 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_735
  · exact partG37c_7_750
  · exact partG37c_7_751
  · exact partG37c_7_752
  · exact partG37c_7_753
  · exact partG37c_7_754
  · exact partG37c_7_755
  · exact partG37c_7_770
  · exact partG37c_7_771
  · exact partG37c_7_772
  · exact partG37c_7_773
  · exact partG37c_7_774
  · exact partG37c_7_789
theorem partG37c_7_793 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɪ","∅","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_794 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɪ","∅","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_795 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɪ","∅","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_796 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɪ","∅","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_797 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɪ","∅","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_798 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɪ","∅","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_799 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɪ","∅","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_800 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɪ","∅","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_801 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɪ","∅","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_802 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɪ","∅","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_803 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɪ","∅","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_804 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɪ","∅","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_805 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɪ","∅","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_792 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɪ","∅","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_793
  · exact partG37c_7_794
  · exact partG37c_7_795
  · exact partG37c_7_796
  · exact partG37c_7_797
  · exact partG37c_7_798
  · exact partG37c_7_799
  · exact partG37c_7_800
  · exact partG37c_7_801
  · exact partG37c_7_802
  · exact partG37c_7_803
  · exact partG37c_7_804
  · exact partG37c_7_805
end ProductiveGua
