import PhonologicalOpacity.Attenuation.Productive.Subject.CertificateParts.OR38_1_008
namespace ProductiveSubjectGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partOR38_1_725 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","o","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_726 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","o","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_727 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","o","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_728 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","o","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_729 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","o","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_730 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","o","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_731 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","o","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_732 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","o","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_733 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","o","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_734 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","o","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_735 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","o","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_736 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","o","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_737 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","o","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_724 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_725
  · exact partOR38_1_726
  · exact partOR38_1_727
  · exact partOR38_1_728
  · exact partOR38_1_729
  · exact partOR38_1_730
  · exact partOR38_1_731
  · exact partOR38_1_732
  · exact partOR38_1_733
  · exact partOR38_1_734
  · exact partOR38_1_735
  · exact partOR38_1_736
  · exact partOR38_1_737
theorem partOR38_1_739 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","ʊ","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_740 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","ʊ","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_741 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","ʊ","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_742 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","ʊ","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_743 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","ʊ","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_744 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","ʊ","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_745 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","ʊ","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_746 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","ʊ","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_747 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","ʊ","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_748 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","ʊ","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_749 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","ʊ","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_750 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","ʊ","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_751 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","ʊ","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_738 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_739
  · exact partOR38_1_740
  · exact partOR38_1_741
  · exact partOR38_1_742
  · exact partOR38_1_743
  · exact partOR38_1_744
  · exact partOR38_1_745
  · exact partOR38_1_746
  · exact partOR38_1_747
  · exact partOR38_1_748
  · exact partOR38_1_749
  · exact partOR38_1_750
  · exact partOR38_1_751
theorem partOR38_1_753 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","u","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_754 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","u","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_755 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","u","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_756 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","u","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_757 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","u","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_758 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","u","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_759 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","u","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_760 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","u","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_761 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","u","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_762 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","u","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_763 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","u","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_764 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","u","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_765 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","u","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_752 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_753
  · exact partOR38_1_754
  · exact partOR38_1_755
  · exact partOR38_1_756
  · exact partOR38_1_757
  · exact partOR38_1_758
  · exact partOR38_1_759
  · exact partOR38_1_760
  · exact partOR38_1_761
  · exact partOR38_1_762
  · exact partOR38_1_763
  · exact partOR38_1_764
  · exact partOR38_1_765
theorem partOR38_1_767 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","j","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_768 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","j","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_769 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","j","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_770 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","j","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_771 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","j","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_772 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","j","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_773 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","j","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_774 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","j","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_775 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","j","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_776 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","j","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_777 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","j","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_778 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","j","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_779 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","j","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_766 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_767
  · exact partOR38_1_768
  · exact partOR38_1_769
  · exact partOR38_1_770
  · exact partOR38_1_771
  · exact partOR38_1_772
  · exact partOR38_1_773
  · exact partOR38_1_774
  · exact partOR38_1_775
  · exact partOR38_1_776
  · exact partOR38_1_777
  · exact partOR38_1_778
  · exact partOR38_1_779
theorem partOR38_1_781 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","w","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_782 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","w","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_783 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","w","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_784 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","w","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_785 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","w","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_786 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","w","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_787 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","w","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_788 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","w","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_789 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","w","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_790 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","w","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_791 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","w","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_792 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","w","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_793 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","w","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_780 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_781
  · exact partOR38_1_782
  · exact partOR38_1_783
  · exact partOR38_1_784
  · exact partOR38_1_785
  · exact partOR38_1_786
  · exact partOR38_1_787
  · exact partOR38_1_788
  · exact partOR38_1_789
  · exact partOR38_1_790
  · exact partOR38_1_791
  · exact partOR38_1_792
  · exact partOR38_1_793
theorem partOR38_1_611 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ","s"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_612
  · exact partOR38_1_626
  · exact partOR38_1_640
  · exact partOR38_1_654
  · exact partOR38_1_668
  · exact partOR38_1_682
  · exact partOR38_1_696
  · exact partOR38_1_710
  · exact partOR38_1_724
  · exact partOR38_1_738
  · exact partOR38_1_752
  · exact partOR38_1_766
  · exact partOR38_1_780
theorem partOR38_1_610 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɪ"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="s" := by simpa using hx
  subst x
  exact partOR38_1_611
theorem partOR38_1_796 : check uOR38 (4) (-2) outOR38 ["a","tʃ","i","s","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_798 : check uOR38 (4) (-2) outOR38 ["a","tʃ","i","s","a","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_799 : check uOR38 (4) (-2) outOR38 ["a","tʃ","i","s","a","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_800 : check uOR38 (4) (-2) outOR38 ["a","tʃ","i","s","a","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_801 : check uOR38 (4) (-2) outOR38 ["a","tʃ","i","s","a","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_802 : check uOR38 (4) (-2) outOR38 ["a","tʃ","i","s","a","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_803 : check uOR38 (4) (-2) outOR38 ["a","tʃ","i","s","a","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_804 : check uOR38 (4) (-2) outOR38 ["a","tʃ","i","s","a","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
end ProductiveSubjectGua
