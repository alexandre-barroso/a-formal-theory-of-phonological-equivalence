import PhonologicalOpacity.Attenuation.Productive.Subject.CertificateParts.G37c_7_083
namespace ProductiveSubjectGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partG37c_7_6727 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","a","∅","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6728 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","a","∅","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6729 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","a","∅","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6730 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","a","∅","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6731 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","a","∅","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6732 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","a","∅","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6733 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","a","∅","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6720 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","a","∅","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_6721
  · exact partG37c_7_6722
  · exact partG37c_7_6723
  · exact partG37c_7_6724
  · exact partG37c_7_6725
  · exact partG37c_7_6726
  · exact partG37c_7_6727
  · exact partG37c_7_6728
  · exact partG37c_7_6729
  · exact partG37c_7_6730
  · exact partG37c_7_6731
  · exact partG37c_7_6732
  · exact partG37c_7_6733
theorem partG37c_7_6719 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","a","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_6720
theorem partG37c_7_6734 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","a","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6735 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","a","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6736 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","a","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6737 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","a","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6738 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","a","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6741 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","a","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6742 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","a","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6743 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","a","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6744 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","a","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6745 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","a","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6746 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","a","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6747 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","a","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6748 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","a","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6749 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","a","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6750 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","a","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6751 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","a","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6752 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","a","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6753 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","a","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6740 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","a","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_6741
  · exact partG37c_7_6742
  · exact partG37c_7_6743
  · exact partG37c_7_6744
  · exact partG37c_7_6745
  · exact partG37c_7_6746
  · exact partG37c_7_6747
  · exact partG37c_7_6748
  · exact partG37c_7_6749
  · exact partG37c_7_6750
  · exact partG37c_7_6751
  · exact partG37c_7_6752
  · exact partG37c_7_6753
theorem partG37c_7_6739 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","a","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_6740
theorem partG37c_7_6754 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","a","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6755 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","a","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6756 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","a","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6757 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","a","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6760 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","a","j","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6761 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","a","j","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6762 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","a","j","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6763 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","a","j","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6764 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","a","j","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6765 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","a","j","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6766 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","a","j","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6767 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","a","j","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6768 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","a","j","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6769 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","a","j","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6770 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","a","j","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6771 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","a","j","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6772 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","a","j","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6759 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","a","j","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_6760
  · exact partG37c_7_6761
  · exact partG37c_7_6762
  · exact partG37c_7_6763
  · exact partG37c_7_6764
  · exact partG37c_7_6765
  · exact partG37c_7_6766
  · exact partG37c_7_6767
  · exact partG37c_7_6768
  · exact partG37c_7_6769
  · exact partG37c_7_6770
  · exact partG37c_7_6771
  · exact partG37c_7_6772
theorem partG37c_7_6758 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","a","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_6759
theorem partG37c_7_6773 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","a","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6718 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_6719
  · exact partG37c_7_6734
  · exact partG37c_7_6735
  · exact partG37c_7_6736
  · exact partG37c_7_6737
  · exact partG37c_7_6738
  · exact partG37c_7_6739
  · exact partG37c_7_6754
  · exact partG37c_7_6755
  · exact partG37c_7_6756
  · exact partG37c_7_6757
  · exact partG37c_7_6758
  · exact partG37c_7_6773
theorem partG37c_7_6775 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ɜ","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6776 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ɜ","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6777 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ɜ","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6778 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ɜ","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6779 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ɜ","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6780 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ɜ","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6783 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ɜ","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6784 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ɜ","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6785 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ɜ","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6786 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ɜ","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6787 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ɜ","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6788 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ɜ","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6789 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ɜ","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6790 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ɜ","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6791 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ɜ","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6792 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ɜ","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6793 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ɜ","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6794 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ɜ","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6795 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ɜ","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6782 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ɜ","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_6783
  · exact partG37c_7_6784
  · exact partG37c_7_6785
  · exact partG37c_7_6786
  · exact partG37c_7_6787
  · exact partG37c_7_6788
  · exact partG37c_7_6789
  · exact partG37c_7_6790
  · exact partG37c_7_6791
  · exact partG37c_7_6792
  · exact partG37c_7_6793
  · exact partG37c_7_6794
  · exact partG37c_7_6795
theorem partG37c_7_6781 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ɜ","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_6782
theorem partG37c_7_6796 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ɜ","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6797 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ɜ","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6798 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ɜ","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6799 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ɜ","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6800 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ɜ","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6801 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ɜ","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6774 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_6775
  · exact partG37c_7_6776
  · exact partG37c_7_6777
  · exact partG37c_7_6778
  · exact partG37c_7_6779
  · exact partG37c_7_6780
  · exact partG37c_7_6781
  · exact partG37c_7_6796
  · exact partG37c_7_6797
  · exact partG37c_7_6798
  · exact partG37c_7_6799
  · exact partG37c_7_6800
  · exact partG37c_7_6801
theorem partG37c_7_6805 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ɛ","∅","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6806 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ɛ","∅","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
end ProductiveSubjectGua
