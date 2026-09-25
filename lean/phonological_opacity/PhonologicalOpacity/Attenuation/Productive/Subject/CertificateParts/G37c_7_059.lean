import PhonologicalOpacity.Attenuation.Productive.Subject.CertificateParts.G37c_7_058
namespace ProductiveSubjectGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partG37c_7_4727 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ʊ","∅","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4728 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ʊ","∅","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4729 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ʊ","∅","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4730 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ʊ","∅","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4731 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ʊ","∅","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4732 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ʊ","∅","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4733 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ʊ","∅","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4734 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ʊ","∅","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4735 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ʊ","∅","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4736 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ʊ","∅","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4737 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ʊ","∅","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4724 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ʊ","∅","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_4725
  · exact partG37c_7_4726
  · exact partG37c_7_4727
  · exact partG37c_7_4728
  · exact partG37c_7_4729
  · exact partG37c_7_4730
  · exact partG37c_7_4731
  · exact partG37c_7_4732
  · exact partG37c_7_4733
  · exact partG37c_7_4734
  · exact partG37c_7_4735
  · exact partG37c_7_4736
  · exact partG37c_7_4737
theorem partG37c_7_4723 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ʊ","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_4724
theorem partG37c_7_4738 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ʊ","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4739 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ʊ","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4740 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ʊ","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4741 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ʊ","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4742 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ʊ","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4745 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ʊ","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4746 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ʊ","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4747 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ʊ","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4748 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ʊ","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4749 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ʊ","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4750 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ʊ","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4751 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ʊ","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4752 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ʊ","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4753 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ʊ","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4754 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ʊ","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4755 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ʊ","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4756 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ʊ","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4757 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ʊ","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4744 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ʊ","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_4745
  · exact partG37c_7_4746
  · exact partG37c_7_4747
  · exact partG37c_7_4748
  · exact partG37c_7_4749
  · exact partG37c_7_4750
  · exact partG37c_7_4751
  · exact partG37c_7_4752
  · exact partG37c_7_4753
  · exact partG37c_7_4754
  · exact partG37c_7_4755
  · exact partG37c_7_4756
  · exact partG37c_7_4757
theorem partG37c_7_4743 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ʊ","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_4744
theorem partG37c_7_4758 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ʊ","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4759 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ʊ","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4760 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ʊ","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4761 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ʊ","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4764 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ʊ","j","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4765 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ʊ","j","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4766 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ʊ","j","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4767 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ʊ","j","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4768 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ʊ","j","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4769 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ʊ","j","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4770 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ʊ","j","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4771 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ʊ","j","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4772 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ʊ","j","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4773 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ʊ","j","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4774 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ʊ","j","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4775 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ʊ","j","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4776 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ʊ","j","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4763 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ʊ","j","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_4764
  · exact partG37c_7_4765
  · exact partG37c_7_4766
  · exact partG37c_7_4767
  · exact partG37c_7_4768
  · exact partG37c_7_4769
  · exact partG37c_7_4770
  · exact partG37c_7_4771
  · exact partG37c_7_4772
  · exact partG37c_7_4773
  · exact partG37c_7_4774
  · exact partG37c_7_4775
  · exact partG37c_7_4776
theorem partG37c_7_4762 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ʊ","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_4763
theorem partG37c_7_4777 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ʊ","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4722 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_4723
  · exact partG37c_7_4738
  · exact partG37c_7_4739
  · exact partG37c_7_4740
  · exact partG37c_7_4741
  · exact partG37c_7_4742
  · exact partG37c_7_4743
  · exact partG37c_7_4758
  · exact partG37c_7_4759
  · exact partG37c_7_4760
  · exact partG37c_7_4761
  · exact partG37c_7_4762
  · exact partG37c_7_4777
theorem partG37c_7_4781 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","u","∅","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4782 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","u","∅","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4783 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","u","∅","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4784 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","u","∅","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4785 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","u","∅","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4786 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","u","∅","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4787 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","u","∅","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4788 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","u","∅","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4789 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","u","∅","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4790 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","u","∅","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4791 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","u","∅","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4792 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","u","∅","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4793 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","u","∅","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4780 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","u","∅","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_4781
  · exact partG37c_7_4782
  · exact partG37c_7_4783
  · exact partG37c_7_4784
  · exact partG37c_7_4785
  · exact partG37c_7_4786
  · exact partG37c_7_4787
  · exact partG37c_7_4788
  · exact partG37c_7_4789
  · exact partG37c_7_4790
  · exact partG37c_7_4791
  · exact partG37c_7_4792
  · exact partG37c_7_4793
theorem partG37c_7_4779 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","u","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_4780
theorem partG37c_7_4794 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","u","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4795 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","u","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4796 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","u","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4797 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","u","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4798 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","u","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4801 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","u","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4802 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","u","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4803 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","u","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4804 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","u","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4805 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","u","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4806 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","u","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
end ProductiveSubjectGua
