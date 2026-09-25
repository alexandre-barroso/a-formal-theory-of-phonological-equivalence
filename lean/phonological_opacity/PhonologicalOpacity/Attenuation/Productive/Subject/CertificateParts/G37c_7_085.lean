import PhonologicalOpacity.Attenuation.Productive.Subject.CertificateParts.G37c_7_084
namespace ProductiveSubjectGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partG37c_7_6807 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ɛ","∅","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6808 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ɛ","∅","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6809 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ɛ","∅","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6810 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ɛ","∅","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6811 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ɛ","∅","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6812 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ɛ","∅","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6813 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ɛ","∅","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6814 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ɛ","∅","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6815 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ɛ","∅","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6816 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ɛ","∅","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6817 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ɛ","∅","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6804 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ɛ","∅","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_6805
  · exact partG37c_7_6806
  · exact partG37c_7_6807
  · exact partG37c_7_6808
  · exact partG37c_7_6809
  · exact partG37c_7_6810
  · exact partG37c_7_6811
  · exact partG37c_7_6812
  · exact partG37c_7_6813
  · exact partG37c_7_6814
  · exact partG37c_7_6815
  · exact partG37c_7_6816
  · exact partG37c_7_6817
theorem partG37c_7_6803 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ɛ","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_6804
theorem partG37c_7_6818 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ɛ","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6819 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ɛ","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6820 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ɛ","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6821 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ɛ","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6822 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ɛ","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6825 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ɛ","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6826 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ɛ","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6827 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ɛ","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6828 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ɛ","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6829 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ɛ","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6830 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ɛ","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6831 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ɛ","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6832 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ɛ","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6833 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ɛ","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6834 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ɛ","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6835 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ɛ","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6836 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ɛ","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6837 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ɛ","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6824 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ɛ","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_6825
  · exact partG37c_7_6826
  · exact partG37c_7_6827
  · exact partG37c_7_6828
  · exact partG37c_7_6829
  · exact partG37c_7_6830
  · exact partG37c_7_6831
  · exact partG37c_7_6832
  · exact partG37c_7_6833
  · exact partG37c_7_6834
  · exact partG37c_7_6835
  · exact partG37c_7_6836
  · exact partG37c_7_6837
theorem partG37c_7_6823 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ɛ","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_6824
theorem partG37c_7_6838 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ɛ","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6839 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ɛ","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6840 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ɛ","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6841 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ɛ","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6844 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ɛ","j","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6845 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ɛ","j","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6846 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ɛ","j","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6847 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ɛ","j","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6848 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ɛ","j","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6849 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ɛ","j","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6850 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ɛ","j","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6851 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ɛ","j","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6852 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ɛ","j","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6853 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ɛ","j","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6854 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ɛ","j","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6855 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ɛ","j","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6856 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ɛ","j","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6843 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ɛ","j","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_6844
  · exact partG37c_7_6845
  · exact partG37c_7_6846
  · exact partG37c_7_6847
  · exact partG37c_7_6848
  · exact partG37c_7_6849
  · exact partG37c_7_6850
  · exact partG37c_7_6851
  · exact partG37c_7_6852
  · exact partG37c_7_6853
  · exact partG37c_7_6854
  · exact partG37c_7_6855
  · exact partG37c_7_6856
theorem partG37c_7_6842 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ɛ","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_6843
theorem partG37c_7_6857 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ɛ","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6802 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_6803
  · exact partG37c_7_6818
  · exact partG37c_7_6819
  · exact partG37c_7_6820
  · exact partG37c_7_6821
  · exact partG37c_7_6822
  · exact partG37c_7_6823
  · exact partG37c_7_6838
  · exact partG37c_7_6839
  · exact partG37c_7_6840
  · exact partG37c_7_6841
  · exact partG37c_7_6842
  · exact partG37c_7_6857
theorem partG37c_7_6859 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","e","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6860 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","e","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6861 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","e","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6862 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","e","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6863 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","e","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6864 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","e","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6867 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","e","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6868 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","e","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6869 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","e","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6870 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","e","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6871 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","e","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6872 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","e","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6873 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","e","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6874 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","e","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6875 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","e","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6876 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","e","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6877 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","e","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6878 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","e","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6879 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","e","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6866 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","e","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_6867
  · exact partG37c_7_6868
  · exact partG37c_7_6869
  · exact partG37c_7_6870
  · exact partG37c_7_6871
  · exact partG37c_7_6872
  · exact partG37c_7_6873
  · exact partG37c_7_6874
  · exact partG37c_7_6875
  · exact partG37c_7_6876
  · exact partG37c_7_6877
  · exact partG37c_7_6878
  · exact partG37c_7_6879
theorem partG37c_7_6865 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","e","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_6866
theorem partG37c_7_6880 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","e","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6881 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","e","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6882 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","e","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6883 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","e","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6884 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","e","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
end ProductiveSubjectGua
