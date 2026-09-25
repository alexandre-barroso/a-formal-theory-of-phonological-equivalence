import PhonologicalOpacity.Attenuation.Productive.Subject.CertificateParts.G37c_7_059
namespace ProductiveSubjectGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partG37c_7_4807 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","u","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4808 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","u","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4809 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","u","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4810 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","u","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4811 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","u","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4812 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","u","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4813 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","u","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4800 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","u","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_4801
  · exact partG37c_7_4802
  · exact partG37c_7_4803
  · exact partG37c_7_4804
  · exact partG37c_7_4805
  · exact partG37c_7_4806
  · exact partG37c_7_4807
  · exact partG37c_7_4808
  · exact partG37c_7_4809
  · exact partG37c_7_4810
  · exact partG37c_7_4811
  · exact partG37c_7_4812
  · exact partG37c_7_4813
theorem partG37c_7_4799 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","u","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_4800
theorem partG37c_7_4814 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","u","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4815 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","u","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4816 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","u","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4817 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","u","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4820 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","u","j","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4821 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","u","j","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4822 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","u","j","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4823 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","u","j","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4824 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","u","j","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4825 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","u","j","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4826 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","u","j","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4827 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","u","j","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4828 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","u","j","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4829 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","u","j","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4830 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","u","j","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4831 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","u","j","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4832 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","u","j","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4819 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","u","j","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_4820
  · exact partG37c_7_4821
  · exact partG37c_7_4822
  · exact partG37c_7_4823
  · exact partG37c_7_4824
  · exact partG37c_7_4825
  · exact partG37c_7_4826
  · exact partG37c_7_4827
  · exact partG37c_7_4828
  · exact partG37c_7_4829
  · exact partG37c_7_4830
  · exact partG37c_7_4831
  · exact partG37c_7_4832
theorem partG37c_7_4818 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","u","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_4819
theorem partG37c_7_4833 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","u","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4778 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_4779
  · exact partG37c_7_4794
  · exact partG37c_7_4795
  · exact partG37c_7_4796
  · exact partG37c_7_4797
  · exact partG37c_7_4798
  · exact partG37c_7_4799
  · exact partG37c_7_4814
  · exact partG37c_7_4815
  · exact partG37c_7_4816
  · exact partG37c_7_4817
  · exact partG37c_7_4818
  · exact partG37c_7_4833
theorem partG37c_7_4837 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","j","∅","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4838 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","j","∅","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4839 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","j","∅","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4840 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","j","∅","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4841 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","j","∅","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4842 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","j","∅","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4843 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","j","∅","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4844 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","j","∅","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4845 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","j","∅","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4846 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","j","∅","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4847 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","j","∅","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4848 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","j","∅","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4849 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","j","∅","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4836 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","j","∅","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_4837
  · exact partG37c_7_4838
  · exact partG37c_7_4839
  · exact partG37c_7_4840
  · exact partG37c_7_4841
  · exact partG37c_7_4842
  · exact partG37c_7_4843
  · exact partG37c_7_4844
  · exact partG37c_7_4845
  · exact partG37c_7_4846
  · exact partG37c_7_4847
  · exact partG37c_7_4848
  · exact partG37c_7_4849
theorem partG37c_7_4835 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","j","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_4836
theorem partG37c_7_4850 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","j","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4851 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","j","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4852 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","j","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4853 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","j","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4854 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","j","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4857 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","j","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4858 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","j","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4859 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","j","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4860 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","j","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4861 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","j","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4862 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","j","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4863 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","j","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4864 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","j","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4865 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","j","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4866 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","j","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4867 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","j","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4868 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","j","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4869 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","j","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4856 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","j","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_4857
  · exact partG37c_7_4858
  · exact partG37c_7_4859
  · exact partG37c_7_4860
  · exact partG37c_7_4861
  · exact partG37c_7_4862
  · exact partG37c_7_4863
  · exact partG37c_7_4864
  · exact partG37c_7_4865
  · exact partG37c_7_4866
  · exact partG37c_7_4867
  · exact partG37c_7_4868
  · exact partG37c_7_4869
theorem partG37c_7_4855 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","j","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_4856
theorem partG37c_7_4870 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","j","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4871 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","j","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4872 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","j","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4873 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","j","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4876 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","j","j","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4877 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","j","j","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4878 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","j","j","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4879 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","j","j","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4880 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","j","j","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4881 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","j","j","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4882 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","j","j","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4883 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","j","j","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4884 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","j","j","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4885 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","j","j","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4886 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","j","j","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
end ProductiveSubjectGua
