import PhonologicalOpacity.Attenuation.Productive.Baseline.CertificateParts.G37c_7_072
namespace ProductiveGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partG37c_7_5845 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","i","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5790 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_5791
  · exact partG37c_7_5806
  · exact partG37c_7_5807
  · exact partG37c_7_5808
  · exact partG37c_7_5809
  · exact partG37c_7_5810
  · exact partG37c_7_5811
  · exact partG37c_7_5826
  · exact partG37c_7_5827
  · exact partG37c_7_5828
  · exact partG37c_7_5829
  · exact partG37c_7_5830
  · exact partG37c_7_5845
theorem partG37c_7_5849 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɔ","∅","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5850 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɔ","∅","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5851 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɔ","∅","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5852 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɔ","∅","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5853 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɔ","∅","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5854 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɔ","∅","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5855 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɔ","∅","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5856 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɔ","∅","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5857 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɔ","∅","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5858 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɔ","∅","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5859 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɔ","∅","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5860 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɔ","∅","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5861 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɔ","∅","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5848 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɔ","∅","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_5849
  · exact partG37c_7_5850
  · exact partG37c_7_5851
  · exact partG37c_7_5852
  · exact partG37c_7_5853
  · exact partG37c_7_5854
  · exact partG37c_7_5855
  · exact partG37c_7_5856
  · exact partG37c_7_5857
  · exact partG37c_7_5858
  · exact partG37c_7_5859
  · exact partG37c_7_5860
  · exact partG37c_7_5861
theorem partG37c_7_5847 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɔ","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_5848
theorem partG37c_7_5862 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɔ","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5863 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɔ","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5864 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɔ","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5865 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɔ","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5866 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɔ","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5869 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɔ","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5870 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɔ","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5871 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɔ","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5872 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɔ","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5873 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɔ","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5874 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɔ","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5875 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɔ","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5876 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɔ","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5877 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɔ","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5878 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɔ","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5879 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɔ","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5880 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɔ","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5881 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɔ","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5868 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɔ","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_5869
  · exact partG37c_7_5870
  · exact partG37c_7_5871
  · exact partG37c_7_5872
  · exact partG37c_7_5873
  · exact partG37c_7_5874
  · exact partG37c_7_5875
  · exact partG37c_7_5876
  · exact partG37c_7_5877
  · exact partG37c_7_5878
  · exact partG37c_7_5879
  · exact partG37c_7_5880
  · exact partG37c_7_5881
theorem partG37c_7_5867 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɔ","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_5868
theorem partG37c_7_5882 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɔ","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5883 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɔ","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5884 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɔ","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5885 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɔ","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5888 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɔ","j","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5889 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɔ","j","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5890 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɔ","j","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5891 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɔ","j","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5892 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɔ","j","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5893 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɔ","j","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5894 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɔ","j","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5895 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɔ","j","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5896 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɔ","j","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5897 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɔ","j","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5898 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɔ","j","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5899 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɔ","j","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5900 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɔ","j","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5887 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɔ","j","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_5888
  · exact partG37c_7_5889
  · exact partG37c_7_5890
  · exact partG37c_7_5891
  · exact partG37c_7_5892
  · exact partG37c_7_5893
  · exact partG37c_7_5894
  · exact partG37c_7_5895
  · exact partG37c_7_5896
  · exact partG37c_7_5897
  · exact partG37c_7_5898
  · exact partG37c_7_5899
  · exact partG37c_7_5900
theorem partG37c_7_5886 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɔ","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_5887
theorem partG37c_7_5901 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɔ","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5846 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_5847
  · exact partG37c_7_5862
  · exact partG37c_7_5863
  · exact partG37c_7_5864
  · exact partG37c_7_5865
  · exact partG37c_7_5866
  · exact partG37c_7_5867
  · exact partG37c_7_5882
  · exact partG37c_7_5883
  · exact partG37c_7_5884
  · exact partG37c_7_5885
  · exact partG37c_7_5886
  · exact partG37c_7_5901
theorem partG37c_7_5905 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","o","∅","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5906 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","o","∅","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5907 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","o","∅","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5908 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","o","∅","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5909 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","o","∅","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5910 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","o","∅","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5911 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","o","∅","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5912 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","o","∅","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5913 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","o","∅","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5914 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","o","∅","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5915 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","o","∅","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5916 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","o","∅","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5917 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","o","∅","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5904 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","o","∅","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_5905
  · exact partG37c_7_5906
  · exact partG37c_7_5907
  · exact partG37c_7_5908
  · exact partG37c_7_5909
  · exact partG37c_7_5910
  · exact partG37c_7_5911
  · exact partG37c_7_5912
  · exact partG37c_7_5913
  · exact partG37c_7_5914
  · exact partG37c_7_5915
  · exact partG37c_7_5916
  · exact partG37c_7_5917
theorem partG37c_7_5903 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","o","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_5904
theorem partG37c_7_5918 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","o","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5919 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","o","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5920 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","o","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5921 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","o","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5922 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","o","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5925 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","o","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5926 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","o","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
end ProductiveGua
