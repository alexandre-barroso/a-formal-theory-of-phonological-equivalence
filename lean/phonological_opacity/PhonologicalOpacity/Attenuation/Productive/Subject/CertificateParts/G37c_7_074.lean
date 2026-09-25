import PhonologicalOpacity.Attenuation.Productive.Subject.CertificateParts.G37c_7_073
namespace ProductiveSubjectGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partG37c_7_5927 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","o","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5928 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","o","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5929 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","o","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5930 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","o","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5931 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","o","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5932 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","o","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5933 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","o","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5934 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","o","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5935 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","o","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5936 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","o","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5937 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","o","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5924 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","o","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_5925
  · exact partG37c_7_5926
  · exact partG37c_7_5927
  · exact partG37c_7_5928
  · exact partG37c_7_5929
  · exact partG37c_7_5930
  · exact partG37c_7_5931
  · exact partG37c_7_5932
  · exact partG37c_7_5933
  · exact partG37c_7_5934
  · exact partG37c_7_5935
  · exact partG37c_7_5936
  · exact partG37c_7_5937
theorem partG37c_7_5923 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","o","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_5924
theorem partG37c_7_5938 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","o","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5939 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","o","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5940 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","o","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5941 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","o","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5944 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","o","j","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5945 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","o","j","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5946 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","o","j","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5947 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","o","j","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5948 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","o","j","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5949 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","o","j","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5950 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","o","j","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5951 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","o","j","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5952 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","o","j","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5953 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","o","j","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5954 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","o","j","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5955 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","o","j","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5956 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","o","j","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5943 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","o","j","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_5944
  · exact partG37c_7_5945
  · exact partG37c_7_5946
  · exact partG37c_7_5947
  · exact partG37c_7_5948
  · exact partG37c_7_5949
  · exact partG37c_7_5950
  · exact partG37c_7_5951
  · exact partG37c_7_5952
  · exact partG37c_7_5953
  · exact partG37c_7_5954
  · exact partG37c_7_5955
  · exact partG37c_7_5956
theorem partG37c_7_5942 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","o","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_5943
theorem partG37c_7_5957 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","o","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5902 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_5903
  · exact partG37c_7_5918
  · exact partG37c_7_5919
  · exact partG37c_7_5920
  · exact partG37c_7_5921
  · exact partG37c_7_5922
  · exact partG37c_7_5923
  · exact partG37c_7_5938
  · exact partG37c_7_5939
  · exact partG37c_7_5940
  · exact partG37c_7_5941
  · exact partG37c_7_5942
  · exact partG37c_7_5957
theorem partG37c_7_5961 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ʊ","∅","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5962 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ʊ","∅","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5963 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ʊ","∅","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5964 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ʊ","∅","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5965 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ʊ","∅","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5966 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ʊ","∅","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5967 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ʊ","∅","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5968 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ʊ","∅","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5969 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ʊ","∅","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5970 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ʊ","∅","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5971 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ʊ","∅","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5972 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ʊ","∅","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5973 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ʊ","∅","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5960 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ʊ","∅","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_5961
  · exact partG37c_7_5962
  · exact partG37c_7_5963
  · exact partG37c_7_5964
  · exact partG37c_7_5965
  · exact partG37c_7_5966
  · exact partG37c_7_5967
  · exact partG37c_7_5968
  · exact partG37c_7_5969
  · exact partG37c_7_5970
  · exact partG37c_7_5971
  · exact partG37c_7_5972
  · exact partG37c_7_5973
theorem partG37c_7_5959 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ʊ","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_5960
theorem partG37c_7_5974 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ʊ","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5975 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ʊ","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5976 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ʊ","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5977 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ʊ","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5978 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ʊ","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5981 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ʊ","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5982 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ʊ","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5983 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ʊ","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5984 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ʊ","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5985 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ʊ","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5986 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ʊ","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5987 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ʊ","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5988 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ʊ","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5989 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ʊ","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5990 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ʊ","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5991 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ʊ","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5992 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ʊ","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5993 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ʊ","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5980 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ʊ","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_5981
  · exact partG37c_7_5982
  · exact partG37c_7_5983
  · exact partG37c_7_5984
  · exact partG37c_7_5985
  · exact partG37c_7_5986
  · exact partG37c_7_5987
  · exact partG37c_7_5988
  · exact partG37c_7_5989
  · exact partG37c_7_5990
  · exact partG37c_7_5991
  · exact partG37c_7_5992
  · exact partG37c_7_5993
theorem partG37c_7_5979 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ʊ","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_5980
theorem partG37c_7_5994 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ʊ","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5995 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ʊ","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5996 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ʊ","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5997 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ʊ","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6000 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ʊ","j","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6001 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ʊ","j","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6002 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ʊ","j","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6003 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ʊ","j","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6004 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ʊ","j","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6005 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ʊ","j","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6006 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ʊ","j","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
end ProductiveSubjectGua
