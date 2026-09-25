import PhonologicalOpacity.Attenuation.Productive.Baseline.CertificateParts.G37c_7_060
namespace ProductiveGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partG37c_7_4887 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","j","j","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4888 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","j","j","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4875 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","j","j","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_4876
  · exact partG37c_7_4877
  · exact partG37c_7_4878
  · exact partG37c_7_4879
  · exact partG37c_7_4880
  · exact partG37c_7_4881
  · exact partG37c_7_4882
  · exact partG37c_7_4883
  · exact partG37c_7_4884
  · exact partG37c_7_4885
  · exact partG37c_7_4886
  · exact partG37c_7_4887
  · exact partG37c_7_4888
theorem partG37c_7_4874 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","j","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_4875
theorem partG37c_7_4889 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","j","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4834 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_4835
  · exact partG37c_7_4850
  · exact partG37c_7_4851
  · exact partG37c_7_4852
  · exact partG37c_7_4853
  · exact partG37c_7_4854
  · exact partG37c_7_4855
  · exact partG37c_7_4870
  · exact partG37c_7_4871
  · exact partG37c_7_4872
  · exact partG37c_7_4873
  · exact partG37c_7_4874
  · exact partG37c_7_4889
theorem partG37c_7_4893 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","w","∅","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4894 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","w","∅","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4895 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","w","∅","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4896 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","w","∅","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4897 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","w","∅","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4898 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","w","∅","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4899 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","w","∅","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4900 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","w","∅","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4901 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","w","∅","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4902 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","w","∅","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4903 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","w","∅","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4904 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","w","∅","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4905 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","w","∅","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4892 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","w","∅","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_4893
  · exact partG37c_7_4894
  · exact partG37c_7_4895
  · exact partG37c_7_4896
  · exact partG37c_7_4897
  · exact partG37c_7_4898
  · exact partG37c_7_4899
  · exact partG37c_7_4900
  · exact partG37c_7_4901
  · exact partG37c_7_4902
  · exact partG37c_7_4903
  · exact partG37c_7_4904
  · exact partG37c_7_4905
theorem partG37c_7_4891 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","w","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_4892
theorem partG37c_7_4906 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","w","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4907 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","w","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4908 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","w","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4909 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","w","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4910 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","w","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4913 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","w","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4914 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","w","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4915 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","w","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4916 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","w","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4917 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","w","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4918 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","w","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4919 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","w","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4920 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","w","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4921 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","w","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4922 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","w","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4923 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","w","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4924 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","w","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4925 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","w","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4912 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","w","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_4913
  · exact partG37c_7_4914
  · exact partG37c_7_4915
  · exact partG37c_7_4916
  · exact partG37c_7_4917
  · exact partG37c_7_4918
  · exact partG37c_7_4919
  · exact partG37c_7_4920
  · exact partG37c_7_4921
  · exact partG37c_7_4922
  · exact partG37c_7_4923
  · exact partG37c_7_4924
  · exact partG37c_7_4925
theorem partG37c_7_4911 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","w","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_4912
theorem partG37c_7_4926 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","w","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4927 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","w","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4928 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","w","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4929 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","w","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4932 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","w","j","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4933 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","w","j","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4934 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","w","j","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4935 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","w","j","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4936 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","w","j","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4937 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","w","j","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4938 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","w","j","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4939 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","w","j","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4940 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","w","j","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4941 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","w","j","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4942 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","w","j","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4943 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","w","j","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4944 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","w","j","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4931 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","w","j","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_4932
  · exact partG37c_7_4933
  · exact partG37c_7_4934
  · exact partG37c_7_4935
  · exact partG37c_7_4936
  · exact partG37c_7_4937
  · exact partG37c_7_4938
  · exact partG37c_7_4939
  · exact partG37c_7_4940
  · exact partG37c_7_4941
  · exact partG37c_7_4942
  · exact partG37c_7_4943
  · exact partG37c_7_4944
theorem partG37c_7_4930 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","w","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_4931
theorem partG37c_7_4945 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","w","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4890 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_4891
  · exact partG37c_7_4906
  · exact partG37c_7_4907
  · exact partG37c_7_4908
  · exact partG37c_7_4909
  · exact partG37c_7_4910
  · exact partG37c_7_4911
  · exact partG37c_7_4926
  · exact partG37c_7_4927
  · exact partG37c_7_4928
  · exact partG37c_7_4929
  · exact partG37c_7_4930
  · exact partG37c_7_4945
theorem partG37c_7_4217 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_4218
  · exact partG37c_7_4274
  · exact partG37c_7_4330
  · exact partG37c_7_4386
  · exact partG37c_7_4442
  · exact partG37c_7_4498
  · exact partG37c_7_4554
  · exact partG37c_7_4610
  · exact partG37c_7_4666
  · exact partG37c_7_4722
  · exact partG37c_7_4778
  · exact partG37c_7_4834
  · exact partG37c_7_4890
theorem partG37c_7_4216 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="s" := by simpa using hx
  subst x
  exact partG37c_7_4217
theorem partG37c_7_4949 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","∅","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4950 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","∅","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4951 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","∅","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4952 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","∅","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4953 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","∅","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4954 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","∅","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4957 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","∅","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4958 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","∅","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4959 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","∅","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4960 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","∅","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4961 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","∅","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4962 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","∅","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4963 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","∅","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4964 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","∅","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4965 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","∅","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4966 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","∅","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
end ProductiveGua
