import PhonologicalOpacity.Attenuation.Productive.Subject.CertificateParts.G37c_7_074
namespace ProductiveSubjectGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partG37c_7_6007 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ʊ","j","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6008 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ʊ","j","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6009 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ʊ","j","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6010 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ʊ","j","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6011 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ʊ","j","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6012 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ʊ","j","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5999 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ʊ","j","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_6000
  · exact partG37c_7_6001
  · exact partG37c_7_6002
  · exact partG37c_7_6003
  · exact partG37c_7_6004
  · exact partG37c_7_6005
  · exact partG37c_7_6006
  · exact partG37c_7_6007
  · exact partG37c_7_6008
  · exact partG37c_7_6009
  · exact partG37c_7_6010
  · exact partG37c_7_6011
  · exact partG37c_7_6012
theorem partG37c_7_5998 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ʊ","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_5999
theorem partG37c_7_6013 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ʊ","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5958 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_5959
  · exact partG37c_7_5974
  · exact partG37c_7_5975
  · exact partG37c_7_5976
  · exact partG37c_7_5977
  · exact partG37c_7_5978
  · exact partG37c_7_5979
  · exact partG37c_7_5994
  · exact partG37c_7_5995
  · exact partG37c_7_5996
  · exact partG37c_7_5997
  · exact partG37c_7_5998
  · exact partG37c_7_6013
theorem partG37c_7_6017 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","u","∅","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6018 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","u","∅","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6019 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","u","∅","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6020 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","u","∅","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6021 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","u","∅","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6022 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","u","∅","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6023 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","u","∅","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6024 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","u","∅","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6025 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","u","∅","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6026 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","u","∅","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6027 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","u","∅","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6028 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","u","∅","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6029 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","u","∅","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6016 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","u","∅","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_6017
  · exact partG37c_7_6018
  · exact partG37c_7_6019
  · exact partG37c_7_6020
  · exact partG37c_7_6021
  · exact partG37c_7_6022
  · exact partG37c_7_6023
  · exact partG37c_7_6024
  · exact partG37c_7_6025
  · exact partG37c_7_6026
  · exact partG37c_7_6027
  · exact partG37c_7_6028
  · exact partG37c_7_6029
theorem partG37c_7_6015 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","u","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_6016
theorem partG37c_7_6030 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","u","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6031 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","u","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6032 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","u","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6033 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","u","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6034 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","u","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6037 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","u","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6038 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","u","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6039 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","u","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6040 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","u","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6041 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","u","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6042 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","u","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6043 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","u","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6044 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","u","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6045 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","u","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6046 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","u","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6047 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","u","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6048 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","u","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6049 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","u","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6036 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","u","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_6037
  · exact partG37c_7_6038
  · exact partG37c_7_6039
  · exact partG37c_7_6040
  · exact partG37c_7_6041
  · exact partG37c_7_6042
  · exact partG37c_7_6043
  · exact partG37c_7_6044
  · exact partG37c_7_6045
  · exact partG37c_7_6046
  · exact partG37c_7_6047
  · exact partG37c_7_6048
  · exact partG37c_7_6049
theorem partG37c_7_6035 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","u","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_6036
theorem partG37c_7_6050 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","u","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6051 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","u","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6052 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","u","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6053 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","u","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6056 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","u","j","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6057 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","u","j","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6058 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","u","j","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6059 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","u","j","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6060 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","u","j","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6061 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","u","j","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6062 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","u","j","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6063 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","u","j","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6064 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","u","j","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6065 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","u","j","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6066 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","u","j","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6067 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","u","j","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6068 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","u","j","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6055 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","u","j","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_6056
  · exact partG37c_7_6057
  · exact partG37c_7_6058
  · exact partG37c_7_6059
  · exact partG37c_7_6060
  · exact partG37c_7_6061
  · exact partG37c_7_6062
  · exact partG37c_7_6063
  · exact partG37c_7_6064
  · exact partG37c_7_6065
  · exact partG37c_7_6066
  · exact partG37c_7_6067
  · exact partG37c_7_6068
theorem partG37c_7_6054 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","u","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_6055
theorem partG37c_7_6069 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","u","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6014 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_6015
  · exact partG37c_7_6030
  · exact partG37c_7_6031
  · exact partG37c_7_6032
  · exact partG37c_7_6033
  · exact partG37c_7_6034
  · exact partG37c_7_6035
  · exact partG37c_7_6050
  · exact partG37c_7_6051
  · exact partG37c_7_6052
  · exact partG37c_7_6053
  · exact partG37c_7_6054
  · exact partG37c_7_6069
theorem partG37c_7_6073 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","j","∅","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6074 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","j","∅","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6075 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","j","∅","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6076 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","j","∅","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6077 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","j","∅","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6078 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","j","∅","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6079 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","j","∅","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6080 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","j","∅","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6081 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","j","∅","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6082 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","j","∅","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6083 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","j","∅","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6084 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","j","∅","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6085 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","j","∅","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6072 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","j","∅","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_6073
  · exact partG37c_7_6074
  · exact partG37c_7_6075
  · exact partG37c_7_6076
  · exact partG37c_7_6077
  · exact partG37c_7_6078
  · exact partG37c_7_6079
  · exact partG37c_7_6080
  · exact partG37c_7_6081
  · exact partG37c_7_6082
  · exact partG37c_7_6083
  · exact partG37c_7_6084
  · exact partG37c_7_6085
end ProductiveSubjectGua
