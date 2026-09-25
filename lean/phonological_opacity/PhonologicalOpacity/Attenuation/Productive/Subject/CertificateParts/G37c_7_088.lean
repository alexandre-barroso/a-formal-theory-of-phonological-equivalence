import PhonologicalOpacity.Attenuation.Productive.Subject.CertificateParts.G37c_7_087
namespace ProductiveSubjectGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partG37c_7_7047 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","o","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7034 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","o","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_7035
  · exact partG37c_7_7036
  · exact partG37c_7_7037
  · exact partG37c_7_7038
  · exact partG37c_7_7039
  · exact partG37c_7_7040
  · exact partG37c_7_7041
  · exact partG37c_7_7042
  · exact partG37c_7_7043
  · exact partG37c_7_7044
  · exact partG37c_7_7045
  · exact partG37c_7_7046
  · exact partG37c_7_7047
theorem partG37c_7_7033 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","o","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_7034
theorem partG37c_7_7048 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","o","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7049 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","o","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7050 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","o","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7051 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","o","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7052 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","o","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7053 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","o","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7026 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_7027
  · exact partG37c_7_7028
  · exact partG37c_7_7029
  · exact partG37c_7_7030
  · exact partG37c_7_7031
  · exact partG37c_7_7032
  · exact partG37c_7_7033
  · exact partG37c_7_7048
  · exact partG37c_7_7049
  · exact partG37c_7_7050
  · exact partG37c_7_7051
  · exact partG37c_7_7052
  · exact partG37c_7_7053
theorem partG37c_7_7057 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ʊ","∅","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7058 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ʊ","∅","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7059 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ʊ","∅","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7060 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ʊ","∅","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7061 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ʊ","∅","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7062 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ʊ","∅","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7063 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ʊ","∅","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7064 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ʊ","∅","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7065 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ʊ","∅","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7066 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ʊ","∅","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7067 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ʊ","∅","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7068 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ʊ","∅","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7069 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ʊ","∅","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7056 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ʊ","∅","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_7057
  · exact partG37c_7_7058
  · exact partG37c_7_7059
  · exact partG37c_7_7060
  · exact partG37c_7_7061
  · exact partG37c_7_7062
  · exact partG37c_7_7063
  · exact partG37c_7_7064
  · exact partG37c_7_7065
  · exact partG37c_7_7066
  · exact partG37c_7_7067
  · exact partG37c_7_7068
  · exact partG37c_7_7069
theorem partG37c_7_7055 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ʊ","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_7056
theorem partG37c_7_7070 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ʊ","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7071 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ʊ","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7072 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ʊ","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7073 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ʊ","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7074 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ʊ","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7077 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ʊ","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7078 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ʊ","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7079 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ʊ","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7080 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ʊ","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7081 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ʊ","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7082 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ʊ","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7083 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ʊ","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7084 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ʊ","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7085 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ʊ","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7086 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ʊ","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7087 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ʊ","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7088 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ʊ","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7089 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ʊ","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7076 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ʊ","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_7077
  · exact partG37c_7_7078
  · exact partG37c_7_7079
  · exact partG37c_7_7080
  · exact partG37c_7_7081
  · exact partG37c_7_7082
  · exact partG37c_7_7083
  · exact partG37c_7_7084
  · exact partG37c_7_7085
  · exact partG37c_7_7086
  · exact partG37c_7_7087
  · exact partG37c_7_7088
  · exact partG37c_7_7089
theorem partG37c_7_7075 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ʊ","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_7076
theorem partG37c_7_7090 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ʊ","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7091 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ʊ","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7092 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ʊ","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7093 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ʊ","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7096 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ʊ","j","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7097 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ʊ","j","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7098 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ʊ","j","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7099 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ʊ","j","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7100 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ʊ","j","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7101 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ʊ","j","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7102 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ʊ","j","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7103 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ʊ","j","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7104 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ʊ","j","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7105 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ʊ","j","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7106 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ʊ","j","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7107 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ʊ","j","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7108 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ʊ","j","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7095 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ʊ","j","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_7096
  · exact partG37c_7_7097
  · exact partG37c_7_7098
  · exact partG37c_7_7099
  · exact partG37c_7_7100
  · exact partG37c_7_7101
  · exact partG37c_7_7102
  · exact partG37c_7_7103
  · exact partG37c_7_7104
  · exact partG37c_7_7105
  · exact partG37c_7_7106
  · exact partG37c_7_7107
  · exact partG37c_7_7108
theorem partG37c_7_7094 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ʊ","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_7095
theorem partG37c_7_7109 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ʊ","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7054 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_7055
  · exact partG37c_7_7070
  · exact partG37c_7_7071
  · exact partG37c_7_7072
  · exact partG37c_7_7073
  · exact partG37c_7_7074
  · exact partG37c_7_7075
  · exact partG37c_7_7090
  · exact partG37c_7_7091
  · exact partG37c_7_7092
  · exact partG37c_7_7093
  · exact partG37c_7_7094
  · exact partG37c_7_7109
theorem partG37c_7_7111 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","u","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7112 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","u","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7113 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","u","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7114 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","u","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7115 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","u","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7116 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","u","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7119 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","u","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7120 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","u","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7121 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","u","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7122 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","u","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7123 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","u","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7124 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","u","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7125 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","u","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7126 : check uG37c (3) (0) outG37c ["ɔ","tʃ","j","s","u","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
end ProductiveSubjectGua
