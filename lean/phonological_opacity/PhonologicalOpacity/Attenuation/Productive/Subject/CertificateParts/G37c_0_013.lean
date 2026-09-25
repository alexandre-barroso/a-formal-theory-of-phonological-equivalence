import PhonologicalOpacity.Attenuation.Productive.Subject.CertificateParts.G37c_0_012
namespace ProductiveSubjectGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partG37c_0_1045 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","ɪ","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1048 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","ɪ","j","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1049 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","ɪ","j","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1050 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","ɪ","j","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1051 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","ɪ","j","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1052 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","ɪ","j","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1053 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","ɪ","j","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1054 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","ɪ","j","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1055 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","ɪ","j","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1056 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","ɪ","j","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1057 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","ɪ","j","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1058 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","ɪ","j","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1059 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","ɪ","j","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1060 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","ɪ","j","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1047 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","ɪ","j","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_0_1048
  · exact partG37c_0_1049
  · exact partG37c_0_1050
  · exact partG37c_0_1051
  · exact partG37c_0_1052
  · exact partG37c_0_1053
  · exact partG37c_0_1054
  · exact partG37c_0_1055
  · exact partG37c_0_1056
  · exact partG37c_0_1057
  · exact partG37c_0_1058
  · exact partG37c_0_1059
  · exact partG37c_0_1060
theorem partG37c_0_1046 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","ɪ","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_0_1047
theorem partG37c_0_1061 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","ɪ","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1006 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_0_1007
  · exact partG37c_0_1022
  · exact partG37c_0_1023
  · exact partG37c_0_1024
  · exact partG37c_0_1025
  · exact partG37c_0_1026
  · exact partG37c_0_1027
  · exact partG37c_0_1042
  · exact partG37c_0_1043
  · exact partG37c_0_1044
  · exact partG37c_0_1045
  · exact partG37c_0_1046
  · exact partG37c_0_1061
theorem partG37c_0_1063 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","i","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1064 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","i","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1065 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","i","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1066 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","i","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1067 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","i","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1068 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","i","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1071 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","i","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1072 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","i","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1073 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","i","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1074 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","i","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1075 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","i","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1076 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","i","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1077 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","i","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1078 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","i","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1079 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","i","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1080 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","i","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1081 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","i","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1082 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","i","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1083 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","i","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1070 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","i","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_0_1071
  · exact partG37c_0_1072
  · exact partG37c_0_1073
  · exact partG37c_0_1074
  · exact partG37c_0_1075
  · exact partG37c_0_1076
  · exact partG37c_0_1077
  · exact partG37c_0_1078
  · exact partG37c_0_1079
  · exact partG37c_0_1080
  · exact partG37c_0_1081
  · exact partG37c_0_1082
  · exact partG37c_0_1083
theorem partG37c_0_1069 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","i","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_0_1070
theorem partG37c_0_1084 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","i","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1085 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","i","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1086 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","i","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1087 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","i","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1088 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","i","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1089 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","i","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1062 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_0_1063
  · exact partG37c_0_1064
  · exact partG37c_0_1065
  · exact partG37c_0_1066
  · exact partG37c_0_1067
  · exact partG37c_0_1068
  · exact partG37c_0_1069
  · exact partG37c_0_1084
  · exact partG37c_0_1085
  · exact partG37c_0_1086
  · exact partG37c_0_1087
  · exact partG37c_0_1088
  · exact partG37c_0_1089
theorem partG37c_0_1093 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","ɔ","∅","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1094 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","ɔ","∅","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1095 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","ɔ","∅","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1096 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","ɔ","∅","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1097 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","ɔ","∅","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1098 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","ɔ","∅","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1099 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","ɔ","∅","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1100 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","ɔ","∅","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1101 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","ɔ","∅","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1102 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","ɔ","∅","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1103 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","ɔ","∅","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1104 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","ɔ","∅","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1105 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","ɔ","∅","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1092 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","ɔ","∅","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_0_1093
  · exact partG37c_0_1094
  · exact partG37c_0_1095
  · exact partG37c_0_1096
  · exact partG37c_0_1097
  · exact partG37c_0_1098
  · exact partG37c_0_1099
  · exact partG37c_0_1100
  · exact partG37c_0_1101
  · exact partG37c_0_1102
  · exact partG37c_0_1103
  · exact partG37c_0_1104
  · exact partG37c_0_1105
theorem partG37c_0_1091 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","ɔ","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_0_1092
theorem partG37c_0_1106 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","ɔ","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1107 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","ɔ","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1108 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","ɔ","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1109 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","ɔ","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1110 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","ɔ","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1113 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","ɔ","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1114 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","ɔ","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1115 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","ɔ","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1116 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","ɔ","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1117 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","ɔ","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1118 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","ɔ","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1119 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","ɔ","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1120 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","ɔ","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1121 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","ɔ","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1122 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","ɔ","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1123 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","ɔ","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1124 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","ɔ","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1125 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","ɔ","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1112 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","ɔ","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_0_1113
  · exact partG37c_0_1114
  · exact partG37c_0_1115
  · exact partG37c_0_1116
  · exact partG37c_0_1117
  · exact partG37c_0_1118
  · exact partG37c_0_1119
  · exact partG37c_0_1120
  · exact partG37c_0_1121
  · exact partG37c_0_1122
  · exact partG37c_0_1123
  · exact partG37c_0_1124
  · exact partG37c_0_1125
end ProductiveSubjectGua
