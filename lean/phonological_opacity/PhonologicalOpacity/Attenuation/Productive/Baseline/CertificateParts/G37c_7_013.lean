import PhonologicalOpacity.Attenuation.Productive.Baseline.CertificateParts.G37c_7_012
namespace ProductiveGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partG37c_7_1047 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ʊ","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1048 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ʊ","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1049 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ʊ","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1036 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ʊ","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_1037
  · exact partG37c_7_1038
  · exact partG37c_7_1039
  · exact partG37c_7_1040
  · exact partG37c_7_1041
  · exact partG37c_7_1042
  · exact partG37c_7_1043
  · exact partG37c_7_1044
  · exact partG37c_7_1045
  · exact partG37c_7_1046
  · exact partG37c_7_1047
  · exact partG37c_7_1048
  · exact partG37c_7_1049
theorem partG37c_7_1035 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ʊ","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_1036
theorem partG37c_7_1050 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ʊ","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1051 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ʊ","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1052 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ʊ","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1053 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ʊ","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1056 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ʊ","j","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1057 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ʊ","j","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1058 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ʊ","j","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1059 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ʊ","j","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1060 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ʊ","j","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1061 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ʊ","j","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1062 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ʊ","j","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1063 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ʊ","j","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1064 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ʊ","j","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1065 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ʊ","j","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1066 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ʊ","j","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1067 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ʊ","j","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1068 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ʊ","j","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1055 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ʊ","j","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_1056
  · exact partG37c_7_1057
  · exact partG37c_7_1058
  · exact partG37c_7_1059
  · exact partG37c_7_1060
  · exact partG37c_7_1061
  · exact partG37c_7_1062
  · exact partG37c_7_1063
  · exact partG37c_7_1064
  · exact partG37c_7_1065
  · exact partG37c_7_1066
  · exact partG37c_7_1067
  · exact partG37c_7_1068
theorem partG37c_7_1054 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ʊ","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_1055
theorem partG37c_7_1069 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ʊ","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1014 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_1015
  · exact partG37c_7_1030
  · exact partG37c_7_1031
  · exact partG37c_7_1032
  · exact partG37c_7_1033
  · exact partG37c_7_1034
  · exact partG37c_7_1035
  · exact partG37c_7_1050
  · exact partG37c_7_1051
  · exact partG37c_7_1052
  · exact partG37c_7_1053
  · exact partG37c_7_1054
  · exact partG37c_7_1069
theorem partG37c_7_1073 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","u","∅","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1074 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","u","∅","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1075 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","u","∅","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1076 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","u","∅","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1077 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","u","∅","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1078 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","u","∅","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1079 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","u","∅","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1080 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","u","∅","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1081 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","u","∅","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1082 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","u","∅","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1083 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","u","∅","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1084 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","u","∅","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1085 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","u","∅","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1072 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","u","∅","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_1073
  · exact partG37c_7_1074
  · exact partG37c_7_1075
  · exact partG37c_7_1076
  · exact partG37c_7_1077
  · exact partG37c_7_1078
  · exact partG37c_7_1079
  · exact partG37c_7_1080
  · exact partG37c_7_1081
  · exact partG37c_7_1082
  · exact partG37c_7_1083
  · exact partG37c_7_1084
  · exact partG37c_7_1085
theorem partG37c_7_1071 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","u","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_1072
theorem partG37c_7_1086 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","u","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1087 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","u","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1088 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","u","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1089 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","u","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1090 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","u","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1093 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","u","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1094 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","u","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1095 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","u","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1096 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","u","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1097 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","u","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1098 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","u","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1099 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","u","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1100 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","u","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1101 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","u","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1102 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","u","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1103 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","u","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1104 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","u","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1105 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","u","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1092 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","u","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_1093
  · exact partG37c_7_1094
  · exact partG37c_7_1095
  · exact partG37c_7_1096
  · exact partG37c_7_1097
  · exact partG37c_7_1098
  · exact partG37c_7_1099
  · exact partG37c_7_1100
  · exact partG37c_7_1101
  · exact partG37c_7_1102
  · exact partG37c_7_1103
  · exact partG37c_7_1104
  · exact partG37c_7_1105
theorem partG37c_7_1091 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","u","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_1092
theorem partG37c_7_1106 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","u","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1107 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","u","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1108 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","u","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1109 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","u","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1112 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","u","j","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1113 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","u","j","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1114 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","u","j","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1115 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","u","j","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1116 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","u","j","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1117 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","u","j","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1118 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","u","j","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1119 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","u","j","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1120 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","u","j","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1121 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","u","j","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1122 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","u","j","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1123 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","u","j","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1124 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","u","j","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1111 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","u","j","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_1112
  · exact partG37c_7_1113
  · exact partG37c_7_1114
  · exact partG37c_7_1115
  · exact partG37c_7_1116
  · exact partG37c_7_1117
  · exact partG37c_7_1118
  · exact partG37c_7_1119
  · exact partG37c_7_1120
  · exact partG37c_7_1121
  · exact partG37c_7_1122
  · exact partG37c_7_1123
  · exact partG37c_7_1124
theorem partG37c_7_1110 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","u","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_1111
end ProductiveGua
