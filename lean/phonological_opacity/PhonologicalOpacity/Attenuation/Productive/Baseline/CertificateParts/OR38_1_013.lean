import PhonologicalOpacity.Attenuation.Productive.Baseline.CertificateParts.OR38_1_012
namespace ProductiveGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partOR38_1_1045 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","w","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1046 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","w","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1047 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","w","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1048 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","w","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1049 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","w","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1050 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","w","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1051 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","w","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1052 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","w","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1053 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","w","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1054 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","w","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1055 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","w","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1056 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","w","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1057 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","w","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1044 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_1045
  · exact partOR38_1_1046
  · exact partOR38_1_1047
  · exact partOR38_1_1048
  · exact partOR38_1_1049
  · exact partOR38_1_1050
  · exact partOR38_1_1051
  · exact partOR38_1_1052
  · exact partOR38_1_1053
  · exact partOR38_1_1054
  · exact partOR38_1_1055
  · exact partOR38_1_1056
  · exact partOR38_1_1057
theorem partOR38_1_875 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_876
  · exact partOR38_1_890
  · exact partOR38_1_904
  · exact partOR38_1_918
  · exact partOR38_1_932
  · exact partOR38_1_946
  · exact partOR38_1_960
  · exact partOR38_1_974
  · exact partOR38_1_988
  · exact partOR38_1_1002
  · exact partOR38_1_1016
  · exact partOR38_1_1030
  · exact partOR38_1_1044
theorem partOR38_1_874 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="s" := by simpa using hx
  subst x
  exact partOR38_1_875
theorem partOR38_1_1060 : check uOR38 (4) (-2) outOR38 ["a","tʃ","o","s","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1062 : check uOR38 (4) (-2) outOR38 ["a","tʃ","o","s","a","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1063 : check uOR38 (4) (-2) outOR38 ["a","tʃ","o","s","a","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1064 : check uOR38 (4) (-2) outOR38 ["a","tʃ","o","s","a","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1065 : check uOR38 (4) (-2) outOR38 ["a","tʃ","o","s","a","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1066 : check uOR38 (4) (-2) outOR38 ["a","tʃ","o","s","a","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1067 : check uOR38 (4) (-2) outOR38 ["a","tʃ","o","s","a","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1068 : check uOR38 (4) (-2) outOR38 ["a","tʃ","o","s","a","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1069 : check uOR38 (4) (-2) outOR38 ["a","tʃ","o","s","a","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1070 : check uOR38 (4) (-2) outOR38 ["a","tʃ","o","s","a","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1071 : check uOR38 (4) (-2) outOR38 ["a","tʃ","o","s","a","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1072 : check uOR38 (4) (-2) outOR38 ["a","tʃ","o","s","a","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1073 : check uOR38 (4) (-2) outOR38 ["a","tʃ","o","s","a","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1074 : check uOR38 (4) (-2) outOR38 ["a","tʃ","o","s","a","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1061 : check uOR38 (4) (-2) outOR38 ["a","tʃ","o","s","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_1062
  · exact partOR38_1_1063
  · exact partOR38_1_1064
  · exact partOR38_1_1065
  · exact partOR38_1_1066
  · exact partOR38_1_1067
  · exact partOR38_1_1068
  · exact partOR38_1_1069
  · exact partOR38_1_1070
  · exact partOR38_1_1071
  · exact partOR38_1_1072
  · exact partOR38_1_1073
  · exact partOR38_1_1074
theorem partOR38_1_1075 : check uOR38 (4) (-2) outOR38 ["a","tʃ","o","s","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1077 : check uOR38 (4) (-2) outOR38 ["a","tʃ","o","s","ɛ","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1078 : check uOR38 (4) (-2) outOR38 ["a","tʃ","o","s","ɛ","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1079 : check uOR38 (4) (-2) outOR38 ["a","tʃ","o","s","ɛ","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1080 : check uOR38 (4) (-2) outOR38 ["a","tʃ","o","s","ɛ","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1081 : check uOR38 (4) (-2) outOR38 ["a","tʃ","o","s","ɛ","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1082 : check uOR38 (4) (-2) outOR38 ["a","tʃ","o","s","ɛ","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1083 : check uOR38 (4) (-2) outOR38 ["a","tʃ","o","s","ɛ","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1084 : check uOR38 (4) (-2) outOR38 ["a","tʃ","o","s","ɛ","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1085 : check uOR38 (4) (-2) outOR38 ["a","tʃ","o","s","ɛ","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1086 : check uOR38 (4) (-2) outOR38 ["a","tʃ","o","s","ɛ","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1087 : check uOR38 (4) (-2) outOR38 ["a","tʃ","o","s","ɛ","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1088 : check uOR38 (4) (-2) outOR38 ["a","tʃ","o","s","ɛ","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1089 : check uOR38 (4) (-2) outOR38 ["a","tʃ","o","s","ɛ","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1076 : check uOR38 (4) (-2) outOR38 ["a","tʃ","o","s","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_1077
  · exact partOR38_1_1078
  · exact partOR38_1_1079
  · exact partOR38_1_1080
  · exact partOR38_1_1081
  · exact partOR38_1_1082
  · exact partOR38_1_1083
  · exact partOR38_1_1084
  · exact partOR38_1_1085
  · exact partOR38_1_1086
  · exact partOR38_1_1087
  · exact partOR38_1_1088
  · exact partOR38_1_1089
theorem partOR38_1_1090 : check uOR38 (4) (-2) outOR38 ["a","tʃ","o","s","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1092 : check uOR38 (4) (-2) outOR38 ["a","tʃ","o","s","ɪ","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1093 : check uOR38 (4) (-2) outOR38 ["a","tʃ","o","s","ɪ","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1094 : check uOR38 (4) (-2) outOR38 ["a","tʃ","o","s","ɪ","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1095 : check uOR38 (4) (-2) outOR38 ["a","tʃ","o","s","ɪ","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1096 : check uOR38 (4) (-2) outOR38 ["a","tʃ","o","s","ɪ","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1097 : check uOR38 (4) (-2) outOR38 ["a","tʃ","o","s","ɪ","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1098 : check uOR38 (4) (-2) outOR38 ["a","tʃ","o","s","ɪ","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1099 : check uOR38 (4) (-2) outOR38 ["a","tʃ","o","s","ɪ","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1100 : check uOR38 (4) (-2) outOR38 ["a","tʃ","o","s","ɪ","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1101 : check uOR38 (4) (-2) outOR38 ["a","tʃ","o","s","ɪ","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1102 : check uOR38 (4) (-2) outOR38 ["a","tʃ","o","s","ɪ","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1103 : check uOR38 (4) (-2) outOR38 ["a","tʃ","o","s","ɪ","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1104 : check uOR38 (4) (-2) outOR38 ["a","tʃ","o","s","ɪ","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1091 : check uOR38 (4) (-2) outOR38 ["a","tʃ","o","s","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_1092
  · exact partOR38_1_1093
  · exact partOR38_1_1094
  · exact partOR38_1_1095
  · exact partOR38_1_1096
  · exact partOR38_1_1097
  · exact partOR38_1_1098
  · exact partOR38_1_1099
  · exact partOR38_1_1100
  · exact partOR38_1_1101
  · exact partOR38_1_1102
  · exact partOR38_1_1103
  · exact partOR38_1_1104
theorem partOR38_1_1106 : check uOR38 (4) (-2) outOR38 ["a","tʃ","o","s","i","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1107 : check uOR38 (4) (-2) outOR38 ["a","tʃ","o","s","i","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1108 : check uOR38 (4) (-2) outOR38 ["a","tʃ","o","s","i","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1109 : check uOR38 (4) (-2) outOR38 ["a","tʃ","o","s","i","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1110 : check uOR38 (4) (-2) outOR38 ["a","tʃ","o","s","i","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1111 : check uOR38 (4) (-2) outOR38 ["a","tʃ","o","s","i","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1112 : check uOR38 (4) (-2) outOR38 ["a","tʃ","o","s","i","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1113 : check uOR38 (4) (-2) outOR38 ["a","tʃ","o","s","i","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1114 : check uOR38 (4) (-2) outOR38 ["a","tʃ","o","s","i","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1115 : check uOR38 (4) (-2) outOR38 ["a","tʃ","o","s","i","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1116 : check uOR38 (4) (-2) outOR38 ["a","tʃ","o","s","i","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1117 : check uOR38 (4) (-2) outOR38 ["a","tʃ","o","s","i","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1118 : check uOR38 (4) (-2) outOR38 ["a","tʃ","o","s","i","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1105 : check uOR38 (4) (-2) outOR38 ["a","tʃ","o","s","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_1106
  · exact partOR38_1_1107
  · exact partOR38_1_1108
  · exact partOR38_1_1109
  · exact partOR38_1_1110
  · exact partOR38_1_1111
  · exact partOR38_1_1112
  · exact partOR38_1_1113
  · exact partOR38_1_1114
  · exact partOR38_1_1115
  · exact partOR38_1_1116
  · exact partOR38_1_1117
  · exact partOR38_1_1118
theorem partOR38_1_1120 : check uOR38 (4) (-2) outOR38 ["a","tʃ","o","s","ɔ","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1121 : check uOR38 (4) (-2) outOR38 ["a","tʃ","o","s","ɔ","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1122 : check uOR38 (4) (-2) outOR38 ["a","tʃ","o","s","ɔ","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1123 : check uOR38 (4) (-2) outOR38 ["a","tʃ","o","s","ɔ","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1124 : check uOR38 (4) (-2) outOR38 ["a","tʃ","o","s","ɔ","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
end ProductiveGua
