import PhonologicalOpacity.Attenuation.Productive.Subject.CertificateParts.OR38_1_013
namespace ProductiveSubjectGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partOR38_1_1125 : check uOR38 (4) (-2) outOR38 ["a","tʃ","o","s","ɔ","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1126 : check uOR38 (4) (-2) outOR38 ["a","tʃ","o","s","ɔ","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1127 : check uOR38 (4) (-2) outOR38 ["a","tʃ","o","s","ɔ","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1128 : check uOR38 (4) (-2) outOR38 ["a","tʃ","o","s","ɔ","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1129 : check uOR38 (4) (-2) outOR38 ["a","tʃ","o","s","ɔ","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1130 : check uOR38 (4) (-2) outOR38 ["a","tʃ","o","s","ɔ","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1131 : check uOR38 (4) (-2) outOR38 ["a","tʃ","o","s","ɔ","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1132 : check uOR38 (4) (-2) outOR38 ["a","tʃ","o","s","ɔ","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1119 : check uOR38 (4) (-2) outOR38 ["a","tʃ","o","s","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_1120
  · exact partOR38_1_1121
  · exact partOR38_1_1122
  · exact partOR38_1_1123
  · exact partOR38_1_1124
  · exact partOR38_1_1125
  · exact partOR38_1_1126
  · exact partOR38_1_1127
  · exact partOR38_1_1128
  · exact partOR38_1_1129
  · exact partOR38_1_1130
  · exact partOR38_1_1131
  · exact partOR38_1_1132
theorem partOR38_1_1133 : check uOR38 (4) (-2) outOR38 ["a","tʃ","o","s","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1135 : check uOR38 (4) (-2) outOR38 ["a","tʃ","o","s","ʊ","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1136 : check uOR38 (4) (-2) outOR38 ["a","tʃ","o","s","ʊ","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1137 : check uOR38 (4) (-2) outOR38 ["a","tʃ","o","s","ʊ","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1138 : check uOR38 (4) (-2) outOR38 ["a","tʃ","o","s","ʊ","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1139 : check uOR38 (4) (-2) outOR38 ["a","tʃ","o","s","ʊ","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1140 : check uOR38 (4) (-2) outOR38 ["a","tʃ","o","s","ʊ","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1141 : check uOR38 (4) (-2) outOR38 ["a","tʃ","o","s","ʊ","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1142 : check uOR38 (4) (-2) outOR38 ["a","tʃ","o","s","ʊ","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1143 : check uOR38 (4) (-2) outOR38 ["a","tʃ","o","s","ʊ","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1144 : check uOR38 (4) (-2) outOR38 ["a","tʃ","o","s","ʊ","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1145 : check uOR38 (4) (-2) outOR38 ["a","tʃ","o","s","ʊ","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1146 : check uOR38 (4) (-2) outOR38 ["a","tʃ","o","s","ʊ","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1147 : check uOR38 (4) (-2) outOR38 ["a","tʃ","o","s","ʊ","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1134 : check uOR38 (4) (-2) outOR38 ["a","tʃ","o","s","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_1135
  · exact partOR38_1_1136
  · exact partOR38_1_1137
  · exact partOR38_1_1138
  · exact partOR38_1_1139
  · exact partOR38_1_1140
  · exact partOR38_1_1141
  · exact partOR38_1_1142
  · exact partOR38_1_1143
  · exact partOR38_1_1144
  · exact partOR38_1_1145
  · exact partOR38_1_1146
  · exact partOR38_1_1147
theorem partOR38_1_1148 : check uOR38 (4) (-2) outOR38 ["a","tʃ","o","s","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1149 : check uOR38 (4) (-2) outOR38 ["a","tʃ","o","s","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1150 : check uOR38 (4) (-2) outOR38 ["a","tʃ","o","s","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1059 : check uOR38 (4) (-2) outOR38 ["a","tʃ","o","s"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_1060
  · exact partOR38_1_1061
  · exact partOR38_1_1075
  · exact partOR38_1_1076
  · exact partOR38_1_1090
  · exact partOR38_1_1091
  · exact partOR38_1_1105
  · exact partOR38_1_1119
  · exact partOR38_1_1133
  · exact partOR38_1_1134
  · exact partOR38_1_1148
  · exact partOR38_1_1149
  · exact partOR38_1_1150
theorem partOR38_1_1058 : check uOR38 (4) (-2) outOR38 ["a","tʃ","o"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="s" := by simpa using hx
  subst x
  exact partOR38_1_1059
theorem partOR38_1_1154 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","∅","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1155 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","∅","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1156 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","∅","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1157 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","∅","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1158 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","∅","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1159 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","∅","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1160 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","∅","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1161 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","∅","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1162 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","∅","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1163 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","∅","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1164 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","∅","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1165 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","∅","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1166 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","∅","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1153 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_1154
  · exact partOR38_1_1155
  · exact partOR38_1_1156
  · exact partOR38_1_1157
  · exact partOR38_1_1158
  · exact partOR38_1_1159
  · exact partOR38_1_1160
  · exact partOR38_1_1161
  · exact partOR38_1_1162
  · exact partOR38_1_1163
  · exact partOR38_1_1164
  · exact partOR38_1_1165
  · exact partOR38_1_1166
theorem partOR38_1_1168 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","a","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1169 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","a","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1170 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","a","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1171 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","a","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1172 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","a","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1173 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","a","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1174 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","a","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1175 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","a","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1176 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","a","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1177 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","a","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1178 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","a","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1179 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","a","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1180 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","a","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1167 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_1168
  · exact partOR38_1_1169
  · exact partOR38_1_1170
  · exact partOR38_1_1171
  · exact partOR38_1_1172
  · exact partOR38_1_1173
  · exact partOR38_1_1174
  · exact partOR38_1_1175
  · exact partOR38_1_1176
  · exact partOR38_1_1177
  · exact partOR38_1_1178
  · exact partOR38_1_1179
  · exact partOR38_1_1180
theorem partOR38_1_1182 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","ɜ","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1183 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","ɜ","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1184 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","ɜ","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1185 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","ɜ","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1186 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","ɜ","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1187 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","ɜ","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1188 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","ɜ","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1189 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","ɜ","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1190 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","ɜ","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1191 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","ɜ","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1192 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","ɜ","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1193 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","ɜ","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1194 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","ɜ","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1181 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_1182
  · exact partOR38_1_1183
  · exact partOR38_1_1184
  · exact partOR38_1_1185
  · exact partOR38_1_1186
  · exact partOR38_1_1187
  · exact partOR38_1_1188
  · exact partOR38_1_1189
  · exact partOR38_1_1190
  · exact partOR38_1_1191
  · exact partOR38_1_1192
  · exact partOR38_1_1193
  · exact partOR38_1_1194
theorem partOR38_1_1196 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","ɛ","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1197 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","ɛ","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1198 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","ɛ","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1199 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","ɛ","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1200 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","ɛ","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1201 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","ɛ","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1202 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","ɛ","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1203 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","ɛ","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1204 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","ɛ","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
end ProductiveSubjectGua
