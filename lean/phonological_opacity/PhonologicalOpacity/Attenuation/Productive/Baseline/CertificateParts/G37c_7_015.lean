import PhonologicalOpacity.Attenuation.Productive.Baseline.CertificateParts.G37c_7_014
namespace ProductiveGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partG37c_7_1207 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","w","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1208 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","w","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1209 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","w","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1210 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","w","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1211 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","w","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1212 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","w","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1213 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","w","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1214 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","w","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1215 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","w","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1216 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","w","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1217 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","w","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1204 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","w","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_1205
  · exact partG37c_7_1206
  · exact partG37c_7_1207
  · exact partG37c_7_1208
  · exact partG37c_7_1209
  · exact partG37c_7_1210
  · exact partG37c_7_1211
  · exact partG37c_7_1212
  · exact partG37c_7_1213
  · exact partG37c_7_1214
  · exact partG37c_7_1215
  · exact partG37c_7_1216
  · exact partG37c_7_1217
theorem partG37c_7_1203 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","w","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_1204
theorem partG37c_7_1218 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","w","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1219 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","w","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1220 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","w","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1221 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","w","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1224 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","w","j","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1225 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","w","j","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1226 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","w","j","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1227 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","w","j","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1228 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","w","j","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1229 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","w","j","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1230 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","w","j","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1231 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","w","j","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1232 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","w","j","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1233 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","w","j","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1234 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","w","j","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1235 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","w","j","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1236 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","w","j","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1223 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","w","j","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_1224
  · exact partG37c_7_1225
  · exact partG37c_7_1226
  · exact partG37c_7_1227
  · exact partG37c_7_1228
  · exact partG37c_7_1229
  · exact partG37c_7_1230
  · exact partG37c_7_1231
  · exact partG37c_7_1232
  · exact partG37c_7_1233
  · exact partG37c_7_1234
  · exact partG37c_7_1235
  · exact partG37c_7_1236
theorem partG37c_7_1222 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","w","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_1223
theorem partG37c_7_1237 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","w","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1182 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_1183
  · exact partG37c_7_1198
  · exact partG37c_7_1199
  · exact partG37c_7_1200
  · exact partG37c_7_1201
  · exact partG37c_7_1202
  · exact partG37c_7_1203
  · exact partG37c_7_1218
  · exact partG37c_7_1219
  · exact partG37c_7_1220
  · exact partG37c_7_1221
  · exact partG37c_7_1222
  · exact partG37c_7_1237
theorem partG37c_7_509 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_510
  · exact partG37c_7_566
  · exact partG37c_7_622
  · exact partG37c_7_678
  · exact partG37c_7_734
  · exact partG37c_7_790
  · exact partG37c_7_846
  · exact partG37c_7_902
  · exact partG37c_7_958
  · exact partG37c_7_1014
  · exact partG37c_7_1070
  · exact partG37c_7_1126
  · exact partG37c_7_1182
theorem partG37c_7_508 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="s" := by simpa using hx
  subst x
  exact partG37c_7_509
theorem partG37c_7_1241 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","∅","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1242 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","∅","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1243 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","∅","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1244 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","∅","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1245 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","∅","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1246 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","∅","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1249 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","∅","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1250 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","∅","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1251 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","∅","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1252 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","∅","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1253 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","∅","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1254 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","∅","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1255 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","∅","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1256 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","∅","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1257 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","∅","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1258 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","∅","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1259 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","∅","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1260 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","∅","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1261 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","∅","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1248 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","∅","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_1249
  · exact partG37c_7_1250
  · exact partG37c_7_1251
  · exact partG37c_7_1252
  · exact partG37c_7_1253
  · exact partG37c_7_1254
  · exact partG37c_7_1255
  · exact partG37c_7_1256
  · exact partG37c_7_1257
  · exact partG37c_7_1258
  · exact partG37c_7_1259
  · exact partG37c_7_1260
  · exact partG37c_7_1261
theorem partG37c_7_1247 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","∅","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_1248
theorem partG37c_7_1262 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","∅","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1263 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","∅","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1264 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","∅","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1265 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","∅","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1266 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","∅","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1267 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","∅","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1240 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_1241
  · exact partG37c_7_1242
  · exact partG37c_7_1243
  · exact partG37c_7_1244
  · exact partG37c_7_1245
  · exact partG37c_7_1246
  · exact partG37c_7_1247
  · exact partG37c_7_1262
  · exact partG37c_7_1263
  · exact partG37c_7_1264
  · exact partG37c_7_1265
  · exact partG37c_7_1266
  · exact partG37c_7_1267
theorem partG37c_7_1271 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","a","∅","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1272 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","a","∅","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1273 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","a","∅","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1274 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","a","∅","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1275 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","a","∅","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1276 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","a","∅","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1277 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","a","∅","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1278 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","a","∅","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1279 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","a","∅","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1280 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","a","∅","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1281 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","a","∅","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1282 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","a","∅","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1283 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","a","∅","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1270 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","a","∅","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_1271
  · exact partG37c_7_1272
  · exact partG37c_7_1273
  · exact partG37c_7_1274
  · exact partG37c_7_1275
  · exact partG37c_7_1276
  · exact partG37c_7_1277
  · exact partG37c_7_1278
  · exact partG37c_7_1279
  · exact partG37c_7_1280
  · exact partG37c_7_1281
  · exact partG37c_7_1282
  · exact partG37c_7_1283
theorem partG37c_7_1269 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","a","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_1270
theorem partG37c_7_1284 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","a","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
end ProductiveGua
