import PhonologicalOpacity.Attenuation.Productive.Baseline.CertificateParts.G37c_0_014
namespace ProductiveGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partG37c_0_1207 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","ʊ","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1208 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","ʊ","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1209 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","ʊ","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1196 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","ʊ","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_0_1197
  · exact partG37c_0_1198
  · exact partG37c_0_1199
  · exact partG37c_0_1200
  · exact partG37c_0_1201
  · exact partG37c_0_1202
  · exact partG37c_0_1203
  · exact partG37c_0_1204
  · exact partG37c_0_1205
  · exact partG37c_0_1206
  · exact partG37c_0_1207
  · exact partG37c_0_1208
  · exact partG37c_0_1209
theorem partG37c_0_1195 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","ʊ","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_0_1196
theorem partG37c_0_1210 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","ʊ","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1211 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","ʊ","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1212 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","ʊ","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1213 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","ʊ","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1216 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","ʊ","j","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1217 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","ʊ","j","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1218 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","ʊ","j","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1219 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","ʊ","j","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1220 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","ʊ","j","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1221 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","ʊ","j","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1222 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","ʊ","j","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1223 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","ʊ","j","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1224 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","ʊ","j","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1225 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","ʊ","j","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1226 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","ʊ","j","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1227 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","ʊ","j","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1228 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","ʊ","j","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1215 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","ʊ","j","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_0_1216
  · exact partG37c_0_1217
  · exact partG37c_0_1218
  · exact partG37c_0_1219
  · exact partG37c_0_1220
  · exact partG37c_0_1221
  · exact partG37c_0_1222
  · exact partG37c_0_1223
  · exact partG37c_0_1224
  · exact partG37c_0_1225
  · exact partG37c_0_1226
  · exact partG37c_0_1227
  · exact partG37c_0_1228
theorem partG37c_0_1214 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","ʊ","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_0_1215
theorem partG37c_0_1229 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","ʊ","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1174 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_0_1175
  · exact partG37c_0_1190
  · exact partG37c_0_1191
  · exact partG37c_0_1192
  · exact partG37c_0_1193
  · exact partG37c_0_1194
  · exact partG37c_0_1195
  · exact partG37c_0_1210
  · exact partG37c_0_1211
  · exact partG37c_0_1212
  · exact partG37c_0_1213
  · exact partG37c_0_1214
  · exact partG37c_0_1229
theorem partG37c_0_1231 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","u","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1232 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","u","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1233 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","u","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1234 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","u","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1235 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","u","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1236 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","u","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1239 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","u","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1240 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","u","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1241 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","u","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1242 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","u","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1243 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","u","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1244 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","u","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1245 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","u","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1246 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","u","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1247 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","u","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1248 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","u","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1249 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","u","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1250 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","u","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1251 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","u","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1238 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","u","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_0_1239
  · exact partG37c_0_1240
  · exact partG37c_0_1241
  · exact partG37c_0_1242
  · exact partG37c_0_1243
  · exact partG37c_0_1244
  · exact partG37c_0_1245
  · exact partG37c_0_1246
  · exact partG37c_0_1247
  · exact partG37c_0_1248
  · exact partG37c_0_1249
  · exact partG37c_0_1250
  · exact partG37c_0_1251
theorem partG37c_0_1237 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","u","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_0_1238
theorem partG37c_0_1252 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","u","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1253 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","u","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1254 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","u","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1255 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","u","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1256 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","u","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1257 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","u","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1230 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_0_1231
  · exact partG37c_0_1232
  · exact partG37c_0_1233
  · exact partG37c_0_1234
  · exact partG37c_0_1235
  · exact partG37c_0_1236
  · exact partG37c_0_1237
  · exact partG37c_0_1252
  · exact partG37c_0_1253
  · exact partG37c_0_1254
  · exact partG37c_0_1255
  · exact partG37c_0_1256
  · exact partG37c_0_1257
theorem partG37c_0_1259 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","j","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1260 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","j","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1261 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","j","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1262 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","j","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1263 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","j","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1264 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","j","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1267 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","j","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1268 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","j","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1269 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","j","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1270 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","j","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1271 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","j","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1272 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","j","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1273 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","j","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1274 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","j","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1275 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","j","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1276 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","j","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1277 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","j","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1278 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","j","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1279 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","j","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1266 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","j","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_0_1267
  · exact partG37c_0_1268
  · exact partG37c_0_1269
  · exact partG37c_0_1270
  · exact partG37c_0_1271
  · exact partG37c_0_1272
  · exact partG37c_0_1273
  · exact partG37c_0_1274
  · exact partG37c_0_1275
  · exact partG37c_0_1276
  · exact partG37c_0_1277
  · exact partG37c_0_1278
  · exact partG37c_0_1279
theorem partG37c_0_1265 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","j","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_0_1266
theorem partG37c_0_1280 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","j","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1281 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","j","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1282 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","j","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1283 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","j","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1284 : check uG37c (3) (0) outG37c ["∅","tʃ","ɛ","s","j","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
end ProductiveGua
