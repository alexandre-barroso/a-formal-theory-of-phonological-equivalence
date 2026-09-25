import PhonologicalOpacity.Attenuation.Productive.Baseline.CertificateParts.OR38_1_014
namespace ProductiveGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partOR38_1_1205 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","ɛ","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1206 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","ɛ","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1207 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","ɛ","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1208 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","ɛ","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1195 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_1196
  · exact partOR38_1_1197
  · exact partOR38_1_1198
  · exact partOR38_1_1199
  · exact partOR38_1_1200
  · exact partOR38_1_1201
  · exact partOR38_1_1202
  · exact partOR38_1_1203
  · exact partOR38_1_1204
  · exact partOR38_1_1205
  · exact partOR38_1_1206
  · exact partOR38_1_1207
  · exact partOR38_1_1208
theorem partOR38_1_1210 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","e","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1211 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","e","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1212 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","e","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1213 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","e","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1214 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","e","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1215 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","e","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1216 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","e","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1217 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","e","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1218 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","e","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1219 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","e","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1220 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","e","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1221 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","e","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1222 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","e","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1209 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_1210
  · exact partOR38_1_1211
  · exact partOR38_1_1212
  · exact partOR38_1_1213
  · exact partOR38_1_1214
  · exact partOR38_1_1215
  · exact partOR38_1_1216
  · exact partOR38_1_1217
  · exact partOR38_1_1218
  · exact partOR38_1_1219
  · exact partOR38_1_1220
  · exact partOR38_1_1221
  · exact partOR38_1_1222
theorem partOR38_1_1224 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","ɪ","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1225 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","ɪ","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1226 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","ɪ","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1227 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","ɪ","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1228 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","ɪ","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1229 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","ɪ","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1230 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","ɪ","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1231 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","ɪ","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1232 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","ɪ","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1233 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","ɪ","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1234 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","ɪ","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1235 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","ɪ","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1236 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","ɪ","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1223 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_1224
  · exact partOR38_1_1225
  · exact partOR38_1_1226
  · exact partOR38_1_1227
  · exact partOR38_1_1228
  · exact partOR38_1_1229
  · exact partOR38_1_1230
  · exact partOR38_1_1231
  · exact partOR38_1_1232
  · exact partOR38_1_1233
  · exact partOR38_1_1234
  · exact partOR38_1_1235
  · exact partOR38_1_1236
theorem partOR38_1_1238 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","i","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1239 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","i","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1240 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","i","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1241 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","i","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1242 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","i","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1243 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","i","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1244 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","i","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1245 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","i","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1246 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","i","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1247 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","i","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1248 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","i","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1249 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","i","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1250 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","i","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1237 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_1238
  · exact partOR38_1_1239
  · exact partOR38_1_1240
  · exact partOR38_1_1241
  · exact partOR38_1_1242
  · exact partOR38_1_1243
  · exact partOR38_1_1244
  · exact partOR38_1_1245
  · exact partOR38_1_1246
  · exact partOR38_1_1247
  · exact partOR38_1_1248
  · exact partOR38_1_1249
  · exact partOR38_1_1250
theorem partOR38_1_1252 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","ɔ","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1253 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","ɔ","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1254 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","ɔ","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1255 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","ɔ","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1256 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","ɔ","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1257 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","ɔ","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1258 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","ɔ","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1259 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","ɔ","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1260 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","ɔ","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1261 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","ɔ","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1262 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","ɔ","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1263 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","ɔ","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1264 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","ɔ","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1251 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_1252
  · exact partOR38_1_1253
  · exact partOR38_1_1254
  · exact partOR38_1_1255
  · exact partOR38_1_1256
  · exact partOR38_1_1257
  · exact partOR38_1_1258
  · exact partOR38_1_1259
  · exact partOR38_1_1260
  · exact partOR38_1_1261
  · exact partOR38_1_1262
  · exact partOR38_1_1263
  · exact partOR38_1_1264
theorem partOR38_1_1266 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","o","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1267 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","o","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1268 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","o","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1269 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","o","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1270 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","o","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1271 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","o","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1272 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","o","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1273 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","o","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1274 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","o","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1275 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","o","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1276 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","o","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1277 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","o","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1278 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","o","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1265 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_1266
  · exact partOR38_1_1267
  · exact partOR38_1_1268
  · exact partOR38_1_1269
  · exact partOR38_1_1270
  · exact partOR38_1_1271
  · exact partOR38_1_1272
  · exact partOR38_1_1273
  · exact partOR38_1_1274
  · exact partOR38_1_1275
  · exact partOR38_1_1276
  · exact partOR38_1_1277
  · exact partOR38_1_1278
theorem partOR38_1_1280 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","ʊ","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1281 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","ʊ","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1282 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","ʊ","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1283 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","ʊ","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1284 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","ʊ","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
end ProductiveGua
