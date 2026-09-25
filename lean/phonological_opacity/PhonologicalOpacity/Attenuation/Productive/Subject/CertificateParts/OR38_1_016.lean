import PhonologicalOpacity.Attenuation.Productive.Subject.CertificateParts.OR38_1_015
namespace ProductiveSubjectGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partOR38_1_1285 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","ʊ","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1286 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","ʊ","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1287 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","ʊ","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1288 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","ʊ","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1289 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","ʊ","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1290 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","ʊ","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1291 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","ʊ","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1292 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","ʊ","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1279 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_1280
  · exact partOR38_1_1281
  · exact partOR38_1_1282
  · exact partOR38_1_1283
  · exact partOR38_1_1284
  · exact partOR38_1_1285
  · exact partOR38_1_1286
  · exact partOR38_1_1287
  · exact partOR38_1_1288
  · exact partOR38_1_1289
  · exact partOR38_1_1290
  · exact partOR38_1_1291
  · exact partOR38_1_1292
theorem partOR38_1_1294 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","u","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1295 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","u","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1296 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","u","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1297 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","u","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1298 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","u","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1299 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","u","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1300 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","u","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1301 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","u","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1302 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","u","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1303 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","u","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1304 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","u","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1305 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","u","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1306 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","u","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1293 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_1294
  · exact partOR38_1_1295
  · exact partOR38_1_1296
  · exact partOR38_1_1297
  · exact partOR38_1_1298
  · exact partOR38_1_1299
  · exact partOR38_1_1300
  · exact partOR38_1_1301
  · exact partOR38_1_1302
  · exact partOR38_1_1303
  · exact partOR38_1_1304
  · exact partOR38_1_1305
  · exact partOR38_1_1306
theorem partOR38_1_1308 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","j","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1309 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","j","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1310 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","j","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1311 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","j","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1312 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","j","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1313 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","j","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1314 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","j","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1315 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","j","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1316 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","j","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1317 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","j","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1318 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","j","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1319 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","j","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1320 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","j","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1307 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_1308
  · exact partOR38_1_1309
  · exact partOR38_1_1310
  · exact partOR38_1_1311
  · exact partOR38_1_1312
  · exact partOR38_1_1313
  · exact partOR38_1_1314
  · exact partOR38_1_1315
  · exact partOR38_1_1316
  · exact partOR38_1_1317
  · exact partOR38_1_1318
  · exact partOR38_1_1319
  · exact partOR38_1_1320
theorem partOR38_1_1322 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","w","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1323 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","w","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1324 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","w","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1325 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","w","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1326 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","w","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1327 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","w","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1328 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","w","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1329 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","w","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1330 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","w","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1331 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","w","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1332 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","w","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1333 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","w","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1334 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","w","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1321 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_1322
  · exact partOR38_1_1323
  · exact partOR38_1_1324
  · exact partOR38_1_1325
  · exact partOR38_1_1326
  · exact partOR38_1_1327
  · exact partOR38_1_1328
  · exact partOR38_1_1329
  · exact partOR38_1_1330
  · exact partOR38_1_1331
  · exact partOR38_1_1332
  · exact partOR38_1_1333
  · exact partOR38_1_1334
theorem partOR38_1_1152 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ","s"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_1153
  · exact partOR38_1_1167
  · exact partOR38_1_1181
  · exact partOR38_1_1195
  · exact partOR38_1_1209
  · exact partOR38_1_1223
  · exact partOR38_1_1237
  · exact partOR38_1_1251
  · exact partOR38_1_1265
  · exact partOR38_1_1279
  · exact partOR38_1_1293
  · exact partOR38_1_1307
  · exact partOR38_1_1321
theorem partOR38_1_1151 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ʊ"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="s" := by simpa using hx
  subst x
  exact partOR38_1_1152
theorem partOR38_1_1337 : check uOR38 (4) (-2) outOR38 ["a","tʃ","u","s","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1339 : check uOR38 (4) (-2) outOR38 ["a","tʃ","u","s","a","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1340 : check uOR38 (4) (-2) outOR38 ["a","tʃ","u","s","a","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1341 : check uOR38 (4) (-2) outOR38 ["a","tʃ","u","s","a","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1342 : check uOR38 (4) (-2) outOR38 ["a","tʃ","u","s","a","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1343 : check uOR38 (4) (-2) outOR38 ["a","tʃ","u","s","a","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1344 : check uOR38 (4) (-2) outOR38 ["a","tʃ","u","s","a","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1345 : check uOR38 (4) (-2) outOR38 ["a","tʃ","u","s","a","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1346 : check uOR38 (4) (-2) outOR38 ["a","tʃ","u","s","a","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1347 : check uOR38 (4) (-2) outOR38 ["a","tʃ","u","s","a","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1348 : check uOR38 (4) (-2) outOR38 ["a","tʃ","u","s","a","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1349 : check uOR38 (4) (-2) outOR38 ["a","tʃ","u","s","a","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1350 : check uOR38 (4) (-2) outOR38 ["a","tʃ","u","s","a","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1351 : check uOR38 (4) (-2) outOR38 ["a","tʃ","u","s","a","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1338 : check uOR38 (4) (-2) outOR38 ["a","tʃ","u","s","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_1339
  · exact partOR38_1_1340
  · exact partOR38_1_1341
  · exact partOR38_1_1342
  · exact partOR38_1_1343
  · exact partOR38_1_1344
  · exact partOR38_1_1345
  · exact partOR38_1_1346
  · exact partOR38_1_1347
  · exact partOR38_1_1348
  · exact partOR38_1_1349
  · exact partOR38_1_1350
  · exact partOR38_1_1351
theorem partOR38_1_1352 : check uOR38 (4) (-2) outOR38 ["a","tʃ","u","s","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1354 : check uOR38 (4) (-2) outOR38 ["a","tʃ","u","s","ɛ","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1355 : check uOR38 (4) (-2) outOR38 ["a","tʃ","u","s","ɛ","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1356 : check uOR38 (4) (-2) outOR38 ["a","tʃ","u","s","ɛ","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1357 : check uOR38 (4) (-2) outOR38 ["a","tʃ","u","s","ɛ","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1358 : check uOR38 (4) (-2) outOR38 ["a","tʃ","u","s","ɛ","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1359 : check uOR38 (4) (-2) outOR38 ["a","tʃ","u","s","ɛ","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1360 : check uOR38 (4) (-2) outOR38 ["a","tʃ","u","s","ɛ","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1361 : check uOR38 (4) (-2) outOR38 ["a","tʃ","u","s","ɛ","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1362 : check uOR38 (4) (-2) outOR38 ["a","tʃ","u","s","ɛ","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1363 : check uOR38 (4) (-2) outOR38 ["a","tʃ","u","s","ɛ","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1364 : check uOR38 (4) (-2) outOR38 ["a","tʃ","u","s","ɛ","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
end ProductiveSubjectGua
