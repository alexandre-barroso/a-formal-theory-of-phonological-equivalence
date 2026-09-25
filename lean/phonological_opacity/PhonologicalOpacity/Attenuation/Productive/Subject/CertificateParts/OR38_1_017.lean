import PhonologicalOpacity.Attenuation.Productive.Subject.CertificateParts.OR38_1_016
namespace ProductiveSubjectGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partOR38_1_1365 : check uOR38 (4) (-2) outOR38 ["a","tʃ","u","s","ɛ","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1366 : check uOR38 (4) (-2) outOR38 ["a","tʃ","u","s","ɛ","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1353 : check uOR38 (4) (-2) outOR38 ["a","tʃ","u","s","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_1354
  · exact partOR38_1_1355
  · exact partOR38_1_1356
  · exact partOR38_1_1357
  · exact partOR38_1_1358
  · exact partOR38_1_1359
  · exact partOR38_1_1360
  · exact partOR38_1_1361
  · exact partOR38_1_1362
  · exact partOR38_1_1363
  · exact partOR38_1_1364
  · exact partOR38_1_1365
  · exact partOR38_1_1366
theorem partOR38_1_1367 : check uOR38 (4) (-2) outOR38 ["a","tʃ","u","s","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1369 : check uOR38 (4) (-2) outOR38 ["a","tʃ","u","s","ɪ","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1370 : check uOR38 (4) (-2) outOR38 ["a","tʃ","u","s","ɪ","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1371 : check uOR38 (4) (-2) outOR38 ["a","tʃ","u","s","ɪ","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1372 : check uOR38 (4) (-2) outOR38 ["a","tʃ","u","s","ɪ","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1373 : check uOR38 (4) (-2) outOR38 ["a","tʃ","u","s","ɪ","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1374 : check uOR38 (4) (-2) outOR38 ["a","tʃ","u","s","ɪ","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1375 : check uOR38 (4) (-2) outOR38 ["a","tʃ","u","s","ɪ","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1376 : check uOR38 (4) (-2) outOR38 ["a","tʃ","u","s","ɪ","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1377 : check uOR38 (4) (-2) outOR38 ["a","tʃ","u","s","ɪ","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1378 : check uOR38 (4) (-2) outOR38 ["a","tʃ","u","s","ɪ","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1379 : check uOR38 (4) (-2) outOR38 ["a","tʃ","u","s","ɪ","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1380 : check uOR38 (4) (-2) outOR38 ["a","tʃ","u","s","ɪ","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1381 : check uOR38 (4) (-2) outOR38 ["a","tʃ","u","s","ɪ","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1368 : check uOR38 (4) (-2) outOR38 ["a","tʃ","u","s","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_1369
  · exact partOR38_1_1370
  · exact partOR38_1_1371
  · exact partOR38_1_1372
  · exact partOR38_1_1373
  · exact partOR38_1_1374
  · exact partOR38_1_1375
  · exact partOR38_1_1376
  · exact partOR38_1_1377
  · exact partOR38_1_1378
  · exact partOR38_1_1379
  · exact partOR38_1_1380
  · exact partOR38_1_1381
theorem partOR38_1_1382 : check uOR38 (4) (-2) outOR38 ["a","tʃ","u","s","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1384 : check uOR38 (4) (-2) outOR38 ["a","tʃ","u","s","ɔ","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1385 : check uOR38 (4) (-2) outOR38 ["a","tʃ","u","s","ɔ","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1386 : check uOR38 (4) (-2) outOR38 ["a","tʃ","u","s","ɔ","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1387 : check uOR38 (4) (-2) outOR38 ["a","tʃ","u","s","ɔ","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1388 : check uOR38 (4) (-2) outOR38 ["a","tʃ","u","s","ɔ","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1389 : check uOR38 (4) (-2) outOR38 ["a","tʃ","u","s","ɔ","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1390 : check uOR38 (4) (-2) outOR38 ["a","tʃ","u","s","ɔ","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1391 : check uOR38 (4) (-2) outOR38 ["a","tʃ","u","s","ɔ","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1392 : check uOR38 (4) (-2) outOR38 ["a","tʃ","u","s","ɔ","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1393 : check uOR38 (4) (-2) outOR38 ["a","tʃ","u","s","ɔ","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1394 : check uOR38 (4) (-2) outOR38 ["a","tʃ","u","s","ɔ","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1395 : check uOR38 (4) (-2) outOR38 ["a","tʃ","u","s","ɔ","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1396 : check uOR38 (4) (-2) outOR38 ["a","tʃ","u","s","ɔ","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1383 : check uOR38 (4) (-2) outOR38 ["a","tʃ","u","s","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_1384
  · exact partOR38_1_1385
  · exact partOR38_1_1386
  · exact partOR38_1_1387
  · exact partOR38_1_1388
  · exact partOR38_1_1389
  · exact partOR38_1_1390
  · exact partOR38_1_1391
  · exact partOR38_1_1392
  · exact partOR38_1_1393
  · exact partOR38_1_1394
  · exact partOR38_1_1395
  · exact partOR38_1_1396
theorem partOR38_1_1397 : check uOR38 (4) (-2) outOR38 ["a","tʃ","u","s","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1399 : check uOR38 (4) (-2) outOR38 ["a","tʃ","u","s","ʊ","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1400 : check uOR38 (4) (-2) outOR38 ["a","tʃ","u","s","ʊ","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1401 : check uOR38 (4) (-2) outOR38 ["a","tʃ","u","s","ʊ","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1402 : check uOR38 (4) (-2) outOR38 ["a","tʃ","u","s","ʊ","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1403 : check uOR38 (4) (-2) outOR38 ["a","tʃ","u","s","ʊ","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1404 : check uOR38 (4) (-2) outOR38 ["a","tʃ","u","s","ʊ","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1405 : check uOR38 (4) (-2) outOR38 ["a","tʃ","u","s","ʊ","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1406 : check uOR38 (4) (-2) outOR38 ["a","tʃ","u","s","ʊ","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1407 : check uOR38 (4) (-2) outOR38 ["a","tʃ","u","s","ʊ","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1408 : check uOR38 (4) (-2) outOR38 ["a","tʃ","u","s","ʊ","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1409 : check uOR38 (4) (-2) outOR38 ["a","tʃ","u","s","ʊ","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1410 : check uOR38 (4) (-2) outOR38 ["a","tʃ","u","s","ʊ","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1411 : check uOR38 (4) (-2) outOR38 ["a","tʃ","u","s","ʊ","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1398 : check uOR38 (4) (-2) outOR38 ["a","tʃ","u","s","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_1399
  · exact partOR38_1_1400
  · exact partOR38_1_1401
  · exact partOR38_1_1402
  · exact partOR38_1_1403
  · exact partOR38_1_1404
  · exact partOR38_1_1405
  · exact partOR38_1_1406
  · exact partOR38_1_1407
  · exact partOR38_1_1408
  · exact partOR38_1_1409
  · exact partOR38_1_1410
  · exact partOR38_1_1411
theorem partOR38_1_1412 : check uOR38 (4) (-2) outOR38 ["a","tʃ","u","s","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1413 : check uOR38 (4) (-2) outOR38 ["a","tʃ","u","s","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1414 : check uOR38 (4) (-2) outOR38 ["a","tʃ","u","s","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1336 : check uOR38 (4) (-2) outOR38 ["a","tʃ","u","s"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_1337
  · exact partOR38_1_1338
  · exact partOR38_1_1352
  · exact partOR38_1_1353
  · exact partOR38_1_1367
  · exact partOR38_1_1368
  · exact partOR38_1_1382
  · exact partOR38_1_1383
  · exact partOR38_1_1397
  · exact partOR38_1_1398
  · exact partOR38_1_1412
  · exact partOR38_1_1413
  · exact partOR38_1_1414
theorem partOR38_1_1335 : check uOR38 (4) (-2) outOR38 ["a","tʃ","u"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="s" := by simpa using hx
  subst x
  exact partOR38_1_1336
theorem partOR38_1_1417 : check uOR38 (4) (-2) outOR38 ["a","tʃ","j","s","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1419 : check uOR38 (4) (-2) outOR38 ["a","tʃ","j","s","a","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1420 : check uOR38 (4) (-2) outOR38 ["a","tʃ","j","s","a","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1421 : check uOR38 (4) (-2) outOR38 ["a","tʃ","j","s","a","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1422 : check uOR38 (4) (-2) outOR38 ["a","tʃ","j","s","a","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1423 : check uOR38 (4) (-2) outOR38 ["a","tʃ","j","s","a","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1424 : check uOR38 (4) (-2) outOR38 ["a","tʃ","j","s","a","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1425 : check uOR38 (4) (-2) outOR38 ["a","tʃ","j","s","a","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1426 : check uOR38 (4) (-2) outOR38 ["a","tʃ","j","s","a","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1427 : check uOR38 (4) (-2) outOR38 ["a","tʃ","j","s","a","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1428 : check uOR38 (4) (-2) outOR38 ["a","tʃ","j","s","a","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1429 : check uOR38 (4) (-2) outOR38 ["a","tʃ","j","s","a","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1430 : check uOR38 (4) (-2) outOR38 ["a","tʃ","j","s","a","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1431 : check uOR38 (4) (-2) outOR38 ["a","tʃ","j","s","a","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1418 : check uOR38 (4) (-2) outOR38 ["a","tʃ","j","s","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_1419
  · exact partOR38_1_1420
  · exact partOR38_1_1421
  · exact partOR38_1_1422
  · exact partOR38_1_1423
  · exact partOR38_1_1424
  · exact partOR38_1_1425
  · exact partOR38_1_1426
  · exact partOR38_1_1427
  · exact partOR38_1_1428
  · exact partOR38_1_1429
  · exact partOR38_1_1430
  · exact partOR38_1_1431
theorem partOR38_1_1432 : check uOR38 (4) (-2) outOR38 ["a","tʃ","j","s","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1434 : check uOR38 (4) (-2) outOR38 ["a","tʃ","j","s","ɛ","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1435 : check uOR38 (4) (-2) outOR38 ["a","tʃ","j","s","ɛ","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1436 : check uOR38 (4) (-2) outOR38 ["a","tʃ","j","s","ɛ","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1437 : check uOR38 (4) (-2) outOR38 ["a","tʃ","j","s","ɛ","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1438 : check uOR38 (4) (-2) outOR38 ["a","tʃ","j","s","ɛ","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1439 : check uOR38 (4) (-2) outOR38 ["a","tʃ","j","s","ɛ","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1440 : check uOR38 (4) (-2) outOR38 ["a","tʃ","j","s","ɛ","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1441 : check uOR38 (4) (-2) outOR38 ["a","tʃ","j","s","ɛ","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1442 : check uOR38 (4) (-2) outOR38 ["a","tʃ","j","s","ɛ","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1443 : check uOR38 (4) (-2) outOR38 ["a","tʃ","j","s","ɛ","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1444 : check uOR38 (4) (-2) outOR38 ["a","tʃ","j","s","ɛ","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
end ProductiveSubjectGua
