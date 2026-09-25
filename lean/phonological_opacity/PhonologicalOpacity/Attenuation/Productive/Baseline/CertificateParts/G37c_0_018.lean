import PhonologicalOpacity.Attenuation.Productive.Baseline.CertificateParts.G37c_0_017
namespace ProductiveGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partG37c_0_1447 : check uG37c (3) (0) outG37c ["∅","tʃ","e","s","ʊ","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1448 : check uG37c (3) (0) outG37c ["∅","tʃ","e","s","ʊ","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1449 : check uG37c (3) (0) outG37c ["∅","tʃ","e","s","ʊ","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1450 : check uG37c (3) (0) outG37c ["∅","tʃ","e","s","ʊ","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1451 : check uG37c (3) (0) outG37c ["∅","tʃ","e","s","ʊ","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1452 : check uG37c (3) (0) outG37c ["∅","tʃ","e","s","ʊ","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1453 : check uG37c (3) (0) outG37c ["∅","tʃ","e","s","ʊ","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1454 : check uG37c (3) (0) outG37c ["∅","tʃ","e","s","ʊ","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1441 : check uG37c (3) (0) outG37c ["∅","tʃ","e","s","ʊ","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_0_1442
  · exact partG37c_0_1443
  · exact partG37c_0_1444
  · exact partG37c_0_1445
  · exact partG37c_0_1446
  · exact partG37c_0_1447
  · exact partG37c_0_1448
  · exact partG37c_0_1449
  · exact partG37c_0_1450
  · exact partG37c_0_1451
  · exact partG37c_0_1452
  · exact partG37c_0_1453
  · exact partG37c_0_1454
theorem partG37c_0_1440 : check uG37c (3) (0) outG37c ["∅","tʃ","e","s","ʊ","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_0_1441
theorem partG37c_0_1455 : check uG37c (3) (0) outG37c ["∅","tʃ","e","s","ʊ","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1456 : check uG37c (3) (0) outG37c ["∅","tʃ","e","s","ʊ","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1457 : check uG37c (3) (0) outG37c ["∅","tʃ","e","s","ʊ","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1458 : check uG37c (3) (0) outG37c ["∅","tʃ","e","s","ʊ","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1459 : check uG37c (3) (0) outG37c ["∅","tʃ","e","s","ʊ","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1460 : check uG37c (3) (0) outG37c ["∅","tʃ","e","s","ʊ","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1433 : check uG37c (3) (0) outG37c ["∅","tʃ","e","s","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_0_1434
  · exact partG37c_0_1435
  · exact partG37c_0_1436
  · exact partG37c_0_1437
  · exact partG37c_0_1438
  · exact partG37c_0_1439
  · exact partG37c_0_1440
  · exact partG37c_0_1455
  · exact partG37c_0_1456
  · exact partG37c_0_1457
  · exact partG37c_0_1458
  · exact partG37c_0_1459
  · exact partG37c_0_1460
theorem partG37c_0_1461 : check uG37c (3) (0) outG37c ["∅","tʃ","e","s","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1462 : check uG37c (3) (0) outG37c ["∅","tʃ","e","s","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1463 : check uG37c (3) (0) outG37c ["∅","tʃ","e","s","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1315 : check uG37c (3) (0) outG37c ["∅","tʃ","e","s"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_0_1316
  · exact partG37c_0_1317
  · exact partG37c_0_1345
  · exact partG37c_0_1346
  · exact partG37c_0_1374
  · exact partG37c_0_1375
  · exact partG37c_0_1403
  · exact partG37c_0_1404
  · exact partG37c_0_1432
  · exact partG37c_0_1433
  · exact partG37c_0_1461
  · exact partG37c_0_1462
  · exact partG37c_0_1463
theorem partG37c_0_1314 : check uG37c (3) (0) outG37c ["∅","tʃ","e"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="s" := by simpa using hx
  subst x
  exact partG37c_0_1315
theorem partG37c_0_1467 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","∅","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1468 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","∅","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1469 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","∅","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1470 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","∅","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1471 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","∅","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1472 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","∅","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1475 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","∅","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1476 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","∅","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1477 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","∅","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1478 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","∅","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1479 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","∅","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1480 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","∅","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1481 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","∅","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1482 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","∅","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1483 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","∅","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1484 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","∅","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1485 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","∅","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1486 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","∅","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1487 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","∅","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1474 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","∅","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_0_1475
  · exact partG37c_0_1476
  · exact partG37c_0_1477
  · exact partG37c_0_1478
  · exact partG37c_0_1479
  · exact partG37c_0_1480
  · exact partG37c_0_1481
  · exact partG37c_0_1482
  · exact partG37c_0_1483
  · exact partG37c_0_1484
  · exact partG37c_0_1485
  · exact partG37c_0_1486
  · exact partG37c_0_1487
theorem partG37c_0_1473 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","∅","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_0_1474
theorem partG37c_0_1488 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","∅","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1489 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","∅","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1490 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","∅","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1491 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","∅","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1492 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","∅","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1493 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","∅","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1466 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_0_1467
  · exact partG37c_0_1468
  · exact partG37c_0_1469
  · exact partG37c_0_1470
  · exact partG37c_0_1471
  · exact partG37c_0_1472
  · exact partG37c_0_1473
  · exact partG37c_0_1488
  · exact partG37c_0_1489
  · exact partG37c_0_1490
  · exact partG37c_0_1491
  · exact partG37c_0_1492
  · exact partG37c_0_1493
theorem partG37c_0_1497 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","a","∅","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1498 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","a","∅","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1499 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","a","∅","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1500 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","a","∅","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1501 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","a","∅","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1502 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","a","∅","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1503 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","a","∅","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1504 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","a","∅","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1505 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","a","∅","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1506 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","a","∅","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1507 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","a","∅","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1508 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","a","∅","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1509 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","a","∅","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1496 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","a","∅","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_0_1497
  · exact partG37c_0_1498
  · exact partG37c_0_1499
  · exact partG37c_0_1500
  · exact partG37c_0_1501
  · exact partG37c_0_1502
  · exact partG37c_0_1503
  · exact partG37c_0_1504
  · exact partG37c_0_1505
  · exact partG37c_0_1506
  · exact partG37c_0_1507
  · exact partG37c_0_1508
  · exact partG37c_0_1509
theorem partG37c_0_1495 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","a","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_0_1496
theorem partG37c_0_1510 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","a","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1511 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","a","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1512 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","a","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1513 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","a","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1514 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","a","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1517 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","a","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1518 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","a","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1519 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","a","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1520 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","a","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1521 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","a","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1522 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","a","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1523 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","a","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1524 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","a","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1525 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","a","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1526 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","a","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
end ProductiveGua
