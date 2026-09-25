import PhonologicalOpacity.Attenuation.Productive.Baseline.CertificateParts.OR38_1_017
namespace ProductiveGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partOR38_1_1445 : check uOR38 (4) (-2) outOR38 ["a","tʃ","j","s","ɛ","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1446 : check uOR38 (4) (-2) outOR38 ["a","tʃ","j","s","ɛ","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1433 : check uOR38 (4) (-2) outOR38 ["a","tʃ","j","s","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_1434
  · exact partOR38_1_1435
  · exact partOR38_1_1436
  · exact partOR38_1_1437
  · exact partOR38_1_1438
  · exact partOR38_1_1439
  · exact partOR38_1_1440
  · exact partOR38_1_1441
  · exact partOR38_1_1442
  · exact partOR38_1_1443
  · exact partOR38_1_1444
  · exact partOR38_1_1445
  · exact partOR38_1_1446
theorem partOR38_1_1447 : check uOR38 (4) (-2) outOR38 ["a","tʃ","j","s","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1449 : check uOR38 (4) (-2) outOR38 ["a","tʃ","j","s","ɪ","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1450 : check uOR38 (4) (-2) outOR38 ["a","tʃ","j","s","ɪ","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1451 : check uOR38 (4) (-2) outOR38 ["a","tʃ","j","s","ɪ","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1452 : check uOR38 (4) (-2) outOR38 ["a","tʃ","j","s","ɪ","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1453 : check uOR38 (4) (-2) outOR38 ["a","tʃ","j","s","ɪ","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1454 : check uOR38 (4) (-2) outOR38 ["a","tʃ","j","s","ɪ","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1455 : check uOR38 (4) (-2) outOR38 ["a","tʃ","j","s","ɪ","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1456 : check uOR38 (4) (-2) outOR38 ["a","tʃ","j","s","ɪ","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1457 : check uOR38 (4) (-2) outOR38 ["a","tʃ","j","s","ɪ","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1458 : check uOR38 (4) (-2) outOR38 ["a","tʃ","j","s","ɪ","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1459 : check uOR38 (4) (-2) outOR38 ["a","tʃ","j","s","ɪ","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1460 : check uOR38 (4) (-2) outOR38 ["a","tʃ","j","s","ɪ","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1461 : check uOR38 (4) (-2) outOR38 ["a","tʃ","j","s","ɪ","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1448 : check uOR38 (4) (-2) outOR38 ["a","tʃ","j","s","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_1449
  · exact partOR38_1_1450
  · exact partOR38_1_1451
  · exact partOR38_1_1452
  · exact partOR38_1_1453
  · exact partOR38_1_1454
  · exact partOR38_1_1455
  · exact partOR38_1_1456
  · exact partOR38_1_1457
  · exact partOR38_1_1458
  · exact partOR38_1_1459
  · exact partOR38_1_1460
  · exact partOR38_1_1461
theorem partOR38_1_1462 : check uOR38 (4) (-2) outOR38 ["a","tʃ","j","s","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1464 : check uOR38 (4) (-2) outOR38 ["a","tʃ","j","s","ɔ","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1465 : check uOR38 (4) (-2) outOR38 ["a","tʃ","j","s","ɔ","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1466 : check uOR38 (4) (-2) outOR38 ["a","tʃ","j","s","ɔ","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1467 : check uOR38 (4) (-2) outOR38 ["a","tʃ","j","s","ɔ","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1468 : check uOR38 (4) (-2) outOR38 ["a","tʃ","j","s","ɔ","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1469 : check uOR38 (4) (-2) outOR38 ["a","tʃ","j","s","ɔ","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1470 : check uOR38 (4) (-2) outOR38 ["a","tʃ","j","s","ɔ","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1471 : check uOR38 (4) (-2) outOR38 ["a","tʃ","j","s","ɔ","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1472 : check uOR38 (4) (-2) outOR38 ["a","tʃ","j","s","ɔ","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1473 : check uOR38 (4) (-2) outOR38 ["a","tʃ","j","s","ɔ","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1474 : check uOR38 (4) (-2) outOR38 ["a","tʃ","j","s","ɔ","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1475 : check uOR38 (4) (-2) outOR38 ["a","tʃ","j","s","ɔ","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1476 : check uOR38 (4) (-2) outOR38 ["a","tʃ","j","s","ɔ","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1463 : check uOR38 (4) (-2) outOR38 ["a","tʃ","j","s","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_1464
  · exact partOR38_1_1465
  · exact partOR38_1_1466
  · exact partOR38_1_1467
  · exact partOR38_1_1468
  · exact partOR38_1_1469
  · exact partOR38_1_1470
  · exact partOR38_1_1471
  · exact partOR38_1_1472
  · exact partOR38_1_1473
  · exact partOR38_1_1474
  · exact partOR38_1_1475
  · exact partOR38_1_1476
theorem partOR38_1_1477 : check uOR38 (4) (-2) outOR38 ["a","tʃ","j","s","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1479 : check uOR38 (4) (-2) outOR38 ["a","tʃ","j","s","ʊ","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1480 : check uOR38 (4) (-2) outOR38 ["a","tʃ","j","s","ʊ","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1481 : check uOR38 (4) (-2) outOR38 ["a","tʃ","j","s","ʊ","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1482 : check uOR38 (4) (-2) outOR38 ["a","tʃ","j","s","ʊ","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1483 : check uOR38 (4) (-2) outOR38 ["a","tʃ","j","s","ʊ","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1484 : check uOR38 (4) (-2) outOR38 ["a","tʃ","j","s","ʊ","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1485 : check uOR38 (4) (-2) outOR38 ["a","tʃ","j","s","ʊ","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1486 : check uOR38 (4) (-2) outOR38 ["a","tʃ","j","s","ʊ","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1487 : check uOR38 (4) (-2) outOR38 ["a","tʃ","j","s","ʊ","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1488 : check uOR38 (4) (-2) outOR38 ["a","tʃ","j","s","ʊ","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1489 : check uOR38 (4) (-2) outOR38 ["a","tʃ","j","s","ʊ","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1490 : check uOR38 (4) (-2) outOR38 ["a","tʃ","j","s","ʊ","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1491 : check uOR38 (4) (-2) outOR38 ["a","tʃ","j","s","ʊ","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1478 : check uOR38 (4) (-2) outOR38 ["a","tʃ","j","s","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_1479
  · exact partOR38_1_1480
  · exact partOR38_1_1481
  · exact partOR38_1_1482
  · exact partOR38_1_1483
  · exact partOR38_1_1484
  · exact partOR38_1_1485
  · exact partOR38_1_1486
  · exact partOR38_1_1487
  · exact partOR38_1_1488
  · exact partOR38_1_1489
  · exact partOR38_1_1490
  · exact partOR38_1_1491
theorem partOR38_1_1492 : check uOR38 (4) (-2) outOR38 ["a","tʃ","j","s","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1493 : check uOR38 (4) (-2) outOR38 ["a","tʃ","j","s","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1494 : check uOR38 (4) (-2) outOR38 ["a","tʃ","j","s","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1416 : check uOR38 (4) (-2) outOR38 ["a","tʃ","j","s"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_1417
  · exact partOR38_1_1418
  · exact partOR38_1_1432
  · exact partOR38_1_1433
  · exact partOR38_1_1447
  · exact partOR38_1_1448
  · exact partOR38_1_1462
  · exact partOR38_1_1463
  · exact partOR38_1_1477
  · exact partOR38_1_1478
  · exact partOR38_1_1492
  · exact partOR38_1_1493
  · exact partOR38_1_1494
theorem partOR38_1_1415 : check uOR38 (4) (-2) outOR38 ["a","tʃ","j"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="s" := by simpa using hx
  subst x
  exact partOR38_1_1416
theorem partOR38_1_1497 : check uOR38 (4) (-2) outOR38 ["a","tʃ","w","s","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1499 : check uOR38 (4) (-2) outOR38 ["a","tʃ","w","s","a","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1500 : check uOR38 (4) (-2) outOR38 ["a","tʃ","w","s","a","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1501 : check uOR38 (4) (-2) outOR38 ["a","tʃ","w","s","a","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1502 : check uOR38 (4) (-2) outOR38 ["a","tʃ","w","s","a","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1503 : check uOR38 (4) (-2) outOR38 ["a","tʃ","w","s","a","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1504 : check uOR38 (4) (-2) outOR38 ["a","tʃ","w","s","a","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1505 : check uOR38 (4) (-2) outOR38 ["a","tʃ","w","s","a","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1506 : check uOR38 (4) (-2) outOR38 ["a","tʃ","w","s","a","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1507 : check uOR38 (4) (-2) outOR38 ["a","tʃ","w","s","a","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1508 : check uOR38 (4) (-2) outOR38 ["a","tʃ","w","s","a","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1509 : check uOR38 (4) (-2) outOR38 ["a","tʃ","w","s","a","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1510 : check uOR38 (4) (-2) outOR38 ["a","tʃ","w","s","a","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1511 : check uOR38 (4) (-2) outOR38 ["a","tʃ","w","s","a","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1498 : check uOR38 (4) (-2) outOR38 ["a","tʃ","w","s","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_1499
  · exact partOR38_1_1500
  · exact partOR38_1_1501
  · exact partOR38_1_1502
  · exact partOR38_1_1503
  · exact partOR38_1_1504
  · exact partOR38_1_1505
  · exact partOR38_1_1506
  · exact partOR38_1_1507
  · exact partOR38_1_1508
  · exact partOR38_1_1509
  · exact partOR38_1_1510
  · exact partOR38_1_1511
theorem partOR38_1_1512 : check uOR38 (4) (-2) outOR38 ["a","tʃ","w","s","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1514 : check uOR38 (4) (-2) outOR38 ["a","tʃ","w","s","ɛ","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1515 : check uOR38 (4) (-2) outOR38 ["a","tʃ","w","s","ɛ","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1516 : check uOR38 (4) (-2) outOR38 ["a","tʃ","w","s","ɛ","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1517 : check uOR38 (4) (-2) outOR38 ["a","tʃ","w","s","ɛ","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1518 : check uOR38 (4) (-2) outOR38 ["a","tʃ","w","s","ɛ","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1519 : check uOR38 (4) (-2) outOR38 ["a","tʃ","w","s","ɛ","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1520 : check uOR38 (4) (-2) outOR38 ["a","tʃ","w","s","ɛ","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1521 : check uOR38 (4) (-2) outOR38 ["a","tʃ","w","s","ɛ","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1522 : check uOR38 (4) (-2) outOR38 ["a","tʃ","w","s","ɛ","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1523 : check uOR38 (4) (-2) outOR38 ["a","tʃ","w","s","ɛ","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1524 : check uOR38 (4) (-2) outOR38 ["a","tʃ","w","s","ɛ","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
end ProductiveGua
