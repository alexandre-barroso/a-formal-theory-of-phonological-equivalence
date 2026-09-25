import PhonologicalOpacity.Attenuation.Productive.Subject.CertificateParts.G37c_7_017
namespace ProductiveSubjectGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partG37c_7_1447 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","ɪ","∅","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1448 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","ɪ","∅","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1449 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","ɪ","∅","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1450 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","ɪ","∅","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1451 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","ɪ","∅","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1438 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","ɪ","∅","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_1439
  · exact partG37c_7_1440
  · exact partG37c_7_1441
  · exact partG37c_7_1442
  · exact partG37c_7_1443
  · exact partG37c_7_1444
  · exact partG37c_7_1445
  · exact partG37c_7_1446
  · exact partG37c_7_1447
  · exact partG37c_7_1448
  · exact partG37c_7_1449
  · exact partG37c_7_1450
  · exact partG37c_7_1451
theorem partG37c_7_1437 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","ɪ","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_1438
theorem partG37c_7_1452 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","ɪ","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1453 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","ɪ","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1454 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","ɪ","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1455 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","ɪ","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1456 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","ɪ","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1459 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","ɪ","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1460 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","ɪ","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1461 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","ɪ","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1462 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","ɪ","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1463 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","ɪ","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1464 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","ɪ","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1465 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","ɪ","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1466 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","ɪ","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1467 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","ɪ","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1468 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","ɪ","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1469 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","ɪ","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1470 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","ɪ","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1471 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","ɪ","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1458 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","ɪ","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_1459
  · exact partG37c_7_1460
  · exact partG37c_7_1461
  · exact partG37c_7_1462
  · exact partG37c_7_1463
  · exact partG37c_7_1464
  · exact partG37c_7_1465
  · exact partG37c_7_1466
  · exact partG37c_7_1467
  · exact partG37c_7_1468
  · exact partG37c_7_1469
  · exact partG37c_7_1470
  · exact partG37c_7_1471
theorem partG37c_7_1457 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","ɪ","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_1458
theorem partG37c_7_1472 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","ɪ","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1473 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","ɪ","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1474 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","ɪ","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1475 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","ɪ","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1478 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","ɪ","j","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1479 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","ɪ","j","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1480 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","ɪ","j","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1481 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","ɪ","j","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1482 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","ɪ","j","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1483 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","ɪ","j","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1484 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","ɪ","j","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1485 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","ɪ","j","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1486 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","ɪ","j","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1487 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","ɪ","j","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1488 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","ɪ","j","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1489 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","ɪ","j","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1490 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","ɪ","j","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1477 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","ɪ","j","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_1478
  · exact partG37c_7_1479
  · exact partG37c_7_1480
  · exact partG37c_7_1481
  · exact partG37c_7_1482
  · exact partG37c_7_1483
  · exact partG37c_7_1484
  · exact partG37c_7_1485
  · exact partG37c_7_1486
  · exact partG37c_7_1487
  · exact partG37c_7_1488
  · exact partG37c_7_1489
  · exact partG37c_7_1490
theorem partG37c_7_1476 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","ɪ","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_1477
theorem partG37c_7_1491 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","ɪ","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1436 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_1437
  · exact partG37c_7_1452
  · exact partG37c_7_1453
  · exact partG37c_7_1454
  · exact partG37c_7_1455
  · exact partG37c_7_1456
  · exact partG37c_7_1457
  · exact partG37c_7_1472
  · exact partG37c_7_1473
  · exact partG37c_7_1474
  · exact partG37c_7_1475
  · exact partG37c_7_1476
  · exact partG37c_7_1491
theorem partG37c_7_1493 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","i","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1494 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","i","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1495 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","i","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1496 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","i","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1497 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","i","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1498 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","i","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1501 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","i","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1502 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","i","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1503 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","i","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1504 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","i","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1505 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","i","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1506 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","i","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1507 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","i","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1508 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","i","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1509 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","i","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1510 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","i","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1511 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","i","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1512 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","i","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1513 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","i","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1500 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","i","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_1501
  · exact partG37c_7_1502
  · exact partG37c_7_1503
  · exact partG37c_7_1504
  · exact partG37c_7_1505
  · exact partG37c_7_1506
  · exact partG37c_7_1507
  · exact partG37c_7_1508
  · exact partG37c_7_1509
  · exact partG37c_7_1510
  · exact partG37c_7_1511
  · exact partG37c_7_1512
  · exact partG37c_7_1513
theorem partG37c_7_1499 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","i","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_1500
theorem partG37c_7_1514 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","i","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1515 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","i","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1516 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","i","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1517 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","i","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1518 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","i","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1519 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","i","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1492 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_1493
  · exact partG37c_7_1494
  · exact partG37c_7_1495
  · exact partG37c_7_1496
  · exact partG37c_7_1497
  · exact partG37c_7_1498
  · exact partG37c_7_1499
  · exact partG37c_7_1514
  · exact partG37c_7_1515
  · exact partG37c_7_1516
  · exact partG37c_7_1517
  · exact partG37c_7_1518
  · exact partG37c_7_1519
theorem partG37c_7_1523 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","ɔ","∅","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1524 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","ɔ","∅","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1525 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","ɔ","∅","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1526 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɜ","s","ɔ","∅","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
end ProductiveSubjectGua
