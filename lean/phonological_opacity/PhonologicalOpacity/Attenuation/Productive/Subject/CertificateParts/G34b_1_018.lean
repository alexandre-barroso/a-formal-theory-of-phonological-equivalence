import PhonologicalOpacity.Attenuation.Productive.Subject.CertificateParts.G34b_1_017
namespace ProductiveSubjectGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partG34b_1_1445 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɛ","i"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1446 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɛ","ɔ"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1449 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɛ","o","h","∅"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1450 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɛ","o","h","a"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1451 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɛ","o","h","ɜ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1452 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɛ","o","h","ɛ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1453 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɛ","o","h","e"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1454 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɛ","o","h","ɪ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1455 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɛ","o","h","i"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1456 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɛ","o","h","ɔ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1457 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɛ","o","h","o"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1458 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɛ","o","h","ʊ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1459 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɛ","o","h","u"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1460 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɛ","o","h","j"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1461 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɛ","o","h","w"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1448 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɛ","o","h"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG34b_1_1449
  · exact partG34b_1_1450
  · exact partG34b_1_1451
  · exact partG34b_1_1452
  · exact partG34b_1_1453
  · exact partG34b_1_1454
  · exact partG34b_1_1455
  · exact partG34b_1_1456
  · exact partG34b_1_1457
  · exact partG34b_1_1458
  · exact partG34b_1_1459
  · exact partG34b_1_1460
  · exact partG34b_1_1461
theorem partG34b_1_1447 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɛ","o"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="h" := by simpa using hx
  subst x
  exact partG34b_1_1448
theorem partG34b_1_1462 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɛ","ʊ"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1463 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɛ","u"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1464 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɛ","j"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1465 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɛ","w"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1424 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG34b_1_1425
  · exact partG34b_1_1440
  · exact partG34b_1_1441
  · exact partG34b_1_1442
  · exact partG34b_1_1443
  · exact partG34b_1_1444
  · exact partG34b_1_1445
  · exact partG34b_1_1446
  · exact partG34b_1_1447
  · exact partG34b_1_1462
  · exact partG34b_1_1463
  · exact partG34b_1_1464
  · exact partG34b_1_1465
theorem partG34b_1_1467 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","e","∅"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1468 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","e","a"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1469 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","e","ɜ"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1470 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","e","ɛ"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1471 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","e","e"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1472 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","e","ɪ"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1473 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","e","i"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1474 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","e","ɔ"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1477 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","e","o","h","∅"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1478 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","e","o","h","a"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1479 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","e","o","h","ɜ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1480 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","e","o","h","ɛ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1481 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","e","o","h","e"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1482 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","e","o","h","ɪ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1483 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","e","o","h","i"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1484 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","e","o","h","ɔ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1485 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","e","o","h","o"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1486 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","e","o","h","ʊ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1487 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","e","o","h","u"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1488 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","e","o","h","j"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1489 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","e","o","h","w"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1476 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","e","o","h"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG34b_1_1477
  · exact partG34b_1_1478
  · exact partG34b_1_1479
  · exact partG34b_1_1480
  · exact partG34b_1_1481
  · exact partG34b_1_1482
  · exact partG34b_1_1483
  · exact partG34b_1_1484
  · exact partG34b_1_1485
  · exact partG34b_1_1486
  · exact partG34b_1_1487
  · exact partG34b_1_1488
  · exact partG34b_1_1489
theorem partG34b_1_1475 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","e","o"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="h" := by simpa using hx
  subst x
  exact partG34b_1_1476
theorem partG34b_1_1490 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","e","ʊ"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1491 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","e","u"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1492 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","e","j"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1493 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","e","w"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1466 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG34b_1_1467
  · exact partG34b_1_1468
  · exact partG34b_1_1469
  · exact partG34b_1_1470
  · exact partG34b_1_1471
  · exact partG34b_1_1472
  · exact partG34b_1_1473
  · exact partG34b_1_1474
  · exact partG34b_1_1475
  · exact partG34b_1_1490
  · exact partG34b_1_1491
  · exact partG34b_1_1492
  · exact partG34b_1_1493
theorem partG34b_1_1497 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɪ","∅","h","∅"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1498 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɪ","∅","h","a"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1499 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɪ","∅","h","ɜ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1500 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɪ","∅","h","ɛ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1501 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɪ","∅","h","e"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1502 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɪ","∅","h","ɪ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1503 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɪ","∅","h","i"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1504 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɪ","∅","h","ɔ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1505 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɪ","∅","h","o"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1506 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɪ","∅","h","ʊ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1507 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɪ","∅","h","u"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1508 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɪ","∅","h","j"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1509 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɪ","∅","h","w"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1496 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɪ","∅","h"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG34b_1_1497
  · exact partG34b_1_1498
  · exact partG34b_1_1499
  · exact partG34b_1_1500
  · exact partG34b_1_1501
  · exact partG34b_1_1502
  · exact partG34b_1_1503
  · exact partG34b_1_1504
  · exact partG34b_1_1505
  · exact partG34b_1_1506
  · exact partG34b_1_1507
  · exact partG34b_1_1508
  · exact partG34b_1_1509
theorem partG34b_1_1495 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɪ","∅"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="h" := by simpa using hx
  subst x
  exact partG34b_1_1496
theorem partG34b_1_1510 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɪ","a"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1511 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɪ","ɜ"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1512 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɪ","ɛ"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1513 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɪ","e"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1514 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɪ","ɪ"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1515 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɪ","i"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1516 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɪ","ɔ"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1519 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɪ","o","h","∅"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1520 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɪ","o","h","a"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1521 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɪ","o","h","ɜ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1522 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɪ","o","h","ɛ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1523 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɪ","o","h","e"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1524 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɪ","o","h","ɪ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1525 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɪ","o","h","i"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1526 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɪ","o","h","ɔ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
end ProductiveSubjectGua
