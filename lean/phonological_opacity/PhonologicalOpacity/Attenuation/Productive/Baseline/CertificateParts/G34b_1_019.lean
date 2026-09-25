import PhonologicalOpacity.Attenuation.Productive.Baseline.CertificateParts.G34b_1_018
namespace ProductiveGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partG34b_1_1527 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɪ","o","h","o"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1528 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɪ","o","h","ʊ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1529 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɪ","o","h","u"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1530 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɪ","o","h","j"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1531 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɪ","o","h","w"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1518 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɪ","o","h"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG34b_1_1519
  · exact partG34b_1_1520
  · exact partG34b_1_1521
  · exact partG34b_1_1522
  · exact partG34b_1_1523
  · exact partG34b_1_1524
  · exact partG34b_1_1525
  · exact partG34b_1_1526
  · exact partG34b_1_1527
  · exact partG34b_1_1528
  · exact partG34b_1_1529
  · exact partG34b_1_1530
  · exact partG34b_1_1531
theorem partG34b_1_1517 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɪ","o"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="h" := by simpa using hx
  subst x
  exact partG34b_1_1518
theorem partG34b_1_1532 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɪ","ʊ"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1533 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɪ","u"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1534 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɪ","j"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1535 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɪ","w"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1494 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG34b_1_1495
  · exact partG34b_1_1510
  · exact partG34b_1_1511
  · exact partG34b_1_1512
  · exact partG34b_1_1513
  · exact partG34b_1_1514
  · exact partG34b_1_1515
  · exact partG34b_1_1516
  · exact partG34b_1_1517
  · exact partG34b_1_1532
  · exact partG34b_1_1533
  · exact partG34b_1_1534
  · exact partG34b_1_1535
theorem partG34b_1_1537 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","i","∅"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1538 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","i","a"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1539 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","i","ɜ"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1540 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","i","ɛ"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1541 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","i","e"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1542 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","i","ɪ"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1543 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","i","i"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1544 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","i","ɔ"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1547 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","i","o","h","∅"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1548 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","i","o","h","a"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1549 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","i","o","h","ɜ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1550 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","i","o","h","ɛ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1551 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","i","o","h","e"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1552 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","i","o","h","ɪ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1553 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","i","o","h","i"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1554 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","i","o","h","ɔ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1555 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","i","o","h","o"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1556 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","i","o","h","ʊ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1557 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","i","o","h","u"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1558 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","i","o","h","j"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1559 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","i","o","h","w"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1546 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","i","o","h"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG34b_1_1547
  · exact partG34b_1_1548
  · exact partG34b_1_1549
  · exact partG34b_1_1550
  · exact partG34b_1_1551
  · exact partG34b_1_1552
  · exact partG34b_1_1553
  · exact partG34b_1_1554
  · exact partG34b_1_1555
  · exact partG34b_1_1556
  · exact partG34b_1_1557
  · exact partG34b_1_1558
  · exact partG34b_1_1559
theorem partG34b_1_1545 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","i","o"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="h" := by simpa using hx
  subst x
  exact partG34b_1_1546
theorem partG34b_1_1560 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","i","ʊ"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1561 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","i","u"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1562 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","i","j"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1563 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","i","w"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1536 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG34b_1_1537
  · exact partG34b_1_1538
  · exact partG34b_1_1539
  · exact partG34b_1_1540
  · exact partG34b_1_1541
  · exact partG34b_1_1542
  · exact partG34b_1_1543
  · exact partG34b_1_1544
  · exact partG34b_1_1545
  · exact partG34b_1_1560
  · exact partG34b_1_1561
  · exact partG34b_1_1562
  · exact partG34b_1_1563
theorem partG34b_1_1567 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɔ","∅","h","∅"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1568 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɔ","∅","h","a"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1569 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɔ","∅","h","ɜ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1570 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɔ","∅","h","ɛ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1571 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɔ","∅","h","e"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1572 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɔ","∅","h","ɪ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1573 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɔ","∅","h","i"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1574 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɔ","∅","h","ɔ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1575 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɔ","∅","h","o"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1576 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɔ","∅","h","ʊ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1577 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɔ","∅","h","u"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1578 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɔ","∅","h","j"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1579 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɔ","∅","h","w"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1566 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɔ","∅","h"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG34b_1_1567
  · exact partG34b_1_1568
  · exact partG34b_1_1569
  · exact partG34b_1_1570
  · exact partG34b_1_1571
  · exact partG34b_1_1572
  · exact partG34b_1_1573
  · exact partG34b_1_1574
  · exact partG34b_1_1575
  · exact partG34b_1_1576
  · exact partG34b_1_1577
  · exact partG34b_1_1578
  · exact partG34b_1_1579
theorem partG34b_1_1565 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɔ","∅"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="h" := by simpa using hx
  subst x
  exact partG34b_1_1566
theorem partG34b_1_1580 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɔ","a"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1581 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɔ","ɜ"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1582 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɔ","ɛ"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1583 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɔ","e"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1584 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɔ","ɪ"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1585 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɔ","i"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1586 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɔ","ɔ"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1589 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɔ","o","h","∅"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1590 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɔ","o","h","a"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1591 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɔ","o","h","ɜ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1592 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɔ","o","h","ɛ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1593 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɔ","o","h","e"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1594 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɔ","o","h","ɪ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1595 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɔ","o","h","i"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1596 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɔ","o","h","ɔ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1597 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɔ","o","h","o"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1598 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɔ","o","h","ʊ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1599 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɔ","o","h","u"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1600 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɔ","o","h","j"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1601 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɔ","o","h","w"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1588 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɔ","o","h"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG34b_1_1589
  · exact partG34b_1_1590
  · exact partG34b_1_1591
  · exact partG34b_1_1592
  · exact partG34b_1_1593
  · exact partG34b_1_1594
  · exact partG34b_1_1595
  · exact partG34b_1_1596
  · exact partG34b_1_1597
  · exact partG34b_1_1598
  · exact partG34b_1_1599
  · exact partG34b_1_1600
  · exact partG34b_1_1601
theorem partG34b_1_1587 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɔ","o"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="h" := by simpa using hx
  subst x
  exact partG34b_1_1588
theorem partG34b_1_1602 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɔ","ʊ"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1603 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɔ","u"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1604 : check uG34b (2) (0) outG34b ["a","f","ɪ","s","ɔ","j"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
end ProductiveGua
