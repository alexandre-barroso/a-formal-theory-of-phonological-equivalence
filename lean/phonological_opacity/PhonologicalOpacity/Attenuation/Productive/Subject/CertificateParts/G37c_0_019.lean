import PhonologicalOpacity.Attenuation.Productive.Subject.CertificateParts.G37c_0_018
namespace ProductiveSubjectGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partG37c_0_1527 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","a","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1528 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","a","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1529 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","a","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1516 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","a","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_0_1517
  · exact partG37c_0_1518
  · exact partG37c_0_1519
  · exact partG37c_0_1520
  · exact partG37c_0_1521
  · exact partG37c_0_1522
  · exact partG37c_0_1523
  · exact partG37c_0_1524
  · exact partG37c_0_1525
  · exact partG37c_0_1526
  · exact partG37c_0_1527
  · exact partG37c_0_1528
  · exact partG37c_0_1529
theorem partG37c_0_1515 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","a","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_0_1516
theorem partG37c_0_1530 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","a","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1531 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","a","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1532 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","a","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1533 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","a","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1536 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","a","j","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1537 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","a","j","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1538 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","a","j","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1539 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","a","j","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1540 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","a","j","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1541 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","a","j","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1542 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","a","j","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1543 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","a","j","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1544 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","a","j","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1545 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","a","j","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1546 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","a","j","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1547 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","a","j","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1548 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","a","j","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1535 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","a","j","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_0_1536
  · exact partG37c_0_1537
  · exact partG37c_0_1538
  · exact partG37c_0_1539
  · exact partG37c_0_1540
  · exact partG37c_0_1541
  · exact partG37c_0_1542
  · exact partG37c_0_1543
  · exact partG37c_0_1544
  · exact partG37c_0_1545
  · exact partG37c_0_1546
  · exact partG37c_0_1547
  · exact partG37c_0_1548
theorem partG37c_0_1534 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","a","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_0_1535
theorem partG37c_0_1549 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","a","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1494 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_0_1495
  · exact partG37c_0_1510
  · exact partG37c_0_1511
  · exact partG37c_0_1512
  · exact partG37c_0_1513
  · exact partG37c_0_1514
  · exact partG37c_0_1515
  · exact partG37c_0_1530
  · exact partG37c_0_1531
  · exact partG37c_0_1532
  · exact partG37c_0_1533
  · exact partG37c_0_1534
  · exact partG37c_0_1549
theorem partG37c_0_1551 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɜ","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1552 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɜ","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1553 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɜ","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1554 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɜ","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1555 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɜ","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1556 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɜ","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1559 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɜ","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1560 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɜ","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1561 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɜ","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1562 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɜ","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1563 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɜ","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1564 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɜ","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1565 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɜ","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1566 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɜ","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1567 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɜ","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1568 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɜ","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1569 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɜ","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1570 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɜ","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1571 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɜ","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1558 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɜ","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_0_1559
  · exact partG37c_0_1560
  · exact partG37c_0_1561
  · exact partG37c_0_1562
  · exact partG37c_0_1563
  · exact partG37c_0_1564
  · exact partG37c_0_1565
  · exact partG37c_0_1566
  · exact partG37c_0_1567
  · exact partG37c_0_1568
  · exact partG37c_0_1569
  · exact partG37c_0_1570
  · exact partG37c_0_1571
theorem partG37c_0_1557 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɜ","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_0_1558
theorem partG37c_0_1572 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɜ","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1573 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɜ","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1574 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɜ","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1575 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɜ","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1576 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɜ","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1577 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɜ","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1550 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_0_1551
  · exact partG37c_0_1552
  · exact partG37c_0_1553
  · exact partG37c_0_1554
  · exact partG37c_0_1555
  · exact partG37c_0_1556
  · exact partG37c_0_1557
  · exact partG37c_0_1572
  · exact partG37c_0_1573
  · exact partG37c_0_1574
  · exact partG37c_0_1575
  · exact partG37c_0_1576
  · exact partG37c_0_1577
theorem partG37c_0_1581 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɛ","∅","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1582 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɛ","∅","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1583 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɛ","∅","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1584 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɛ","∅","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1585 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɛ","∅","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1586 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɛ","∅","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1587 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɛ","∅","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1588 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɛ","∅","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1589 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɛ","∅","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1590 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɛ","∅","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1591 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɛ","∅","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1592 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɛ","∅","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1593 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɛ","∅","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1580 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɛ","∅","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_0_1581
  · exact partG37c_0_1582
  · exact partG37c_0_1583
  · exact partG37c_0_1584
  · exact partG37c_0_1585
  · exact partG37c_0_1586
  · exact partG37c_0_1587
  · exact partG37c_0_1588
  · exact partG37c_0_1589
  · exact partG37c_0_1590
  · exact partG37c_0_1591
  · exact partG37c_0_1592
  · exact partG37c_0_1593
theorem partG37c_0_1579 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɛ","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_0_1580
theorem partG37c_0_1594 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɛ","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1595 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɛ","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1596 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɛ","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1597 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɛ","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1598 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɛ","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1601 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɛ","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1602 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɛ","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1603 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɛ","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1604 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɛ","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1605 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɛ","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_1606 : check uG37c (3) (0) outG37c ["∅","tʃ","ɪ","s","ɛ","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
end ProductiveSubjectGua
