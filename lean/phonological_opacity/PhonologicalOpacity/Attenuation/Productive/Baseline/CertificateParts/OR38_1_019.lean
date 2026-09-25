import PhonologicalOpacity.Attenuation.Productive.Baseline.CertificateParts.OR38_1_018
namespace ProductiveGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partOR38_1_1525 : check uOR38 (4) (-2) outOR38 ["a","tʃ","w","s","ɛ","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1526 : check uOR38 (4) (-2) outOR38 ["a","tʃ","w","s","ɛ","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1513 : check uOR38 (4) (-2) outOR38 ["a","tʃ","w","s","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_1514
  · exact partOR38_1_1515
  · exact partOR38_1_1516
  · exact partOR38_1_1517
  · exact partOR38_1_1518
  · exact partOR38_1_1519
  · exact partOR38_1_1520
  · exact partOR38_1_1521
  · exact partOR38_1_1522
  · exact partOR38_1_1523
  · exact partOR38_1_1524
  · exact partOR38_1_1525
  · exact partOR38_1_1526
theorem partOR38_1_1527 : check uOR38 (4) (-2) outOR38 ["a","tʃ","w","s","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1529 : check uOR38 (4) (-2) outOR38 ["a","tʃ","w","s","ɪ","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1530 : check uOR38 (4) (-2) outOR38 ["a","tʃ","w","s","ɪ","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1531 : check uOR38 (4) (-2) outOR38 ["a","tʃ","w","s","ɪ","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1532 : check uOR38 (4) (-2) outOR38 ["a","tʃ","w","s","ɪ","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1533 : check uOR38 (4) (-2) outOR38 ["a","tʃ","w","s","ɪ","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1534 : check uOR38 (4) (-2) outOR38 ["a","tʃ","w","s","ɪ","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1535 : check uOR38 (4) (-2) outOR38 ["a","tʃ","w","s","ɪ","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1536 : check uOR38 (4) (-2) outOR38 ["a","tʃ","w","s","ɪ","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1537 : check uOR38 (4) (-2) outOR38 ["a","tʃ","w","s","ɪ","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1538 : check uOR38 (4) (-2) outOR38 ["a","tʃ","w","s","ɪ","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1539 : check uOR38 (4) (-2) outOR38 ["a","tʃ","w","s","ɪ","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1540 : check uOR38 (4) (-2) outOR38 ["a","tʃ","w","s","ɪ","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1541 : check uOR38 (4) (-2) outOR38 ["a","tʃ","w","s","ɪ","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1528 : check uOR38 (4) (-2) outOR38 ["a","tʃ","w","s","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_1529
  · exact partOR38_1_1530
  · exact partOR38_1_1531
  · exact partOR38_1_1532
  · exact partOR38_1_1533
  · exact partOR38_1_1534
  · exact partOR38_1_1535
  · exact partOR38_1_1536
  · exact partOR38_1_1537
  · exact partOR38_1_1538
  · exact partOR38_1_1539
  · exact partOR38_1_1540
  · exact partOR38_1_1541
theorem partOR38_1_1542 : check uOR38 (4) (-2) outOR38 ["a","tʃ","w","s","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1544 : check uOR38 (4) (-2) outOR38 ["a","tʃ","w","s","ɔ","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1545 : check uOR38 (4) (-2) outOR38 ["a","tʃ","w","s","ɔ","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1546 : check uOR38 (4) (-2) outOR38 ["a","tʃ","w","s","ɔ","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1547 : check uOR38 (4) (-2) outOR38 ["a","tʃ","w","s","ɔ","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1548 : check uOR38 (4) (-2) outOR38 ["a","tʃ","w","s","ɔ","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1549 : check uOR38 (4) (-2) outOR38 ["a","tʃ","w","s","ɔ","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1550 : check uOR38 (4) (-2) outOR38 ["a","tʃ","w","s","ɔ","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1551 : check uOR38 (4) (-2) outOR38 ["a","tʃ","w","s","ɔ","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1552 : check uOR38 (4) (-2) outOR38 ["a","tʃ","w","s","ɔ","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1553 : check uOR38 (4) (-2) outOR38 ["a","tʃ","w","s","ɔ","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1554 : check uOR38 (4) (-2) outOR38 ["a","tʃ","w","s","ɔ","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1555 : check uOR38 (4) (-2) outOR38 ["a","tʃ","w","s","ɔ","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1556 : check uOR38 (4) (-2) outOR38 ["a","tʃ","w","s","ɔ","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1543 : check uOR38 (4) (-2) outOR38 ["a","tʃ","w","s","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_1544
  · exact partOR38_1_1545
  · exact partOR38_1_1546
  · exact partOR38_1_1547
  · exact partOR38_1_1548
  · exact partOR38_1_1549
  · exact partOR38_1_1550
  · exact partOR38_1_1551
  · exact partOR38_1_1552
  · exact partOR38_1_1553
  · exact partOR38_1_1554
  · exact partOR38_1_1555
  · exact partOR38_1_1556
theorem partOR38_1_1557 : check uOR38 (4) (-2) outOR38 ["a","tʃ","w","s","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1559 : check uOR38 (4) (-2) outOR38 ["a","tʃ","w","s","ʊ","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1560 : check uOR38 (4) (-2) outOR38 ["a","tʃ","w","s","ʊ","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1561 : check uOR38 (4) (-2) outOR38 ["a","tʃ","w","s","ʊ","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1562 : check uOR38 (4) (-2) outOR38 ["a","tʃ","w","s","ʊ","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1563 : check uOR38 (4) (-2) outOR38 ["a","tʃ","w","s","ʊ","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1564 : check uOR38 (4) (-2) outOR38 ["a","tʃ","w","s","ʊ","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1565 : check uOR38 (4) (-2) outOR38 ["a","tʃ","w","s","ʊ","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1566 : check uOR38 (4) (-2) outOR38 ["a","tʃ","w","s","ʊ","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1567 : check uOR38 (4) (-2) outOR38 ["a","tʃ","w","s","ʊ","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1568 : check uOR38 (4) (-2) outOR38 ["a","tʃ","w","s","ʊ","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1569 : check uOR38 (4) (-2) outOR38 ["a","tʃ","w","s","ʊ","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1570 : check uOR38 (4) (-2) outOR38 ["a","tʃ","w","s","ʊ","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1571 : check uOR38 (4) (-2) outOR38 ["a","tʃ","w","s","ʊ","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1558 : check uOR38 (4) (-2) outOR38 ["a","tʃ","w","s","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_1559
  · exact partOR38_1_1560
  · exact partOR38_1_1561
  · exact partOR38_1_1562
  · exact partOR38_1_1563
  · exact partOR38_1_1564
  · exact partOR38_1_1565
  · exact partOR38_1_1566
  · exact partOR38_1_1567
  · exact partOR38_1_1568
  · exact partOR38_1_1569
  · exact partOR38_1_1570
  · exact partOR38_1_1571
theorem partOR38_1_1572 : check uOR38 (4) (-2) outOR38 ["a","tʃ","w","s","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1573 : check uOR38 (4) (-2) outOR38 ["a","tʃ","w","s","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1574 : check uOR38 (4) (-2) outOR38 ["a","tʃ","w","s","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1496 : check uOR38 (4) (-2) outOR38 ["a","tʃ","w","s"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_1497
  · exact partOR38_1_1498
  · exact partOR38_1_1512
  · exact partOR38_1_1513
  · exact partOR38_1_1527
  · exact partOR38_1_1528
  · exact partOR38_1_1542
  · exact partOR38_1_1543
  · exact partOR38_1_1557
  · exact partOR38_1_1558
  · exact partOR38_1_1572
  · exact partOR38_1_1573
  · exact partOR38_1_1574
theorem partOR38_1_1495 : check uOR38 (4) (-2) outOR38 ["a","tʃ","w"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="s" := by simpa using hx
  subst x
  exact partOR38_1_1496
theorem partOR38_1_1 : check uOR38 (4) (-2) outOR38 ["a","tʃ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_2
  · exact partOR38_1_82
  · exact partOR38_1_266
  · exact partOR38_1_346
  · exact partOR38_1_530
  · exact partOR38_1_610
  · exact partOR38_1_794
  · exact partOR38_1_874
  · exact partOR38_1_1058
  · exact partOR38_1_1151
  · exact partOR38_1_1335
  · exact partOR38_1_1415
  · exact partOR38_1_1495
theorem checkedOR38_1 : check uOR38 (4) (-2) outOR38 ["a"] [["tʃ"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="tʃ" := by simpa using hx
  subst x
  exact partOR38_1_1
end ProductiveGua
