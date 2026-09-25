import PhonologicalOpacity.Attenuation.Productive.Baseline.CertificateParts.G34a_1_017
namespace ProductiveGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partG34a_1_1448 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","a","ɔ","k","p","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1449 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","a","ɔ","k","p","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1450 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","a","ɔ","k","p","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1451 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","a","ɔ","k","p","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1452 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","a","ɔ","k","p","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1453 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","a","ɔ","k","p","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1454 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","a","ɔ","k","p","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1455 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","a","ɔ","k","p","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1456 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","a","ɔ","k","p","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1457 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","a","ɔ","k","p","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1444 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","a","ɔ","k","p"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG34a_1_1445
  · exact partG34a_1_1446
  · exact partG34a_1_1447
  · exact partG34a_1_1448
  · exact partG34a_1_1449
  · exact partG34a_1_1450
  · exact partG34a_1_1451
  · exact partG34a_1_1452
  · exact partG34a_1_1453
  · exact partG34a_1_1454
  · exact partG34a_1_1455
  · exact partG34a_1_1456
  · exact partG34a_1_1457
theorem partG34a_1_1443 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","a","ɔ","k"] [["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="p" := by simpa using hx
  subst x
  exact partG34a_1_1444
theorem partG34a_1_1442 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","a","ɔ"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="k" := by simpa using hx
  subst x
  exact partG34a_1_1443
theorem partG34a_1_1458 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","a","o"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1459 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","a","ʊ"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1460 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","a","u"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1461 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","a","j"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1462 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","a","w"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1434 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG34a_1_1435
  · exact partG34a_1_1436
  · exact partG34a_1_1437
  · exact partG34a_1_1438
  · exact partG34a_1_1439
  · exact partG34a_1_1440
  · exact partG34a_1_1441
  · exact partG34a_1_1442
  · exact partG34a_1_1458
  · exact partG34a_1_1459
  · exact partG34a_1_1460
  · exact partG34a_1_1461
  · exact partG34a_1_1462
theorem partG34a_1_1467 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","ɜ","∅","k","p","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1468 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","ɜ","∅","k","p","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1469 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","ɜ","∅","k","p","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1470 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","ɜ","∅","k","p","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1471 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","ɜ","∅","k","p","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1472 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","ɜ","∅","k","p","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1473 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","ɜ","∅","k","p","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1474 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","ɜ","∅","k","p","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1475 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","ɜ","∅","k","p","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1476 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","ɜ","∅","k","p","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1477 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","ɜ","∅","k","p","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1478 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","ɜ","∅","k","p","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1479 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","ɜ","∅","k","p","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1466 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","ɜ","∅","k","p"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG34a_1_1467
  · exact partG34a_1_1468
  · exact partG34a_1_1469
  · exact partG34a_1_1470
  · exact partG34a_1_1471
  · exact partG34a_1_1472
  · exact partG34a_1_1473
  · exact partG34a_1_1474
  · exact partG34a_1_1475
  · exact partG34a_1_1476
  · exact partG34a_1_1477
  · exact partG34a_1_1478
  · exact partG34a_1_1479
theorem partG34a_1_1465 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","ɜ","∅","k"] [["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="p" := by simpa using hx
  subst x
  exact partG34a_1_1466
theorem partG34a_1_1464 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","ɜ","∅"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="k" := by simpa using hx
  subst x
  exact partG34a_1_1465
theorem partG34a_1_1480 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","ɜ","a"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1481 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","ɜ","ɜ"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1482 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","ɜ","ɛ"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1483 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","ɜ","e"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1484 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","ɜ","ɪ"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1485 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","ɜ","i"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1489 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","ɜ","ɔ","k","p","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1490 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","ɜ","ɔ","k","p","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1491 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","ɜ","ɔ","k","p","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1492 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","ɜ","ɔ","k","p","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1493 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","ɜ","ɔ","k","p","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1494 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","ɜ","ɔ","k","p","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1495 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","ɜ","ɔ","k","p","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1496 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","ɜ","ɔ","k","p","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1497 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","ɜ","ɔ","k","p","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1498 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","ɜ","ɔ","k","p","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1499 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","ɜ","ɔ","k","p","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1500 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","ɜ","ɔ","k","p","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1501 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","ɜ","ɔ","k","p","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1488 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","ɜ","ɔ","k","p"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG34a_1_1489
  · exact partG34a_1_1490
  · exact partG34a_1_1491
  · exact partG34a_1_1492
  · exact partG34a_1_1493
  · exact partG34a_1_1494
  · exact partG34a_1_1495
  · exact partG34a_1_1496
  · exact partG34a_1_1497
  · exact partG34a_1_1498
  · exact partG34a_1_1499
  · exact partG34a_1_1500
  · exact partG34a_1_1501
theorem partG34a_1_1487 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","ɜ","ɔ","k"] [["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="p" := by simpa using hx
  subst x
  exact partG34a_1_1488
theorem partG34a_1_1486 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","ɜ","ɔ"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="k" := by simpa using hx
  subst x
  exact partG34a_1_1487
theorem partG34a_1_1502 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","ɜ","o"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1503 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","ɜ","ʊ"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1504 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","ɜ","u"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1505 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","ɜ","j"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1506 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","ɜ","w"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1463 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG34a_1_1464
  · exact partG34a_1_1480
  · exact partG34a_1_1481
  · exact partG34a_1_1482
  · exact partG34a_1_1483
  · exact partG34a_1_1484
  · exact partG34a_1_1485
  · exact partG34a_1_1486
  · exact partG34a_1_1502
  · exact partG34a_1_1503
  · exact partG34a_1_1504
  · exact partG34a_1_1505
  · exact partG34a_1_1506
theorem partG34a_1_1508 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","ɛ","∅"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1509 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","ɛ","a"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1510 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","ɛ","ɜ"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1511 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","ɛ","ɛ"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1512 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","ɛ","e"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1513 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","ɛ","ɪ"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1514 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","ɛ","i"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1518 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","ɛ","ɔ","k","p","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1519 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","ɛ","ɔ","k","p","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1520 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","ɛ","ɔ","k","p","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1521 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","ɛ","ɔ","k","p","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1522 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","ɛ","ɔ","k","p","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1523 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","ɛ","ɔ","k","p","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1524 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","ɛ","ɔ","k","p","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1525 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","ɛ","ɔ","k","p","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1526 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","ɛ","ɔ","k","p","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34a_1_1527 : check uG34a (3) (-2) outG34a ["a","h","ɪ","t","ɛ","ɔ","k","p","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
end ProductiveGua
