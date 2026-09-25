import PhonologicalOpacity.Attenuation.Productive.Baseline.CertificateParts.G37c_0_030
namespace ProductiveGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partG37c_0_2485 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","o","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2458 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_0_2459
  · exact partG37c_0_2460
  · exact partG37c_0_2461
  · exact partG37c_0_2462
  · exact partG37c_0_2463
  · exact partG37c_0_2464
  · exact partG37c_0_2465
  · exact partG37c_0_2480
  · exact partG37c_0_2481
  · exact partG37c_0_2482
  · exact partG37c_0_2483
  · exact partG37c_0_2484
  · exact partG37c_0_2485
theorem partG37c_0_2489 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ʊ","∅","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2490 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ʊ","∅","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2491 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ʊ","∅","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2492 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ʊ","∅","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2493 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ʊ","∅","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2494 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ʊ","∅","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2495 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ʊ","∅","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2496 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ʊ","∅","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2497 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ʊ","∅","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2498 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ʊ","∅","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2499 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ʊ","∅","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2500 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ʊ","∅","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2501 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ʊ","∅","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2488 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ʊ","∅","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_0_2489
  · exact partG37c_0_2490
  · exact partG37c_0_2491
  · exact partG37c_0_2492
  · exact partG37c_0_2493
  · exact partG37c_0_2494
  · exact partG37c_0_2495
  · exact partG37c_0_2496
  · exact partG37c_0_2497
  · exact partG37c_0_2498
  · exact partG37c_0_2499
  · exact partG37c_0_2500
  · exact partG37c_0_2501
theorem partG37c_0_2487 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ʊ","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_0_2488
theorem partG37c_0_2502 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ʊ","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2503 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ʊ","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2504 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ʊ","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2505 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ʊ","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2506 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ʊ","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2509 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ʊ","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2510 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ʊ","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2511 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ʊ","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2512 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ʊ","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2513 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ʊ","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2514 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ʊ","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2515 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ʊ","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2516 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ʊ","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2517 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ʊ","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2518 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ʊ","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2519 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ʊ","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2520 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ʊ","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2521 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ʊ","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2508 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ʊ","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_0_2509
  · exact partG37c_0_2510
  · exact partG37c_0_2511
  · exact partG37c_0_2512
  · exact partG37c_0_2513
  · exact partG37c_0_2514
  · exact partG37c_0_2515
  · exact partG37c_0_2516
  · exact partG37c_0_2517
  · exact partG37c_0_2518
  · exact partG37c_0_2519
  · exact partG37c_0_2520
  · exact partG37c_0_2521
theorem partG37c_0_2507 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ʊ","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_0_2508
theorem partG37c_0_2522 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ʊ","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2523 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ʊ","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2524 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ʊ","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2525 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ʊ","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2528 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ʊ","j","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2529 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ʊ","j","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2530 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ʊ","j","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2531 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ʊ","j","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2532 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ʊ","j","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2533 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ʊ","j","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2534 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ʊ","j","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2535 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ʊ","j","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2536 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ʊ","j","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2537 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ʊ","j","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2538 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ʊ","j","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2539 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ʊ","j","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2540 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ʊ","j","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2527 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ʊ","j","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_0_2528
  · exact partG37c_0_2529
  · exact partG37c_0_2530
  · exact partG37c_0_2531
  · exact partG37c_0_2532
  · exact partG37c_0_2533
  · exact partG37c_0_2534
  · exact partG37c_0_2535
  · exact partG37c_0_2536
  · exact partG37c_0_2537
  · exact partG37c_0_2538
  · exact partG37c_0_2539
  · exact partG37c_0_2540
theorem partG37c_0_2526 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ʊ","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_0_2527
theorem partG37c_0_2541 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ʊ","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2486 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_0_2487
  · exact partG37c_0_2502
  · exact partG37c_0_2503
  · exact partG37c_0_2504
  · exact partG37c_0_2505
  · exact partG37c_0_2506
  · exact partG37c_0_2507
  · exact partG37c_0_2522
  · exact partG37c_0_2523
  · exact partG37c_0_2524
  · exact partG37c_0_2525
  · exact partG37c_0_2526
  · exact partG37c_0_2541
theorem partG37c_0_2543 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","u","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2544 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","u","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2545 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","u","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2546 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","u","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2547 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","u","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2548 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","u","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2551 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","u","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2552 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","u","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2553 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","u","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2554 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","u","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2555 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","u","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2556 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","u","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2557 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","u","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2558 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","u","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2559 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","u","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2560 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","u","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2561 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","u","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2562 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","u","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2563 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","u","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2550 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","u","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_0_2551
  · exact partG37c_0_2552
  · exact partG37c_0_2553
  · exact partG37c_0_2554
  · exact partG37c_0_2555
  · exact partG37c_0_2556
  · exact partG37c_0_2557
  · exact partG37c_0_2558
  · exact partG37c_0_2559
  · exact partG37c_0_2560
  · exact partG37c_0_2561
  · exact partG37c_0_2562
  · exact partG37c_0_2563
theorem partG37c_0_2549 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","u","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_0_2550
theorem partG37c_0_2564 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","u","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
end ProductiveGua
