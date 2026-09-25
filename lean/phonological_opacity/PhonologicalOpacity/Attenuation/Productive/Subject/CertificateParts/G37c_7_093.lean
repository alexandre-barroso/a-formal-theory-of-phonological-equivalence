import PhonologicalOpacity.Attenuation.Productive.Subject.CertificateParts.G37c_7_092
namespace ProductiveSubjectGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partG37c_7_7433 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɪ","j","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_7434
  · exact partG37c_7_7435
  · exact partG37c_7_7436
  · exact partG37c_7_7437
  · exact partG37c_7_7438
  · exact partG37c_7_7439
  · exact partG37c_7_7440
  · exact partG37c_7_7441
  · exact partG37c_7_7442
  · exact partG37c_7_7443
  · exact partG37c_7_7444
  · exact partG37c_7_7445
  · exact partG37c_7_7446
theorem partG37c_7_7432 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɪ","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_7433
theorem partG37c_7_7447 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɪ","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7392 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_7393
  · exact partG37c_7_7408
  · exact partG37c_7_7409
  · exact partG37c_7_7410
  · exact partG37c_7_7411
  · exact partG37c_7_7412
  · exact partG37c_7_7413
  · exact partG37c_7_7428
  · exact partG37c_7_7429
  · exact partG37c_7_7430
  · exact partG37c_7_7431
  · exact partG37c_7_7432
  · exact partG37c_7_7447
theorem partG37c_7_7449 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","i","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7450 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","i","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7451 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","i","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7452 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","i","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7453 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","i","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7454 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","i","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7457 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","i","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7458 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","i","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7459 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","i","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7460 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","i","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7461 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","i","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7462 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","i","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7463 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","i","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7464 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","i","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7465 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","i","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7466 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","i","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7467 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","i","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7468 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","i","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7469 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","i","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7456 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","i","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_7457
  · exact partG37c_7_7458
  · exact partG37c_7_7459
  · exact partG37c_7_7460
  · exact partG37c_7_7461
  · exact partG37c_7_7462
  · exact partG37c_7_7463
  · exact partG37c_7_7464
  · exact partG37c_7_7465
  · exact partG37c_7_7466
  · exact partG37c_7_7467
  · exact partG37c_7_7468
  · exact partG37c_7_7469
theorem partG37c_7_7455 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","i","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_7456
theorem partG37c_7_7470 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","i","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7471 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","i","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7472 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","i","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7473 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","i","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7474 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","i","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7475 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","i","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7448 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_7449
  · exact partG37c_7_7450
  · exact partG37c_7_7451
  · exact partG37c_7_7452
  · exact partG37c_7_7453
  · exact partG37c_7_7454
  · exact partG37c_7_7455
  · exact partG37c_7_7470
  · exact partG37c_7_7471
  · exact partG37c_7_7472
  · exact partG37c_7_7473
  · exact partG37c_7_7474
  · exact partG37c_7_7475
theorem partG37c_7_7479 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɔ","∅","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7480 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɔ","∅","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7481 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɔ","∅","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7482 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɔ","∅","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7483 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɔ","∅","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7484 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɔ","∅","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7485 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɔ","∅","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7486 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɔ","∅","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7487 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɔ","∅","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7488 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɔ","∅","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7489 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɔ","∅","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7490 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɔ","∅","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7491 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɔ","∅","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7478 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɔ","∅","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_7479
  · exact partG37c_7_7480
  · exact partG37c_7_7481
  · exact partG37c_7_7482
  · exact partG37c_7_7483
  · exact partG37c_7_7484
  · exact partG37c_7_7485
  · exact partG37c_7_7486
  · exact partG37c_7_7487
  · exact partG37c_7_7488
  · exact partG37c_7_7489
  · exact partG37c_7_7490
  · exact partG37c_7_7491
theorem partG37c_7_7477 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɔ","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_7478
theorem partG37c_7_7492 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɔ","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7493 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɔ","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7494 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɔ","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7495 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɔ","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7496 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɔ","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7499 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɔ","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7500 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɔ","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7501 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɔ","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7502 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɔ","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7503 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɔ","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7504 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɔ","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7505 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɔ","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7506 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɔ","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7507 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɔ","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7508 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɔ","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7509 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɔ","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7510 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɔ","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7511 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɔ","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7498 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɔ","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_7499
  · exact partG37c_7_7500
  · exact partG37c_7_7501
  · exact partG37c_7_7502
  · exact partG37c_7_7503
  · exact partG37c_7_7504
  · exact partG37c_7_7505
  · exact partG37c_7_7506
  · exact partG37c_7_7507
  · exact partG37c_7_7508
  · exact partG37c_7_7509
  · exact partG37c_7_7510
  · exact partG37c_7_7511
theorem partG37c_7_7497 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɔ","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_7498
theorem partG37c_7_7512 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɔ","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7513 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɔ","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7514 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɔ","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7515 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɔ","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7518 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɔ","j","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7519 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɔ","j","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7520 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɔ","j","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7521 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɔ","j","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7522 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɔ","j","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7523 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɔ","j","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7524 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɔ","j","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7525 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɔ","j","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7526 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","ɔ","j","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
end ProductiveSubjectGua
