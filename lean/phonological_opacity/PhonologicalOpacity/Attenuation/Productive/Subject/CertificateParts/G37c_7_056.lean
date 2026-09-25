import PhonologicalOpacity.Attenuation.Productive.Subject.CertificateParts.G37c_7_055
namespace ProductiveSubjectGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partG37c_7_4487 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","e","j","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4488 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","e","j","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4489 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","e","j","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4490 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","e","j","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4491 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","e","j","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4492 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","e","j","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4493 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","e","j","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4494 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","e","j","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4495 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","e","j","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4496 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","e","j","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4483 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","e","j","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_4484
  · exact partG37c_7_4485
  · exact partG37c_7_4486
  · exact partG37c_7_4487
  · exact partG37c_7_4488
  · exact partG37c_7_4489
  · exact partG37c_7_4490
  · exact partG37c_7_4491
  · exact partG37c_7_4492
  · exact partG37c_7_4493
  · exact partG37c_7_4494
  · exact partG37c_7_4495
  · exact partG37c_7_4496
theorem partG37c_7_4482 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","e","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_4483
theorem partG37c_7_4497 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","e","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4442 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_4443
  · exact partG37c_7_4458
  · exact partG37c_7_4459
  · exact partG37c_7_4460
  · exact partG37c_7_4461
  · exact partG37c_7_4462
  · exact partG37c_7_4463
  · exact partG37c_7_4478
  · exact partG37c_7_4479
  · exact partG37c_7_4480
  · exact partG37c_7_4481
  · exact partG37c_7_4482
  · exact partG37c_7_4497
theorem partG37c_7_4501 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɪ","∅","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4502 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɪ","∅","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4503 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɪ","∅","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4504 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɪ","∅","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4505 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɪ","∅","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4506 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɪ","∅","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4507 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɪ","∅","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4508 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɪ","∅","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4509 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɪ","∅","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4510 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɪ","∅","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4511 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɪ","∅","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4512 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɪ","∅","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4513 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɪ","∅","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4500 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɪ","∅","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_4501
  · exact partG37c_7_4502
  · exact partG37c_7_4503
  · exact partG37c_7_4504
  · exact partG37c_7_4505
  · exact partG37c_7_4506
  · exact partG37c_7_4507
  · exact partG37c_7_4508
  · exact partG37c_7_4509
  · exact partG37c_7_4510
  · exact partG37c_7_4511
  · exact partG37c_7_4512
  · exact partG37c_7_4513
theorem partG37c_7_4499 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɪ","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_4500
theorem partG37c_7_4514 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɪ","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4515 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɪ","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4516 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɪ","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4517 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɪ","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4518 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɪ","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4521 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɪ","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4522 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɪ","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4523 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɪ","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4524 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɪ","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4525 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɪ","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4526 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɪ","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4527 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɪ","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4528 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɪ","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4529 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɪ","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4530 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɪ","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4531 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɪ","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4532 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɪ","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4533 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɪ","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4520 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɪ","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_4521
  · exact partG37c_7_4522
  · exact partG37c_7_4523
  · exact partG37c_7_4524
  · exact partG37c_7_4525
  · exact partG37c_7_4526
  · exact partG37c_7_4527
  · exact partG37c_7_4528
  · exact partG37c_7_4529
  · exact partG37c_7_4530
  · exact partG37c_7_4531
  · exact partG37c_7_4532
  · exact partG37c_7_4533
theorem partG37c_7_4519 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɪ","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_4520
theorem partG37c_7_4534 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɪ","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4535 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɪ","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4536 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɪ","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4537 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɪ","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4540 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɪ","j","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4541 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɪ","j","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4542 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɪ","j","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4543 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɪ","j","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4544 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɪ","j","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4545 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɪ","j","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4546 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɪ","j","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4547 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɪ","j","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4548 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɪ","j","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4549 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɪ","j","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4550 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɪ","j","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4551 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɪ","j","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4552 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɪ","j","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4539 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɪ","j","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_4540
  · exact partG37c_7_4541
  · exact partG37c_7_4542
  · exact partG37c_7_4543
  · exact partG37c_7_4544
  · exact partG37c_7_4545
  · exact partG37c_7_4546
  · exact partG37c_7_4547
  · exact partG37c_7_4548
  · exact partG37c_7_4549
  · exact partG37c_7_4550
  · exact partG37c_7_4551
  · exact partG37c_7_4552
theorem partG37c_7_4538 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɪ","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_4539
theorem partG37c_7_4553 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɪ","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4498 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_4499
  · exact partG37c_7_4514
  · exact partG37c_7_4515
  · exact partG37c_7_4516
  · exact partG37c_7_4517
  · exact partG37c_7_4518
  · exact partG37c_7_4519
  · exact partG37c_7_4534
  · exact partG37c_7_4535
  · exact partG37c_7_4536
  · exact partG37c_7_4537
  · exact partG37c_7_4538
  · exact partG37c_7_4553
theorem partG37c_7_4557 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","i","∅","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4558 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","i","∅","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4559 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","i","∅","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4560 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","i","∅","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4561 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","i","∅","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4562 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","i","∅","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4563 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","i","∅","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4564 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","i","∅","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4565 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","i","∅","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4566 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","i","∅","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
end ProductiveSubjectGua
