import PhonologicalOpacity.Attenuation.Productive.Subject.CertificateParts.G37c_7_067
namespace ProductiveSubjectGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partG37c_7_5431 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","w","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_5432
theorem partG37c_7_5446 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","w","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5447 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","w","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5448 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","w","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5449 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","w","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5450 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","w","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5451 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","w","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5424 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_5425
  · exact partG37c_7_5426
  · exact partG37c_7_5427
  · exact partG37c_7_5428
  · exact partG37c_7_5429
  · exact partG37c_7_5430
  · exact partG37c_7_5431
  · exact partG37c_7_5446
  · exact partG37c_7_5447
  · exact partG37c_7_5448
  · exact partG37c_7_5449
  · exact partG37c_7_5450
  · exact partG37c_7_5451
theorem partG37c_7_4947 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o","s"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_4948
  · exact partG37c_7_4976
  · exact partG37c_7_5032
  · exact partG37c_7_5060
  · exact partG37c_7_5116
  · exact partG37c_7_5144
  · exact partG37c_7_5200
  · exact partG37c_7_5228
  · exact partG37c_7_5284
  · exact partG37c_7_5312
  · exact partG37c_7_5368
  · exact partG37c_7_5396
  · exact partG37c_7_5424
theorem partG37c_7_4946 : check uG37c (3) (0) outG37c ["ɔ","tʃ","o"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="s" := by simpa using hx
  subst x
  exact partG37c_7_4947
theorem partG37c_7_5457 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","∅","∅","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5458 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","∅","∅","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5459 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","∅","∅","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5460 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","∅","∅","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5461 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","∅","∅","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5462 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","∅","∅","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5463 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","∅","∅","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5464 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","∅","∅","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5465 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","∅","∅","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5466 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","∅","∅","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5467 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","∅","∅","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5468 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","∅","∅","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5469 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","∅","∅","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5456 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","∅","∅","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_5457
  · exact partG37c_7_5458
  · exact partG37c_7_5459
  · exact partG37c_7_5460
  · exact partG37c_7_5461
  · exact partG37c_7_5462
  · exact partG37c_7_5463
  · exact partG37c_7_5464
  · exact partG37c_7_5465
  · exact partG37c_7_5466
  · exact partG37c_7_5467
  · exact partG37c_7_5468
  · exact partG37c_7_5469
theorem partG37c_7_5455 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","∅","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_5456
theorem partG37c_7_5470 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","∅","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5471 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","∅","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5472 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","∅","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5473 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","∅","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5474 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","∅","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5477 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","∅","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5478 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","∅","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5479 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","∅","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5480 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","∅","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5481 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","∅","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5482 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","∅","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5483 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","∅","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5484 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","∅","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5485 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","∅","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5486 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","∅","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5487 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","∅","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5488 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","∅","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5489 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","∅","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5476 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","∅","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_5477
  · exact partG37c_7_5478
  · exact partG37c_7_5479
  · exact partG37c_7_5480
  · exact partG37c_7_5481
  · exact partG37c_7_5482
  · exact partG37c_7_5483
  · exact partG37c_7_5484
  · exact partG37c_7_5485
  · exact partG37c_7_5486
  · exact partG37c_7_5487
  · exact partG37c_7_5488
  · exact partG37c_7_5489
theorem partG37c_7_5475 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","∅","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_5476
theorem partG37c_7_5490 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","∅","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5491 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","∅","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5492 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","∅","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5493 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","∅","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5496 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","∅","j","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5497 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","∅","j","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5498 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","∅","j","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5499 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","∅","j","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5500 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","∅","j","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5501 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","∅","j","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5502 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","∅","j","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5503 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","∅","j","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5504 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","∅","j","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5505 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","∅","j","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5506 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","∅","j","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5507 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","∅","j","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5508 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","∅","j","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5495 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","∅","j","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_5496
  · exact partG37c_7_5497
  · exact partG37c_7_5498
  · exact partG37c_7_5499
  · exact partG37c_7_5500
  · exact partG37c_7_5501
  · exact partG37c_7_5502
  · exact partG37c_7_5503
  · exact partG37c_7_5504
  · exact partG37c_7_5505
  · exact partG37c_7_5506
  · exact partG37c_7_5507
  · exact partG37c_7_5508
theorem partG37c_7_5494 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","∅","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_5495
theorem partG37c_7_5509 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","∅","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5454 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_5455
  · exact partG37c_7_5470
  · exact partG37c_7_5471
  · exact partG37c_7_5472
  · exact partG37c_7_5473
  · exact partG37c_7_5474
  · exact partG37c_7_5475
  · exact partG37c_7_5490
  · exact partG37c_7_5491
  · exact partG37c_7_5492
  · exact partG37c_7_5493
  · exact partG37c_7_5494
  · exact partG37c_7_5509
theorem partG37c_7_5513 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","a","∅","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5514 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","a","∅","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5515 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","a","∅","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5516 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","a","∅","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5517 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","a","∅","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5518 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","a","∅","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5519 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","a","∅","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5520 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","a","∅","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5521 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","a","∅","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5522 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","a","∅","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5523 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","a","∅","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5524 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","a","∅","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5525 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","a","∅","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5512 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","a","∅","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_5513
  · exact partG37c_7_5514
  · exact partG37c_7_5515
  · exact partG37c_7_5516
  · exact partG37c_7_5517
  · exact partG37c_7_5518
  · exact partG37c_7_5519
  · exact partG37c_7_5520
  · exact partG37c_7_5521
  · exact partG37c_7_5522
  · exact partG37c_7_5523
  · exact partG37c_7_5524
  · exact partG37c_7_5525
end ProductiveSubjectGua
