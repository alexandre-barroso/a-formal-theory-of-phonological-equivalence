import PhonologicalOpacity.Attenuation.Productive.Baseline.CertificateParts.G37c_7_054
namespace ProductiveGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partG37c_7_4405 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɛ","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4406 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɛ","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4409 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɛ","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4410 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɛ","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4411 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɛ","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4412 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɛ","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4413 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɛ","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4414 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɛ","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4415 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɛ","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4416 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɛ","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4417 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɛ","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4418 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɛ","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4419 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɛ","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4420 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɛ","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4421 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɛ","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4408 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɛ","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_4409
  · exact partG37c_7_4410
  · exact partG37c_7_4411
  · exact partG37c_7_4412
  · exact partG37c_7_4413
  · exact partG37c_7_4414
  · exact partG37c_7_4415
  · exact partG37c_7_4416
  · exact partG37c_7_4417
  · exact partG37c_7_4418
  · exact partG37c_7_4419
  · exact partG37c_7_4420
  · exact partG37c_7_4421
theorem partG37c_7_4407 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɛ","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_4408
theorem partG37c_7_4422 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɛ","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4423 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɛ","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4424 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɛ","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4425 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɛ","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4428 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɛ","j","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4429 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɛ","j","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4430 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɛ","j","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4431 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɛ","j","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4432 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɛ","j","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4433 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɛ","j","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4434 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɛ","j","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4435 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɛ","j","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4436 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɛ","j","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4437 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɛ","j","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4438 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɛ","j","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4439 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɛ","j","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4440 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɛ","j","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4427 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɛ","j","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_4428
  · exact partG37c_7_4429
  · exact partG37c_7_4430
  · exact partG37c_7_4431
  · exact partG37c_7_4432
  · exact partG37c_7_4433
  · exact partG37c_7_4434
  · exact partG37c_7_4435
  · exact partG37c_7_4436
  · exact partG37c_7_4437
  · exact partG37c_7_4438
  · exact partG37c_7_4439
  · exact partG37c_7_4440
theorem partG37c_7_4426 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɛ","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_4427
theorem partG37c_7_4441 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɛ","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4386 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_4387
  · exact partG37c_7_4402
  · exact partG37c_7_4403
  · exact partG37c_7_4404
  · exact partG37c_7_4405
  · exact partG37c_7_4406
  · exact partG37c_7_4407
  · exact partG37c_7_4422
  · exact partG37c_7_4423
  · exact partG37c_7_4424
  · exact partG37c_7_4425
  · exact partG37c_7_4426
  · exact partG37c_7_4441
theorem partG37c_7_4445 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","e","∅","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4446 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","e","∅","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4447 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","e","∅","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4448 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","e","∅","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4449 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","e","∅","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4450 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","e","∅","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4451 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","e","∅","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4452 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","e","∅","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4453 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","e","∅","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4454 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","e","∅","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4455 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","e","∅","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4456 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","e","∅","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4457 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","e","∅","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4444 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","e","∅","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_4445
  · exact partG37c_7_4446
  · exact partG37c_7_4447
  · exact partG37c_7_4448
  · exact partG37c_7_4449
  · exact partG37c_7_4450
  · exact partG37c_7_4451
  · exact partG37c_7_4452
  · exact partG37c_7_4453
  · exact partG37c_7_4454
  · exact partG37c_7_4455
  · exact partG37c_7_4456
  · exact partG37c_7_4457
theorem partG37c_7_4443 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","e","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_4444
theorem partG37c_7_4458 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","e","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4459 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","e","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4460 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","e","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4461 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","e","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4462 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","e","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4465 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","e","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4466 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","e","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4467 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","e","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4468 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","e","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4469 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","e","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4470 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","e","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4471 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","e","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4472 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","e","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4473 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","e","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4474 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","e","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4475 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","e","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4476 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","e","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4477 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","e","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4464 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","e","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_4465
  · exact partG37c_7_4466
  · exact partG37c_7_4467
  · exact partG37c_7_4468
  · exact partG37c_7_4469
  · exact partG37c_7_4470
  · exact partG37c_7_4471
  · exact partG37c_7_4472
  · exact partG37c_7_4473
  · exact partG37c_7_4474
  · exact partG37c_7_4475
  · exact partG37c_7_4476
  · exact partG37c_7_4477
theorem partG37c_7_4463 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","e","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_4464
theorem partG37c_7_4478 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","e","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4479 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","e","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4480 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","e","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4481 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","e","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4484 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","e","j","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4485 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","e","j","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4486 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","e","j","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
end ProductiveGua
