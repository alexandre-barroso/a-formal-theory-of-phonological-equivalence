import PhonologicalOpacity.Attenuation.Productive.Subject.CertificateParts.G37c_7_029
namespace ProductiveSubjectGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partG37c_7_2407 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","j","j","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2408 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","j","j","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2409 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","j","j","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2410 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","j","j","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2411 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","j","j","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2412 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","j","j","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2413 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","j","j","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2414 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","j","j","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2415 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","j","j","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2416 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","j","j","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2403 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","j","j","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_2404
  · exact partG37c_7_2405
  · exact partG37c_7_2406
  · exact partG37c_7_2407
  · exact partG37c_7_2408
  · exact partG37c_7_2409
  · exact partG37c_7_2410
  · exact partG37c_7_2411
  · exact partG37c_7_2412
  · exact partG37c_7_2413
  · exact partG37c_7_2414
  · exact partG37c_7_2415
  · exact partG37c_7_2416
theorem partG37c_7_2402 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","j","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_2403
theorem partG37c_7_2417 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","j","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2362 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_2363
  · exact partG37c_7_2378
  · exact partG37c_7_2379
  · exact partG37c_7_2380
  · exact partG37c_7_2381
  · exact partG37c_7_2382
  · exact partG37c_7_2383
  · exact partG37c_7_2398
  · exact partG37c_7_2399
  · exact partG37c_7_2400
  · exact partG37c_7_2401
  · exact partG37c_7_2402
  · exact partG37c_7_2417
theorem partG37c_7_2421 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","w","∅","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2422 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","w","∅","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2423 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","w","∅","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2424 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","w","∅","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2425 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","w","∅","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2426 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","w","∅","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2427 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","w","∅","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2428 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","w","∅","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2429 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","w","∅","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2430 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","w","∅","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2431 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","w","∅","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2432 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","w","∅","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2433 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","w","∅","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2420 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","w","∅","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_2421
  · exact partG37c_7_2422
  · exact partG37c_7_2423
  · exact partG37c_7_2424
  · exact partG37c_7_2425
  · exact partG37c_7_2426
  · exact partG37c_7_2427
  · exact partG37c_7_2428
  · exact partG37c_7_2429
  · exact partG37c_7_2430
  · exact partG37c_7_2431
  · exact partG37c_7_2432
  · exact partG37c_7_2433
theorem partG37c_7_2419 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","w","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_2420
theorem partG37c_7_2434 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","w","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2435 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","w","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2436 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","w","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2437 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","w","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2438 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","w","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2441 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","w","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2442 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","w","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2443 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","w","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2444 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","w","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2445 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","w","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2446 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","w","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2447 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","w","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2448 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","w","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2449 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","w","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2450 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","w","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2451 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","w","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2452 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","w","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2453 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","w","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2440 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","w","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_2441
  · exact partG37c_7_2442
  · exact partG37c_7_2443
  · exact partG37c_7_2444
  · exact partG37c_7_2445
  · exact partG37c_7_2446
  · exact partG37c_7_2447
  · exact partG37c_7_2448
  · exact partG37c_7_2449
  · exact partG37c_7_2450
  · exact partG37c_7_2451
  · exact partG37c_7_2452
  · exact partG37c_7_2453
theorem partG37c_7_2439 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","w","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_2440
theorem partG37c_7_2454 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","w","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2455 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","w","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2456 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","w","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2457 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","w","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2460 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","w","j","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2461 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","w","j","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2462 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","w","j","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2463 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","w","j","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2464 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","w","j","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2465 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","w","j","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2466 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","w","j","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2467 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","w","j","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2468 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","w","j","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2469 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","w","j","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2470 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","w","j","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2471 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","w","j","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2472 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","w","j","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2459 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","w","j","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_2460
  · exact partG37c_7_2461
  · exact partG37c_7_2462
  · exact partG37c_7_2463
  · exact partG37c_7_2464
  · exact partG37c_7_2465
  · exact partG37c_7_2466
  · exact partG37c_7_2467
  · exact partG37c_7_2468
  · exact partG37c_7_2469
  · exact partG37c_7_2470
  · exact partG37c_7_2471
  · exact partG37c_7_2472
theorem partG37c_7_2458 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","w","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_2459
theorem partG37c_7_2473 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","w","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2418 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_2419
  · exact partG37c_7_2434
  · exact partG37c_7_2435
  · exact partG37c_7_2436
  · exact partG37c_7_2437
  · exact partG37c_7_2438
  · exact partG37c_7_2439
  · exact partG37c_7_2454
  · exact partG37c_7_2455
  · exact partG37c_7_2456
  · exact partG37c_7_2457
  · exact partG37c_7_2458
  · exact partG37c_7_2473
theorem partG37c_7_1745 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_1746
  · exact partG37c_7_1802
  · exact partG37c_7_1858
  · exact partG37c_7_1914
  · exact partG37c_7_1970
  · exact partG37c_7_2026
  · exact partG37c_7_2082
  · exact partG37c_7_2138
  · exact partG37c_7_2194
  · exact partG37c_7_2250
  · exact partG37c_7_2306
  · exact partG37c_7_2362
  · exact partG37c_7_2418
theorem partG37c_7_1744 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="s" := by simpa using hx
  subst x
  exact partG37c_7_1745
theorem partG37c_7_2477 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","∅","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2478 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","∅","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2479 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","∅","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2480 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","∅","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2481 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","∅","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2482 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","∅","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2485 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","∅","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2486 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","∅","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
end ProductiveSubjectGua
