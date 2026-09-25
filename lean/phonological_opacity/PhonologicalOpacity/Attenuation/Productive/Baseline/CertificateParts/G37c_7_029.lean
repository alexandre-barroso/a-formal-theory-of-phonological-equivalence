import PhonologicalOpacity.Attenuation.Productive.Baseline.CertificateParts.G37c_7_028
namespace ProductiveGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partG37c_7_2325 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","u","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2326 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","u","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2329 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","u","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2330 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","u","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2331 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","u","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2332 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","u","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2333 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","u","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2334 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","u","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2335 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","u","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2336 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","u","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2337 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","u","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2338 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","u","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2339 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","u","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2340 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","u","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2341 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","u","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2328 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","u","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_2329
  · exact partG37c_7_2330
  · exact partG37c_7_2331
  · exact partG37c_7_2332
  · exact partG37c_7_2333
  · exact partG37c_7_2334
  · exact partG37c_7_2335
  · exact partG37c_7_2336
  · exact partG37c_7_2337
  · exact partG37c_7_2338
  · exact partG37c_7_2339
  · exact partG37c_7_2340
  · exact partG37c_7_2341
theorem partG37c_7_2327 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","u","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_2328
theorem partG37c_7_2342 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","u","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2343 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","u","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2344 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","u","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2345 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","u","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2348 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","u","j","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2349 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","u","j","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2350 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","u","j","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2351 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","u","j","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2352 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","u","j","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2353 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","u","j","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2354 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","u","j","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2355 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","u","j","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2356 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","u","j","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2357 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","u","j","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2358 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","u","j","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2359 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","u","j","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2360 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","u","j","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2347 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","u","j","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_2348
  · exact partG37c_7_2349
  · exact partG37c_7_2350
  · exact partG37c_7_2351
  · exact partG37c_7_2352
  · exact partG37c_7_2353
  · exact partG37c_7_2354
  · exact partG37c_7_2355
  · exact partG37c_7_2356
  · exact partG37c_7_2357
  · exact partG37c_7_2358
  · exact partG37c_7_2359
  · exact partG37c_7_2360
theorem partG37c_7_2346 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","u","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_2347
theorem partG37c_7_2361 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","u","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2306 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_2307
  · exact partG37c_7_2322
  · exact partG37c_7_2323
  · exact partG37c_7_2324
  · exact partG37c_7_2325
  · exact partG37c_7_2326
  · exact partG37c_7_2327
  · exact partG37c_7_2342
  · exact partG37c_7_2343
  · exact partG37c_7_2344
  · exact partG37c_7_2345
  · exact partG37c_7_2346
  · exact partG37c_7_2361
theorem partG37c_7_2365 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","j","∅","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2366 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","j","∅","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2367 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","j","∅","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2368 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","j","∅","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2369 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","j","∅","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2370 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","j","∅","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2371 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","j","∅","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2372 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","j","∅","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2373 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","j","∅","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2374 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","j","∅","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2375 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","j","∅","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2376 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","j","∅","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2377 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","j","∅","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2364 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","j","∅","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_2365
  · exact partG37c_7_2366
  · exact partG37c_7_2367
  · exact partG37c_7_2368
  · exact partG37c_7_2369
  · exact partG37c_7_2370
  · exact partG37c_7_2371
  · exact partG37c_7_2372
  · exact partG37c_7_2373
  · exact partG37c_7_2374
  · exact partG37c_7_2375
  · exact partG37c_7_2376
  · exact partG37c_7_2377
theorem partG37c_7_2363 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","j","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_2364
theorem partG37c_7_2378 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","j","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2379 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","j","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2380 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","j","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2381 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","j","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2382 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","j","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2385 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","j","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2386 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","j","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2387 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","j","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2388 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","j","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2389 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","j","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2390 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","j","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2391 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","j","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2392 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","j","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2393 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","j","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2394 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","j","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2395 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","j","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2396 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","j","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2397 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","j","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2384 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","j","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_2385
  · exact partG37c_7_2386
  · exact partG37c_7_2387
  · exact partG37c_7_2388
  · exact partG37c_7_2389
  · exact partG37c_7_2390
  · exact partG37c_7_2391
  · exact partG37c_7_2392
  · exact partG37c_7_2393
  · exact partG37c_7_2394
  · exact partG37c_7_2395
  · exact partG37c_7_2396
  · exact partG37c_7_2397
theorem partG37c_7_2383 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","j","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_2384
theorem partG37c_7_2398 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","j","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2399 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","j","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2400 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","j","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2401 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","j","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2404 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","j","j","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2405 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","j","j","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2406 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","j","j","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
end ProductiveGua
