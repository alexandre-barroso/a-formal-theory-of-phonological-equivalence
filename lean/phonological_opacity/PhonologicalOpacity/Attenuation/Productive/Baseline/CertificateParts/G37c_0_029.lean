import PhonologicalOpacity.Attenuation.Productive.Baseline.CertificateParts.G37c_0_028
namespace ProductiveGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partG37c_0_2327 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɪ","∅","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2328 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɪ","∅","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2329 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɪ","∅","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2330 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɪ","∅","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2331 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɪ","∅","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2332 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɪ","∅","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2333 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɪ","∅","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2320 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɪ","∅","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_0_2321
  · exact partG37c_0_2322
  · exact partG37c_0_2323
  · exact partG37c_0_2324
  · exact partG37c_0_2325
  · exact partG37c_0_2326
  · exact partG37c_0_2327
  · exact partG37c_0_2328
  · exact partG37c_0_2329
  · exact partG37c_0_2330
  · exact partG37c_0_2331
  · exact partG37c_0_2332
  · exact partG37c_0_2333
theorem partG37c_0_2319 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɪ","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_0_2320
theorem partG37c_0_2334 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɪ","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2335 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɪ","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2336 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɪ","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2337 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɪ","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2338 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɪ","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2341 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɪ","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2342 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɪ","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2343 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɪ","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2344 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɪ","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2345 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɪ","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2346 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɪ","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2347 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɪ","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2348 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɪ","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2349 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɪ","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2350 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɪ","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2351 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɪ","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2352 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɪ","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2353 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɪ","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2340 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɪ","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_0_2341
  · exact partG37c_0_2342
  · exact partG37c_0_2343
  · exact partG37c_0_2344
  · exact partG37c_0_2345
  · exact partG37c_0_2346
  · exact partG37c_0_2347
  · exact partG37c_0_2348
  · exact partG37c_0_2349
  · exact partG37c_0_2350
  · exact partG37c_0_2351
  · exact partG37c_0_2352
  · exact partG37c_0_2353
theorem partG37c_0_2339 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɪ","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_0_2340
theorem partG37c_0_2354 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɪ","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2355 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɪ","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2356 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɪ","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2357 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɪ","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2360 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɪ","j","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2361 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɪ","j","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2362 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɪ","j","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2363 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɪ","j","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2364 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɪ","j","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2365 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɪ","j","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2366 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɪ","j","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2367 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɪ","j","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2368 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɪ","j","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2369 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɪ","j","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2370 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɪ","j","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2371 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɪ","j","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2372 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɪ","j","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2359 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɪ","j","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_0_2360
  · exact partG37c_0_2361
  · exact partG37c_0_2362
  · exact partG37c_0_2363
  · exact partG37c_0_2364
  · exact partG37c_0_2365
  · exact partG37c_0_2366
  · exact partG37c_0_2367
  · exact partG37c_0_2368
  · exact partG37c_0_2369
  · exact partG37c_0_2370
  · exact partG37c_0_2371
  · exact partG37c_0_2372
theorem partG37c_0_2358 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɪ","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_0_2359
theorem partG37c_0_2373 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɪ","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2318 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_0_2319
  · exact partG37c_0_2334
  · exact partG37c_0_2335
  · exact partG37c_0_2336
  · exact partG37c_0_2337
  · exact partG37c_0_2338
  · exact partG37c_0_2339
  · exact partG37c_0_2354
  · exact partG37c_0_2355
  · exact partG37c_0_2356
  · exact partG37c_0_2357
  · exact partG37c_0_2358
  · exact partG37c_0_2373
theorem partG37c_0_2375 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","i","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2376 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","i","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2377 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","i","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2378 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","i","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2379 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","i","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2380 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","i","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2383 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","i","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2384 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","i","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2385 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","i","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2386 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","i","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2387 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","i","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2388 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","i","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2389 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","i","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2390 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","i","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2391 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","i","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2392 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","i","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2393 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","i","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2394 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","i","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2395 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","i","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2382 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","i","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_0_2383
  · exact partG37c_0_2384
  · exact partG37c_0_2385
  · exact partG37c_0_2386
  · exact partG37c_0_2387
  · exact partG37c_0_2388
  · exact partG37c_0_2389
  · exact partG37c_0_2390
  · exact partG37c_0_2391
  · exact partG37c_0_2392
  · exact partG37c_0_2393
  · exact partG37c_0_2394
  · exact partG37c_0_2395
theorem partG37c_0_2381 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","i","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_0_2382
theorem partG37c_0_2396 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","i","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2397 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","i","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2398 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","i","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2399 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","i","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2400 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","i","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2401 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","i","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2374 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_0_2375
  · exact partG37c_0_2376
  · exact partG37c_0_2377
  · exact partG37c_0_2378
  · exact partG37c_0_2379
  · exact partG37c_0_2380
  · exact partG37c_0_2381
  · exact partG37c_0_2396
  · exact partG37c_0_2397
  · exact partG37c_0_2398
  · exact partG37c_0_2399
  · exact partG37c_0_2400
  · exact partG37c_0_2401
theorem partG37c_0_2405 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɔ","∅","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2406 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɔ","∅","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
end ProductiveGua
