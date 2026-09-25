import PhonologicalOpacity.Attenuation.Productive.Baseline.CertificateParts.G37c_7_053
namespace ProductiveGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partG37c_7_4327 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","a","j","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4328 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","a","j","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4315 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","a","j","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_4316
  · exact partG37c_7_4317
  · exact partG37c_7_4318
  · exact partG37c_7_4319
  · exact partG37c_7_4320
  · exact partG37c_7_4321
  · exact partG37c_7_4322
  · exact partG37c_7_4323
  · exact partG37c_7_4324
  · exact partG37c_7_4325
  · exact partG37c_7_4326
  · exact partG37c_7_4327
  · exact partG37c_7_4328
theorem partG37c_7_4314 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","a","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_4315
theorem partG37c_7_4329 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","a","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4274 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_4275
  · exact partG37c_7_4290
  · exact partG37c_7_4291
  · exact partG37c_7_4292
  · exact partG37c_7_4293
  · exact partG37c_7_4294
  · exact partG37c_7_4295
  · exact partG37c_7_4310
  · exact partG37c_7_4311
  · exact partG37c_7_4312
  · exact partG37c_7_4313
  · exact partG37c_7_4314
  · exact partG37c_7_4329
theorem partG37c_7_4333 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɜ","∅","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4334 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɜ","∅","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4335 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɜ","∅","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4336 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɜ","∅","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4337 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɜ","∅","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4338 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɜ","∅","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4339 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɜ","∅","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4340 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɜ","∅","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4341 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɜ","∅","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4342 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɜ","∅","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4343 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɜ","∅","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4344 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɜ","∅","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4345 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɜ","∅","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4332 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɜ","∅","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_4333
  · exact partG37c_7_4334
  · exact partG37c_7_4335
  · exact partG37c_7_4336
  · exact partG37c_7_4337
  · exact partG37c_7_4338
  · exact partG37c_7_4339
  · exact partG37c_7_4340
  · exact partG37c_7_4341
  · exact partG37c_7_4342
  · exact partG37c_7_4343
  · exact partG37c_7_4344
  · exact partG37c_7_4345
theorem partG37c_7_4331 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɜ","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_4332
theorem partG37c_7_4346 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɜ","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4347 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɜ","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4348 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɜ","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4349 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɜ","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4350 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɜ","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4353 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɜ","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4354 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɜ","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4355 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɜ","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4356 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɜ","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4357 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɜ","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4358 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɜ","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4359 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɜ","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4360 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɜ","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4361 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɜ","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4362 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɜ","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4363 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɜ","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4364 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɜ","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4365 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɜ","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4352 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɜ","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_4353
  · exact partG37c_7_4354
  · exact partG37c_7_4355
  · exact partG37c_7_4356
  · exact partG37c_7_4357
  · exact partG37c_7_4358
  · exact partG37c_7_4359
  · exact partG37c_7_4360
  · exact partG37c_7_4361
  · exact partG37c_7_4362
  · exact partG37c_7_4363
  · exact partG37c_7_4364
  · exact partG37c_7_4365
theorem partG37c_7_4351 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɜ","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_4352
theorem partG37c_7_4366 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɜ","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4367 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɜ","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4368 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɜ","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4369 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɜ","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4372 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɜ","j","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4373 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɜ","j","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4374 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɜ","j","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4375 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɜ","j","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4376 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɜ","j","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4377 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɜ","j","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4378 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɜ","j","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4379 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɜ","j","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4380 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɜ","j","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4381 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɜ","j","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4382 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɜ","j","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4383 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɜ","j","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4384 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɜ","j","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4371 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɜ","j","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_4372
  · exact partG37c_7_4373
  · exact partG37c_7_4374
  · exact partG37c_7_4375
  · exact partG37c_7_4376
  · exact partG37c_7_4377
  · exact partG37c_7_4378
  · exact partG37c_7_4379
  · exact partG37c_7_4380
  · exact partG37c_7_4381
  · exact partG37c_7_4382
  · exact partG37c_7_4383
  · exact partG37c_7_4384
theorem partG37c_7_4370 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɜ","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_4371
theorem partG37c_7_4385 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɜ","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4330 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_4331
  · exact partG37c_7_4346
  · exact partG37c_7_4347
  · exact partG37c_7_4348
  · exact partG37c_7_4349
  · exact partG37c_7_4350
  · exact partG37c_7_4351
  · exact partG37c_7_4366
  · exact partG37c_7_4367
  · exact partG37c_7_4368
  · exact partG37c_7_4369
  · exact partG37c_7_4370
  · exact partG37c_7_4385
theorem partG37c_7_4389 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɛ","∅","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4390 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɛ","∅","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4391 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɛ","∅","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4392 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɛ","∅","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4393 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɛ","∅","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4394 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɛ","∅","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4395 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɛ","∅","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4396 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɛ","∅","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4397 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɛ","∅","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4398 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɛ","∅","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4399 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɛ","∅","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4400 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɛ","∅","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4401 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɛ","∅","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4388 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɛ","∅","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_4389
  · exact partG37c_7_4390
  · exact partG37c_7_4391
  · exact partG37c_7_4392
  · exact partG37c_7_4393
  · exact partG37c_7_4394
  · exact partG37c_7_4395
  · exact partG37c_7_4396
  · exact partG37c_7_4397
  · exact partG37c_7_4398
  · exact partG37c_7_4399
  · exact partG37c_7_4400
  · exact partG37c_7_4401
theorem partG37c_7_4387 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɛ","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_4388
theorem partG37c_7_4402 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɛ","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4403 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɛ","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4404 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","ɛ","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
end ProductiveGua
