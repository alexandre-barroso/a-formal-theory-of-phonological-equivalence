import PhonologicalOpacity.Attenuation.Productive.Subject.CertificateParts.OR38_1_002
namespace ProductiveSubjectGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partOR38_1_245 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","j","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_246 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","j","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_247 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","j","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_248 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","j","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_249 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","j","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_250 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","j","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_251 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","j","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_238 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_239
  · exact partOR38_1_240
  · exact partOR38_1_241
  · exact partOR38_1_242
  · exact partOR38_1_243
  · exact partOR38_1_244
  · exact partOR38_1_245
  · exact partOR38_1_246
  · exact partOR38_1_247
  · exact partOR38_1_248
  · exact partOR38_1_249
  · exact partOR38_1_250
  · exact partOR38_1_251
theorem partOR38_1_253 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","w","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_254 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","w","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_255 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","w","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_256 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","w","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_257 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","w","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_258 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","w","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_259 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","w","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_260 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","w","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_261 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","w","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_262 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","w","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_263 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","w","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_264 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","w","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_265 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","w","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_252 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_253
  · exact partOR38_1_254
  · exact partOR38_1_255
  · exact partOR38_1_256
  · exact partOR38_1_257
  · exact partOR38_1_258
  · exact partOR38_1_259
  · exact partOR38_1_260
  · exact partOR38_1_261
  · exact partOR38_1_262
  · exact partOR38_1_263
  · exact partOR38_1_264
  · exact partOR38_1_265
theorem partOR38_1_83 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a","s"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_84
  · exact partOR38_1_98
  · exact partOR38_1_112
  · exact partOR38_1_126
  · exact partOR38_1_140
  · exact partOR38_1_154
  · exact partOR38_1_168
  · exact partOR38_1_182
  · exact partOR38_1_196
  · exact partOR38_1_210
  · exact partOR38_1_224
  · exact partOR38_1_238
  · exact partOR38_1_252
theorem partOR38_1_82 : check uOR38 (4) (-2) outOR38 ["a","tʃ","a"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="s" := by simpa using hx
  subst x
  exact partOR38_1_83
theorem partOR38_1_268 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɜ","s","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_270 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɜ","s","a","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_271 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɜ","s","a","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_272 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɜ","s","a","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_273 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɜ","s","a","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_274 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɜ","s","a","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_275 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɜ","s","a","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_276 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɜ","s","a","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_277 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɜ","s","a","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_278 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɜ","s","a","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_279 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɜ","s","a","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_280 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɜ","s","a","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_281 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɜ","s","a","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_282 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɜ","s","a","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_269 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɜ","s","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_270
  · exact partOR38_1_271
  · exact partOR38_1_272
  · exact partOR38_1_273
  · exact partOR38_1_274
  · exact partOR38_1_275
  · exact partOR38_1_276
  · exact partOR38_1_277
  · exact partOR38_1_278
  · exact partOR38_1_279
  · exact partOR38_1_280
  · exact partOR38_1_281
  · exact partOR38_1_282
theorem partOR38_1_283 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɜ","s","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_285 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɜ","s","ɛ","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_286 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɜ","s","ɛ","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_287 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɜ","s","ɛ","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_288 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɜ","s","ɛ","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_289 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɜ","s","ɛ","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_290 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɜ","s","ɛ","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_291 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɜ","s","ɛ","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_292 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɜ","s","ɛ","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_293 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɜ","s","ɛ","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_294 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɜ","s","ɛ","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_295 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɜ","s","ɛ","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_296 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɜ","s","ɛ","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_297 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɜ","s","ɛ","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_284 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɜ","s","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_285
  · exact partOR38_1_286
  · exact partOR38_1_287
  · exact partOR38_1_288
  · exact partOR38_1_289
  · exact partOR38_1_290
  · exact partOR38_1_291
  · exact partOR38_1_292
  · exact partOR38_1_293
  · exact partOR38_1_294
  · exact partOR38_1_295
  · exact partOR38_1_296
  · exact partOR38_1_297
theorem partOR38_1_298 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɜ","s","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_300 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɜ","s","ɪ","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_301 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɜ","s","ɪ","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_302 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɜ","s","ɪ","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_303 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɜ","s","ɪ","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_304 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɜ","s","ɪ","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_305 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɜ","s","ɪ","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_306 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɜ","s","ɪ","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_307 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɜ","s","ɪ","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_308 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɜ","s","ɪ","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_309 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɜ","s","ɪ","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_310 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɜ","s","ɪ","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_311 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɜ","s","ɪ","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_312 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɜ","s","ɪ","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_299 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɜ","s","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_300
  · exact partOR38_1_301
  · exact partOR38_1_302
  · exact partOR38_1_303
  · exact partOR38_1_304
  · exact partOR38_1_305
  · exact partOR38_1_306
  · exact partOR38_1_307
  · exact partOR38_1_308
  · exact partOR38_1_309
  · exact partOR38_1_310
  · exact partOR38_1_311
  · exact partOR38_1_312
theorem partOR38_1_313 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɜ","s","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_315 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɜ","s","ɔ","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_316 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɜ","s","ɔ","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_317 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɜ","s","ɔ","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_318 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɜ","s","ɔ","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_319 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɜ","s","ɔ","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_320 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɜ","s","ɔ","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_321 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɜ","s","ɔ","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_322 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɜ","s","ɔ","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_323 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɜ","s","ɔ","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_324 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɜ","s","ɔ","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
end ProductiveSubjectGua
