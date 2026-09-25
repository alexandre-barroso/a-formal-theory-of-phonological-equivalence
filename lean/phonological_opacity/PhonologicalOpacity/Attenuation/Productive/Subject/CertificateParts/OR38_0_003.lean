import PhonologicalOpacity.Attenuation.Productive.Subject.CertificateParts.OR38_0_002
namespace ProductiveSubjectGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partOR38_0_245 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɪ","s","ɪ","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_246 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɪ","s","ɪ","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_247 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɪ","s","ɪ","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_248 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɪ","s","ɪ","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_249 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɪ","s","ɪ","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_250 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɪ","s","ɪ","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_251 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɪ","s","ɪ","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_252 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɪ","s","ɪ","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_253 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɪ","s","ɪ","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_240 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɪ","s","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_0_241
  · exact partOR38_0_242
  · exact partOR38_0_243
  · exact partOR38_0_244
  · exact partOR38_0_245
  · exact partOR38_0_246
  · exact partOR38_0_247
  · exact partOR38_0_248
  · exact partOR38_0_249
  · exact partOR38_0_250
  · exact partOR38_0_251
  · exact partOR38_0_252
  · exact partOR38_0_253
theorem partOR38_0_254 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɪ","s","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_256 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɪ","s","ɔ","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_257 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɪ","s","ɔ","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_258 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɪ","s","ɔ","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_259 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɪ","s","ɔ","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_260 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɪ","s","ɔ","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_261 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɪ","s","ɔ","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_262 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɪ","s","ɔ","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_263 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɪ","s","ɔ","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_264 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɪ","s","ɔ","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_265 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɪ","s","ɔ","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_266 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɪ","s","ɔ","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_267 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɪ","s","ɔ","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_268 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɪ","s","ɔ","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_255 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɪ","s","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_0_256
  · exact partOR38_0_257
  · exact partOR38_0_258
  · exact partOR38_0_259
  · exact partOR38_0_260
  · exact partOR38_0_261
  · exact partOR38_0_262
  · exact partOR38_0_263
  · exact partOR38_0_264
  · exact partOR38_0_265
  · exact partOR38_0_266
  · exact partOR38_0_267
  · exact partOR38_0_268
theorem partOR38_0_269 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɪ","s","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_271 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɪ","s","ʊ","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_272 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɪ","s","ʊ","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_273 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɪ","s","ʊ","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_274 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɪ","s","ʊ","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_275 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɪ","s","ʊ","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_276 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɪ","s","ʊ","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_277 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɪ","s","ʊ","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_278 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɪ","s","ʊ","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_279 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɪ","s","ʊ","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_280 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɪ","s","ʊ","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_281 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɪ","s","ʊ","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_282 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɪ","s","ʊ","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_283 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɪ","s","ʊ","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_270 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɪ","s","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_0_271
  · exact partOR38_0_272
  · exact partOR38_0_273
  · exact partOR38_0_274
  · exact partOR38_0_275
  · exact partOR38_0_276
  · exact partOR38_0_277
  · exact partOR38_0_278
  · exact partOR38_0_279
  · exact partOR38_0_280
  · exact partOR38_0_281
  · exact partOR38_0_282
  · exact partOR38_0_283
theorem partOR38_0_284 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɪ","s","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_285 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɪ","s","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_286 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɪ","s","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_208 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɪ","s"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_0_209
  · exact partOR38_0_210
  · exact partOR38_0_224
  · exact partOR38_0_225
  · exact partOR38_0_239
  · exact partOR38_0_240
  · exact partOR38_0_254
  · exact partOR38_0_255
  · exact partOR38_0_269
  · exact partOR38_0_270
  · exact partOR38_0_284
  · exact partOR38_0_285
  · exact partOR38_0_286
theorem partOR38_0_207 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɪ"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="s" := by simpa using hx
  subst x
  exact partOR38_0_208
theorem partOR38_0_289 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","i","s","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_290 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","i","s","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_291 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","i","s","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_292 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","i","s","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_293 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","i","s","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_294 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","i","s","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_295 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","i","s","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_296 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","i","s","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_297 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","i","s","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_298 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","i","s","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_299 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","i","s","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_300 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","i","s","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_301 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","i","s","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_288 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","i","s"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_0_289
  · exact partOR38_0_290
  · exact partOR38_0_291
  · exact partOR38_0_292
  · exact partOR38_0_293
  · exact partOR38_0_294
  · exact partOR38_0_295
  · exact partOR38_0_296
  · exact partOR38_0_297
  · exact partOR38_0_298
  · exact partOR38_0_299
  · exact partOR38_0_300
  · exact partOR38_0_301
theorem partOR38_0_287 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","i"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="s" := by simpa using hx
  subst x
  exact partOR38_0_288
theorem partOR38_0_304 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɔ","s","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_306 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɔ","s","a","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_307 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɔ","s","a","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_308 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɔ","s","a","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_309 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɔ","s","a","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_310 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɔ","s","a","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_311 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɔ","s","a","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_312 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɔ","s","a","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_313 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɔ","s","a","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_314 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɔ","s","a","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_315 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɔ","s","a","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_316 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɔ","s","a","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_317 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɔ","s","a","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_318 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɔ","s","a","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_305 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɔ","s","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_0_306
  · exact partOR38_0_307
  · exact partOR38_0_308
  · exact partOR38_0_309
  · exact partOR38_0_310
  · exact partOR38_0_311
  · exact partOR38_0_312
  · exact partOR38_0_313
  · exact partOR38_0_314
  · exact partOR38_0_315
  · exact partOR38_0_316
  · exact partOR38_0_317
  · exact partOR38_0_318
theorem partOR38_0_319 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɔ","s","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_321 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɔ","s","ɛ","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_322 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɔ","s","ɛ","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_323 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɔ","s","ɛ","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_0_324 : check uOR38 (4) (-2) outOR38 ["∅","tʃ","ɔ","s","ɛ","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
end ProductiveSubjectGua
