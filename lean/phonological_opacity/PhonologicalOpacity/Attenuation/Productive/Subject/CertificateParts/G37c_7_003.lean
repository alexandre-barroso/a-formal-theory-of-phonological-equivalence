import PhonologicalOpacity.Attenuation.Productive.Subject.CertificateParts.G37c_7_002
namespace ProductiveSubjectGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partG37c_7_247 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","ɪ","j","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_248 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","ɪ","j","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_249 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","ɪ","j","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_250 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","ɪ","j","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_251 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","ɪ","j","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_252 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","ɪ","j","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_253 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","ɪ","j","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_254 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","ɪ","j","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_241 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","ɪ","j","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_242
  · exact partG37c_7_243
  · exact partG37c_7_244
  · exact partG37c_7_245
  · exact partG37c_7_246
  · exact partG37c_7_247
  · exact partG37c_7_248
  · exact partG37c_7_249
  · exact partG37c_7_250
  · exact partG37c_7_251
  · exact partG37c_7_252
  · exact partG37c_7_253
  · exact partG37c_7_254
theorem partG37c_7_240 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","ɪ","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_241
theorem partG37c_7_255 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","ɪ","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_200 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_201
  · exact partG37c_7_216
  · exact partG37c_7_217
  · exact partG37c_7_218
  · exact partG37c_7_219
  · exact partG37c_7_220
  · exact partG37c_7_221
  · exact partG37c_7_236
  · exact partG37c_7_237
  · exact partG37c_7_238
  · exact partG37c_7_239
  · exact partG37c_7_240
  · exact partG37c_7_255
theorem partG37c_7_257 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","i","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_258 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","i","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_259 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","i","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_260 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","i","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_261 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","i","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_262 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","i","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_265 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","i","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_266 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","i","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_267 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","i","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_268 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","i","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_269 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","i","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_270 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","i","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_271 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","i","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_272 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","i","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_273 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","i","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_274 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","i","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_275 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","i","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_276 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","i","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_277 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","i","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_264 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","i","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_265
  · exact partG37c_7_266
  · exact partG37c_7_267
  · exact partG37c_7_268
  · exact partG37c_7_269
  · exact partG37c_7_270
  · exact partG37c_7_271
  · exact partG37c_7_272
  · exact partG37c_7_273
  · exact partG37c_7_274
  · exact partG37c_7_275
  · exact partG37c_7_276
  · exact partG37c_7_277
theorem partG37c_7_263 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","i","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_264
theorem partG37c_7_278 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","i","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_279 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","i","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_280 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","i","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_281 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","i","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_282 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","i","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_283 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","i","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_256 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_257
  · exact partG37c_7_258
  · exact partG37c_7_259
  · exact partG37c_7_260
  · exact partG37c_7_261
  · exact partG37c_7_262
  · exact partG37c_7_263
  · exact partG37c_7_278
  · exact partG37c_7_279
  · exact partG37c_7_280
  · exact partG37c_7_281
  · exact partG37c_7_282
  · exact partG37c_7_283
theorem partG37c_7_287 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","ɔ","∅","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_288 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","ɔ","∅","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_289 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","ɔ","∅","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_290 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","ɔ","∅","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_291 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","ɔ","∅","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_292 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","ɔ","∅","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_293 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","ɔ","∅","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_294 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","ɔ","∅","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_295 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","ɔ","∅","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_296 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","ɔ","∅","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_297 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","ɔ","∅","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_298 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","ɔ","∅","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_299 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","ɔ","∅","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_286 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","ɔ","∅","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_287
  · exact partG37c_7_288
  · exact partG37c_7_289
  · exact partG37c_7_290
  · exact partG37c_7_291
  · exact partG37c_7_292
  · exact partG37c_7_293
  · exact partG37c_7_294
  · exact partG37c_7_295
  · exact partG37c_7_296
  · exact partG37c_7_297
  · exact partG37c_7_298
  · exact partG37c_7_299
theorem partG37c_7_285 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","ɔ","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_286
theorem partG37c_7_300 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","ɔ","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_301 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","ɔ","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_302 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","ɔ","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_303 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","ɔ","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_304 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","ɔ","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_307 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","ɔ","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_308 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","ɔ","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_309 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","ɔ","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_310 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","ɔ","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_311 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","ɔ","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_312 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","ɔ","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_313 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","ɔ","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_314 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","ɔ","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_315 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","ɔ","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_316 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","ɔ","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_317 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","ɔ","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_318 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","ɔ","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_319 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","ɔ","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_306 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","ɔ","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_307
  · exact partG37c_7_308
  · exact partG37c_7_309
  · exact partG37c_7_310
  · exact partG37c_7_311
  · exact partG37c_7_312
  · exact partG37c_7_313
  · exact partG37c_7_314
  · exact partG37c_7_315
  · exact partG37c_7_316
  · exact partG37c_7_317
  · exact partG37c_7_318
  · exact partG37c_7_319
theorem partG37c_7_305 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","ɔ","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_306
theorem partG37c_7_320 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","ɔ","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_321 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","ɔ","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_322 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","ɔ","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_323 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","ɔ","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_326 : check uG37c (3) (0) outG37c ["ɔ","tʃ","∅","s","ɔ","j","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
end ProductiveSubjectGua
