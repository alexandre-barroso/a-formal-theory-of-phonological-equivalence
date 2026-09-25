import PhonologicalOpacity.Attenuation.Productive.Baseline.FixedCertificateParts.FixedCertificateG34a_1_002
namespace ProductiveGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem fixedPartG34a_1_245 : fixedCheck uG34a (24) goalG34a ["a","h","i","t","e","i"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_249 : fixedCheck uG34a (24) goalG34a ["a","h","i","t","e","ɔ","k","p","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_250 : fixedCheck uG34a (24) goalG34a ["a","h","i","t","e","ɔ","k","p","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_251 : fixedCheck uG34a (24) goalG34a ["a","h","i","t","e","ɔ","k","p","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_252 : fixedCheck uG34a (24) goalG34a ["a","h","i","t","e","ɔ","k","p","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_253 : fixedCheck uG34a (24) goalG34a ["a","h","i","t","e","ɔ","k","p","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_254 : fixedCheck uG34a (24) goalG34a ["a","h","i","t","e","ɔ","k","p","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_255 : fixedCheck uG34a (24) goalG34a ["a","h","i","t","e","ɔ","k","p","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_256 : fixedCheck uG34a (24) goalG34a ["a","h","i","t","e","ɔ","k","p","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_257 : fixedCheck uG34a (24) goalG34a ["a","h","i","t","e","ɔ","k","p","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_258 : fixedCheck uG34a (24) goalG34a ["a","h","i","t","e","ɔ","k","p","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_259 : fixedCheck uG34a (24) goalG34a ["a","h","i","t","e","ɔ","k","p","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_260 : fixedCheck uG34a (24) goalG34a ["a","h","i","t","e","ɔ","k","p","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_261 : fixedCheck uG34a (24) goalG34a ["a","h","i","t","e","ɔ","k","p","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_248 : fixedCheck uG34a (24) goalG34a ["a","h","i","t","e","ɔ","k","p"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply fixedCheck_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixedPartG34a_1_249
  · exact fixedPartG34a_1_250
  · exact fixedPartG34a_1_251
  · exact fixedPartG34a_1_252
  · exact fixedPartG34a_1_253
  · exact fixedPartG34a_1_254
  · exact fixedPartG34a_1_255
  · exact fixedPartG34a_1_256
  · exact fixedPartG34a_1_257
  · exact fixedPartG34a_1_258
  · exact fixedPartG34a_1_259
  · exact fixedPartG34a_1_260
  · exact fixedPartG34a_1_261
theorem fixedPartG34a_1_247 : fixedCheck uG34a (24) goalG34a ["a","h","i","t","e","ɔ","k"] [["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply fixedCheck_of_children
  intro x hx
  have he : x="p" := by simpa using hx
  subst x
  exact fixedPartG34a_1_248
theorem fixedPartG34a_1_246 : fixedCheck uG34a (24) goalG34a ["a","h","i","t","e","ɔ"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply fixedCheck_of_children
  intro x hx
  have he : x="k" := by simpa using hx
  subst x
  exact fixedPartG34a_1_247
theorem fixedPartG34a_1_262 : fixedCheck uG34a (24) goalG34a ["a","h","i","t","e","o"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_263 : fixedCheck uG34a (24) goalG34a ["a","h","i","t","e","ʊ"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_264 : fixedCheck uG34a (24) goalG34a ["a","h","i","t","e","u"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_265 : fixedCheck uG34a (24) goalG34a ["a","h","i","t","e","j"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_266 : fixedCheck uG34a (24) goalG34a ["a","h","i","t","e","w"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_238 : fixedCheck uG34a (24) goalG34a ["a","h","i","t","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply fixedCheck_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixedPartG34a_1_239
  · exact fixedPartG34a_1_240
  · exact fixedPartG34a_1_241
  · exact fixedPartG34a_1_242
  · exact fixedPartG34a_1_243
  · exact fixedPartG34a_1_244
  · exact fixedPartG34a_1_245
  · exact fixedPartG34a_1_246
  · exact fixedPartG34a_1_262
  · exact fixedPartG34a_1_263
  · exact fixedPartG34a_1_264
  · exact fixedPartG34a_1_265
  · exact fixedPartG34a_1_266
theorem fixedPartG34a_1_267 : fixedCheck uG34a (24) goalG34a ["a","h","i","t","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_268 : fixedCheck uG34a (24) goalG34a ["a","h","i","t","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_269 : fixedCheck uG34a (24) goalG34a ["a","h","i","t","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_270 : fixedCheck uG34a (24) goalG34a ["a","h","i","t","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_271 : fixedCheck uG34a (24) goalG34a ["a","h","i","t","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_272 : fixedCheck uG34a (24) goalG34a ["a","h","i","t","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_273 : fixedCheck uG34a (24) goalG34a ["a","h","i","t","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_274 : fixedCheck uG34a (24) goalG34a ["a","h","i","t","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_233 : fixedCheck uG34a (24) goalG34a ["a","h","i","t"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply fixedCheck_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixedPartG34a_1_234
  · exact fixedPartG34a_1_235
  · exact fixedPartG34a_1_236
  · exact fixedPartG34a_1_237
  · exact fixedPartG34a_1_238
  · exact fixedPartG34a_1_267
  · exact fixedPartG34a_1_268
  · exact fixedPartG34a_1_269
  · exact fixedPartG34a_1_270
  · exact fixedPartG34a_1_271
  · exact fixedPartG34a_1_272
  · exact fixedPartG34a_1_273
  · exact fixedPartG34a_1_274
theorem fixedPartG34a_1_232 : fixedCheck uG34a (24) goalG34a ["a","h","i"] [["t"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply fixedCheck_of_children
  intro x hx
  have he : x="t" := by simpa using hx
  subst x
  exact fixedPartG34a_1_233
theorem fixedPartG34a_1_275 : fixedCheck uG34a (24) goalG34a ["a","h","ɔ"] [["t"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_278 : fixedCheck uG34a (24) goalG34a ["a","h","o","t","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_279 : fixedCheck uG34a (24) goalG34a ["a","h","o","t","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_280 : fixedCheck uG34a (24) goalG34a ["a","h","o","t","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_281 : fixedCheck uG34a (24) goalG34a ["a","h","o","t","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_283 : fixedCheck uG34a (24) goalG34a ["a","h","o","t","e","∅"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_284 : fixedCheck uG34a (24) goalG34a ["a","h","o","t","e","a"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_285 : fixedCheck uG34a (24) goalG34a ["a","h","o","t","e","ɜ"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_286 : fixedCheck uG34a (24) goalG34a ["a","h","o","t","e","ɛ"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_287 : fixedCheck uG34a (24) goalG34a ["a","h","o","t","e","e"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_288 : fixedCheck uG34a (24) goalG34a ["a","h","o","t","e","ɪ"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_289 : fixedCheck uG34a (24) goalG34a ["a","h","o","t","e","i"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_293 : fixedCheck uG34a (24) goalG34a ["a","h","o","t","e","ɔ","k","p","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_294 : fixedCheck uG34a (24) goalG34a ["a","h","o","t","e","ɔ","k","p","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_295 : fixedCheck uG34a (24) goalG34a ["a","h","o","t","e","ɔ","k","p","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_296 : fixedCheck uG34a (24) goalG34a ["a","h","o","t","e","ɔ","k","p","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_297 : fixedCheck uG34a (24) goalG34a ["a","h","o","t","e","ɔ","k","p","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_298 : fixedCheck uG34a (24) goalG34a ["a","h","o","t","e","ɔ","k","p","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_299 : fixedCheck uG34a (24) goalG34a ["a","h","o","t","e","ɔ","k","p","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_300 : fixedCheck uG34a (24) goalG34a ["a","h","o","t","e","ɔ","k","p","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_301 : fixedCheck uG34a (24) goalG34a ["a","h","o","t","e","ɔ","k","p","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_302 : fixedCheck uG34a (24) goalG34a ["a","h","o","t","e","ɔ","k","p","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_303 : fixedCheck uG34a (24) goalG34a ["a","h","o","t","e","ɔ","k","p","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_304 : fixedCheck uG34a (24) goalG34a ["a","h","o","t","e","ɔ","k","p","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_305 : fixedCheck uG34a (24) goalG34a ["a","h","o","t","e","ɔ","k","p","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_292 : fixedCheck uG34a (24) goalG34a ["a","h","o","t","e","ɔ","k","p"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply fixedCheck_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixedPartG34a_1_293
  · exact fixedPartG34a_1_294
  · exact fixedPartG34a_1_295
  · exact fixedPartG34a_1_296
  · exact fixedPartG34a_1_297
  · exact fixedPartG34a_1_298
  · exact fixedPartG34a_1_299
  · exact fixedPartG34a_1_300
  · exact fixedPartG34a_1_301
  · exact fixedPartG34a_1_302
  · exact fixedPartG34a_1_303
  · exact fixedPartG34a_1_304
  · exact fixedPartG34a_1_305
theorem fixedPartG34a_1_291 : fixedCheck uG34a (24) goalG34a ["a","h","o","t","e","ɔ","k"] [["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply fixedCheck_of_children
  intro x hx
  have he : x="p" := by simpa using hx
  subst x
  exact fixedPartG34a_1_292
theorem fixedPartG34a_1_290 : fixedCheck uG34a (24) goalG34a ["a","h","o","t","e","ɔ"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply fixedCheck_of_children
  intro x hx
  have he : x="k" := by simpa using hx
  subst x
  exact fixedPartG34a_1_291
theorem fixedPartG34a_1_306 : fixedCheck uG34a (24) goalG34a ["a","h","o","t","e","o"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_307 : fixedCheck uG34a (24) goalG34a ["a","h","o","t","e","ʊ"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_308 : fixedCheck uG34a (24) goalG34a ["a","h","o","t","e","u"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_309 : fixedCheck uG34a (24) goalG34a ["a","h","o","t","e","j"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_310 : fixedCheck uG34a (24) goalG34a ["a","h","o","t","e","w"] [["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_282 : fixedCheck uG34a (24) goalG34a ["a","h","o","t","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply fixedCheck_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixedPartG34a_1_283
  · exact fixedPartG34a_1_284
  · exact fixedPartG34a_1_285
  · exact fixedPartG34a_1_286
  · exact fixedPartG34a_1_287
  · exact fixedPartG34a_1_288
  · exact fixedPartG34a_1_289
  · exact fixedPartG34a_1_290
  · exact fixedPartG34a_1_306
  · exact fixedPartG34a_1_307
  · exact fixedPartG34a_1_308
  · exact fixedPartG34a_1_309
  · exact fixedPartG34a_1_310
theorem fixedPartG34a_1_311 : fixedCheck uG34a (24) goalG34a ["a","h","o","t","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_312 : fixedCheck uG34a (24) goalG34a ["a","h","o","t","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_313 : fixedCheck uG34a (24) goalG34a ["a","h","o","t","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_314 : fixedCheck uG34a (24) goalG34a ["a","h","o","t","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_315 : fixedCheck uG34a (24) goalG34a ["a","h","o","t","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_316 : fixedCheck uG34a (24) goalG34a ["a","h","o","t","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_317 : fixedCheck uG34a (24) goalG34a ["a","h","o","t","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_318 : fixedCheck uG34a (24) goalG34a ["a","h","o","t","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_277 : fixedCheck uG34a (24) goalG34a ["a","h","o","t"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply fixedCheck_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact fixedPartG34a_1_278
  · exact fixedPartG34a_1_279
  · exact fixedPartG34a_1_280
  · exact fixedPartG34a_1_281
  · exact fixedPartG34a_1_282
  · exact fixedPartG34a_1_311
  · exact fixedPartG34a_1_312
  · exact fixedPartG34a_1_313
  · exact fixedPartG34a_1_314
  · exact fixedPartG34a_1_315
  · exact fixedPartG34a_1_316
  · exact fixedPartG34a_1_317
  · exact fixedPartG34a_1_318
theorem fixedPartG34a_1_276 : fixedCheck uG34a (24) goalG34a ["a","h","o"] [["t"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply fixedCheck_of_children
  intro x hx
  have he : x="t" := by simpa using hx
  subst x
  exact fixedPartG34a_1_277
theorem fixedPartG34a_1_319 : fixedCheck uG34a (24) goalG34a ["a","h","ʊ"] [["t"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_322 : fixedCheck uG34a (24) goalG34a ["a","h","u","t","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem fixedPartG34a_1_323 : fixedCheck uG34a (24) goalG34a ["a","h","u","t","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["p"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
end ProductiveGua
