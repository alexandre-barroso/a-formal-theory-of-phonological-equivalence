import PhonologicalOpacity.Attenuation.Productive.Subject.CertificateParts.C21b_12_002
namespace ProductiveSubjectGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partC21b_12_244 : check uC21b (3) (-4) outC21b ["w","ʊ","s","ʊ","i"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_245 : check uC21b (3) (-4) outC21b ["w","ʊ","s","ʊ","ɔ"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_246 : check uC21b (3) (-4) outC21b ["w","ʊ","s","ʊ","o"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_247 : check uC21b (3) (-4) outC21b ["w","ʊ","s","ʊ","ʊ"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_248 : check uC21b (3) (-4) outC21b ["w","ʊ","s","ʊ","u"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_249 : check uC21b (3) (-4) outC21b ["w","ʊ","s","ʊ","j"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_250 : check uC21b (3) (-4) outC21b ["w","ʊ","s","ʊ","w"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_237 : check uC21b (3) (-4) outC21b ["w","ʊ","s","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partC21b_12_238
  · exact partC21b_12_239
  · exact partC21b_12_240
  · exact partC21b_12_241
  · exact partC21b_12_242
  · exact partC21b_12_243
  · exact partC21b_12_244
  · exact partC21b_12_245
  · exact partC21b_12_246
  · exact partC21b_12_247
  · exact partC21b_12_248
  · exact partC21b_12_249
  · exact partC21b_12_250
theorem partC21b_12_252 : check uC21b (3) (-4) outC21b ["w","ʊ","s","u","∅"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_253 : check uC21b (3) (-4) outC21b ["w","ʊ","s","u","a"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_254 : check uC21b (3) (-4) outC21b ["w","ʊ","s","u","ɜ"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_255 : check uC21b (3) (-4) outC21b ["w","ʊ","s","u","ɛ"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_256 : check uC21b (3) (-4) outC21b ["w","ʊ","s","u","e"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_257 : check uC21b (3) (-4) outC21b ["w","ʊ","s","u","ɪ"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_258 : check uC21b (3) (-4) outC21b ["w","ʊ","s","u","i"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_259 : check uC21b (3) (-4) outC21b ["w","ʊ","s","u","ɔ"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_260 : check uC21b (3) (-4) outC21b ["w","ʊ","s","u","o"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_261 : check uC21b (3) (-4) outC21b ["w","ʊ","s","u","ʊ"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_262 : check uC21b (3) (-4) outC21b ["w","ʊ","s","u","u"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_263 : check uC21b (3) (-4) outC21b ["w","ʊ","s","u","j"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_264 : check uC21b (3) (-4) outC21b ["w","ʊ","s","u","w"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_251 : check uC21b (3) (-4) outC21b ["w","ʊ","s","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partC21b_12_252
  · exact partC21b_12_253
  · exact partC21b_12_254
  · exact partC21b_12_255
  · exact partC21b_12_256
  · exact partC21b_12_257
  · exact partC21b_12_258
  · exact partC21b_12_259
  · exact partC21b_12_260
  · exact partC21b_12_261
  · exact partC21b_12_262
  · exact partC21b_12_263
  · exact partC21b_12_264
theorem partC21b_12_265 : check uC21b (3) (-4) outC21b ["w","ʊ","s","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_266 : check uC21b (3) (-4) outC21b ["w","ʊ","s","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_175 : check uC21b (3) (-4) outC21b ["w","ʊ","s"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partC21b_12_176
  · exact partC21b_12_177
  · exact partC21b_12_191
  · exact partC21b_12_192
  · exact partC21b_12_206
  · exact partC21b_12_207
  · exact partC21b_12_221
  · exact partC21b_12_222
  · exact partC21b_12_236
  · exact partC21b_12_237
  · exact partC21b_12_251
  · exact partC21b_12_265
  · exact partC21b_12_266
theorem partC21b_12_174 : check uC21b (3) (-4) outC21b ["w","ʊ"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="s" := by simpa using hx
  subst x
  exact partC21b_12_175
theorem partC21b_12_269 : check uC21b (3) (-4) outC21b ["w","u","s","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_270 : check uC21b (3) (-4) outC21b ["w","u","s","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_271 : check uC21b (3) (-4) outC21b ["w","u","s","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_272 : check uC21b (3) (-4) outC21b ["w","u","s","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_273 : check uC21b (3) (-4) outC21b ["w","u","s","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_274 : check uC21b (3) (-4) outC21b ["w","u","s","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_275 : check uC21b (3) (-4) outC21b ["w","u","s","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_276 : check uC21b (3) (-4) outC21b ["w","u","s","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_277 : check uC21b (3) (-4) outC21b ["w","u","s","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_279 : check uC21b (3) (-4) outC21b ["w","u","s","ʊ","∅"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_280 : check uC21b (3) (-4) outC21b ["w","u","s","ʊ","a"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_281 : check uC21b (3) (-4) outC21b ["w","u","s","ʊ","ɜ"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_282 : check uC21b (3) (-4) outC21b ["w","u","s","ʊ","ɛ"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_283 : check uC21b (3) (-4) outC21b ["w","u","s","ʊ","e"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_284 : check uC21b (3) (-4) outC21b ["w","u","s","ʊ","ɪ"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_285 : check uC21b (3) (-4) outC21b ["w","u","s","ʊ","i"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_286 : check uC21b (3) (-4) outC21b ["w","u","s","ʊ","ɔ"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_287 : check uC21b (3) (-4) outC21b ["w","u","s","ʊ","o"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_288 : check uC21b (3) (-4) outC21b ["w","u","s","ʊ","ʊ"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_289 : check uC21b (3) (-4) outC21b ["w","u","s","ʊ","u"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_290 : check uC21b (3) (-4) outC21b ["w","u","s","ʊ","j"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_291 : check uC21b (3) (-4) outC21b ["w","u","s","ʊ","w"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_278 : check uC21b (3) (-4) outC21b ["w","u","s","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partC21b_12_279
  · exact partC21b_12_280
  · exact partC21b_12_281
  · exact partC21b_12_282
  · exact partC21b_12_283
  · exact partC21b_12_284
  · exact partC21b_12_285
  · exact partC21b_12_286
  · exact partC21b_12_287
  · exact partC21b_12_288
  · exact partC21b_12_289
  · exact partC21b_12_290
  · exact partC21b_12_291
theorem partC21b_12_292 : check uC21b (3) (-4) outC21b ["w","u","s","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_293 : check uC21b (3) (-4) outC21b ["w","u","s","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_294 : check uC21b (3) (-4) outC21b ["w","u","s","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_268 : check uC21b (3) (-4) outC21b ["w","u","s"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partC21b_12_269
  · exact partC21b_12_270
  · exact partC21b_12_271
  · exact partC21b_12_272
  · exact partC21b_12_273
  · exact partC21b_12_274
  · exact partC21b_12_275
  · exact partC21b_12_276
  · exact partC21b_12_277
  · exact partC21b_12_278
  · exact partC21b_12_292
  · exact partC21b_12_293
  · exact partC21b_12_294
theorem partC21b_12_267 : check uC21b (3) (-4) outC21b ["w","u"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="s" := by simpa using hx
  subst x
  exact partC21b_12_268
theorem partC21b_12_295 : check uC21b (3) (-4) outC21b ["w","j"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_298 : check uC21b (3) (-4) outC21b ["w","w","s","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_299 : check uC21b (3) (-4) outC21b ["w","w","s","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_300 : check uC21b (3) (-4) outC21b ["w","w","s","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_301 : check uC21b (3) (-4) outC21b ["w","w","s","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_302 : check uC21b (3) (-4) outC21b ["w","w","s","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_303 : check uC21b (3) (-4) outC21b ["w","w","s","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_304 : check uC21b (3) (-4) outC21b ["w","w","s","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_305 : check uC21b (3) (-4) outC21b ["w","w","s","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_306 : check uC21b (3) (-4) outC21b ["w","w","s","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_307 : check uC21b (3) (-4) outC21b ["w","w","s","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_308 : check uC21b (3) (-4) outC21b ["w","w","s","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_309 : check uC21b (3) (-4) outC21b ["w","w","s","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_310 : check uC21b (3) (-4) outC21b ["w","w","s","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partC21b_12_297 : check uC21b (3) (-4) outC21b ["w","w","s"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partC21b_12_298
  · exact partC21b_12_299
  · exact partC21b_12_300
  · exact partC21b_12_301
  · exact partC21b_12_302
  · exact partC21b_12_303
  · exact partC21b_12_304
  · exact partC21b_12_305
  · exact partC21b_12_306
  · exact partC21b_12_307
  · exact partC21b_12_308
  · exact partC21b_12_309
  · exact partC21b_12_310
theorem partC21b_12_296 : check uC21b (3) (-4) outC21b ["w","w"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="s" := by simpa using hx
  subst x
  exact partC21b_12_297
theorem checkedC21b_12 : check uC21b (3) (-4) outC21b ["w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partC21b_12_1
  · exact partC21b_12_2
  · exact partC21b_12_30
  · exact partC21b_12_45
  · exact partC21b_12_73
  · exact partC21b_12_88
  · exact partC21b_12_116
  · exact partC21b_12_131
  · exact partC21b_12_159
  · exact partC21b_12_174
  · exact partC21b_12_267
  · exact partC21b_12_295
  · exact partC21b_12_296
end ProductiveSubjectGua
