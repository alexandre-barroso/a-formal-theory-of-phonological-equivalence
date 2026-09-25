import PhonologicalOpacity.Attenuation.Productive.Baseline.CertificateParts.G37c_7_052
namespace ProductiveGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partG37c_7_4247 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","∅","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4248 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","∅","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4249 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","∅","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4250 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","∅","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4251 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","∅","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4252 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","∅","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4253 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","∅","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4240 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","∅","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_4241
  · exact partG37c_7_4242
  · exact partG37c_7_4243
  · exact partG37c_7_4244
  · exact partG37c_7_4245
  · exact partG37c_7_4246
  · exact partG37c_7_4247
  · exact partG37c_7_4248
  · exact partG37c_7_4249
  · exact partG37c_7_4250
  · exact partG37c_7_4251
  · exact partG37c_7_4252
  · exact partG37c_7_4253
theorem partG37c_7_4239 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","∅","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_4240
theorem partG37c_7_4254 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","∅","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4255 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","∅","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4256 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","∅","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4257 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","∅","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4260 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","∅","j","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4261 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","∅","j","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4262 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","∅","j","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4263 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","∅","j","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4264 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","∅","j","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4265 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","∅","j","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4266 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","∅","j","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4267 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","∅","j","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4268 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","∅","j","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4269 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","∅","j","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4270 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","∅","j","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4271 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","∅","j","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4272 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","∅","j","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4259 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","∅","j","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_4260
  · exact partG37c_7_4261
  · exact partG37c_7_4262
  · exact partG37c_7_4263
  · exact partG37c_7_4264
  · exact partG37c_7_4265
  · exact partG37c_7_4266
  · exact partG37c_7_4267
  · exact partG37c_7_4268
  · exact partG37c_7_4269
  · exact partG37c_7_4270
  · exact partG37c_7_4271
  · exact partG37c_7_4272
theorem partG37c_7_4258 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","∅","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_4259
theorem partG37c_7_4273 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","∅","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4218 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_4219
  · exact partG37c_7_4234
  · exact partG37c_7_4235
  · exact partG37c_7_4236
  · exact partG37c_7_4237
  · exact partG37c_7_4238
  · exact partG37c_7_4239
  · exact partG37c_7_4254
  · exact partG37c_7_4255
  · exact partG37c_7_4256
  · exact partG37c_7_4257
  · exact partG37c_7_4258
  · exact partG37c_7_4273
theorem partG37c_7_4277 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","a","∅","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4278 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","a","∅","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4279 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","a","∅","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4280 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","a","∅","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4281 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","a","∅","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4282 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","a","∅","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4283 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","a","∅","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4284 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","a","∅","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4285 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","a","∅","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4286 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","a","∅","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4287 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","a","∅","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4288 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","a","∅","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4289 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","a","∅","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4276 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","a","∅","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_4277
  · exact partG37c_7_4278
  · exact partG37c_7_4279
  · exact partG37c_7_4280
  · exact partG37c_7_4281
  · exact partG37c_7_4282
  · exact partG37c_7_4283
  · exact partG37c_7_4284
  · exact partG37c_7_4285
  · exact partG37c_7_4286
  · exact partG37c_7_4287
  · exact partG37c_7_4288
  · exact partG37c_7_4289
theorem partG37c_7_4275 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","a","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_4276
theorem partG37c_7_4290 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","a","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4291 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","a","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4292 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","a","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4293 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","a","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4294 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","a","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4297 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","a","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4298 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","a","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4299 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","a","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4300 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","a","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4301 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","a","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4302 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","a","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4303 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","a","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4304 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","a","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4305 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","a","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4306 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","a","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4307 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","a","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4308 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","a","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4309 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","a","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4296 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","a","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_4297
  · exact partG37c_7_4298
  · exact partG37c_7_4299
  · exact partG37c_7_4300
  · exact partG37c_7_4301
  · exact partG37c_7_4302
  · exact partG37c_7_4303
  · exact partG37c_7_4304
  · exact partG37c_7_4305
  · exact partG37c_7_4306
  · exact partG37c_7_4307
  · exact partG37c_7_4308
  · exact partG37c_7_4309
theorem partG37c_7_4295 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","a","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_4296
theorem partG37c_7_4310 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","a","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4311 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","a","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4312 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","a","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4313 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","a","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4316 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","a","j","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4317 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","a","j","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4318 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","a","j","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4319 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","a","j","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4320 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","a","j","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4321 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","a","j","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4322 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","a","j","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4323 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","a","j","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4324 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","a","j","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4325 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","a","j","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_4326 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɔ","s","a","j","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
end ProductiveGua
