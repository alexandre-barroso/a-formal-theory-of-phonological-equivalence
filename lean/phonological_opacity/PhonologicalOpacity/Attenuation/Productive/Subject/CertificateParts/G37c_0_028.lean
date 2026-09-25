import PhonologicalOpacity.Attenuation.Productive.Subject.CertificateParts.G37c_0_027
namespace ProductiveSubjectGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partG37c_0_2247 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɛ","∅","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2248 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɛ","∅","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2249 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɛ","∅","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2236 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɛ","∅","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_0_2237
  · exact partG37c_0_2238
  · exact partG37c_0_2239
  · exact partG37c_0_2240
  · exact partG37c_0_2241
  · exact partG37c_0_2242
  · exact partG37c_0_2243
  · exact partG37c_0_2244
  · exact partG37c_0_2245
  · exact partG37c_0_2246
  · exact partG37c_0_2247
  · exact partG37c_0_2248
  · exact partG37c_0_2249
theorem partG37c_0_2235 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɛ","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_0_2236
theorem partG37c_0_2250 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɛ","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2251 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɛ","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2252 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɛ","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2253 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɛ","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2254 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɛ","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2257 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɛ","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2258 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɛ","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2259 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɛ","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2260 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɛ","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2261 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɛ","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2262 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɛ","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2263 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɛ","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2264 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɛ","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2265 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɛ","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2266 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɛ","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2267 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɛ","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2268 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɛ","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2269 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɛ","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2256 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɛ","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_0_2257
  · exact partG37c_0_2258
  · exact partG37c_0_2259
  · exact partG37c_0_2260
  · exact partG37c_0_2261
  · exact partG37c_0_2262
  · exact partG37c_0_2263
  · exact partG37c_0_2264
  · exact partG37c_0_2265
  · exact partG37c_0_2266
  · exact partG37c_0_2267
  · exact partG37c_0_2268
  · exact partG37c_0_2269
theorem partG37c_0_2255 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɛ","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_0_2256
theorem partG37c_0_2270 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɛ","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2271 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɛ","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2272 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɛ","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2273 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɛ","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2276 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɛ","j","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2277 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɛ","j","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2278 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɛ","j","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2279 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɛ","j","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2280 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɛ","j","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2281 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɛ","j","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2282 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɛ","j","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2283 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɛ","j","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2284 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɛ","j","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2285 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɛ","j","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2286 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɛ","j","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2287 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɛ","j","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2288 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɛ","j","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2275 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɛ","j","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_0_2276
  · exact partG37c_0_2277
  · exact partG37c_0_2278
  · exact partG37c_0_2279
  · exact partG37c_0_2280
  · exact partG37c_0_2281
  · exact partG37c_0_2282
  · exact partG37c_0_2283
  · exact partG37c_0_2284
  · exact partG37c_0_2285
  · exact partG37c_0_2286
  · exact partG37c_0_2287
  · exact partG37c_0_2288
theorem partG37c_0_2274 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɛ","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_0_2275
theorem partG37c_0_2289 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɛ","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2234 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_0_2235
  · exact partG37c_0_2250
  · exact partG37c_0_2251
  · exact partG37c_0_2252
  · exact partG37c_0_2253
  · exact partG37c_0_2254
  · exact partG37c_0_2255
  · exact partG37c_0_2270
  · exact partG37c_0_2271
  · exact partG37c_0_2272
  · exact partG37c_0_2273
  · exact partG37c_0_2274
  · exact partG37c_0_2289
theorem partG37c_0_2291 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","e","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2292 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","e","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2293 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","e","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2294 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","e","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2295 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","e","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2296 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","e","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2299 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","e","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2300 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","e","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2301 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","e","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2302 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","e","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2303 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","e","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2304 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","e","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2305 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","e","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2306 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","e","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2307 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","e","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2308 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","e","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2309 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","e","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2310 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","e","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2311 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","e","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2298 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","e","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_0_2299
  · exact partG37c_0_2300
  · exact partG37c_0_2301
  · exact partG37c_0_2302
  · exact partG37c_0_2303
  · exact partG37c_0_2304
  · exact partG37c_0_2305
  · exact partG37c_0_2306
  · exact partG37c_0_2307
  · exact partG37c_0_2308
  · exact partG37c_0_2309
  · exact partG37c_0_2310
  · exact partG37c_0_2311
theorem partG37c_0_2297 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","e","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_0_2298
theorem partG37c_0_2312 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","e","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2313 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","e","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2314 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","e","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2315 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","e","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2316 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","e","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2317 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","e","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2290 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_0_2291
  · exact partG37c_0_2292
  · exact partG37c_0_2293
  · exact partG37c_0_2294
  · exact partG37c_0_2295
  · exact partG37c_0_2296
  · exact partG37c_0_2297
  · exact partG37c_0_2312
  · exact partG37c_0_2313
  · exact partG37c_0_2314
  · exact partG37c_0_2315
  · exact partG37c_0_2316
  · exact partG37c_0_2317
theorem partG37c_0_2321 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɪ","∅","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2322 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɪ","∅","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2323 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɪ","∅","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2324 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɪ","∅","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2325 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɪ","∅","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2326 : check uG37c (3) (0) outG37c ["∅","tʃ","ɔ","s","ɪ","∅","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
end ProductiveSubjectGua
