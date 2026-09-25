import PhonologicalOpacity.Attenuation.Productive.Baseline.CertificateParts.G34b_1_027
namespace ProductiveGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partG34b_1_2247 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","ʊ","o","h","ɜ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2248 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","ʊ","o","h","ɛ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2249 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","ʊ","o","h","e"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2250 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","ʊ","o","h","ɪ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2251 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","ʊ","o","h","i"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2252 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","ʊ","o","h","ɔ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2253 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","ʊ","o","h","o"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2254 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","ʊ","o","h","ʊ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2255 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","ʊ","o","h","u"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2256 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","ʊ","o","h","j"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2257 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","ʊ","o","h","w"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2244 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","ʊ","o","h"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG34b_1_2245
  · exact partG34b_1_2246
  · exact partG34b_1_2247
  · exact partG34b_1_2248
  · exact partG34b_1_2249
  · exact partG34b_1_2250
  · exact partG34b_1_2251
  · exact partG34b_1_2252
  · exact partG34b_1_2253
  · exact partG34b_1_2254
  · exact partG34b_1_2255
  · exact partG34b_1_2256
  · exact partG34b_1_2257
theorem partG34b_1_2243 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","ʊ","o"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="h" := by simpa using hx
  subst x
  exact partG34b_1_2244
theorem partG34b_1_2258 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","ʊ","ʊ"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2259 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","ʊ","u"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2260 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","ʊ","j"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2261 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","ʊ","w"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2220 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG34b_1_2221
  · exact partG34b_1_2236
  · exact partG34b_1_2237
  · exact partG34b_1_2238
  · exact partG34b_1_2239
  · exact partG34b_1_2240
  · exact partG34b_1_2241
  · exact partG34b_1_2242
  · exact partG34b_1_2243
  · exact partG34b_1_2258
  · exact partG34b_1_2259
  · exact partG34b_1_2260
  · exact partG34b_1_2261
theorem partG34b_1_2263 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","u","∅"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2264 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","u","a"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2265 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","u","ɜ"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2266 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","u","ɛ"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2267 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","u","e"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2268 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","u","ɪ"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2269 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","u","i"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2270 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","u","ɔ"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2273 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","u","o","h","∅"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2274 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","u","o","h","a"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2275 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","u","o","h","ɜ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2276 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","u","o","h","ɛ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2277 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","u","o","h","e"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2278 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","u","o","h","ɪ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2279 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","u","o","h","i"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2280 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","u","o","h","ɔ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2281 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","u","o","h","o"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2282 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","u","o","h","ʊ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2283 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","u","o","h","u"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2284 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","u","o","h","j"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2285 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","u","o","h","w"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2272 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","u","o","h"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG34b_1_2273
  · exact partG34b_1_2274
  · exact partG34b_1_2275
  · exact partG34b_1_2276
  · exact partG34b_1_2277
  · exact partG34b_1_2278
  · exact partG34b_1_2279
  · exact partG34b_1_2280
  · exact partG34b_1_2281
  · exact partG34b_1_2282
  · exact partG34b_1_2283
  · exact partG34b_1_2284
  · exact partG34b_1_2285
theorem partG34b_1_2271 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","u","o"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="h" := by simpa using hx
  subst x
  exact partG34b_1_2272
theorem partG34b_1_2286 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","u","ʊ"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2287 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","u","u"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2288 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","u","j"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2289 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","u","w"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2262 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG34b_1_2263
  · exact partG34b_1_2264
  · exact partG34b_1_2265
  · exact partG34b_1_2266
  · exact partG34b_1_2267
  · exact partG34b_1_2268
  · exact partG34b_1_2269
  · exact partG34b_1_2270
  · exact partG34b_1_2271
  · exact partG34b_1_2286
  · exact partG34b_1_2287
  · exact partG34b_1_2288
  · exact partG34b_1_2289
theorem partG34b_1_2291 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","j","∅"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2292 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","j","a"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2293 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","j","ɜ"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2294 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","j","ɛ"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2295 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","j","e"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2296 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","j","ɪ"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2297 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","j","i"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2298 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","j","ɔ"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2301 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","j","o","h","∅"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2302 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","j","o","h","a"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2303 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","j","o","h","ɜ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2304 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","j","o","h","ɛ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2305 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","j","o","h","e"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2306 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","j","o","h","ɪ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2307 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","j","o","h","i"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2308 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","j","o","h","ɔ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2309 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","j","o","h","o"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2310 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","j","o","h","ʊ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2311 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","j","o","h","u"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2312 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","j","o","h","j"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2313 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","j","o","h","w"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2300 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","j","o","h"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG34b_1_2301
  · exact partG34b_1_2302
  · exact partG34b_1_2303
  · exact partG34b_1_2304
  · exact partG34b_1_2305
  · exact partG34b_1_2306
  · exact partG34b_1_2307
  · exact partG34b_1_2308
  · exact partG34b_1_2309
  · exact partG34b_1_2310
  · exact partG34b_1_2311
  · exact partG34b_1_2312
  · exact partG34b_1_2313
theorem partG34b_1_2299 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","j","o"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="h" := by simpa using hx
  subst x
  exact partG34b_1_2300
theorem partG34b_1_2314 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","j","ʊ"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2315 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","j","u"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2316 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","j","j"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2317 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","j","w"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2290 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG34b_1_2291
  · exact partG34b_1_2292
  · exact partG34b_1_2293
  · exact partG34b_1_2294
  · exact partG34b_1_2295
  · exact partG34b_1_2296
  · exact partG34b_1_2297
  · exact partG34b_1_2298
  · exact partG34b_1_2299
  · exact partG34b_1_2314
  · exact partG34b_1_2315
  · exact partG34b_1_2316
  · exact partG34b_1_2317
theorem partG34b_1_2319 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","w","∅"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2320 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","w","a"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2321 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","w","ɜ"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2322 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","w","ɛ"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2323 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","w","e"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2324 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","w","ɪ"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
end ProductiveGua
