import PhonologicalOpacity.Attenuation.Productive.Subject.CertificateParts.G37c_7_027
namespace ProductiveSubjectGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partG37c_7_2247 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","o","j","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2248 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","o","j","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2235 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","o","j","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_2236
  · exact partG37c_7_2237
  · exact partG37c_7_2238
  · exact partG37c_7_2239
  · exact partG37c_7_2240
  · exact partG37c_7_2241
  · exact partG37c_7_2242
  · exact partG37c_7_2243
  · exact partG37c_7_2244
  · exact partG37c_7_2245
  · exact partG37c_7_2246
  · exact partG37c_7_2247
  · exact partG37c_7_2248
theorem partG37c_7_2234 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","o","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_2235
theorem partG37c_7_2249 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","o","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2194 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_2195
  · exact partG37c_7_2210
  · exact partG37c_7_2211
  · exact partG37c_7_2212
  · exact partG37c_7_2213
  · exact partG37c_7_2214
  · exact partG37c_7_2215
  · exact partG37c_7_2230
  · exact partG37c_7_2231
  · exact partG37c_7_2232
  · exact partG37c_7_2233
  · exact partG37c_7_2234
  · exact partG37c_7_2249
theorem partG37c_7_2253 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ʊ","∅","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2254 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ʊ","∅","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2255 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ʊ","∅","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2256 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ʊ","∅","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2257 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ʊ","∅","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2258 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ʊ","∅","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2259 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ʊ","∅","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2260 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ʊ","∅","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2261 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ʊ","∅","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2262 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ʊ","∅","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2263 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ʊ","∅","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2264 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ʊ","∅","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2265 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ʊ","∅","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2252 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ʊ","∅","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_2253
  · exact partG37c_7_2254
  · exact partG37c_7_2255
  · exact partG37c_7_2256
  · exact partG37c_7_2257
  · exact partG37c_7_2258
  · exact partG37c_7_2259
  · exact partG37c_7_2260
  · exact partG37c_7_2261
  · exact partG37c_7_2262
  · exact partG37c_7_2263
  · exact partG37c_7_2264
  · exact partG37c_7_2265
theorem partG37c_7_2251 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ʊ","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_2252
theorem partG37c_7_2266 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ʊ","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2267 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ʊ","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2268 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ʊ","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2269 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ʊ","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2270 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ʊ","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2273 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ʊ","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2274 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ʊ","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2275 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ʊ","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2276 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ʊ","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2277 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ʊ","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2278 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ʊ","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2279 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ʊ","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2280 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ʊ","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2281 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ʊ","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2282 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ʊ","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2283 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ʊ","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2284 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ʊ","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2285 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ʊ","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2272 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ʊ","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_2273
  · exact partG37c_7_2274
  · exact partG37c_7_2275
  · exact partG37c_7_2276
  · exact partG37c_7_2277
  · exact partG37c_7_2278
  · exact partG37c_7_2279
  · exact partG37c_7_2280
  · exact partG37c_7_2281
  · exact partG37c_7_2282
  · exact partG37c_7_2283
  · exact partG37c_7_2284
  · exact partG37c_7_2285
theorem partG37c_7_2271 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ʊ","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_2272
theorem partG37c_7_2286 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ʊ","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2287 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ʊ","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2288 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ʊ","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2289 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ʊ","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2292 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ʊ","j","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2293 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ʊ","j","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2294 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ʊ","j","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2295 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ʊ","j","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2296 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ʊ","j","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2297 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ʊ","j","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2298 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ʊ","j","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2299 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ʊ","j","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2300 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ʊ","j","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2301 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ʊ","j","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2302 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ʊ","j","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2303 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ʊ","j","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2304 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ʊ","j","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2291 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ʊ","j","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_2292
  · exact partG37c_7_2293
  · exact partG37c_7_2294
  · exact partG37c_7_2295
  · exact partG37c_7_2296
  · exact partG37c_7_2297
  · exact partG37c_7_2298
  · exact partG37c_7_2299
  · exact partG37c_7_2300
  · exact partG37c_7_2301
  · exact partG37c_7_2302
  · exact partG37c_7_2303
  · exact partG37c_7_2304
theorem partG37c_7_2290 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ʊ","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_2291
theorem partG37c_7_2305 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ʊ","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2250 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_2251
  · exact partG37c_7_2266
  · exact partG37c_7_2267
  · exact partG37c_7_2268
  · exact partG37c_7_2269
  · exact partG37c_7_2270
  · exact partG37c_7_2271
  · exact partG37c_7_2286
  · exact partG37c_7_2287
  · exact partG37c_7_2288
  · exact partG37c_7_2289
  · exact partG37c_7_2290
  · exact partG37c_7_2305
theorem partG37c_7_2309 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","u","∅","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2310 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","u","∅","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2311 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","u","∅","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2312 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","u","∅","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2313 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","u","∅","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2314 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","u","∅","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2315 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","u","∅","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2316 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","u","∅","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2317 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","u","∅","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2318 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","u","∅","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2319 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","u","∅","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2320 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","u","∅","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2321 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","u","∅","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2308 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","u","∅","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_2309
  · exact partG37c_7_2310
  · exact partG37c_7_2311
  · exact partG37c_7_2312
  · exact partG37c_7_2313
  · exact partG37c_7_2314
  · exact partG37c_7_2315
  · exact partG37c_7_2316
  · exact partG37c_7_2317
  · exact partG37c_7_2318
  · exact partG37c_7_2319
  · exact partG37c_7_2320
  · exact partG37c_7_2321
theorem partG37c_7_2307 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","u","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_2308
theorem partG37c_7_2322 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","u","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2323 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","u","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2324 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","u","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
end ProductiveSubjectGua
