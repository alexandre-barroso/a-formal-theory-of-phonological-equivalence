import PhonologicalOpacity.Attenuation.Productive.Subject.CertificateParts.G37c_7_026
namespace ProductiveSubjectGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partG37c_7_2167 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɔ","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2168 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɔ","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2169 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɔ","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2170 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɔ","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2171 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɔ","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2172 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɔ","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2173 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɔ","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2160 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɔ","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_2161
  · exact partG37c_7_2162
  · exact partG37c_7_2163
  · exact partG37c_7_2164
  · exact partG37c_7_2165
  · exact partG37c_7_2166
  · exact partG37c_7_2167
  · exact partG37c_7_2168
  · exact partG37c_7_2169
  · exact partG37c_7_2170
  · exact partG37c_7_2171
  · exact partG37c_7_2172
  · exact partG37c_7_2173
theorem partG37c_7_2159 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɔ","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_2160
theorem partG37c_7_2174 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɔ","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2175 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɔ","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2176 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɔ","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2177 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɔ","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2180 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɔ","j","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2181 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɔ","j","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2182 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɔ","j","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2183 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɔ","j","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2184 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɔ","j","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2185 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɔ","j","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2186 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɔ","j","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2187 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɔ","j","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2188 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɔ","j","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2189 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɔ","j","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2190 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɔ","j","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2191 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɔ","j","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2192 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɔ","j","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2179 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɔ","j","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_2180
  · exact partG37c_7_2181
  · exact partG37c_7_2182
  · exact partG37c_7_2183
  · exact partG37c_7_2184
  · exact partG37c_7_2185
  · exact partG37c_7_2186
  · exact partG37c_7_2187
  · exact partG37c_7_2188
  · exact partG37c_7_2189
  · exact partG37c_7_2190
  · exact partG37c_7_2191
  · exact partG37c_7_2192
theorem partG37c_7_2178 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɔ","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_2179
theorem partG37c_7_2193 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɔ","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2138 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_2139
  · exact partG37c_7_2154
  · exact partG37c_7_2155
  · exact partG37c_7_2156
  · exact partG37c_7_2157
  · exact partG37c_7_2158
  · exact partG37c_7_2159
  · exact partG37c_7_2174
  · exact partG37c_7_2175
  · exact partG37c_7_2176
  · exact partG37c_7_2177
  · exact partG37c_7_2178
  · exact partG37c_7_2193
theorem partG37c_7_2197 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","o","∅","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2198 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","o","∅","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2199 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","o","∅","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2200 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","o","∅","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2201 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","o","∅","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2202 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","o","∅","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2203 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","o","∅","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2204 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","o","∅","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2205 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","o","∅","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2206 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","o","∅","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2207 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","o","∅","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2208 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","o","∅","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2209 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","o","∅","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2196 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","o","∅","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_2197
  · exact partG37c_7_2198
  · exact partG37c_7_2199
  · exact partG37c_7_2200
  · exact partG37c_7_2201
  · exact partG37c_7_2202
  · exact partG37c_7_2203
  · exact partG37c_7_2204
  · exact partG37c_7_2205
  · exact partG37c_7_2206
  · exact partG37c_7_2207
  · exact partG37c_7_2208
  · exact partG37c_7_2209
theorem partG37c_7_2195 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","o","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_2196
theorem partG37c_7_2210 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","o","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2211 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","o","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2212 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","o","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2213 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","o","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2214 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","o","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2217 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","o","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2218 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","o","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2219 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","o","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2220 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","o","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2221 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","o","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2222 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","o","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2223 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","o","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2224 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","o","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2225 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","o","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2226 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","o","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2227 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","o","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2228 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","o","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2229 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","o","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2216 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","o","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_2217
  · exact partG37c_7_2218
  · exact partG37c_7_2219
  · exact partG37c_7_2220
  · exact partG37c_7_2221
  · exact partG37c_7_2222
  · exact partG37c_7_2223
  · exact partG37c_7_2224
  · exact partG37c_7_2225
  · exact partG37c_7_2226
  · exact partG37c_7_2227
  · exact partG37c_7_2228
  · exact partG37c_7_2229
theorem partG37c_7_2215 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","o","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_2216
theorem partG37c_7_2230 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","o","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2231 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","o","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2232 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","o","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2233 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","o","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2236 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","o","j","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2237 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","o","j","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2238 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","o","j","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2239 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","o","j","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2240 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","o","j","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2241 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","o","j","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2242 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","o","j","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2243 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","o","j","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2244 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","o","j","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2245 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","o","j","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2246 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","o","j","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
end ProductiveSubjectGua
