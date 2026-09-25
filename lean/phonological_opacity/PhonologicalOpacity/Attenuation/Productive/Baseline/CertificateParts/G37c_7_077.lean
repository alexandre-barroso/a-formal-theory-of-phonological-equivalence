import PhonologicalOpacity.Attenuation.Productive.Baseline.CertificateParts.G37c_7_076
namespace ProductiveGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partG37c_7_6165 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","w","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6168 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","w","j","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6169 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","w","j","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6170 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","w","j","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6171 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","w","j","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6172 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","w","j","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6173 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","w","j","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6174 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","w","j","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6175 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","w","j","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6176 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","w","j","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6177 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","w","j","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6178 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","w","j","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6179 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","w","j","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6180 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","w","j","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6167 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","w","j","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_6168
  · exact partG37c_7_6169
  · exact partG37c_7_6170
  · exact partG37c_7_6171
  · exact partG37c_7_6172
  · exact partG37c_7_6173
  · exact partG37c_7_6174
  · exact partG37c_7_6175
  · exact partG37c_7_6176
  · exact partG37c_7_6177
  · exact partG37c_7_6178
  · exact partG37c_7_6179
  · exact partG37c_7_6180
theorem partG37c_7_6166 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","w","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_6167
theorem partG37c_7_6181 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","w","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6126 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_6127
  · exact partG37c_7_6142
  · exact partG37c_7_6143
  · exact partG37c_7_6144
  · exact partG37c_7_6145
  · exact partG37c_7_6146
  · exact partG37c_7_6147
  · exact partG37c_7_6162
  · exact partG37c_7_6163
  · exact partG37c_7_6164
  · exact partG37c_7_6165
  · exact partG37c_7_6166
  · exact partG37c_7_6181
theorem partG37c_7_5453 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_5454
  · exact partG37c_7_5510
  · exact partG37c_7_5566
  · exact partG37c_7_5622
  · exact partG37c_7_5678
  · exact partG37c_7_5734
  · exact partG37c_7_5790
  · exact partG37c_7_5846
  · exact partG37c_7_5902
  · exact partG37c_7_5958
  · exact partG37c_7_6014
  · exact partG37c_7_6070
  · exact partG37c_7_6126
theorem partG37c_7_5452 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="s" := by simpa using hx
  subst x
  exact partG37c_7_5453
theorem partG37c_7_6185 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","∅","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6186 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","∅","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6187 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","∅","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6188 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","∅","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6189 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","∅","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6190 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","∅","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6193 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","∅","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6194 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","∅","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6195 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","∅","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6196 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","∅","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6197 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","∅","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6198 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","∅","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6199 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","∅","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6200 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","∅","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6201 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","∅","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6202 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","∅","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6203 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","∅","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6204 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","∅","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6205 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","∅","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6192 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","∅","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_6193
  · exact partG37c_7_6194
  · exact partG37c_7_6195
  · exact partG37c_7_6196
  · exact partG37c_7_6197
  · exact partG37c_7_6198
  · exact partG37c_7_6199
  · exact partG37c_7_6200
  · exact partG37c_7_6201
  · exact partG37c_7_6202
  · exact partG37c_7_6203
  · exact partG37c_7_6204
  · exact partG37c_7_6205
theorem partG37c_7_6191 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","∅","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_6192
theorem partG37c_7_6206 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","∅","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6207 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","∅","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6208 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","∅","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6209 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","∅","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6210 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","∅","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6211 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","∅","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6184 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_6185
  · exact partG37c_7_6186
  · exact partG37c_7_6187
  · exact partG37c_7_6188
  · exact partG37c_7_6189
  · exact partG37c_7_6190
  · exact partG37c_7_6191
  · exact partG37c_7_6206
  · exact partG37c_7_6207
  · exact partG37c_7_6208
  · exact partG37c_7_6209
  · exact partG37c_7_6210
  · exact partG37c_7_6211
theorem partG37c_7_6215 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","a","∅","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6216 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","a","∅","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6217 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","a","∅","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6218 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","a","∅","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6219 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","a","∅","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6220 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","a","∅","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6221 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","a","∅","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6222 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","a","∅","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6223 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","a","∅","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6224 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","a","∅","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6225 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","a","∅","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6226 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","a","∅","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6227 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","a","∅","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6214 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","a","∅","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_6215
  · exact partG37c_7_6216
  · exact partG37c_7_6217
  · exact partG37c_7_6218
  · exact partG37c_7_6219
  · exact partG37c_7_6220
  · exact partG37c_7_6221
  · exact partG37c_7_6222
  · exact partG37c_7_6223
  · exact partG37c_7_6224
  · exact partG37c_7_6225
  · exact partG37c_7_6226
  · exact partG37c_7_6227
theorem partG37c_7_6213 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","a","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_6214
theorem partG37c_7_6228 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","a","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6229 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","a","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6230 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","a","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6231 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","a","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6232 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","a","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6235 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","a","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6236 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","a","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6237 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","a","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6238 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","a","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6239 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","a","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6240 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","a","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6241 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","a","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6242 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","a","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6243 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","a","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6244 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","a","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6245 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","a","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_6246 : check uG37c (3) (0) outG37c ["ɔ","tʃ","u","s","a","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
end ProductiveGua
