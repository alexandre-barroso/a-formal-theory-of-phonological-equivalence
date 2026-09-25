import PhonologicalOpacity.Attenuation.Productive.Subject.CertificateParts.G37c_7_038
namespace ProductiveSubjectGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partG37c_7_3127 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɜ","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3128 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɜ","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3129 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɜ","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3116 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɜ","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_3117
  · exact partG37c_7_3118
  · exact partG37c_7_3119
  · exact partG37c_7_3120
  · exact partG37c_7_3121
  · exact partG37c_7_3122
  · exact partG37c_7_3123
  · exact partG37c_7_3124
  · exact partG37c_7_3125
  · exact partG37c_7_3126
  · exact partG37c_7_3127
  · exact partG37c_7_3128
  · exact partG37c_7_3129
theorem partG37c_7_3115 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɜ","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_3116
theorem partG37c_7_3130 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɜ","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3131 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɜ","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3132 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɜ","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3133 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɜ","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3136 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɜ","j","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3137 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɜ","j","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3138 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɜ","j","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3139 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɜ","j","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3140 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɜ","j","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3141 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɜ","j","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3142 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɜ","j","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3143 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɜ","j","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3144 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɜ","j","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3145 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɜ","j","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3146 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɜ","j","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3147 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɜ","j","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3148 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɜ","j","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3135 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɜ","j","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_3136
  · exact partG37c_7_3137
  · exact partG37c_7_3138
  · exact partG37c_7_3139
  · exact partG37c_7_3140
  · exact partG37c_7_3141
  · exact partG37c_7_3142
  · exact partG37c_7_3143
  · exact partG37c_7_3144
  · exact partG37c_7_3145
  · exact partG37c_7_3146
  · exact partG37c_7_3147
  · exact partG37c_7_3148
theorem partG37c_7_3134 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɜ","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_3135
theorem partG37c_7_3149 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɜ","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3094 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_3095
  · exact partG37c_7_3110
  · exact partG37c_7_3111
  · exact partG37c_7_3112
  · exact partG37c_7_3113
  · exact partG37c_7_3114
  · exact partG37c_7_3115
  · exact partG37c_7_3130
  · exact partG37c_7_3131
  · exact partG37c_7_3132
  · exact partG37c_7_3133
  · exact partG37c_7_3134
  · exact partG37c_7_3149
theorem partG37c_7_3153 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɛ","∅","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3154 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɛ","∅","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3155 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɛ","∅","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3156 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɛ","∅","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3157 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɛ","∅","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3158 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɛ","∅","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3159 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɛ","∅","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3160 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɛ","∅","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3161 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɛ","∅","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3162 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɛ","∅","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3163 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɛ","∅","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3164 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɛ","∅","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3165 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɛ","∅","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3152 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɛ","∅","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_3153
  · exact partG37c_7_3154
  · exact partG37c_7_3155
  · exact partG37c_7_3156
  · exact partG37c_7_3157
  · exact partG37c_7_3158
  · exact partG37c_7_3159
  · exact partG37c_7_3160
  · exact partG37c_7_3161
  · exact partG37c_7_3162
  · exact partG37c_7_3163
  · exact partG37c_7_3164
  · exact partG37c_7_3165
theorem partG37c_7_3151 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɛ","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_3152
theorem partG37c_7_3166 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɛ","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3167 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɛ","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3168 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɛ","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3169 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɛ","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3170 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɛ","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3173 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɛ","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3174 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɛ","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3175 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɛ","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3176 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɛ","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3177 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɛ","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3178 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɛ","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3179 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɛ","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3180 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɛ","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3181 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɛ","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3182 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɛ","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3183 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɛ","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3184 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɛ","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3185 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɛ","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3172 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɛ","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_3173
  · exact partG37c_7_3174
  · exact partG37c_7_3175
  · exact partG37c_7_3176
  · exact partG37c_7_3177
  · exact partG37c_7_3178
  · exact partG37c_7_3179
  · exact partG37c_7_3180
  · exact partG37c_7_3181
  · exact partG37c_7_3182
  · exact partG37c_7_3183
  · exact partG37c_7_3184
  · exact partG37c_7_3185
theorem partG37c_7_3171 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɛ","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_3172
theorem partG37c_7_3186 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɛ","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3187 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɛ","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3188 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɛ","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3189 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɛ","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3192 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɛ","j","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3193 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɛ","j","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3194 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɛ","j","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3195 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɛ","j","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3196 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɛ","j","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3197 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɛ","j","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3198 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɛ","j","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3199 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɛ","j","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3200 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɛ","j","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3201 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɛ","j","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3202 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɛ","j","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3203 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɛ","j","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3204 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɛ","j","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3191 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɛ","j","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_3192
  · exact partG37c_7_3193
  · exact partG37c_7_3194
  · exact partG37c_7_3195
  · exact partG37c_7_3196
  · exact partG37c_7_3197
  · exact partG37c_7_3198
  · exact partG37c_7_3199
  · exact partG37c_7_3200
  · exact partG37c_7_3201
  · exact partG37c_7_3202
  · exact partG37c_7_3203
  · exact partG37c_7_3204
theorem partG37c_7_3190 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɛ","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_3191
end ProductiveSubjectGua
