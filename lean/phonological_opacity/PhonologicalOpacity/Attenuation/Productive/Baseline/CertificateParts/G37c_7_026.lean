import PhonologicalOpacity.Attenuation.Productive.Baseline.CertificateParts.G37c_7_025
namespace ProductiveGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partG37c_7_2087 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","i","∅","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2088 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","i","∅","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2089 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","i","∅","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2090 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","i","∅","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2091 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","i","∅","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2092 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","i","∅","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2093 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","i","∅","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2094 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","i","∅","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2095 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","i","∅","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2096 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","i","∅","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2097 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","i","∅","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2084 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","i","∅","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_2085
  · exact partG37c_7_2086
  · exact partG37c_7_2087
  · exact partG37c_7_2088
  · exact partG37c_7_2089
  · exact partG37c_7_2090
  · exact partG37c_7_2091
  · exact partG37c_7_2092
  · exact partG37c_7_2093
  · exact partG37c_7_2094
  · exact partG37c_7_2095
  · exact partG37c_7_2096
  · exact partG37c_7_2097
theorem partG37c_7_2083 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","i","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_2084
theorem partG37c_7_2098 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","i","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2099 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","i","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2100 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","i","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2101 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","i","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2102 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","i","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2105 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","i","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2106 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","i","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2107 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","i","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2108 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","i","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2109 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","i","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2110 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","i","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2111 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","i","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2112 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","i","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2113 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","i","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2114 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","i","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2115 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","i","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2116 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","i","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2117 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","i","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2104 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","i","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_2105
  · exact partG37c_7_2106
  · exact partG37c_7_2107
  · exact partG37c_7_2108
  · exact partG37c_7_2109
  · exact partG37c_7_2110
  · exact partG37c_7_2111
  · exact partG37c_7_2112
  · exact partG37c_7_2113
  · exact partG37c_7_2114
  · exact partG37c_7_2115
  · exact partG37c_7_2116
  · exact partG37c_7_2117
theorem partG37c_7_2103 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","i","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_2104
theorem partG37c_7_2118 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","i","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2119 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","i","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2120 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","i","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2121 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","i","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2124 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","i","j","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2125 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","i","j","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2126 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","i","j","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2127 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","i","j","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2128 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","i","j","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2129 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","i","j","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2130 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","i","j","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2131 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","i","j","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2132 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","i","j","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2133 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","i","j","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2134 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","i","j","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2135 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","i","j","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2136 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","i","j","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2123 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","i","j","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_2124
  · exact partG37c_7_2125
  · exact partG37c_7_2126
  · exact partG37c_7_2127
  · exact partG37c_7_2128
  · exact partG37c_7_2129
  · exact partG37c_7_2130
  · exact partG37c_7_2131
  · exact partG37c_7_2132
  · exact partG37c_7_2133
  · exact partG37c_7_2134
  · exact partG37c_7_2135
  · exact partG37c_7_2136
theorem partG37c_7_2122 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","i","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_2123
theorem partG37c_7_2137 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","i","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2082 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_2083
  · exact partG37c_7_2098
  · exact partG37c_7_2099
  · exact partG37c_7_2100
  · exact partG37c_7_2101
  · exact partG37c_7_2102
  · exact partG37c_7_2103
  · exact partG37c_7_2118
  · exact partG37c_7_2119
  · exact partG37c_7_2120
  · exact partG37c_7_2121
  · exact partG37c_7_2122
  · exact partG37c_7_2137
theorem partG37c_7_2141 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɔ","∅","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2142 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɔ","∅","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2143 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɔ","∅","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2144 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɔ","∅","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2145 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɔ","∅","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2146 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɔ","∅","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2147 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɔ","∅","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2148 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɔ","∅","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2149 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɔ","∅","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2150 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɔ","∅","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2151 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɔ","∅","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2152 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɔ","∅","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2153 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɔ","∅","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2140 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɔ","∅","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_2141
  · exact partG37c_7_2142
  · exact partG37c_7_2143
  · exact partG37c_7_2144
  · exact partG37c_7_2145
  · exact partG37c_7_2146
  · exact partG37c_7_2147
  · exact partG37c_7_2148
  · exact partG37c_7_2149
  · exact partG37c_7_2150
  · exact partG37c_7_2151
  · exact partG37c_7_2152
  · exact partG37c_7_2153
theorem partG37c_7_2139 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɔ","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_2140
theorem partG37c_7_2154 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɔ","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2155 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɔ","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2156 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɔ","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2157 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɔ","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2158 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɔ","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2161 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɔ","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2162 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɔ","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2163 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɔ","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2164 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɔ","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2165 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɔ","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2166 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɛ","s","ɔ","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
end ProductiveGua
