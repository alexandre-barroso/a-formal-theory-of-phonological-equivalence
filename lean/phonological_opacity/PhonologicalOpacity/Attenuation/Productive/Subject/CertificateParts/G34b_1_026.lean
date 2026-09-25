import PhonologicalOpacity.Attenuation.Productive.Subject.CertificateParts.G34b_1_025
namespace ProductiveSubjectGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partG34b_1_2087 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","ɪ","∅","h","e"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2088 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","ɪ","∅","h","ɪ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2089 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","ɪ","∅","h","i"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2090 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","ɪ","∅","h","ɔ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2091 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","ɪ","∅","h","o"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2092 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","ɪ","∅","h","ʊ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2093 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","ɪ","∅","h","u"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2094 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","ɪ","∅","h","j"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2095 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","ɪ","∅","h","w"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2082 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","ɪ","∅","h"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG34b_1_2083
  · exact partG34b_1_2084
  · exact partG34b_1_2085
  · exact partG34b_1_2086
  · exact partG34b_1_2087
  · exact partG34b_1_2088
  · exact partG34b_1_2089
  · exact partG34b_1_2090
  · exact partG34b_1_2091
  · exact partG34b_1_2092
  · exact partG34b_1_2093
  · exact partG34b_1_2094
  · exact partG34b_1_2095
theorem partG34b_1_2081 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","ɪ","∅"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="h" := by simpa using hx
  subst x
  exact partG34b_1_2082
theorem partG34b_1_2096 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","ɪ","a"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2097 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","ɪ","ɜ"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2098 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","ɪ","ɛ"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2099 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","ɪ","e"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2100 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","ɪ","ɪ"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2101 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","ɪ","i"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2102 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","ɪ","ɔ"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2105 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","ɪ","o","h","∅"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2106 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","ɪ","o","h","a"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2107 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","ɪ","o","h","ɜ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2108 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","ɪ","o","h","ɛ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2109 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","ɪ","o","h","e"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2110 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","ɪ","o","h","ɪ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2111 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","ɪ","o","h","i"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2112 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","ɪ","o","h","ɔ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2113 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","ɪ","o","h","o"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2114 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","ɪ","o","h","ʊ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2115 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","ɪ","o","h","u"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2116 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","ɪ","o","h","j"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2117 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","ɪ","o","h","w"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2104 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","ɪ","o","h"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG34b_1_2105
  · exact partG34b_1_2106
  · exact partG34b_1_2107
  · exact partG34b_1_2108
  · exact partG34b_1_2109
  · exact partG34b_1_2110
  · exact partG34b_1_2111
  · exact partG34b_1_2112
  · exact partG34b_1_2113
  · exact partG34b_1_2114
  · exact partG34b_1_2115
  · exact partG34b_1_2116
  · exact partG34b_1_2117
theorem partG34b_1_2103 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","ɪ","o"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="h" := by simpa using hx
  subst x
  exact partG34b_1_2104
theorem partG34b_1_2118 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","ɪ","ʊ"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2119 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","ɪ","u"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2120 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","ɪ","j"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2121 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","ɪ","w"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2080 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG34b_1_2081
  · exact partG34b_1_2096
  · exact partG34b_1_2097
  · exact partG34b_1_2098
  · exact partG34b_1_2099
  · exact partG34b_1_2100
  · exact partG34b_1_2101
  · exact partG34b_1_2102
  · exact partG34b_1_2103
  · exact partG34b_1_2118
  · exact partG34b_1_2119
  · exact partG34b_1_2120
  · exact partG34b_1_2121
theorem partG34b_1_2123 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","i","∅"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2124 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","i","a"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2125 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","i","ɜ"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2126 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","i","ɛ"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2127 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","i","e"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2128 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","i","ɪ"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2129 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","i","i"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2130 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","i","ɔ"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2133 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","i","o","h","∅"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2134 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","i","o","h","a"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2135 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","i","o","h","ɜ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2136 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","i","o","h","ɛ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2137 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","i","o","h","e"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2138 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","i","o","h","ɪ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2139 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","i","o","h","i"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2140 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","i","o","h","ɔ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2141 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","i","o","h","o"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2142 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","i","o","h","ʊ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2143 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","i","o","h","u"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2144 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","i","o","h","j"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2145 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","i","o","h","w"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2132 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","i","o","h"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG34b_1_2133
  · exact partG34b_1_2134
  · exact partG34b_1_2135
  · exact partG34b_1_2136
  · exact partG34b_1_2137
  · exact partG34b_1_2138
  · exact partG34b_1_2139
  · exact partG34b_1_2140
  · exact partG34b_1_2141
  · exact partG34b_1_2142
  · exact partG34b_1_2143
  · exact partG34b_1_2144
  · exact partG34b_1_2145
theorem partG34b_1_2131 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","i","o"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="h" := by simpa using hx
  subst x
  exact partG34b_1_2132
theorem partG34b_1_2146 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","i","ʊ"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2147 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","i","u"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2148 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","i","j"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2149 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","i","w"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2122 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG34b_1_2123
  · exact partG34b_1_2124
  · exact partG34b_1_2125
  · exact partG34b_1_2126
  · exact partG34b_1_2127
  · exact partG34b_1_2128
  · exact partG34b_1_2129
  · exact partG34b_1_2130
  · exact partG34b_1_2131
  · exact partG34b_1_2146
  · exact partG34b_1_2147
  · exact partG34b_1_2148
  · exact partG34b_1_2149
theorem partG34b_1_2153 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","ɔ","∅","h","∅"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2154 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","ɔ","∅","h","a"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2155 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","ɔ","∅","h","ɜ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2156 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","ɔ","∅","h","ɛ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2157 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","ɔ","∅","h","e"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2158 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","ɔ","∅","h","ɪ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2159 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","ɔ","∅","h","i"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2160 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","ɔ","∅","h","ɔ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2161 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","ɔ","∅","h","o"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2162 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","ɔ","∅","h","ʊ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2163 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","ɔ","∅","h","u"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2164 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","ɔ","∅","h","j"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2165 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","ɔ","∅","h","w"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2152 : check uG34b (2) (0) outG34b ["a","f","ɔ","s","ɔ","∅","h"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG34b_1_2153
  · exact partG34b_1_2154
  · exact partG34b_1_2155
  · exact partG34b_1_2156
  · exact partG34b_1_2157
  · exact partG34b_1_2158
  · exact partG34b_1_2159
  · exact partG34b_1_2160
  · exact partG34b_1_2161
  · exact partG34b_1_2162
  · exact partG34b_1_2163
  · exact partG34b_1_2164
  · exact partG34b_1_2165
end ProductiveSubjectGua
