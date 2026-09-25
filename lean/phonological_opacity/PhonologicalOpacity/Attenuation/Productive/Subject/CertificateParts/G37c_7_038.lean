import PhonologicalOpacity.Attenuation.Productive.Subject.CertificateParts.G37c_7_037
namespace ProductiveSubjectGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partG37c_7_3047 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","a","∅","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3048 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","a","∅","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3049 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","a","∅","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3050 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","a","∅","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3051 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","a","∅","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3052 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","a","∅","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3053 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","a","∅","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3040 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","a","∅","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_3041
  · exact partG37c_7_3042
  · exact partG37c_7_3043
  · exact partG37c_7_3044
  · exact partG37c_7_3045
  · exact partG37c_7_3046
  · exact partG37c_7_3047
  · exact partG37c_7_3048
  · exact partG37c_7_3049
  · exact partG37c_7_3050
  · exact partG37c_7_3051
  · exact partG37c_7_3052
  · exact partG37c_7_3053
theorem partG37c_7_3039 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","a","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_3040
theorem partG37c_7_3054 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","a","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3055 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","a","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3056 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","a","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3057 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","a","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3058 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","a","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3061 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","a","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3062 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","a","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3063 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","a","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3064 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","a","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3065 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","a","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3066 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","a","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3067 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","a","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3068 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","a","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3069 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","a","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3070 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","a","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3071 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","a","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3072 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","a","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3073 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","a","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3060 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","a","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_3061
  · exact partG37c_7_3062
  · exact partG37c_7_3063
  · exact partG37c_7_3064
  · exact partG37c_7_3065
  · exact partG37c_7_3066
  · exact partG37c_7_3067
  · exact partG37c_7_3068
  · exact partG37c_7_3069
  · exact partG37c_7_3070
  · exact partG37c_7_3071
  · exact partG37c_7_3072
  · exact partG37c_7_3073
theorem partG37c_7_3059 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","a","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_3060
theorem partG37c_7_3074 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","a","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3075 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","a","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3076 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","a","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3077 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","a","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3080 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","a","j","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3081 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","a","j","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3082 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","a","j","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3083 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","a","j","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3084 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","a","j","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3085 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","a","j","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3086 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","a","j","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3087 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","a","j","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3088 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","a","j","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3089 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","a","j","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3090 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","a","j","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3091 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","a","j","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3092 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","a","j","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3079 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","a","j","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_3080
  · exact partG37c_7_3081
  · exact partG37c_7_3082
  · exact partG37c_7_3083
  · exact partG37c_7_3084
  · exact partG37c_7_3085
  · exact partG37c_7_3086
  · exact partG37c_7_3087
  · exact partG37c_7_3088
  · exact partG37c_7_3089
  · exact partG37c_7_3090
  · exact partG37c_7_3091
  · exact partG37c_7_3092
theorem partG37c_7_3078 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","a","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_3079
theorem partG37c_7_3093 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","a","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3038 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_3039
  · exact partG37c_7_3054
  · exact partG37c_7_3055
  · exact partG37c_7_3056
  · exact partG37c_7_3057
  · exact partG37c_7_3058
  · exact partG37c_7_3059
  · exact partG37c_7_3074
  · exact partG37c_7_3075
  · exact partG37c_7_3076
  · exact partG37c_7_3077
  · exact partG37c_7_3078
  · exact partG37c_7_3093
theorem partG37c_7_3097 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɜ","∅","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3098 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɜ","∅","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3099 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɜ","∅","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3100 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɜ","∅","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3101 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɜ","∅","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3102 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɜ","∅","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3103 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɜ","∅","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3104 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɜ","∅","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3105 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɜ","∅","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3106 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɜ","∅","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3107 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɜ","∅","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3108 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɜ","∅","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3109 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɜ","∅","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3096 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɜ","∅","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_3097
  · exact partG37c_7_3098
  · exact partG37c_7_3099
  · exact partG37c_7_3100
  · exact partG37c_7_3101
  · exact partG37c_7_3102
  · exact partG37c_7_3103
  · exact partG37c_7_3104
  · exact partG37c_7_3105
  · exact partG37c_7_3106
  · exact partG37c_7_3107
  · exact partG37c_7_3108
  · exact partG37c_7_3109
theorem partG37c_7_3095 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɜ","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_3096
theorem partG37c_7_3110 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɜ","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3111 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɜ","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3112 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɜ","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3113 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɜ","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3114 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɜ","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3117 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɜ","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3118 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɜ","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3119 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɜ","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3120 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɜ","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3121 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɜ","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3122 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɜ","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3123 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɜ","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3124 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɜ","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3125 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɜ","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3126 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","ɜ","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
end ProductiveSubjectGua
