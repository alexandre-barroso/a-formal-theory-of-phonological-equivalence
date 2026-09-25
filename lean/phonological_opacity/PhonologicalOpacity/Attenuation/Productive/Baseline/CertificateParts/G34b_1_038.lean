import PhonologicalOpacity.Attenuation.Productive.Baseline.CertificateParts.G34b_1_037
namespace ProductiveGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partG34b_1_3031 : check uG34b (2) (0) outG34b ["a","f","u","s","ɔ","o"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="h" := by simpa using hx
  subst x
  exact partG34b_1_3032
theorem partG34b_1_3046 : check uG34b (2) (0) outG34b ["a","f","u","s","ɔ","ʊ"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_3047 : check uG34b (2) (0) outG34b ["a","f","u","s","ɔ","u"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_3048 : check uG34b (2) (0) outG34b ["a","f","u","s","ɔ","j"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_3049 : check uG34b (2) (0) outG34b ["a","f","u","s","ɔ","w"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_3022 : check uG34b (2) (0) outG34b ["a","f","u","s","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG34b_1_3023
  · exact partG34b_1_3024
  · exact partG34b_1_3025
  · exact partG34b_1_3026
  · exact partG34b_1_3027
  · exact partG34b_1_3028
  · exact partG34b_1_3029
  · exact partG34b_1_3030
  · exact partG34b_1_3031
  · exact partG34b_1_3046
  · exact partG34b_1_3047
  · exact partG34b_1_3048
  · exact partG34b_1_3049
theorem partG34b_1_3050 : check uG34b (2) (0) outG34b ["a","f","u","s","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_3052 : check uG34b (2) (0) outG34b ["a","f","u","s","ʊ","∅"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_3053 : check uG34b (2) (0) outG34b ["a","f","u","s","ʊ","a"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_3054 : check uG34b (2) (0) outG34b ["a","f","u","s","ʊ","ɜ"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_3055 : check uG34b (2) (0) outG34b ["a","f","u","s","ʊ","ɛ"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_3056 : check uG34b (2) (0) outG34b ["a","f","u","s","ʊ","e"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_3057 : check uG34b (2) (0) outG34b ["a","f","u","s","ʊ","ɪ"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_3058 : check uG34b (2) (0) outG34b ["a","f","u","s","ʊ","i"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_3059 : check uG34b (2) (0) outG34b ["a","f","u","s","ʊ","ɔ"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_3062 : check uG34b (2) (0) outG34b ["a","f","u","s","ʊ","o","h","∅"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_3063 : check uG34b (2) (0) outG34b ["a","f","u","s","ʊ","o","h","a"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_3064 : check uG34b (2) (0) outG34b ["a","f","u","s","ʊ","o","h","ɜ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_3065 : check uG34b (2) (0) outG34b ["a","f","u","s","ʊ","o","h","ɛ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_3066 : check uG34b (2) (0) outG34b ["a","f","u","s","ʊ","o","h","e"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_3067 : check uG34b (2) (0) outG34b ["a","f","u","s","ʊ","o","h","ɪ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_3068 : check uG34b (2) (0) outG34b ["a","f","u","s","ʊ","o","h","i"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_3069 : check uG34b (2) (0) outG34b ["a","f","u","s","ʊ","o","h","ɔ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_3070 : check uG34b (2) (0) outG34b ["a","f","u","s","ʊ","o","h","o"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_3071 : check uG34b (2) (0) outG34b ["a","f","u","s","ʊ","o","h","ʊ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_3072 : check uG34b (2) (0) outG34b ["a","f","u","s","ʊ","o","h","u"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_3073 : check uG34b (2) (0) outG34b ["a","f","u","s","ʊ","o","h","j"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_3074 : check uG34b (2) (0) outG34b ["a","f","u","s","ʊ","o","h","w"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_3061 : check uG34b (2) (0) outG34b ["a","f","u","s","ʊ","o","h"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG34b_1_3062
  · exact partG34b_1_3063
  · exact partG34b_1_3064
  · exact partG34b_1_3065
  · exact partG34b_1_3066
  · exact partG34b_1_3067
  · exact partG34b_1_3068
  · exact partG34b_1_3069
  · exact partG34b_1_3070
  · exact partG34b_1_3071
  · exact partG34b_1_3072
  · exact partG34b_1_3073
  · exact partG34b_1_3074
theorem partG34b_1_3060 : check uG34b (2) (0) outG34b ["a","f","u","s","ʊ","o"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="h" := by simpa using hx
  subst x
  exact partG34b_1_3061
theorem partG34b_1_3075 : check uG34b (2) (0) outG34b ["a","f","u","s","ʊ","ʊ"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_3076 : check uG34b (2) (0) outG34b ["a","f","u","s","ʊ","u"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_3077 : check uG34b (2) (0) outG34b ["a","f","u","s","ʊ","j"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_3078 : check uG34b (2) (0) outG34b ["a","f","u","s","ʊ","w"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_3051 : check uG34b (2) (0) outG34b ["a","f","u","s","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG34b_1_3052
  · exact partG34b_1_3053
  · exact partG34b_1_3054
  · exact partG34b_1_3055
  · exact partG34b_1_3056
  · exact partG34b_1_3057
  · exact partG34b_1_3058
  · exact partG34b_1_3059
  · exact partG34b_1_3060
  · exact partG34b_1_3075
  · exact partG34b_1_3076
  · exact partG34b_1_3077
  · exact partG34b_1_3078
theorem partG34b_1_3079 : check uG34b (2) (0) outG34b ["a","f","u","s","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_3080 : check uG34b (2) (0) outG34b ["a","f","u","s","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_3081 : check uG34b (2) (0) outG34b ["a","f","u","s","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_2933 : check uG34b (2) (0) outG34b ["a","f","u","s"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG34b_1_2934
  · exact partG34b_1_2935
  · exact partG34b_1_2963
  · exact partG34b_1_2964
  · exact partG34b_1_2992
  · exact partG34b_1_2993
  · exact partG34b_1_3021
  · exact partG34b_1_3022
  · exact partG34b_1_3050
  · exact partG34b_1_3051
  · exact partG34b_1_3079
  · exact partG34b_1_3080
  · exact partG34b_1_3081
theorem partG34b_1_2932 : check uG34b (2) (0) outG34b ["a","f","u"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="s" := by simpa using hx
  subst x
  exact partG34b_1_2933
theorem partG34b_1_3084 : check uG34b (2) (0) outG34b ["a","f","j","s","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_3086 : check uG34b (2) (0) outG34b ["a","f","j","s","a","∅"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_3087 : check uG34b (2) (0) outG34b ["a","f","j","s","a","a"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_3088 : check uG34b (2) (0) outG34b ["a","f","j","s","a","ɜ"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_3089 : check uG34b (2) (0) outG34b ["a","f","j","s","a","ɛ"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_3090 : check uG34b (2) (0) outG34b ["a","f","j","s","a","e"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_3091 : check uG34b (2) (0) outG34b ["a","f","j","s","a","ɪ"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_3092 : check uG34b (2) (0) outG34b ["a","f","j","s","a","i"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_3093 : check uG34b (2) (0) outG34b ["a","f","j","s","a","ɔ"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_3096 : check uG34b (2) (0) outG34b ["a","f","j","s","a","o","h","∅"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_3097 : check uG34b (2) (0) outG34b ["a","f","j","s","a","o","h","a"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_3098 : check uG34b (2) (0) outG34b ["a","f","j","s","a","o","h","ɜ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_3099 : check uG34b (2) (0) outG34b ["a","f","j","s","a","o","h","ɛ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_3100 : check uG34b (2) (0) outG34b ["a","f","j","s","a","o","h","e"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_3101 : check uG34b (2) (0) outG34b ["a","f","j","s","a","o","h","ɪ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_3102 : check uG34b (2) (0) outG34b ["a","f","j","s","a","o","h","i"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_3103 : check uG34b (2) (0) outG34b ["a","f","j","s","a","o","h","ɔ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_3104 : check uG34b (2) (0) outG34b ["a","f","j","s","a","o","h","o"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_3105 : check uG34b (2) (0) outG34b ["a","f","j","s","a","o","h","ʊ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_3106 : check uG34b (2) (0) outG34b ["a","f","j","s","a","o","h","u"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_3107 : check uG34b (2) (0) outG34b ["a","f","j","s","a","o","h","j"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_3108 : check uG34b (2) (0) outG34b ["a","f","j","s","a","o","h","w"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_3095 : check uG34b (2) (0) outG34b ["a","f","j","s","a","o","h"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG34b_1_3096
  · exact partG34b_1_3097
  · exact partG34b_1_3098
  · exact partG34b_1_3099
  · exact partG34b_1_3100
  · exact partG34b_1_3101
  · exact partG34b_1_3102
  · exact partG34b_1_3103
  · exact partG34b_1_3104
  · exact partG34b_1_3105
  · exact partG34b_1_3106
  · exact partG34b_1_3107
  · exact partG34b_1_3108
theorem partG34b_1_3094 : check uG34b (2) (0) outG34b ["a","f","j","s","a","o"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="h" := by simpa using hx
  subst x
  exact partG34b_1_3095
theorem partG34b_1_3109 : check uG34b (2) (0) outG34b ["a","f","j","s","a","ʊ"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_3110 : check uG34b (2) (0) outG34b ["a","f","j","s","a","u"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_3111 : check uG34b (2) (0) outG34b ["a","f","j","s","a","j"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_3112 : check uG34b (2) (0) outG34b ["a","f","j","s","a","w"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_3085 : check uG34b (2) (0) outG34b ["a","f","j","s","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG34b_1_3086
  · exact partG34b_1_3087
  · exact partG34b_1_3088
  · exact partG34b_1_3089
  · exact partG34b_1_3090
  · exact partG34b_1_3091
  · exact partG34b_1_3092
  · exact partG34b_1_3093
  · exact partG34b_1_3094
  · exact partG34b_1_3109
  · exact partG34b_1_3110
  · exact partG34b_1_3111
  · exact partG34b_1_3112
theorem partG34b_1_3113 : check uG34b (2) (0) outG34b ["a","f","j","s","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_3115 : check uG34b (2) (0) outG34b ["a","f","j","s","ɛ","∅"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_3116 : check uG34b (2) (0) outG34b ["a","f","j","s","ɛ","a"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_3117 : check uG34b (2) (0) outG34b ["a","f","j","s","ɛ","ɜ"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_3118 : check uG34b (2) (0) outG34b ["a","f","j","s","ɛ","ɛ"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_3119 : check uG34b (2) (0) outG34b ["a","f","j","s","ɛ","e"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_3120 : check uG34b (2) (0) outG34b ["a","f","j","s","ɛ","ɪ"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_3121 : check uG34b (2) (0) outG34b ["a","f","j","s","ɛ","i"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_3122 : check uG34b (2) (0) outG34b ["a","f","j","s","ɛ","ɔ"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_3125 : check uG34b (2) (0) outG34b ["a","f","j","s","ɛ","o","h","∅"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_3126 : check uG34b (2) (0) outG34b ["a","f","j","s","ɛ","o","h","a"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
end ProductiveGua
