import PhonologicalOpacity.Attenuation.Productive.Subject.CertificateParts.G37c_7_036
namespace ProductiveSubjectGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partG37c_7_2967 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","w","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2968 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","w","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2969 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","w","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2970 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","w","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2971 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","w","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2972 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","w","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2973 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","w","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2960 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","w","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_2961
  · exact partG37c_7_2962
  · exact partG37c_7_2963
  · exact partG37c_7_2964
  · exact partG37c_7_2965
  · exact partG37c_7_2966
  · exact partG37c_7_2967
  · exact partG37c_7_2968
  · exact partG37c_7_2969
  · exact partG37c_7_2970
  · exact partG37c_7_2971
  · exact partG37c_7_2972
  · exact partG37c_7_2973
theorem partG37c_7_2959 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","w","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_2960
theorem partG37c_7_2974 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","w","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2975 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","w","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2976 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","w","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2977 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","w","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2978 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","w","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2979 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","w","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2952 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_2953
  · exact partG37c_7_2954
  · exact partG37c_7_2955
  · exact partG37c_7_2956
  · exact partG37c_7_2957
  · exact partG37c_7_2958
  · exact partG37c_7_2959
  · exact partG37c_7_2974
  · exact partG37c_7_2975
  · exact partG37c_7_2976
  · exact partG37c_7_2977
  · exact partG37c_7_2978
  · exact partG37c_7_2979
theorem partG37c_7_2475 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_2476
  · exact partG37c_7_2504
  · exact partG37c_7_2560
  · exact partG37c_7_2588
  · exact partG37c_7_2644
  · exact partG37c_7_2672
  · exact partG37c_7_2728
  · exact partG37c_7_2756
  · exact partG37c_7_2812
  · exact partG37c_7_2840
  · exact partG37c_7_2896
  · exact partG37c_7_2924
  · exact partG37c_7_2952
theorem partG37c_7_2474 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="s" := by simpa using hx
  subst x
  exact partG37c_7_2475
theorem partG37c_7_2985 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","∅","∅","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2986 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","∅","∅","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2987 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","∅","∅","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2988 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","∅","∅","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2989 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","∅","∅","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2990 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","∅","∅","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2991 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","∅","∅","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2992 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","∅","∅","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2993 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","∅","∅","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2994 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","∅","∅","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2995 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","∅","∅","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2996 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","∅","∅","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2997 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","∅","∅","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2984 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","∅","∅","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_2985
  · exact partG37c_7_2986
  · exact partG37c_7_2987
  · exact partG37c_7_2988
  · exact partG37c_7_2989
  · exact partG37c_7_2990
  · exact partG37c_7_2991
  · exact partG37c_7_2992
  · exact partG37c_7_2993
  · exact partG37c_7_2994
  · exact partG37c_7_2995
  · exact partG37c_7_2996
  · exact partG37c_7_2997
theorem partG37c_7_2983 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","∅","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_2984
theorem partG37c_7_2998 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","∅","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2999 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","∅","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3000 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","∅","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3001 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","∅","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3002 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","∅","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3005 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","∅","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3006 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","∅","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3007 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","∅","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3008 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","∅","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3009 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","∅","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3010 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","∅","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3011 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","∅","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3012 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","∅","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3013 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","∅","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3014 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","∅","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3015 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","∅","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3016 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","∅","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3017 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","∅","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3004 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","∅","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_3005
  · exact partG37c_7_3006
  · exact partG37c_7_3007
  · exact partG37c_7_3008
  · exact partG37c_7_3009
  · exact partG37c_7_3010
  · exact partG37c_7_3011
  · exact partG37c_7_3012
  · exact partG37c_7_3013
  · exact partG37c_7_3014
  · exact partG37c_7_3015
  · exact partG37c_7_3016
  · exact partG37c_7_3017
theorem partG37c_7_3003 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","∅","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_3004
theorem partG37c_7_3018 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","∅","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3019 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","∅","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3020 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","∅","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3021 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","∅","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3024 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","∅","j","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3025 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","∅","j","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3026 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","∅","j","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3027 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","∅","j","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3028 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","∅","j","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3029 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","∅","j","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3030 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","∅","j","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3031 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","∅","j","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3032 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","∅","j","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3033 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","∅","j","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3034 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","∅","j","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3035 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","∅","j","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3036 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","∅","j","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3023 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","∅","j","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_3024
  · exact partG37c_7_3025
  · exact partG37c_7_3026
  · exact partG37c_7_3027
  · exact partG37c_7_3028
  · exact partG37c_7_3029
  · exact partG37c_7_3030
  · exact partG37c_7_3031
  · exact partG37c_7_3032
  · exact partG37c_7_3033
  · exact partG37c_7_3034
  · exact partG37c_7_3035
  · exact partG37c_7_3036
theorem partG37c_7_3022 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","∅","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_3023
theorem partG37c_7_3037 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","∅","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2982 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_2983
  · exact partG37c_7_2998
  · exact partG37c_7_2999
  · exact partG37c_7_3000
  · exact partG37c_7_3001
  · exact partG37c_7_3002
  · exact partG37c_7_3003
  · exact partG37c_7_3018
  · exact partG37c_7_3019
  · exact partG37c_7_3020
  · exact partG37c_7_3021
  · exact partG37c_7_3022
  · exact partG37c_7_3037
theorem partG37c_7_3041 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","a","∅","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3042 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","a","∅","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3043 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","a","∅","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3044 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","a","∅","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3045 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","a","∅","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_3046 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ɪ","s","a","∅","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
end ProductiveSubjectGua
