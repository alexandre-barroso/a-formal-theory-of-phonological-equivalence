import PhonologicalOpacity.Attenuation.Productive.Baseline.CertificateParts.G37c_0_035
namespace ProductiveGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partG37c_0_2885 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","ɜ","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2886 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","ɜ","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2887 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","ɜ","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2888 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","ɜ","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2889 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","ɜ","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2862 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_0_2863
  · exact partG37c_0_2864
  · exact partG37c_0_2865
  · exact partG37c_0_2866
  · exact partG37c_0_2867
  · exact partG37c_0_2868
  · exact partG37c_0_2869
  · exact partG37c_0_2884
  · exact partG37c_0_2885
  · exact partG37c_0_2886
  · exact partG37c_0_2887
  · exact partG37c_0_2888
  · exact partG37c_0_2889
theorem partG37c_0_2893 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","ɛ","∅","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2894 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","ɛ","∅","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2895 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","ɛ","∅","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2896 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","ɛ","∅","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2897 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","ɛ","∅","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2898 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","ɛ","∅","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2899 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","ɛ","∅","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2900 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","ɛ","∅","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2901 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","ɛ","∅","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2902 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","ɛ","∅","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2903 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","ɛ","∅","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2904 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","ɛ","∅","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2905 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","ɛ","∅","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2892 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","ɛ","∅","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_0_2893
  · exact partG37c_0_2894
  · exact partG37c_0_2895
  · exact partG37c_0_2896
  · exact partG37c_0_2897
  · exact partG37c_0_2898
  · exact partG37c_0_2899
  · exact partG37c_0_2900
  · exact partG37c_0_2901
  · exact partG37c_0_2902
  · exact partG37c_0_2903
  · exact partG37c_0_2904
  · exact partG37c_0_2905
theorem partG37c_0_2891 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","ɛ","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_0_2892
theorem partG37c_0_2906 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","ɛ","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2907 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","ɛ","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2908 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","ɛ","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2909 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","ɛ","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2910 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","ɛ","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2913 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","ɛ","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2914 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","ɛ","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2915 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","ɛ","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2916 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","ɛ","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2917 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","ɛ","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2918 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","ɛ","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2919 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","ɛ","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2920 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","ɛ","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2921 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","ɛ","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2922 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","ɛ","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2923 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","ɛ","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2924 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","ɛ","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2925 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","ɛ","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2912 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","ɛ","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_0_2913
  · exact partG37c_0_2914
  · exact partG37c_0_2915
  · exact partG37c_0_2916
  · exact partG37c_0_2917
  · exact partG37c_0_2918
  · exact partG37c_0_2919
  · exact partG37c_0_2920
  · exact partG37c_0_2921
  · exact partG37c_0_2922
  · exact partG37c_0_2923
  · exact partG37c_0_2924
  · exact partG37c_0_2925
theorem partG37c_0_2911 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","ɛ","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_0_2912
theorem partG37c_0_2926 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","ɛ","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2927 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","ɛ","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2928 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","ɛ","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2929 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","ɛ","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2932 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","ɛ","j","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2933 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","ɛ","j","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2934 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","ɛ","j","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2935 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","ɛ","j","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2936 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","ɛ","j","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2937 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","ɛ","j","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2938 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","ɛ","j","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2939 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","ɛ","j","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2940 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","ɛ","j","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2941 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","ɛ","j","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2942 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","ɛ","j","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2943 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","ɛ","j","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2944 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","ɛ","j","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2931 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","ɛ","j","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_0_2932
  · exact partG37c_0_2933
  · exact partG37c_0_2934
  · exact partG37c_0_2935
  · exact partG37c_0_2936
  · exact partG37c_0_2937
  · exact partG37c_0_2938
  · exact partG37c_0_2939
  · exact partG37c_0_2940
  · exact partG37c_0_2941
  · exact partG37c_0_2942
  · exact partG37c_0_2943
  · exact partG37c_0_2944
theorem partG37c_0_2930 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","ɛ","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_0_2931
theorem partG37c_0_2945 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","ɛ","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2890 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_0_2891
  · exact partG37c_0_2906
  · exact partG37c_0_2907
  · exact partG37c_0_2908
  · exact partG37c_0_2909
  · exact partG37c_0_2910
  · exact partG37c_0_2911
  · exact partG37c_0_2926
  · exact partG37c_0_2927
  · exact partG37c_0_2928
  · exact partG37c_0_2929
  · exact partG37c_0_2930
  · exact partG37c_0_2945
theorem partG37c_0_2947 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","e","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2948 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","e","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2949 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","e","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2950 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","e","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2951 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","e","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2952 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","e","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2955 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","e","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2956 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","e","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2957 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","e","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2958 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","e","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2959 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","e","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2960 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","e","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2961 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","e","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2962 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","e","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2963 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","e","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2964 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","e","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2965 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","e","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_0_2966 : check uG37c (3) (0) outG37c ["∅","tʃ","ʊ","s","e","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
end ProductiveGua
