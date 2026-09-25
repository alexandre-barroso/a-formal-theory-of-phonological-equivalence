import PhonologicalOpacity.Attenuation.Productive.Subject.CertificateParts.G37c_7_035
namespace ProductiveSubjectGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partG37c_7_2887 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ʊ","j","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2888 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ʊ","j","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2889 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ʊ","j","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2890 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ʊ","j","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2891 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ʊ","j","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2892 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ʊ","j","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2893 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ʊ","j","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2894 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ʊ","j","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2881 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ʊ","j","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_2882
  · exact partG37c_7_2883
  · exact partG37c_7_2884
  · exact partG37c_7_2885
  · exact partG37c_7_2886
  · exact partG37c_7_2887
  · exact partG37c_7_2888
  · exact partG37c_7_2889
  · exact partG37c_7_2890
  · exact partG37c_7_2891
  · exact partG37c_7_2892
  · exact partG37c_7_2893
  · exact partG37c_7_2894
theorem partG37c_7_2880 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ʊ","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_2881
theorem partG37c_7_2895 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ʊ","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2840 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_2841
  · exact partG37c_7_2856
  · exact partG37c_7_2857
  · exact partG37c_7_2858
  · exact partG37c_7_2859
  · exact partG37c_7_2860
  · exact partG37c_7_2861
  · exact partG37c_7_2876
  · exact partG37c_7_2877
  · exact partG37c_7_2878
  · exact partG37c_7_2879
  · exact partG37c_7_2880
  · exact partG37c_7_2895
theorem partG37c_7_2897 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","u","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2898 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","u","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2899 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","u","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2900 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","u","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2901 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","u","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2902 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","u","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2905 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","u","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2906 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","u","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2907 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","u","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2908 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","u","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2909 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","u","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2910 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","u","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2911 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","u","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2912 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","u","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2913 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","u","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2914 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","u","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2915 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","u","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2916 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","u","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2917 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","u","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2904 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","u","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_2905
  · exact partG37c_7_2906
  · exact partG37c_7_2907
  · exact partG37c_7_2908
  · exact partG37c_7_2909
  · exact partG37c_7_2910
  · exact partG37c_7_2911
  · exact partG37c_7_2912
  · exact partG37c_7_2913
  · exact partG37c_7_2914
  · exact partG37c_7_2915
  · exact partG37c_7_2916
  · exact partG37c_7_2917
theorem partG37c_7_2903 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","u","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_2904
theorem partG37c_7_2918 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","u","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2919 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","u","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2920 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","u","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2921 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","u","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2922 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","u","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2923 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","u","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2896 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_2897
  · exact partG37c_7_2898
  · exact partG37c_7_2899
  · exact partG37c_7_2900
  · exact partG37c_7_2901
  · exact partG37c_7_2902
  · exact partG37c_7_2903
  · exact partG37c_7_2918
  · exact partG37c_7_2919
  · exact partG37c_7_2920
  · exact partG37c_7_2921
  · exact partG37c_7_2922
  · exact partG37c_7_2923
theorem partG37c_7_2925 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","j","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2926 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","j","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2927 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","j","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2928 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","j","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2929 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","j","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2930 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","j","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2933 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","j","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2934 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","j","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2935 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","j","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2936 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","j","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2937 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","j","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2938 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","j","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2939 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","j","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2940 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","j","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2941 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","j","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2942 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","j","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2943 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","j","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2944 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","j","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2945 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","j","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2932 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","j","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_2933
  · exact partG37c_7_2934
  · exact partG37c_7_2935
  · exact partG37c_7_2936
  · exact partG37c_7_2937
  · exact partG37c_7_2938
  · exact partG37c_7_2939
  · exact partG37c_7_2940
  · exact partG37c_7_2941
  · exact partG37c_7_2942
  · exact partG37c_7_2943
  · exact partG37c_7_2944
  · exact partG37c_7_2945
theorem partG37c_7_2931 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","j","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_2932
theorem partG37c_7_2946 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","j","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2947 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","j","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2948 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","j","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2949 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","j","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2950 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","j","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2951 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","j","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2924 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_2925
  · exact partG37c_7_2926
  · exact partG37c_7_2927
  · exact partG37c_7_2928
  · exact partG37c_7_2929
  · exact partG37c_7_2930
  · exact partG37c_7_2931
  · exact partG37c_7_2946
  · exact partG37c_7_2947
  · exact partG37c_7_2948
  · exact partG37c_7_2949
  · exact partG37c_7_2950
  · exact partG37c_7_2951
theorem partG37c_7_2953 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","w","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2954 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","w","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2955 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","w","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2956 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","w","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2957 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","w","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2958 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","w","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2961 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","w","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2962 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","w","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2963 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","w","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2964 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","w","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2965 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","w","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2966 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","w","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
end ProductiveSubjectGua
