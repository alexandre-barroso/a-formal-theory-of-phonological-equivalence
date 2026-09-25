import PhonologicalOpacity.Attenuation.Productive.Baseline.CertificateParts.G37c_7_010
namespace ProductiveGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partG37c_7_885 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","i","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_888 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","i","j","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_889 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","i","j","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_890 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","i","j","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_891 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","i","j","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_892 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","i","j","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_893 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","i","j","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_894 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","i","j","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_895 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","i","j","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_896 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","i","j","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_897 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","i","j","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_898 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","i","j","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_899 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","i","j","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_900 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","i","j","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_887 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","i","j","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_888
  · exact partG37c_7_889
  · exact partG37c_7_890
  · exact partG37c_7_891
  · exact partG37c_7_892
  · exact partG37c_7_893
  · exact partG37c_7_894
  · exact partG37c_7_895
  · exact partG37c_7_896
  · exact partG37c_7_897
  · exact partG37c_7_898
  · exact partG37c_7_899
  · exact partG37c_7_900
theorem partG37c_7_886 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","i","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_887
theorem partG37c_7_901 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","i","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_846 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_847
  · exact partG37c_7_862
  · exact partG37c_7_863
  · exact partG37c_7_864
  · exact partG37c_7_865
  · exact partG37c_7_866
  · exact partG37c_7_867
  · exact partG37c_7_882
  · exact partG37c_7_883
  · exact partG37c_7_884
  · exact partG37c_7_885
  · exact partG37c_7_886
  · exact partG37c_7_901
theorem partG37c_7_905 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɔ","∅","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_906 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɔ","∅","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_907 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɔ","∅","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_908 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɔ","∅","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_909 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɔ","∅","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_910 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɔ","∅","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_911 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɔ","∅","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_912 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɔ","∅","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_913 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɔ","∅","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_914 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɔ","∅","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_915 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɔ","∅","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_916 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɔ","∅","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_917 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɔ","∅","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_904 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɔ","∅","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_905
  · exact partG37c_7_906
  · exact partG37c_7_907
  · exact partG37c_7_908
  · exact partG37c_7_909
  · exact partG37c_7_910
  · exact partG37c_7_911
  · exact partG37c_7_912
  · exact partG37c_7_913
  · exact partG37c_7_914
  · exact partG37c_7_915
  · exact partG37c_7_916
  · exact partG37c_7_917
theorem partG37c_7_903 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɔ","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_904
theorem partG37c_7_918 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɔ","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_919 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɔ","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_920 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɔ","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_921 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɔ","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_922 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɔ","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_925 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɔ","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_926 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɔ","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_927 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɔ","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_928 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɔ","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_929 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɔ","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_930 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɔ","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_931 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɔ","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_932 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɔ","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_933 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɔ","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_934 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɔ","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_935 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɔ","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_936 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɔ","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_937 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɔ","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_924 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɔ","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_925
  · exact partG37c_7_926
  · exact partG37c_7_927
  · exact partG37c_7_928
  · exact partG37c_7_929
  · exact partG37c_7_930
  · exact partG37c_7_931
  · exact partG37c_7_932
  · exact partG37c_7_933
  · exact partG37c_7_934
  · exact partG37c_7_935
  · exact partG37c_7_936
  · exact partG37c_7_937
theorem partG37c_7_923 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɔ","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_924
theorem partG37c_7_938 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɔ","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_939 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɔ","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_940 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɔ","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_941 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɔ","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_944 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɔ","j","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_945 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɔ","j","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_946 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɔ","j","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_947 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɔ","j","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_948 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɔ","j","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_949 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɔ","j","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_950 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɔ","j","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_951 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɔ","j","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_952 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɔ","j","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_953 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɔ","j","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_954 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɔ","j","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_955 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɔ","j","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_956 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɔ","j","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_943 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɔ","j","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_944
  · exact partG37c_7_945
  · exact partG37c_7_946
  · exact partG37c_7_947
  · exact partG37c_7_948
  · exact partG37c_7_949
  · exact partG37c_7_950
  · exact partG37c_7_951
  · exact partG37c_7_952
  · exact partG37c_7_953
  · exact partG37c_7_954
  · exact partG37c_7_955
  · exact partG37c_7_956
theorem partG37c_7_942 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɔ","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_943
theorem partG37c_7_957 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɔ","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_902 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_903
  · exact partG37c_7_918
  · exact partG37c_7_919
  · exact partG37c_7_920
  · exact partG37c_7_921
  · exact partG37c_7_922
  · exact partG37c_7_923
  · exact partG37c_7_938
  · exact partG37c_7_939
  · exact partG37c_7_940
  · exact partG37c_7_941
  · exact partG37c_7_942
  · exact partG37c_7_957
theorem partG37c_7_961 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","o","∅","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_962 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","o","∅","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_963 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","o","∅","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_964 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","o","∅","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_965 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","o","∅","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_966 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","o","∅","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
end ProductiveGua
