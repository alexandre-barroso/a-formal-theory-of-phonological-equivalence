import PhonologicalOpacity.Attenuation.Productive.Subject.CertificateParts.OR38_1_010
namespace ProductiveSubjectGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partOR38_1_885 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","∅","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_886 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","∅","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_887 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","∅","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_888 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","∅","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_889 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","∅","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_876 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_877
  · exact partOR38_1_878
  · exact partOR38_1_879
  · exact partOR38_1_880
  · exact partOR38_1_881
  · exact partOR38_1_882
  · exact partOR38_1_883
  · exact partOR38_1_884
  · exact partOR38_1_885
  · exact partOR38_1_886
  · exact partOR38_1_887
  · exact partOR38_1_888
  · exact partOR38_1_889
theorem partOR38_1_891 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","a","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_892 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","a","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_893 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","a","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_894 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","a","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_895 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","a","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_896 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","a","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_897 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","a","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_898 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","a","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_899 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","a","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_900 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","a","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_901 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","a","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_902 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","a","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_903 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","a","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_890 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_891
  · exact partOR38_1_892
  · exact partOR38_1_893
  · exact partOR38_1_894
  · exact partOR38_1_895
  · exact partOR38_1_896
  · exact partOR38_1_897
  · exact partOR38_1_898
  · exact partOR38_1_899
  · exact partOR38_1_900
  · exact partOR38_1_901
  · exact partOR38_1_902
  · exact partOR38_1_903
theorem partOR38_1_905 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","ɜ","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_906 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","ɜ","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_907 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","ɜ","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_908 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","ɜ","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_909 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","ɜ","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_910 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","ɜ","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_911 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","ɜ","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_912 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","ɜ","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_913 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","ɜ","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_914 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","ɜ","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_915 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","ɜ","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_916 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","ɜ","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_917 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","ɜ","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_904 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_905
  · exact partOR38_1_906
  · exact partOR38_1_907
  · exact partOR38_1_908
  · exact partOR38_1_909
  · exact partOR38_1_910
  · exact partOR38_1_911
  · exact partOR38_1_912
  · exact partOR38_1_913
  · exact partOR38_1_914
  · exact partOR38_1_915
  · exact partOR38_1_916
  · exact partOR38_1_917
theorem partOR38_1_919 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","ɛ","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_920 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","ɛ","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_921 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","ɛ","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_922 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","ɛ","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_923 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","ɛ","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_924 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","ɛ","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_925 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","ɛ","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_926 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","ɛ","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_927 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","ɛ","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_928 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","ɛ","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_929 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","ɛ","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_930 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","ɛ","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_931 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","ɛ","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_918 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_919
  · exact partOR38_1_920
  · exact partOR38_1_921
  · exact partOR38_1_922
  · exact partOR38_1_923
  · exact partOR38_1_924
  · exact partOR38_1_925
  · exact partOR38_1_926
  · exact partOR38_1_927
  · exact partOR38_1_928
  · exact partOR38_1_929
  · exact partOR38_1_930
  · exact partOR38_1_931
theorem partOR38_1_933 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","e","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_934 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","e","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_935 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","e","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_936 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","e","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_937 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","e","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_938 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","e","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_939 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","e","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_940 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","e","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_941 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","e","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_942 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","e","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_943 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","e","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_944 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","e","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_945 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","e","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_932 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_933
  · exact partOR38_1_934
  · exact partOR38_1_935
  · exact partOR38_1_936
  · exact partOR38_1_937
  · exact partOR38_1_938
  · exact partOR38_1_939
  · exact partOR38_1_940
  · exact partOR38_1_941
  · exact partOR38_1_942
  · exact partOR38_1_943
  · exact partOR38_1_944
  · exact partOR38_1_945
theorem partOR38_1_947 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","ɪ","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_948 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","ɪ","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_949 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","ɪ","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_950 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","ɪ","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_951 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","ɪ","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_952 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","ɪ","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_953 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","ɪ","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_954 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","ɪ","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_955 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","ɪ","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_956 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","ɪ","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_957 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","ɪ","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_958 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","ɪ","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_959 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","ɪ","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_946 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_947
  · exact partOR38_1_948
  · exact partOR38_1_949
  · exact partOR38_1_950
  · exact partOR38_1_951
  · exact partOR38_1_952
  · exact partOR38_1_953
  · exact partOR38_1_954
  · exact partOR38_1_955
  · exact partOR38_1_956
  · exact partOR38_1_957
  · exact partOR38_1_958
  · exact partOR38_1_959
theorem partOR38_1_961 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","i","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_962 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","i","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_963 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","i","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_964 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","i","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
end ProductiveSubjectGua
