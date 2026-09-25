import PhonologicalOpacity.Attenuation.Productive.Subject.CertificateParts.G37c_7_011
namespace ProductiveSubjectGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partG37c_7_967 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","o","∅","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_968 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","o","∅","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_969 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","o","∅","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_970 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","o","∅","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_971 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","o","∅","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_972 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","o","∅","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_973 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","o","∅","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_960 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","o","∅","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_961
  · exact partG37c_7_962
  · exact partG37c_7_963
  · exact partG37c_7_964
  · exact partG37c_7_965
  · exact partG37c_7_966
  · exact partG37c_7_967
  · exact partG37c_7_968
  · exact partG37c_7_969
  · exact partG37c_7_970
  · exact partG37c_7_971
  · exact partG37c_7_972
  · exact partG37c_7_973
theorem partG37c_7_959 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","o","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_960
theorem partG37c_7_974 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","o","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_975 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","o","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_976 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","o","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_977 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","o","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_978 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","o","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_981 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","o","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_982 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","o","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_983 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","o","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_984 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","o","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_985 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","o","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_986 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","o","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_987 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","o","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_988 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","o","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_989 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","o","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_990 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","o","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_991 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","o","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_992 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","o","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_993 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","o","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_980 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","o","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_981
  · exact partG37c_7_982
  · exact partG37c_7_983
  · exact partG37c_7_984
  · exact partG37c_7_985
  · exact partG37c_7_986
  · exact partG37c_7_987
  · exact partG37c_7_988
  · exact partG37c_7_989
  · exact partG37c_7_990
  · exact partG37c_7_991
  · exact partG37c_7_992
  · exact partG37c_7_993
theorem partG37c_7_979 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","o","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_980
theorem partG37c_7_994 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","o","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_995 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","o","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_996 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","o","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_997 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","o","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1000 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","o","j","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1001 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","o","j","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1002 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","o","j","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1003 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","o","j","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1004 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","o","j","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1005 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","o","j","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1006 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","o","j","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1007 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","o","j","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1008 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","o","j","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1009 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","o","j","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1010 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","o","j","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1011 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","o","j","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1012 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","o","j","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_999 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","o","j","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_1000
  · exact partG37c_7_1001
  · exact partG37c_7_1002
  · exact partG37c_7_1003
  · exact partG37c_7_1004
  · exact partG37c_7_1005
  · exact partG37c_7_1006
  · exact partG37c_7_1007
  · exact partG37c_7_1008
  · exact partG37c_7_1009
  · exact partG37c_7_1010
  · exact partG37c_7_1011
  · exact partG37c_7_1012
theorem partG37c_7_998 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","o","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_999
theorem partG37c_7_1013 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","o","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_958 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_959
  · exact partG37c_7_974
  · exact partG37c_7_975
  · exact partG37c_7_976
  · exact partG37c_7_977
  · exact partG37c_7_978
  · exact partG37c_7_979
  · exact partG37c_7_994
  · exact partG37c_7_995
  · exact partG37c_7_996
  · exact partG37c_7_997
  · exact partG37c_7_998
  · exact partG37c_7_1013
theorem partG37c_7_1017 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ʊ","∅","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1018 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ʊ","∅","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1019 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ʊ","∅","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1020 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ʊ","∅","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1021 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ʊ","∅","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1022 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ʊ","∅","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1023 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ʊ","∅","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1024 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ʊ","∅","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1025 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ʊ","∅","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1026 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ʊ","∅","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1027 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ʊ","∅","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1028 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ʊ","∅","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1029 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ʊ","∅","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1016 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ʊ","∅","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_1017
  · exact partG37c_7_1018
  · exact partG37c_7_1019
  · exact partG37c_7_1020
  · exact partG37c_7_1021
  · exact partG37c_7_1022
  · exact partG37c_7_1023
  · exact partG37c_7_1024
  · exact partG37c_7_1025
  · exact partG37c_7_1026
  · exact partG37c_7_1027
  · exact partG37c_7_1028
  · exact partG37c_7_1029
theorem partG37c_7_1015 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ʊ","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_1016
theorem partG37c_7_1030 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ʊ","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1031 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ʊ","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1032 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ʊ","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1033 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ʊ","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1034 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ʊ","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1037 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ʊ","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1038 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ʊ","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1039 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ʊ","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1040 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ʊ","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1041 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ʊ","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1042 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ʊ","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1043 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ʊ","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1044 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ʊ","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1045 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ʊ","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_1046 : check uG37c (3) (0) outG37c ["ɔ","tʃ","a","s","ʊ","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
end ProductiveSubjectGua
