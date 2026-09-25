import PhonologicalOpacity.Attenuation.Productive.Subject.CertificateParts.G34b_1_011
namespace ProductiveSubjectGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partG34b_1_967 : check uG34b (2) (0) outG34b ["a","f","ɛ","s","i","o","h","i"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_968 : check uG34b (2) (0) outG34b ["a","f","ɛ","s","i","o","h","ɔ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_969 : check uG34b (2) (0) outG34b ["a","f","ɛ","s","i","o","h","o"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_970 : check uG34b (2) (0) outG34b ["a","f","ɛ","s","i","o","h","ʊ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_971 : check uG34b (2) (0) outG34b ["a","f","ɛ","s","i","o","h","u"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_972 : check uG34b (2) (0) outG34b ["a","f","ɛ","s","i","o","h","j"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_973 : check uG34b (2) (0) outG34b ["a","f","ɛ","s","i","o","h","w"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_960 : check uG34b (2) (0) outG34b ["a","f","ɛ","s","i","o","h"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG34b_1_961
  · exact partG34b_1_962
  · exact partG34b_1_963
  · exact partG34b_1_964
  · exact partG34b_1_965
  · exact partG34b_1_966
  · exact partG34b_1_967
  · exact partG34b_1_968
  · exact partG34b_1_969
  · exact partG34b_1_970
  · exact partG34b_1_971
  · exact partG34b_1_972
  · exact partG34b_1_973
theorem partG34b_1_959 : check uG34b (2) (0) outG34b ["a","f","ɛ","s","i","o"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="h" := by simpa using hx
  subst x
  exact partG34b_1_960
theorem partG34b_1_974 : check uG34b (2) (0) outG34b ["a","f","ɛ","s","i","ʊ"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_975 : check uG34b (2) (0) outG34b ["a","f","ɛ","s","i","u"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_976 : check uG34b (2) (0) outG34b ["a","f","ɛ","s","i","j"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_977 : check uG34b (2) (0) outG34b ["a","f","ɛ","s","i","w"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_950 : check uG34b (2) (0) outG34b ["a","f","ɛ","s","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG34b_1_951
  · exact partG34b_1_952
  · exact partG34b_1_953
  · exact partG34b_1_954
  · exact partG34b_1_955
  · exact partG34b_1_956
  · exact partG34b_1_957
  · exact partG34b_1_958
  · exact partG34b_1_959
  · exact partG34b_1_974
  · exact partG34b_1_975
  · exact partG34b_1_976
  · exact partG34b_1_977
theorem partG34b_1_981 : check uG34b (2) (0) outG34b ["a","f","ɛ","s","ɔ","∅","h","∅"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_982 : check uG34b (2) (0) outG34b ["a","f","ɛ","s","ɔ","∅","h","a"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_983 : check uG34b (2) (0) outG34b ["a","f","ɛ","s","ɔ","∅","h","ɜ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_984 : check uG34b (2) (0) outG34b ["a","f","ɛ","s","ɔ","∅","h","ɛ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_985 : check uG34b (2) (0) outG34b ["a","f","ɛ","s","ɔ","∅","h","e"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_986 : check uG34b (2) (0) outG34b ["a","f","ɛ","s","ɔ","∅","h","ɪ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_987 : check uG34b (2) (0) outG34b ["a","f","ɛ","s","ɔ","∅","h","i"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_988 : check uG34b (2) (0) outG34b ["a","f","ɛ","s","ɔ","∅","h","ɔ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_989 : check uG34b (2) (0) outG34b ["a","f","ɛ","s","ɔ","∅","h","o"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_990 : check uG34b (2) (0) outG34b ["a","f","ɛ","s","ɔ","∅","h","ʊ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_991 : check uG34b (2) (0) outG34b ["a","f","ɛ","s","ɔ","∅","h","u"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_992 : check uG34b (2) (0) outG34b ["a","f","ɛ","s","ɔ","∅","h","j"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_993 : check uG34b (2) (0) outG34b ["a","f","ɛ","s","ɔ","∅","h","w"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_980 : check uG34b (2) (0) outG34b ["a","f","ɛ","s","ɔ","∅","h"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG34b_1_981
  · exact partG34b_1_982
  · exact partG34b_1_983
  · exact partG34b_1_984
  · exact partG34b_1_985
  · exact partG34b_1_986
  · exact partG34b_1_987
  · exact partG34b_1_988
  · exact partG34b_1_989
  · exact partG34b_1_990
  · exact partG34b_1_991
  · exact partG34b_1_992
  · exact partG34b_1_993
theorem partG34b_1_979 : check uG34b (2) (0) outG34b ["a","f","ɛ","s","ɔ","∅"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="h" := by simpa using hx
  subst x
  exact partG34b_1_980
theorem partG34b_1_994 : check uG34b (2) (0) outG34b ["a","f","ɛ","s","ɔ","a"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_995 : check uG34b (2) (0) outG34b ["a","f","ɛ","s","ɔ","ɜ"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_996 : check uG34b (2) (0) outG34b ["a","f","ɛ","s","ɔ","ɛ"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_997 : check uG34b (2) (0) outG34b ["a","f","ɛ","s","ɔ","e"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_998 : check uG34b (2) (0) outG34b ["a","f","ɛ","s","ɔ","ɪ"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_999 : check uG34b (2) (0) outG34b ["a","f","ɛ","s","ɔ","i"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1000 : check uG34b (2) (0) outG34b ["a","f","ɛ","s","ɔ","ɔ"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1003 : check uG34b (2) (0) outG34b ["a","f","ɛ","s","ɔ","o","h","∅"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1004 : check uG34b (2) (0) outG34b ["a","f","ɛ","s","ɔ","o","h","a"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1005 : check uG34b (2) (0) outG34b ["a","f","ɛ","s","ɔ","o","h","ɜ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1006 : check uG34b (2) (0) outG34b ["a","f","ɛ","s","ɔ","o","h","ɛ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1007 : check uG34b (2) (0) outG34b ["a","f","ɛ","s","ɔ","o","h","e"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1008 : check uG34b (2) (0) outG34b ["a","f","ɛ","s","ɔ","o","h","ɪ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1009 : check uG34b (2) (0) outG34b ["a","f","ɛ","s","ɔ","o","h","i"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1010 : check uG34b (2) (0) outG34b ["a","f","ɛ","s","ɔ","o","h","ɔ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1011 : check uG34b (2) (0) outG34b ["a","f","ɛ","s","ɔ","o","h","o"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1012 : check uG34b (2) (0) outG34b ["a","f","ɛ","s","ɔ","o","h","ʊ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1013 : check uG34b (2) (0) outG34b ["a","f","ɛ","s","ɔ","o","h","u"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1014 : check uG34b (2) (0) outG34b ["a","f","ɛ","s","ɔ","o","h","j"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1015 : check uG34b (2) (0) outG34b ["a","f","ɛ","s","ɔ","o","h","w"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1002 : check uG34b (2) (0) outG34b ["a","f","ɛ","s","ɔ","o","h"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG34b_1_1003
  · exact partG34b_1_1004
  · exact partG34b_1_1005
  · exact partG34b_1_1006
  · exact partG34b_1_1007
  · exact partG34b_1_1008
  · exact partG34b_1_1009
  · exact partG34b_1_1010
  · exact partG34b_1_1011
  · exact partG34b_1_1012
  · exact partG34b_1_1013
  · exact partG34b_1_1014
  · exact partG34b_1_1015
theorem partG34b_1_1001 : check uG34b (2) (0) outG34b ["a","f","ɛ","s","ɔ","o"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="h" := by simpa using hx
  subst x
  exact partG34b_1_1002
theorem partG34b_1_1016 : check uG34b (2) (0) outG34b ["a","f","ɛ","s","ɔ","ʊ"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1017 : check uG34b (2) (0) outG34b ["a","f","ɛ","s","ɔ","u"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1018 : check uG34b (2) (0) outG34b ["a","f","ɛ","s","ɔ","j"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1019 : check uG34b (2) (0) outG34b ["a","f","ɛ","s","ɔ","w"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_978 : check uG34b (2) (0) outG34b ["a","f","ɛ","s","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG34b_1_979
  · exact partG34b_1_994
  · exact partG34b_1_995
  · exact partG34b_1_996
  · exact partG34b_1_997
  · exact partG34b_1_998
  · exact partG34b_1_999
  · exact partG34b_1_1000
  · exact partG34b_1_1001
  · exact partG34b_1_1016
  · exact partG34b_1_1017
  · exact partG34b_1_1018
  · exact partG34b_1_1019
theorem partG34b_1_1021 : check uG34b (2) (0) outG34b ["a","f","ɛ","s","o","∅"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1022 : check uG34b (2) (0) outG34b ["a","f","ɛ","s","o","a"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1023 : check uG34b (2) (0) outG34b ["a","f","ɛ","s","o","ɜ"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1024 : check uG34b (2) (0) outG34b ["a","f","ɛ","s","o","ɛ"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1025 : check uG34b (2) (0) outG34b ["a","f","ɛ","s","o","e"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1026 : check uG34b (2) (0) outG34b ["a","f","ɛ","s","o","ɪ"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1027 : check uG34b (2) (0) outG34b ["a","f","ɛ","s","o","i"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1028 : check uG34b (2) (0) outG34b ["a","f","ɛ","s","o","ɔ"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1031 : check uG34b (2) (0) outG34b ["a","f","ɛ","s","o","o","h","∅"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1032 : check uG34b (2) (0) outG34b ["a","f","ɛ","s","o","o","h","a"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1033 : check uG34b (2) (0) outG34b ["a","f","ɛ","s","o","o","h","ɜ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1034 : check uG34b (2) (0) outG34b ["a","f","ɛ","s","o","o","h","ɛ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1035 : check uG34b (2) (0) outG34b ["a","f","ɛ","s","o","o","h","e"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1036 : check uG34b (2) (0) outG34b ["a","f","ɛ","s","o","o","h","ɪ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1037 : check uG34b (2) (0) outG34b ["a","f","ɛ","s","o","o","h","i"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1038 : check uG34b (2) (0) outG34b ["a","f","ɛ","s","o","o","h","ɔ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1039 : check uG34b (2) (0) outG34b ["a","f","ɛ","s","o","o","h","o"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1040 : check uG34b (2) (0) outG34b ["a","f","ɛ","s","o","o","h","ʊ"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1041 : check uG34b (2) (0) outG34b ["a","f","ɛ","s","o","o","h","u"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1042 : check uG34b (2) (0) outG34b ["a","f","ɛ","s","o","o","h","j"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1043 : check uG34b (2) (0) outG34b ["a","f","ɛ","s","o","o","h","w"] [["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG34b_1_1030 : check uG34b (2) (0) outG34b ["a","f","ɛ","s","o","o","h"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG34b_1_1031
  · exact partG34b_1_1032
  · exact partG34b_1_1033
  · exact partG34b_1_1034
  · exact partG34b_1_1035
  · exact partG34b_1_1036
  · exact partG34b_1_1037
  · exact partG34b_1_1038
  · exact partG34b_1_1039
  · exact partG34b_1_1040
  · exact partG34b_1_1041
  · exact partG34b_1_1042
  · exact partG34b_1_1043
theorem partG34b_1_1029 : check uG34b (2) (0) outG34b ["a","f","ɛ","s","o","o"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="h" := by simpa using hx
  subst x
  exact partG34b_1_1030
theorem partG34b_1_1044 : check uG34b (2) (0) outG34b ["a","f","ɛ","s","o","ʊ"] [["h"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["l"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
end ProductiveSubjectGua
