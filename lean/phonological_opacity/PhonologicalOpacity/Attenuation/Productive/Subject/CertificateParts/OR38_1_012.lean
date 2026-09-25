import PhonologicalOpacity.Attenuation.Productive.Subject.CertificateParts.OR38_1_011
namespace ProductiveSubjectGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partOR38_1_965 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","i","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_966 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","i","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_967 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","i","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_968 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","i","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_969 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","i","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_970 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","i","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_971 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","i","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_972 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","i","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_973 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","i","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_960 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_961
  · exact partOR38_1_962
  · exact partOR38_1_963
  · exact partOR38_1_964
  · exact partOR38_1_965
  · exact partOR38_1_966
  · exact partOR38_1_967
  · exact partOR38_1_968
  · exact partOR38_1_969
  · exact partOR38_1_970
  · exact partOR38_1_971
  · exact partOR38_1_972
  · exact partOR38_1_973
theorem partOR38_1_975 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","ɔ","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_976 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","ɔ","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_977 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","ɔ","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_978 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","ɔ","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_979 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","ɔ","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_980 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","ɔ","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_981 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","ɔ","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_982 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","ɔ","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_983 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","ɔ","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_984 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","ɔ","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_985 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","ɔ","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_986 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","ɔ","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_987 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","ɔ","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_974 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_975
  · exact partOR38_1_976
  · exact partOR38_1_977
  · exact partOR38_1_978
  · exact partOR38_1_979
  · exact partOR38_1_980
  · exact partOR38_1_981
  · exact partOR38_1_982
  · exact partOR38_1_983
  · exact partOR38_1_984
  · exact partOR38_1_985
  · exact partOR38_1_986
  · exact partOR38_1_987
theorem partOR38_1_989 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","o","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_990 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","o","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_991 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","o","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_992 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","o","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_993 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","o","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_994 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","o","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_995 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","o","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_996 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","o","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_997 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","o","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_998 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","o","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_999 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","o","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1000 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","o","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1001 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","o","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_988 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_989
  · exact partOR38_1_990
  · exact partOR38_1_991
  · exact partOR38_1_992
  · exact partOR38_1_993
  · exact partOR38_1_994
  · exact partOR38_1_995
  · exact partOR38_1_996
  · exact partOR38_1_997
  · exact partOR38_1_998
  · exact partOR38_1_999
  · exact partOR38_1_1000
  · exact partOR38_1_1001
theorem partOR38_1_1003 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","ʊ","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1004 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","ʊ","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1005 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","ʊ","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1006 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","ʊ","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1007 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","ʊ","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1008 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","ʊ","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1009 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","ʊ","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1010 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","ʊ","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1011 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","ʊ","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1012 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","ʊ","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1013 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","ʊ","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1014 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","ʊ","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1015 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","ʊ","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1002 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_1003
  · exact partOR38_1_1004
  · exact partOR38_1_1005
  · exact partOR38_1_1006
  · exact partOR38_1_1007
  · exact partOR38_1_1008
  · exact partOR38_1_1009
  · exact partOR38_1_1010
  · exact partOR38_1_1011
  · exact partOR38_1_1012
  · exact partOR38_1_1013
  · exact partOR38_1_1014
  · exact partOR38_1_1015
theorem partOR38_1_1017 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","u","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1018 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","u","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1019 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","u","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1020 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","u","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1021 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","u","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1022 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","u","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1023 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","u","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1024 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","u","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1025 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","u","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1026 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","u","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1027 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","u","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1028 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","u","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1029 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","u","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1016 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_1017
  · exact partOR38_1_1018
  · exact partOR38_1_1019
  · exact partOR38_1_1020
  · exact partOR38_1_1021
  · exact partOR38_1_1022
  · exact partOR38_1_1023
  · exact partOR38_1_1024
  · exact partOR38_1_1025
  · exact partOR38_1_1026
  · exact partOR38_1_1027
  · exact partOR38_1_1028
  · exact partOR38_1_1029
theorem partOR38_1_1031 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","j","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1032 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","j","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1033 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","j","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1034 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","j","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1035 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","j","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1036 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","j","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1037 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","j","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1038 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","j","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1039 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","j","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1040 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","j","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1041 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","j","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1042 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","j","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1043 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","j","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_1030 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_1031
  · exact partOR38_1_1032
  · exact partOR38_1_1033
  · exact partOR38_1_1034
  · exact partOR38_1_1035
  · exact partOR38_1_1036
  · exact partOR38_1_1037
  · exact partOR38_1_1038
  · exact partOR38_1_1039
  · exact partOR38_1_1040
  · exact partOR38_1_1041
  · exact partOR38_1_1042
  · exact partOR38_1_1043
end ProductiveSubjectGua
