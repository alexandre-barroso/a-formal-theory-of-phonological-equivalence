import PhonologicalOpacity.Attenuation.Productive.Subject.CertificateParts.G37c_7_095
namespace ProductiveSubjectGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partG37c_7_7687 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","w","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7688 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","w","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7689 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","w","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7690 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","w","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7691 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","w","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7692 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","w","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7693 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","w","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7680 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","w","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_7681
  · exact partG37c_7_7682
  · exact partG37c_7_7683
  · exact partG37c_7_7684
  · exact partG37c_7_7685
  · exact partG37c_7_7686
  · exact partG37c_7_7687
  · exact partG37c_7_7688
  · exact partG37c_7_7689
  · exact partG37c_7_7690
  · exact partG37c_7_7691
  · exact partG37c_7_7692
  · exact partG37c_7_7693
theorem partG37c_7_7679 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","w","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_7680
theorem partG37c_7_7694 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","w","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7695 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","w","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7696 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","w","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7697 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","w","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7698 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","w","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7699 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","w","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_7672 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_7673
  · exact partG37c_7_7674
  · exact partG37c_7_7675
  · exact partG37c_7_7676
  · exact partG37c_7_7677
  · exact partG37c_7_7678
  · exact partG37c_7_7679
  · exact partG37c_7_7694
  · exact partG37c_7_7695
  · exact partG37c_7_7696
  · exact partG37c_7_7697
  · exact partG37c_7_7698
  · exact partG37c_7_7699
theorem partG37c_7_7195 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w","s"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_7196
  · exact partG37c_7_7224
  · exact partG37c_7_7280
  · exact partG37c_7_7308
  · exact partG37c_7_7364
  · exact partG37c_7_7392
  · exact partG37c_7_7448
  · exact partG37c_7_7476
  · exact partG37c_7_7532
  · exact partG37c_7_7560
  · exact partG37c_7_7616
  · exact partG37c_7_7644
  · exact partG37c_7_7672
theorem partG37c_7_7194 : check uG37c (3) (0) outG37c ["ɔ","tʃ","w"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="s" := by simpa using hx
  subst x
  exact partG37c_7_7195
theorem partG37c_7_1 : check uG37c (3) (0) outG37c ["ɔ","tʃ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_2
  · exact partG37c_7_508
  · exact partG37c_7_1238
  · exact partG37c_7_1744
  · exact partG37c_7_2474
  · exact partG37c_7_2980
  · exact partG37c_7_3710
  · exact partG37c_7_4216
  · exact partG37c_7_4946
  · exact partG37c_7_5452
  · exact partG37c_7_6182
  · exact partG37c_7_6688
  · exact partG37c_7_7194
theorem checkedG37c_7 : check uG37c (3) (0) outG37c ["ɔ"] [["tʃ"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="tʃ" := by simpa using hx
  subst x
  exact partG37c_7_1
end ProductiveSubjectGua
