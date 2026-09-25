import PhonologicalOpacity.Attenuation.Productive.Subject.CertificateParts.G37c_7_070
namespace ProductiveSubjectGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partG37c_7_5687 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","e","∅","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5688 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","e","∅","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5689 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","e","∅","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5690 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","e","∅","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5691 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","e","∅","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5692 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","e","∅","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5693 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","e","∅","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5680 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","e","∅","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_5681
  · exact partG37c_7_5682
  · exact partG37c_7_5683
  · exact partG37c_7_5684
  · exact partG37c_7_5685
  · exact partG37c_7_5686
  · exact partG37c_7_5687
  · exact partG37c_7_5688
  · exact partG37c_7_5689
  · exact partG37c_7_5690
  · exact partG37c_7_5691
  · exact partG37c_7_5692
  · exact partG37c_7_5693
theorem partG37c_7_5679 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","e","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_5680
theorem partG37c_7_5694 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","e","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5695 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","e","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5696 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","e","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5697 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","e","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5698 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","e","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5701 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","e","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5702 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","e","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5703 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","e","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5704 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","e","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5705 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","e","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5706 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","e","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5707 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","e","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5708 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","e","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5709 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","e","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5710 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","e","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5711 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","e","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5712 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","e","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5713 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","e","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5700 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","e","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_5701
  · exact partG37c_7_5702
  · exact partG37c_7_5703
  · exact partG37c_7_5704
  · exact partG37c_7_5705
  · exact partG37c_7_5706
  · exact partG37c_7_5707
  · exact partG37c_7_5708
  · exact partG37c_7_5709
  · exact partG37c_7_5710
  · exact partG37c_7_5711
  · exact partG37c_7_5712
  · exact partG37c_7_5713
theorem partG37c_7_5699 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","e","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_5700
theorem partG37c_7_5714 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","e","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5715 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","e","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5716 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","e","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5717 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","e","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5720 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","e","j","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5721 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","e","j","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5722 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","e","j","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5723 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","e","j","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5724 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","e","j","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5725 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","e","j","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5726 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","e","j","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5727 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","e","j","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5728 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","e","j","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5729 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","e","j","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5730 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","e","j","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5731 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","e","j","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5732 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","e","j","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5719 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","e","j","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_5720
  · exact partG37c_7_5721
  · exact partG37c_7_5722
  · exact partG37c_7_5723
  · exact partG37c_7_5724
  · exact partG37c_7_5725
  · exact partG37c_7_5726
  · exact partG37c_7_5727
  · exact partG37c_7_5728
  · exact partG37c_7_5729
  · exact partG37c_7_5730
  · exact partG37c_7_5731
  · exact partG37c_7_5732
theorem partG37c_7_5718 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","e","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_5719
theorem partG37c_7_5733 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","e","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5678 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_5679
  · exact partG37c_7_5694
  · exact partG37c_7_5695
  · exact partG37c_7_5696
  · exact partG37c_7_5697
  · exact partG37c_7_5698
  · exact partG37c_7_5699
  · exact partG37c_7_5714
  · exact partG37c_7_5715
  · exact partG37c_7_5716
  · exact partG37c_7_5717
  · exact partG37c_7_5718
  · exact partG37c_7_5733
theorem partG37c_7_5737 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɪ","∅","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5738 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɪ","∅","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5739 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɪ","∅","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5740 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɪ","∅","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5741 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɪ","∅","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5742 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɪ","∅","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5743 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɪ","∅","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5744 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɪ","∅","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5745 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɪ","∅","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5746 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɪ","∅","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5747 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɪ","∅","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5748 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɪ","∅","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5749 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɪ","∅","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5736 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɪ","∅","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_5737
  · exact partG37c_7_5738
  · exact partG37c_7_5739
  · exact partG37c_7_5740
  · exact partG37c_7_5741
  · exact partG37c_7_5742
  · exact partG37c_7_5743
  · exact partG37c_7_5744
  · exact partG37c_7_5745
  · exact partG37c_7_5746
  · exact partG37c_7_5747
  · exact partG37c_7_5748
  · exact partG37c_7_5749
theorem partG37c_7_5735 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɪ","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_5736
theorem partG37c_7_5750 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɪ","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5751 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɪ","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5752 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɪ","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5753 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɪ","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5754 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɪ","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5757 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɪ","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5758 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɪ","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5759 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɪ","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5760 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɪ","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5761 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɪ","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5762 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɪ","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5763 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɪ","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5764 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɪ","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5765 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɪ","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5766 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɪ","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
end ProductiveSubjectGua
