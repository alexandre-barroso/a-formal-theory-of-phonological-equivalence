import PhonologicalOpacity.Attenuation.Productive.Subject.CertificateParts.OR38_1_009
namespace ProductiveSubjectGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partOR38_1_805 : check uOR38 (4) (-2) outOR38 ["a","tʃ","i","s","a","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_806 : check uOR38 (4) (-2) outOR38 ["a","tʃ","i","s","a","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_807 : check uOR38 (4) (-2) outOR38 ["a","tʃ","i","s","a","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_808 : check uOR38 (4) (-2) outOR38 ["a","tʃ","i","s","a","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_809 : check uOR38 (4) (-2) outOR38 ["a","tʃ","i","s","a","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_810 : check uOR38 (4) (-2) outOR38 ["a","tʃ","i","s","a","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_797 : check uOR38 (4) (-2) outOR38 ["a","tʃ","i","s","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_798
  · exact partOR38_1_799
  · exact partOR38_1_800
  · exact partOR38_1_801
  · exact partOR38_1_802
  · exact partOR38_1_803
  · exact partOR38_1_804
  · exact partOR38_1_805
  · exact partOR38_1_806
  · exact partOR38_1_807
  · exact partOR38_1_808
  · exact partOR38_1_809
  · exact partOR38_1_810
theorem partOR38_1_811 : check uOR38 (4) (-2) outOR38 ["a","tʃ","i","s","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_813 : check uOR38 (4) (-2) outOR38 ["a","tʃ","i","s","ɛ","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_814 : check uOR38 (4) (-2) outOR38 ["a","tʃ","i","s","ɛ","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_815 : check uOR38 (4) (-2) outOR38 ["a","tʃ","i","s","ɛ","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_816 : check uOR38 (4) (-2) outOR38 ["a","tʃ","i","s","ɛ","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_817 : check uOR38 (4) (-2) outOR38 ["a","tʃ","i","s","ɛ","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_818 : check uOR38 (4) (-2) outOR38 ["a","tʃ","i","s","ɛ","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_819 : check uOR38 (4) (-2) outOR38 ["a","tʃ","i","s","ɛ","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_820 : check uOR38 (4) (-2) outOR38 ["a","tʃ","i","s","ɛ","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_821 : check uOR38 (4) (-2) outOR38 ["a","tʃ","i","s","ɛ","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_822 : check uOR38 (4) (-2) outOR38 ["a","tʃ","i","s","ɛ","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_823 : check uOR38 (4) (-2) outOR38 ["a","tʃ","i","s","ɛ","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_824 : check uOR38 (4) (-2) outOR38 ["a","tʃ","i","s","ɛ","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_825 : check uOR38 (4) (-2) outOR38 ["a","tʃ","i","s","ɛ","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_812 : check uOR38 (4) (-2) outOR38 ["a","tʃ","i","s","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_813
  · exact partOR38_1_814
  · exact partOR38_1_815
  · exact partOR38_1_816
  · exact partOR38_1_817
  · exact partOR38_1_818
  · exact partOR38_1_819
  · exact partOR38_1_820
  · exact partOR38_1_821
  · exact partOR38_1_822
  · exact partOR38_1_823
  · exact partOR38_1_824
  · exact partOR38_1_825
theorem partOR38_1_826 : check uOR38 (4) (-2) outOR38 ["a","tʃ","i","s","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_828 : check uOR38 (4) (-2) outOR38 ["a","tʃ","i","s","ɪ","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_829 : check uOR38 (4) (-2) outOR38 ["a","tʃ","i","s","ɪ","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_830 : check uOR38 (4) (-2) outOR38 ["a","tʃ","i","s","ɪ","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_831 : check uOR38 (4) (-2) outOR38 ["a","tʃ","i","s","ɪ","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_832 : check uOR38 (4) (-2) outOR38 ["a","tʃ","i","s","ɪ","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_833 : check uOR38 (4) (-2) outOR38 ["a","tʃ","i","s","ɪ","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_834 : check uOR38 (4) (-2) outOR38 ["a","tʃ","i","s","ɪ","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_835 : check uOR38 (4) (-2) outOR38 ["a","tʃ","i","s","ɪ","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_836 : check uOR38 (4) (-2) outOR38 ["a","tʃ","i","s","ɪ","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_837 : check uOR38 (4) (-2) outOR38 ["a","tʃ","i","s","ɪ","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_838 : check uOR38 (4) (-2) outOR38 ["a","tʃ","i","s","ɪ","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_839 : check uOR38 (4) (-2) outOR38 ["a","tʃ","i","s","ɪ","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_840 : check uOR38 (4) (-2) outOR38 ["a","tʃ","i","s","ɪ","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_827 : check uOR38 (4) (-2) outOR38 ["a","tʃ","i","s","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_828
  · exact partOR38_1_829
  · exact partOR38_1_830
  · exact partOR38_1_831
  · exact partOR38_1_832
  · exact partOR38_1_833
  · exact partOR38_1_834
  · exact partOR38_1_835
  · exact partOR38_1_836
  · exact partOR38_1_837
  · exact partOR38_1_838
  · exact partOR38_1_839
  · exact partOR38_1_840
theorem partOR38_1_841 : check uOR38 (4) (-2) outOR38 ["a","tʃ","i","s","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_843 : check uOR38 (4) (-2) outOR38 ["a","tʃ","i","s","ɔ","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_844 : check uOR38 (4) (-2) outOR38 ["a","tʃ","i","s","ɔ","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_845 : check uOR38 (4) (-2) outOR38 ["a","tʃ","i","s","ɔ","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_846 : check uOR38 (4) (-2) outOR38 ["a","tʃ","i","s","ɔ","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_847 : check uOR38 (4) (-2) outOR38 ["a","tʃ","i","s","ɔ","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_848 : check uOR38 (4) (-2) outOR38 ["a","tʃ","i","s","ɔ","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_849 : check uOR38 (4) (-2) outOR38 ["a","tʃ","i","s","ɔ","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_850 : check uOR38 (4) (-2) outOR38 ["a","tʃ","i","s","ɔ","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_851 : check uOR38 (4) (-2) outOR38 ["a","tʃ","i","s","ɔ","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_852 : check uOR38 (4) (-2) outOR38 ["a","tʃ","i","s","ɔ","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_853 : check uOR38 (4) (-2) outOR38 ["a","tʃ","i","s","ɔ","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_854 : check uOR38 (4) (-2) outOR38 ["a","tʃ","i","s","ɔ","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_855 : check uOR38 (4) (-2) outOR38 ["a","tʃ","i","s","ɔ","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_842 : check uOR38 (4) (-2) outOR38 ["a","tʃ","i","s","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_843
  · exact partOR38_1_844
  · exact partOR38_1_845
  · exact partOR38_1_846
  · exact partOR38_1_847
  · exact partOR38_1_848
  · exact partOR38_1_849
  · exact partOR38_1_850
  · exact partOR38_1_851
  · exact partOR38_1_852
  · exact partOR38_1_853
  · exact partOR38_1_854
  · exact partOR38_1_855
theorem partOR38_1_856 : check uOR38 (4) (-2) outOR38 ["a","tʃ","i","s","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_858 : check uOR38 (4) (-2) outOR38 ["a","tʃ","i","s","ʊ","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_859 : check uOR38 (4) (-2) outOR38 ["a","tʃ","i","s","ʊ","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_860 : check uOR38 (4) (-2) outOR38 ["a","tʃ","i","s","ʊ","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_861 : check uOR38 (4) (-2) outOR38 ["a","tʃ","i","s","ʊ","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_862 : check uOR38 (4) (-2) outOR38 ["a","tʃ","i","s","ʊ","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_863 : check uOR38 (4) (-2) outOR38 ["a","tʃ","i","s","ʊ","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_864 : check uOR38 (4) (-2) outOR38 ["a","tʃ","i","s","ʊ","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_865 : check uOR38 (4) (-2) outOR38 ["a","tʃ","i","s","ʊ","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_866 : check uOR38 (4) (-2) outOR38 ["a","tʃ","i","s","ʊ","o"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_867 : check uOR38 (4) (-2) outOR38 ["a","tʃ","i","s","ʊ","ʊ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_868 : check uOR38 (4) (-2) outOR38 ["a","tʃ","i","s","ʊ","u"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_869 : check uOR38 (4) (-2) outOR38 ["a","tʃ","i","s","ʊ","j"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_870 : check uOR38 (4) (-2) outOR38 ["a","tʃ","i","s","ʊ","w"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_857 : check uOR38 (4) (-2) outOR38 ["a","tʃ","i","s","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_858
  · exact partOR38_1_859
  · exact partOR38_1_860
  · exact partOR38_1_861
  · exact partOR38_1_862
  · exact partOR38_1_863
  · exact partOR38_1_864
  · exact partOR38_1_865
  · exact partOR38_1_866
  · exact partOR38_1_867
  · exact partOR38_1_868
  · exact partOR38_1_869
  · exact partOR38_1_870
theorem partOR38_1_871 : check uOR38 (4) (-2) outOR38 ["a","tʃ","i","s","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_872 : check uOR38 (4) (-2) outOR38 ["a","tʃ","i","s","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_873 : check uOR38 (4) (-2) outOR38 ["a","tʃ","i","s","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_795 : check uOR38 (4) (-2) outOR38 ["a","tʃ","i","s"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partOR38_1_796
  · exact partOR38_1_797
  · exact partOR38_1_811
  · exact partOR38_1_812
  · exact partOR38_1_826
  · exact partOR38_1_827
  · exact partOR38_1_841
  · exact partOR38_1_842
  · exact partOR38_1_856
  · exact partOR38_1_857
  · exact partOR38_1_871
  · exact partOR38_1_872
  · exact partOR38_1_873
theorem partOR38_1_794 : check uOR38 (4) (-2) outOR38 ["a","tʃ","i"] [["s"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="s" := by simpa using hx
  subst x
  exact partOR38_1_795
theorem partOR38_1_877 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","∅","∅"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_878 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","∅","a"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_879 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","∅","ɜ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_880 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","∅","ɛ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_881 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","∅","e"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_882 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","∅","ɪ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_883 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","∅","i"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partOR38_1_884 : check uOR38 (4) (-2) outOR38 ["a","tʃ","ɔ","s","∅","ɔ"] [["k"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
end ProductiveSubjectGua
