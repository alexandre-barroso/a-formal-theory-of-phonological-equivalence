import PhonologicalOpacity.Attenuation.Productive.Baseline.CertificateParts.G37c_7_071
namespace ProductiveGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partG37c_7_5767 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɪ","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5768 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɪ","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5769 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɪ","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5756 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɪ","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_5757
  · exact partG37c_7_5758
  · exact partG37c_7_5759
  · exact partG37c_7_5760
  · exact partG37c_7_5761
  · exact partG37c_7_5762
  · exact partG37c_7_5763
  · exact partG37c_7_5764
  · exact partG37c_7_5765
  · exact partG37c_7_5766
  · exact partG37c_7_5767
  · exact partG37c_7_5768
  · exact partG37c_7_5769
theorem partG37c_7_5755 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɪ","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_5756
theorem partG37c_7_5770 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɪ","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5771 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɪ","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5772 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɪ","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5773 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɪ","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5776 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɪ","j","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5777 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɪ","j","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5778 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɪ","j","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5779 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɪ","j","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5780 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɪ","j","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5781 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɪ","j","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5782 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɪ","j","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5783 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɪ","j","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5784 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɪ","j","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5785 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɪ","j","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5786 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɪ","j","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5787 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɪ","j","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5788 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɪ","j","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5775 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɪ","j","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_5776
  · exact partG37c_7_5777
  · exact partG37c_7_5778
  · exact partG37c_7_5779
  · exact partG37c_7_5780
  · exact partG37c_7_5781
  · exact partG37c_7_5782
  · exact partG37c_7_5783
  · exact partG37c_7_5784
  · exact partG37c_7_5785
  · exact partG37c_7_5786
  · exact partG37c_7_5787
  · exact partG37c_7_5788
theorem partG37c_7_5774 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɪ","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_5775
theorem partG37c_7_5789 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɪ","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5734 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_5735
  · exact partG37c_7_5750
  · exact partG37c_7_5751
  · exact partG37c_7_5752
  · exact partG37c_7_5753
  · exact partG37c_7_5754
  · exact partG37c_7_5755
  · exact partG37c_7_5770
  · exact partG37c_7_5771
  · exact partG37c_7_5772
  · exact partG37c_7_5773
  · exact partG37c_7_5774
  · exact partG37c_7_5789
theorem partG37c_7_5793 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","i","∅","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5794 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","i","∅","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5795 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","i","∅","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5796 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","i","∅","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5797 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","i","∅","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5798 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","i","∅","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5799 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","i","∅","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5800 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","i","∅","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5801 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","i","∅","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5802 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","i","∅","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5803 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","i","∅","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5804 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","i","∅","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5805 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","i","∅","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5792 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","i","∅","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_5793
  · exact partG37c_7_5794
  · exact partG37c_7_5795
  · exact partG37c_7_5796
  · exact partG37c_7_5797
  · exact partG37c_7_5798
  · exact partG37c_7_5799
  · exact partG37c_7_5800
  · exact partG37c_7_5801
  · exact partG37c_7_5802
  · exact partG37c_7_5803
  · exact partG37c_7_5804
  · exact partG37c_7_5805
theorem partG37c_7_5791 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","i","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_5792
theorem partG37c_7_5806 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","i","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5807 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","i","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5808 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","i","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5809 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","i","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5810 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","i","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5813 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","i","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5814 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","i","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5815 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","i","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5816 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","i","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5817 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","i","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5818 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","i","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5819 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","i","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5820 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","i","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5821 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","i","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5822 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","i","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5823 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","i","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5824 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","i","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5825 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","i","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5812 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","i","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_5813
  · exact partG37c_7_5814
  · exact partG37c_7_5815
  · exact partG37c_7_5816
  · exact partG37c_7_5817
  · exact partG37c_7_5818
  · exact partG37c_7_5819
  · exact partG37c_7_5820
  · exact partG37c_7_5821
  · exact partG37c_7_5822
  · exact partG37c_7_5823
  · exact partG37c_7_5824
  · exact partG37c_7_5825
theorem partG37c_7_5811 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","i","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_5812
theorem partG37c_7_5826 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","i","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5827 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","i","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5828 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","i","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5829 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","i","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5832 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","i","j","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5833 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","i","j","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5834 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","i","j","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5835 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","i","j","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5836 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","i","j","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5837 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","i","j","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5838 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","i","j","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5839 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","i","j","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5840 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","i","j","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5841 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","i","j","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5842 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","i","j","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5843 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","i","j","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5844 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","i","j","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_5831 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","i","j","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_5832
  · exact partG37c_7_5833
  · exact partG37c_7_5834
  · exact partG37c_7_5835
  · exact partG37c_7_5836
  · exact partG37c_7_5837
  · exact partG37c_7_5838
  · exact partG37c_7_5839
  · exact partG37c_7_5840
  · exact partG37c_7_5841
  · exact partG37c_7_5842
  · exact partG37c_7_5843
  · exact partG37c_7_5844
theorem partG37c_7_5830 : check uG37c (3) (0) outG37c ["ɔ","tʃ","ʊ","s","i","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_5831
end ProductiveGua
