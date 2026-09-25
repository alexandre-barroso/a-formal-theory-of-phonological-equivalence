import PhonologicalOpacity.Attenuation.Productive.Subject.CertificateParts.G37c_7_034
namespace ProductiveSubjectGua
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem partG37c_7_2807 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ɔ","j","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2808 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ɔ","j","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2809 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ɔ","j","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2810 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ɔ","j","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2797 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ɔ","j","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_2798
  · exact partG37c_7_2799
  · exact partG37c_7_2800
  · exact partG37c_7_2801
  · exact partG37c_7_2802
  · exact partG37c_7_2803
  · exact partG37c_7_2804
  · exact partG37c_7_2805
  · exact partG37c_7_2806
  · exact partG37c_7_2807
  · exact partG37c_7_2808
  · exact partG37c_7_2809
  · exact partG37c_7_2810
theorem partG37c_7_2796 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ɔ","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_2797
theorem partG37c_7_2811 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ɔ","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2756 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_2757
  · exact partG37c_7_2772
  · exact partG37c_7_2773
  · exact partG37c_7_2774
  · exact partG37c_7_2775
  · exact partG37c_7_2776
  · exact partG37c_7_2777
  · exact partG37c_7_2792
  · exact partG37c_7_2793
  · exact partG37c_7_2794
  · exact partG37c_7_2795
  · exact partG37c_7_2796
  · exact partG37c_7_2811
theorem partG37c_7_2813 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","o","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2814 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","o","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2815 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","o","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2816 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","o","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2817 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","o","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2818 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","o","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2821 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","o","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2822 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","o","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2823 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","o","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2824 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","o","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2825 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","o","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2826 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","o","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2827 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","o","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2828 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","o","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2829 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","o","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2830 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","o","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2831 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","o","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2832 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","o","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2833 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","o","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2820 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","o","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_2821
  · exact partG37c_7_2822
  · exact partG37c_7_2823
  · exact partG37c_7_2824
  · exact partG37c_7_2825
  · exact partG37c_7_2826
  · exact partG37c_7_2827
  · exact partG37c_7_2828
  · exact partG37c_7_2829
  · exact partG37c_7_2830
  · exact partG37c_7_2831
  · exact partG37c_7_2832
  · exact partG37c_7_2833
theorem partG37c_7_2819 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","o","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_2820
theorem partG37c_7_2834 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","o","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2835 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","o","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2836 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","o","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2837 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","o","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2838 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","o","j"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2839 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","o","w"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2812 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_2813
  · exact partG37c_7_2814
  · exact partG37c_7_2815
  · exact partG37c_7_2816
  · exact partG37c_7_2817
  · exact partG37c_7_2818
  · exact partG37c_7_2819
  · exact partG37c_7_2834
  · exact partG37c_7_2835
  · exact partG37c_7_2836
  · exact partG37c_7_2837
  · exact partG37c_7_2838
  · exact partG37c_7_2839
theorem partG37c_7_2843 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ʊ","∅","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2844 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ʊ","∅","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2845 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ʊ","∅","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2846 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ʊ","∅","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2847 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ʊ","∅","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2848 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ʊ","∅","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2849 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ʊ","∅","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2850 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ʊ","∅","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2851 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ʊ","∅","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2852 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ʊ","∅","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2853 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ʊ","∅","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2854 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ʊ","∅","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2855 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ʊ","∅","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2842 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ʊ","∅","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_2843
  · exact partG37c_7_2844
  · exact partG37c_7_2845
  · exact partG37c_7_2846
  · exact partG37c_7_2847
  · exact partG37c_7_2848
  · exact partG37c_7_2849
  · exact partG37c_7_2850
  · exact partG37c_7_2851
  · exact partG37c_7_2852
  · exact partG37c_7_2853
  · exact partG37c_7_2854
  · exact partG37c_7_2855
theorem partG37c_7_2841 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ʊ","∅"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_2842
theorem partG37c_7_2856 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ʊ","a"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2857 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ʊ","ɜ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2858 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ʊ","ɛ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2859 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ʊ","e"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2860 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ʊ","ɪ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2863 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ʊ","i","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2864 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ʊ","i","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2865 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ʊ","i","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2866 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ʊ","i","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2867 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ʊ","i","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2868 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ʊ","i","b","ɪ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2869 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ʊ","i","b","i"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2870 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ʊ","i","b","ɔ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2871 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ʊ","i","b","o"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2872 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ʊ","i","b","ʊ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2873 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ʊ","i","b","u"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2874 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ʊ","i","b","j"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2875 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ʊ","i","b","w"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2862 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ʊ","i","b"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  simp only [List.mem_cons,List.mem_nil_iff,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact partG37c_7_2863
  · exact partG37c_7_2864
  · exact partG37c_7_2865
  · exact partG37c_7_2866
  · exact partG37c_7_2867
  · exact partG37c_7_2868
  · exact partG37c_7_2869
  · exact partG37c_7_2870
  · exact partG37c_7_2871
  · exact partG37c_7_2872
  · exact partG37c_7_2873
  · exact partG37c_7_2874
  · exact partG37c_7_2875
theorem partG37c_7_2861 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ʊ","i"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by
  apply check_of_children
  intro x hx
  have he : x="b" := by simpa using hx
  subst x
  exact partG37c_7_2862
theorem partG37c_7_2876 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ʊ","ɔ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2877 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ʊ","o"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2878 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ʊ","ʊ"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2879 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ʊ","u"] [["b"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"],["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2882 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ʊ","j","b","∅"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2883 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ʊ","j","b","a"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2884 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ʊ","j","b","ɜ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2885 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ʊ","j","b","ɛ"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
theorem partG37c_7_2886 : check uG37c (3) (0) outG37c ["ɔ","tʃ","e","s","ʊ","j","b","e"] [["∅","a","ɜ","ɛ","e","ɪ","i","ɔ","o","ʊ","u","j","w"]] = true := by decide +kernel
end ProductiveSubjectGua
